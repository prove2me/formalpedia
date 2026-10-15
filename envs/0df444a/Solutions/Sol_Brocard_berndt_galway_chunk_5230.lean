-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5230
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:10:52.535991+00:00
-- url     : https://prove2.me/submissions/975be4cb-4432-424c-9ecc-cf5234d6fe43

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 940467625 ≤ n < 940647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 940468875 1250 940467625 940467641
    0x30a0c030f06090e0c030304060f120f020a090e1e010501081003020907020a031202042103021c0c060b0f010e3303010305060c0c1005060f0405010b0a020708240613 72
    0x15031350348503141989942c040201c941d8085055009516003410f02d82e02604012104105608105403208140c0c5c28031156000810f20700c100c104c0641d1075480c6080064941c58032400b071450000865000508054501200620302c40c44289810103540d00f490011504440000c1c041a6003541c604030000050311a10b030510f1080c001790f030242c8591441d80c503000b81004c0740c824028420a0040c001808002e03140c0b0600070040c004000c540c80706614038681a03040502c009500e00620001108150002d5000400e0b4030211b0b214000c108840030700300080048841404c40007034002080c14889640e182072030f111400d0b820500e0104601c13400140401203101040c02e40c420408030750048010800c000c2d04124081e00701086c555441c0c1072001012945a03600c2c1c0c584940150141c450f0302245e115110350740125201000a4130074030040d81c45200d844401e912003105100180b2590b0720000c1d050f80b01295111101c6070355400c0e9035501050100b800c80103030020301001e0f4040382d0b5040760301c5159883d1080100c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 940470125 1250 940468875 940468889
    0x103090c0b0405040b0105040302030d050702220203160507120e030a02042c28230106060207080325111f08070809031b0304180f1a06030a0c030f06 65
    0xb503141d040105010980e035001c04031a05100081c0000e0005a602090300306903a44a45052500d900c0a400041c2000c2c41e49009040c40c1d9188680c005c0701c42465400662140012203130349039004c48608000c0314288a02c100142c107040203071000d640124800ca1011054900050440707070210301540004040701c661a07122240105060100c841e014440d03014086c040c00004041c007400d028050030300d2481d4800000c000b4001c1c3c8000060b0b8100148203580c13030f503201d020a0f42c802c040d0500c04580341c0248480d0040704058811100001070a00b0000308840e54841554003200c000c01f00c0007002202d002034117804581d49840c64880e102c103512000307110110440c4c1c030989026101940c29014000800c058412403c000a581c1000f07062200042281d03250109800d030b20400740c0c4203143d158214002d81d0440e602041415a5000040071940c004a55280b110b0300c04000c900192184144104000701006421090620010b03084502546c00850068124100407418508070056a400c81d00981c00240b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 940471375 1250 940470125 940470127
    0xc061e090b01050303090307030b0a140106081e161b020415031101171f08070609061215120c0b031003031d0603011401050c070b0c1c0801050f0103090c0b 68
    0x200c1840300741d0300464010681a40950700d46294a00400e13103602d03081c000506501981404030341e80100a43c40500380b03020b003481c00d003410b58640d00010207501d4183d42152580001c0c105a82007001d021401c43c3c0541c1602a4020005550400980e00100c0440402400c50284408038016865a00810070315010142c9580d0b00780e8250f2415100701ea0201d814141080600c0c0c090101b0b40d9506003039540c00043d19036150658080e0200c58140c0c3c1d1105030050240b5010309200080c01e1500003401e4000d84405803940e04500c1c100200311000c030b40c2c02c0c40c850001649195020449030703180041c201d00e81030207060f481411540306c200c2e0301c04580c800d450b03440d494402c1d442c00704141980000126400081c04d2900b14041160000042d43c2c0e00041c020f18140303000040101a090b80640100c40d0800c20700c1c003e903030140c2e5071000d00403581c1c0c00050b840c0945e802074074042d51003401d8080004020250701d4a500e18140d0031301050180100c03100c1403280c14142c0d00c46d024000b1440031409030005010006002e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 940472625 1250 940471375 940471391
    0x1051c0302120f0910021b01050f130611070905040b27011e06270f0204120c03020a0509190b04020912060603012904050403171f060c080a0c061e 64
    0xc0002038080300511130454000c80b45001d034000c01f501c0b05501610b82480c016845841d83d00c61000207210308031261100400c09800042c0994200d021005c000369000c042d2000385030703a11518025a001158020203500542c00040d4020760f0155484a0441840c010308500040c04030400d403c45110007034484801d0362203440c4c100d01010500416001d002c0780032607960101070b441c0c21031034404440c0001c0454192595418080d40340350394140c82c0204020026001440c5080c101100300501c1d901050307009081074540401c01d420034140d864091103081ba5166010710405440c20300a0401d21b00d001d42c419002c11148129540b007c580d4015501c004000e00b82e01c1c20480201400c440210703181841b000c40c2401624056a00100c5070003101405a41c00b103101e98a901c0c040f154040740701031240d006d140c03840a101a0b08204803884100240240541c1ca810f81c58400680b0500701d0306a004040e040d04001a402d1070f4462204540018490400442c40074611001248480b41140b0341c091440d0b40c0b0850303 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 940473875 1250 940472625 940472629
    0x408160302030616080a0e25091803020a0f0201031d162102090a06030b01120c08010209060910090b0c1f0b090708041104091109060901051c0302120f09 67
    0x1106400c40d0713515015140303482c940708000d4000711000b01540e1481e40e540d0707070310300d0200700501070380015040300c1c2e0200400b003820050003900e5041e5802200c1002d45440c5529512003060070403030721030a8040d001450f0100d0702ea80c0d0361401e111407006c101d0415448150703081407000c2d000031000010115030050030241c1c0e03024543c1903500e02c265000300201c29840100882c08010f03602c4031071400341c041e5a850b6290340c40703a0f06040641016800180149000c1000060403001d1035401d500d554485d900d0082010b40d038044840c00e070300603011410383c090300412030507c4500d05800c1200721441e05052102d034440c1e5520301d0341800c2d007111045182603008085424602c41c0d40b48030400108405480400071260544041050018000c2941e0103126910011405201d071425251500c000010002e02507a0018135140024844d030683ca68040c248a00108107580b41003201103044c3c4038003600c4c4400101d01d140468880e04814001078065004042030f2082144404000342905520f0050715a90b84040d441 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 940475125 1250 940473875 940473883
    0x307030c1104060b0a030903090f060207030b090601051c02010c020d0506060a0f121101090320010e090432060108070e0f07050d05060406180f1508150a02040816030203 74
    0x1e04a100390f2400d9014002c090480090380c6001c59546000600714045180548041c1003e810806007000e80c2c8000190050380001d000040c1c80c81070700c1c1c2c3c200b59118880070707907615007080c040c1d903a002c40325492106c815105064403603005801491314046400e00b94011414100094000340c5458005d03a042003941d08141400d1001401e076554449009072400401000b00d03040e003000188400c04440c102601680b040c1c40100143da00b1501012030102d0008031904541101c684072400305d403440800404a1a0a01907940b0a0b86c11600011750503544942c0d4010340c803c402c0e80c49111000104004035043d030104440d5010b40983c1c0c00505a4500700075140d8038180d0000c0400f103500744510b0030004035070350150954100c1c1c400c610022402d52600d8000601424242c0c000391105108142e8495440d229038010786020600d00b88100411100c0d05c2d501e58255490740101801644091f14480d1498844458035a02c480d01c40001428036807140300603805d12041140310071140c1c00c100f10510551030140 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 940476375 1250 940475125 940475153
    0x303011e03020603041b1d0a0b031501092306010c1202120417010b091306050411060d02120907050d08090f0904080408010e06011208030403300f0b030a02120304080307030c 76
    0xb0842c8840d501c8401f40300c0d8a240d00040003096403640b61010622075442c1001000e05007454001c62491640e1180385220040400c4100000da00b008a43c074501c5145450307648a0103010184d640c200880455103403011200c10540301e020071445854440d450030300e60000a08090f100c03440c80e01201c0403c3c2c20049080d00c90004c08588260000820310140030007844c1d84840c1d855000c900031440340d49a040c07820500c0038051180d0780240001030242060326050303008040d80005a010364003c0d80321b54040c50350390109801769035080000078a060020581080103410300050040070740c5092000780001c1030480f2010740d4202c86203103002c10b0a111070002801510400ca092600414081d031501070424000d8020701c101410f1441d0000200c4d061600c2500c50143c0c02e02d0406d420342040d240300443c14410140c00880004144c5006082d00e40004240101000f003900103005002641d01038081041405641c6210075152004002c0014100018405042c3c00c074080c5e110050102801e0410b1513135243c1c0c034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 940477625 1250 940476375 940476389
    0x12080403320d0b0a15091a0408060703020a08370204051201090b180c0d02120105100f440105010b0a080c1e09010314011e0b0a020303011e03020603041b 67
    0x35442c124212540a00c0d140201c40c600d410503050787d030810520070310a2050343c109212900460b8104001550107400421a0b055550796080c6181d46620b06140c0743c2d240d40d000104004207000628505d50071803030380310004071041303000140b529030b07903500107140000709002d00d00080c0d440c0c514640910410400150b44540500c441059407100d54030701e1503d420f20b20049034484c0c0c1201c0052419134480850004401c04000002c10081c00c0080b2040a049120302c2003040102110342c2c0824550301724940d00120b40c9480440c100030f02c10f8240010b901124410792298000340d8000011074242d000d000d400c1c0201304060b650365503405036130030041105000a1041c41011010050311484e820024041c50400c84400c10558075204c00d036004902400c0c00c500d4103401006104004500c0300c80212820034072042c4441c6494a042e40d0b034595840a020b54059000543c0041c00100000503003056155000440701205c0311000d6141e500055071500309403000d03101b1419110750100800b0404699801901c50 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 940478875 1250 940477625 940477649
    0xc0809030d0903030209060313150e0c10020f0d0e1e010c0605063001050a06030209160c1703060114130b07080909011212080403320d0b0a 61
    0x1062089a6078460322051921482d60341080c1c406041c030030350545e1124100146450f5483c00c01104c002e4802c8248030050fa5608035550160306a500503104c2c40e004400544040c0080364125030400c074031074400742c8050040d805054030300032031490140141c05005540d9200e024020403a541031048501c400703c440c1010510301410880a80c1e0010980f04403694041004038499641d04041640c0c007003091003040340241141c05000c2c020003e4615003d403c48610001c00c803e541d00340c202816a0b46510020f504039824102045481624940e41c0d54a56040e00300708042c0c1c1c82d240d5401d140f4003a0031504190104000c024132106691051424200380e50a600550904262168076074810b60940316002106a00155134010405144285c0d6501d010043c10070f6103540e03480c5220701031000b064100b111020506044104010b00800800f40215010382d00ea03c41160110381e8940c0300c0c10f00801080c000264001428096040c2c14014003c01c4000403010410386160803d01c8106d0342c16800c00c44e440e01d1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 940480125 1250 940478875 940478881
    0x5031803030f030f07090b1b100504210309150614100e0418020405090a2306180c03010911040c0203160305090105070f03032306130c020f0715030c08 66
    0x1400080d80c1c0c0210f1303100340b40c8a83e81c542041c00d80d8000f910f58484034080d06c1c04146030680d031070411955141c07040d00700c040e140d48036020f0500c83c088420840f0300809004100e0500c48840061000b980034410950800040c003d0103070300c0d0102644c00c0004803e0000742c030f40b001404804115080810031080558440b00030408185000d084140c3e0703022001d0245d5596101d48414600c40700d0383ca8501c0e40c001e4020007290a00b0706010751503a01842d81030354400361084900080200501141071010420300c040d116a8031030009090f4400924030141a551087c00c0c0f850700107540c203200f4402c10a21039024050411100f80c280300075100c1483e00d8506641080c042115040c0380000311072001581480e21942d1044c030640140d4031406000409403d0b0701e501c6000c48105501503108080116540e028803240c0b0241c4160a6600f40d0704440e9681c1001210452055110f2140c00031002e002c07141c01035038151154049105d24001041d84886d64041044402178820740d094401d100b5900c0c62031070284441d00e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 940481375 1250 940480125 940480147
    0x30e030a0b0f1f0305010b04060b0a050a1b1b060e0a1a030402040e060901051b030c07030c080d020a020309270721020706090b0109061206050c0d090503180303 70
    0x7410061208200800c41c1e4000f0780c06150540110400e85501100c0c18009a1607042c824001e04d8100c03183c41c052454a2000f294401200094402c03841c8030350303912490600040c40c21100d41c01508040900040c403c1c01036000290b500008501c64480191040b81c07091410100424520007000410302452841ea41484820760240210070394011a18245540c3e448901c0803400410f00d8201c00400ca008803420301004120642005010306011308450305041c0122030b215401c0d1105540c4480340c00020042c1200280c09502040c1d2141e019412150030320f503d85020700e090b81e11408010340140c00024442c415403409010140b800042c00052600401c0c1142405594000142050041c45000751461018a400d5880064030f000004419903e0f0410340c80c10b180900b6080d0400c0b50f547e55400c001084050a078071130501201d86503105a44c01c0c0945882e000000e18028010152050041005201c1045503001d04803049115100640c2e580214000340444c001054202c02d100f50010082e1002d48 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 940482625 1250 940481375 940481393
    0x102150105060f0313290c0a0801260303010f0e0108070302010507080f0903011401081506090a1806020a090509100e041e02150301210c0909031b080403030e030a 71
    0x840c2d00d08543d10394940751030f45500e40c000005200202940790f900c0064440d01000380f244103c0c4030a50040354001d032030f5140548002c0c0290009080080c2c0c3c0c8100401ca5491285a10101c804012024003503400782030780e170281954400d070000a021015402d041000b0010f014029004041c0b03d07000c0d1a0b96800d55000901c2c6200d00607015080320f01c08505152080000c1c0211009480000e0080001c90305100c00c1c0107550100348039050050190802c10200c45041c219424440c2a00800000041c1d95500b181c900400e00001500d468004c068035580000f051032009080450190311610705251400f0304110100400801c442c403040110780c0100b200038900925a600282c4c040c2c00c41c2d10216241c048921070060240b0040c0d40403d605494402d140c2640d00154140c41071000c7c8a92440c0e16585403400c0440301080007130000c2d6010400f00a03103c0f90340d00a010061103841c002c20108559141001069001c00084d601240001010410540c000f031038100c4c1d5810a6028146c0c2c1001b940710041340c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 940483875 1250 940482625 940482637
    0xe062416020109090501240e090c30041209080c01050304140a230f07180b030d020f0118150f060812130503071a2a0c010215010506 58
    0x15a400900098085a02031066000071308a061420001da6135201c0382c608140b103040ba084410410b018030f820014511410b6003903203241340600a07501c0c1c0e4582002c42c60075580031a100b5555080f51100703800c0c0ca590054441120401131401c01007440c10141410701c0760a50000c0c00805001d00c20324100311281c0042783c038076604002400c116489648900748106008050076011070a0301464a4510421050743c2c600107120711600c0a9111640d00090307050703502c1c202e000040e2001e6220394010880e01c50720340210b4004401d078000100750984040b010074a0a40b16500700c00150b0001442c0c81c006400900c125100300801502c0c0701000d44180c0c4811612a0b544500c0030340183c1c036007404c602c8c01042a045400140214000c4501107028900c0014181d002080c1240b072020b50220000381038500041d03100c041c4c418030141d02c2c888010140900c0040d61003605145048408503802070341100c1d848104141419102d4041c02c030411400d0300090404041e69110741c0d810300840d00500040c2c91302010740d0a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 940485125 1250 940483875 940483897
    0x3020705060112231005150a0504090503070c0b0703021002180f011107140a0503060402150c0a0b0a06180603030504090902030312010801060512030c190f0b010e0624 73
    0x48040280c1007014a9110a0513080c00b00c3c1e43c2c0712064135681c0c400040360001c005031a6410070054540c0a243c0000190f01140c007540a01d21b02414802c0c0d113055481004034074868400c5078038000307241d80c072640d074030100d0b42c022510080301241031030501d5014841c8040b0510091011442d02119081801500c0068450307913000780b04568064a45902489500c00007515410484210783da070b031070000c0341d80024040158000e040b40000000e1600b400514a4010b43c6e00a00c0e1121140ca01e00200c030036034110354401c40785482503070740708030204201807100b9001c0c500400b404110142844110b1910190014419170140d16006041003c2940001034034281d821400700440c0c51012400068a94050160104d420120140000130b80b860150700c03101c2200c609884003007048601c0c40409481c1d000300010f82504d13800c0288600e801980024290741510700c5004010042c00c41521480d413510b401b41c10103100c0142032001d0042c245441c2d165000205145c1803424034801c1174800c00c034894000d11138040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 940486375 1250 940485125 940485149
    0x3020703201f050c060c0c0f0f060c0f13141206040c091d011a041b0c1212050708010302030705030313031202010e030d050105040f0203220312060f15030207050601 72
    0x41c002d4410700403540668030500c03c4078194104903800700440d5000304c00781e0701c09100f00d4090040000d000301d85680002210405045265201001e0041c19401691804d0189030204020a0f929090007848405003a07180c1c0080d1040050741c00740544407026031f8103484154013180401002440c2c0c1d0100400703a80448c1c0d0b0101e4404040402502c01c1c00c1c042c074140305076500300754840c0703901c0c45521006203000c04115001d01407004112258a0880900308541e030000b03844403800c0c0c02141c5c01d910302e4401a00a49410505a120001c1e04401c40e0005e4941100180c240307801001980707000c015440280c0011405580b425440103012a0014114030005100b4200350f410b1184460007944070106450482c4140c0e5580c2c8030944503e03004000034081c452141d4036000e4a01d010003428400d881c4100c0d0304445001020f00409074010340f200180100f241000302c0460440500c04032402a040140001c503000c003161800e1010315546030401881030300400d44103105803c00310303100040351411500c00d4100c0b8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 940487625 1250 940486375 940486429
    0xf0e031909091406030d030e030315010504090212090705031222030c030f03140906070b06190801090611070309060c050c062a0c0303040621090302070320 68
    0x361140260750b44011289460400c0a0a4548010300c219200789800c5041e10030a0f200c0c5442602252100050709072290700620000b820f105091020180750320050422900f000d50b14019142a039200c10042401a01840140200000200441300244c801180502000d024412410056005034a4051440c10040041c00079601c080200c1e00042c540100888429a4032380c1419100c000c04132404030001466050040c603100a54029240e002d94001c0241d458084030f6215240c0350440074000c1c65200d400c240c0c454101c0816000008028180c010022400107000d0801c034085500f829902441c41204010140020394001507210542d00b5a0803364060249410458a000441030503260444400100340c0c0406440055101c05043c0d4064911040c65a05038813070745131400e0041c1680c04d68014042400014000d4140d16481d107950301c49012917504442c100d0003660000502a00540c000c080d05105005041100c0302c03952680140d1850b01c4445040414500610805943c0411107543c090b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 940488875 1250 940487625 940487627
    0x6230c070f0f0f020a060804030c0f031101050106030606021b06030402060f0415050d050106020327130603380703110f07051b010306030809120f0f0c040f0e0319 71
    0x90741035007500080d00102d104030616140003060799a0034141d00c2500c140a0001e80c0034442c41030144940e40c5a0f5500740b8080d460381da40d8182c070301000b400b1410b02004e14080103c0080034400c5a000300880d5902148543c589a000b070f0604140e181015640d070360166880203140c450b4006c803030f0003581c1a100190344010108440c421401141c00c0050481d044100804080c0d81c07000c0034100c806001c0000304041d90ba80c90782a0f940f88910039040f001c0c0e800c15280301024040c100c010300c404007400380001081030001c2c01ca0004407580c90b003045556848102500452048440a000c016400045207104100500c0c0182c202001c0051181c800c2544462000c2c01c2060b050003a110701d905080c0c2c100f0b440340307500d15049444140051101c11401c4145035069025840b90003124200d98128049501e000e05103820700501a03800340000310b051180c4815802c01c042c0c200465240524542e000d07100d030510100422040d12b0441c450790079002c0c00c01c40380181210011041342e4045070a00d058640c1c041c90414 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 940490125 1250 940488875 940488893
    0x90d0804031502030a0b0906030a2d0f0b06150f090a030f15110313030c0c0f031b080c0a09050402130203010902210f130510110706230c07 61
    0x28802c0e4850300d080045510070b41c010754050001c0390390034400ca042803070501504c600704a400e0703039255020a480b10003040148850030020305040c8140c80e41c0703200441e0204420b080500c0221400a91402e40302c080c095175407000e0380c000340110745018203010300e0101c0385603600400f0402208a140014910340c20b07603c1401c284000c3d507100c6204142e00300103080c0b2241c1c402c4120100080345082481c0702401c18501e07401c4901c140b05580c400080e854164504407110300d0054421944024904400300b031991150711340701c0080d0300c070f02c40b107a84041e241c1c1c40c2c20f25244140da20510250703000f0f013415100f680d42d00f030084003602c2c1d030688001010359950002031100410b402c0e03500340c507a10000000c1107115550b0000c0c541440c220450032100d141c1c801c8800780c000c80813030341203d0001c81d04000c40d41003640c01d607903c125103014004940c1c00c40f035030082050843d00800070040708050002446402c1080601481031101003130484900c441c3c3e010b41e043c80d20003100510071401000002a1481006004a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 940491375 1250 940490125 940490129
    0x70b0901020913020d0509010b3102031528210c0b03220210080405030c1c0e0303030f060f2b0204050c04060203042c090a060f020a0203090d0804 64
    0x1807018915042c50006030b402940700d04921541e05086c000002c4800805014820200101400842c41c014078003c402620b005e00d0034034a012040001c04c006568601800518000e00c0d12070606a1030102c10403c11400d2001c041c401040a0340c80d1182079482580202c0e02000c955038403100103d075416081030b0000000380d4103030003451212080b00209001d41840091440707201d640741c8903071250741080140107000b52480c200035400082c2c5070181e01e80e00d00c81c010454200d440b6100302c0342054101c501241c2010304140e1061100f2000404a14440d03034400700b51100d40b80c2c2076010314654104200c0900c542d140080002d405600381c40b0200701e01d42c441c5030081010b9144a511100c802040e00f1800f000e007003810310240d10550401000c504000c040c0070071a803c8614540082d03103480d103441103a8070b854000c03210304103040790455444404440c01c041098890300700c403c05003810152030300e0580d00711200c0c501001c5800d4410310190920540010484000400440b446501540c840ca400382c6e041c8116 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 940492625 1250 940491375 940491379
    0x702061b0d2403050c030c0d0f08090a031b092a12111e19030f021b01020a0f0e0a05060d020d020c070f060f0e0d060b060c0f150705070b09010209 64
    0x410440c1c2c41c40a20320314100039648100c0070f4600c0030a04d0340806954056010103164465180340c02c0030005519502c8500b00c2c98415404103007860403800c0010051079440c2c0c03064681801039864041c440b40306040c40005015200b0041102e095010342c034003401c0121042c03030f110a00d80340014160940c064a4150030000c5400002e01860455025801e0207400c8542c0c8490241c00c2510b000300c08010240c01c0c0e4003102c441d00c0e030040c5001050380c000c5000d082004040c081866003007200b6030345c9008188044041c0074071080051ba075030354111401010010680342007810041051241c00107551218050310440e0130498065840c0c0c01c204284900034461808122042c6100150000f0400e201043d084101c841154800300002e60320a410f6a42800540d9014000345995195440900d4290000c49205026050001c2c4800c21b0b02c01040541d07001503070030032859005070580180c2e0641080441007204003405240030390b040042c2d01400e03500606100a044404030000121a80750940c141d549403980 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 940493875 1250 940492625 940492661
    0x40c030206210c070303180302032b110a1205040b1503030d061403100e0304060f0c0507080c041d0d0e012c0a0915060e010908061801050702061b0d 65
    0x840410b80384e0110794101c001c01e0034003008000e180e4183c0e8032110300c0c5c0c0d00341c3c000d50b00e420a103ca00e001050303082401000218504601d014141e013551041c202c1299030000300c07035651900c8240213003800880c0406908818282410000010049652075030407041a0075036034013415227440040d0540c01140c0452020038500880098000e1200500820701c2c1c40650990300c4d8104d0041100040d1085034a04002640c002c1004106a40c410100340720014010b03e4540341c0c0c401d9558807103043c20b9640d030240c0d172282e0003c01203010502e4a84100c42c0c1590f0214403810b0400107070782d05180c030b5056451026040c4110100c602905034041c1c1c02c0020380d4120501e01109a000180326034032042500d0148500440c014200851051701d03e121b01c080300e1030801c0340056524640901240c040c0e404040c5641000368008001501c81c03810015075000350203013002c400090f160200340d1404c59000810600031980140107014050120010700c3c0340031621504566600c80c14604004050b00000018070300d1840 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 940495125 1250 940493875 940493881
    0xb0a05041406100c0b06011404050d05060115050a090e13020603040b150925090918020f0402120703052205030c01050702010c451403010203040c03020621 68
    0xa000c4040c0391103607a00722600c0e4403401035240b08540314121444c0052480c07141d000883d149601400c2c488065014003003031103280c5038a507070104203074050104040328281d01c0000180f2240b51581c4400400d1069840e225003009410440248031224510800303c80b0340d1a030021851080006001c00c1d50160081e008950b2030174035180c00c2219503401c0703c0c1e41c46039040b1503090403071600d01200f04034012100c9820030075859848a14000c00f65003066018401e03c40f60500009420000e40a044915801442c04c1d03036040c9081d00600c0003d548480c01d0510480c4100720260303080240d800240c3d040140e91400140300d94603500c020718803185842c8011031032100a402e034801c00c20004000c0c20700c000f100c0c0c02070040740c481070300581c2a105100410317004540c00d103001c008805440c44240e025940e29600101d403940908420945802d5400c66071611421181d0307061120605811907141d60150a4000314039528150b150340c2da04001e0f03400000e105403000034480c48807c040c40700c6d00050514203c1c7e07a44681c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 940496375 1250 940495125 940495151
    0x106080a21080f0610020a060e070501080a0204030c0b0d02090d0f0219080c15070c06053a0e0a1505010503121e0c07030507030309030c24030b0a0504 66
    0xc10014003101c06000c450300300035401e03201d0a01a40241c0c0740000540b1142c961070100245030084500301402c500c1103c0c50354000c2501c9000f02c0341a03842c0c042c054010343d03081400060072800024880440c0d940108010000101000850301c100d8816001442c2c4442030854100f01038407881400d981d0144180c90284180300003000408503c030300c02c48800309200c805180401800c1a07a01c0f80b403029400a1004051710304109031501d4024462001051030084180d4514410a045030084000140d0108580403d4034012103c1c070001c410b040c11300c080794552110010600c0b40403480a40041c4d80b00c0c40c0c2c44581202c2000001c0080da40305013480265034800d04400c0051509100d418400e00c2200300100207440494200c2c0c188940352544894041000c18040ba41540070f08408000b0b4400c11800202241c0c05000c000d025501c640c1d500040e03107141d414003440c0141260403000c1c40101c032205556a0904004240002040c28107011500c10042c000286202085520642d041030034104005000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 940497625 1250 940496375 940496393
    0x120f04030207080703112b0201051c14090c011704230d03090201020d0e0d060203040804420219140d030e061e010b0f07080d0e070503210c0106080a 65
    0x54902513448003400c40d2100401c0c1c01514210f00701f40f5003400e07906118805548204005e00d6080400d14506e07403c6030382c91820740704884c107084001d002c0e24804410703c811900c06001250003044240382030b00c540054080c0a412840000d0b04c018105a031401c00010105030780658528920b800d80c00b503c0307200c0488107014020346000320040703006002d110000d444050041001c40d400b000b010300960028640b9944400003580f01a0060320148414400000c0780603c03801401900001800c6180742c2e00c610b05490784954600c0348200c102000c102c050f01c01681c0d80014200180002010140a2036000741001c01e0f041c4e2022641c080c81d80540d8026000c1250113170041502c000800048464596401d050010180c041c000c40328490b00000004001c05840305002d400022171020800b0318080e1955a581010350248070020b00003501c0f42c0c482241d02c2800c0c011040200750941c054840c024036424120883c46500c09000d50f04140030803070300e2401c0340035400003018143d2101104c040000a051200720 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 940498875 1250 940497625 940497653
    0x6031c02060f01050108010b0a03050606093706210b120708101401050d170703081504060b03160903020d03090807080c030706140d11091302120f04030207080703 71
    0x203100c100b100008003544540c180e541220845418241485140b1504030301426024045640c0000f080c800020b2503501c401d04161024100c2d03c540910b40c0f40d280705c10103a203500c0000c040a0000b044070400c015034000c8035030480c064962815030342c5c01d241484000c00900728595215080300038140c2d0042010700009402c42668887c4003100c034592440304c8c030042035800c3c1d0b00101c490840404010011070403d035080c03a00c950b2040851403c02c6000d01501200c80c1c00030682500011005410712182c2c0521562841e020030081c0ca05000c8541000b5011009200c0900818900045025503549041c40b031030546003d03582c020007002c41c094483c1070041001460340243d00c424051060002414000003c10600103680a405011071518000080c1d0355000c0e002280c00041a0410400c00021003a100301100c0031140c07a1419110103080301070000c01a122400d51020f03910411180b81d07001e10401003a40e0010f546a81e50750107503140c0c030f0224288040b0354484522445840804000c10501a583c490 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 940500125 1250 940498875 940498891
    0xd120504060e0a14150c10020a0314040221030c030c03180d1101030203070302160c060318030912031713110a03080706050a0b1809010c140307030506031c0206 70
    0x185070842c0a0400a94480f070740304202c0d20701003640c000c20f400e00300308501c004000450b070a120b0814032058852400d003a8004c0304a0b15160740020809000e581510078080a20031740d4061415920b0305501140d440000707074501e030b8091000035604404e41b80040007128035210350380045c0d98031046030020480e030340c0c0c0003403441e00e0240f882d0045000240c104400b001109035081100d00302c0c2c01d640c240040d0001c4d40090700000401d902000540824031070010441140ca20825400d0b100502e040381c000c00301c13080b004408920011202405003c65030100340c10701502c481200c1d40003240d0541ca429507000f0b01c4030320452105070044d0100004004041c110408246c010000304100080360420000c100e011408010a0040280007900102c2d185500007507104051200018070a462400001c004442c03808042128480c1d4808119080c0d00c02e00580c0c0680741c860a2a440442448d003100d0847d010083c0440c04240d42ca42c00100341b070358200246078040710701130118003071300c07010f950001d45403241101c10769 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 940501375 1250 940500125 940500137
    0x304060e0609030a0e0a031403091305100308090612010b070c0b040302010512041a0901020d0e0303160513050613150807120905030f0a090501120e0705040504020d12050406 76
    0x15040c001090180c882c000d800b014500e800c955150541c2c15140d100800c41d0403201e40c5d0f202000003810b05614280020818000b16107513240c04040100800e1085041d02c902d50800051000b0795100125060079603510101d40380e1901d00440129006000d10a5500c040101190002500005801c001c003075035409907010a11181d01d81c3c2e45005a48110700c030082c0001c00c108001001c2e2088400003542003803003240340d00f0300810001c204028010301070b650003402d65400110301e852007016128212400d1100000745003545481c4c0c000c40b80300c400d8000c40c1414041e0000f8001d10303415000880c031020b01b500504403501e801c0d04201700c00703100c3c1c0c80380182c84000240c04d1202c01d040d8040d5000c14420381250f07480c110700318060880c0e20080d0146040454203480207000d0305591041c2c84010304100c1945070b944a180900d014001850340031080d80c000003440c98150403607200300d0082002020ba800607a00409c5503112480071500b003884442015120210860418030325a6012009000b200d1243d5901 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 940502625 1250 940501375 940501391
    0x603020405030d030b060702040e01090b0901050601090905060a030320010c021f051b0a021e030903331005131a040b0a030f020f030a112d010309140102040803030406 73
    0x19005c40300f48944903648024184800c1e0014601074002c1490031150300004900d0700c0c802d94070507807541000d0707070048c1e51a51074208021141d42d12250160041440910601460408402181c001551404041c040040c0d95011550742d0b10790381c81400b00c0614080c000c2100c0b014486009468802c41d0f6204032954400b41101203145d5401d000e40390055080c911036103107080d450210740310594010001392055014502250f031031011140b6107841004138940141d0b648140c400105814500381b42e0381c2104400040c859048200c81650204642028926481c00f082d00d440603031060b007d0b0f0f03079804140d100886400303140742c40145401000d100f103d544500003e6107040000c0000f62180c8185041d0048034846d01000801c8500e4902420035001034141002e4201c0b41002c03a00740310b01494143d482c0300568103510160704001c1120103038611502e640c1e29000c41d07806050b20402034820304260405417901145400d00c604403a0400940010b01e008665460362103228540360f40080b6010f03161303d4901410 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 940503875 1250 940502625 940502627
    0x31a01081005090309040b1f08040b06040501121b0e01061e020f1207060f140405100507051902100606030f0e0f0c09070909050708090f0f06070507080d05010603020405030d 76
    0x1a041c02410158065405c0901a00c02c0c4801000c440301c8541d0701112545c8611025004034100081040f0030f940d40c3e16481c5490304003070044600140115008501d080c00400105050304e0001d9011580a101c10341090f0002511620b1178001750030050b14a8112070000800030340100407403418581c03d14001000f00800c002c00c0ea2110200d6110302110b030000c4140a807942a840d00410404d88540300c005115204100c42004840b032100102100f00540030901c42401410403519040d2202000148841d103031070100102503009000c0c0826001080d01d40820002e80280400f941c0c0c82c211000c10820301e030352980001e015080144880501d41d02d4804104009a0082082e505c50701c1a50300900c80c18022805010030420002d100d60100102107030b0105000c5254004c0d40c0c001d848603622030f04242090100581018101c40400d0440e030310000c40441c00c007038089070b03040d400541820210340b03444407070034a400b19200d10141d80240398a4440040345494060340031b8021364500b542100c00c501e9400318 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 940505125 1250 940503875 940503881
    0x80a051f0b1e03011b051909090608150a0b060d0504020103140c0a17010e01031b090e01051e04050c1c081303231b010c05010203090c04050a11030a09030306031a010810 74
    0x10005c00003203041120440d501c1625411841d00200c0d440e080c1c002aa644055008841f15604030981c56000450060104c40f200c0002c03540080c43c00c0c3c420000c004414002841d507115901e02d101c000d54813140003400b568041e078413111400101d80384028252070521908200303980030700d0311240400c41c1841c4010441d003a0320341e014141d44644c040802c459003147c0b29114006140c1025821840100c2c0c008580804503004008481c040c0030000304540c207040c3e18400d030101c0340380700c62a504240c1030204408181c0004480610100c16904114454018040c04d030702e010b030304607003c0c0012100080700b905040d441a5040c007141d00400405d07100052150000d040126180b05040e220b0384a50343c40c4501903000c00c2035900700712050504000ba88841d50b64107082ea0801c44141295400c03400010403a42464014a42c1c0500c00c010200100c106406440c481070002405544070603a80b29041c4007014001e0b40031700d002e1034020743c1c010b0501c01a00421803d508003402030454a00461165400c100d031980 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 940506375 1250 940505125 940505171
    0x210b040f090b0a15120c080705062a0717160806070807030b0619050c0c0f0a0b1803010608060106030e0102030105010c12021513020109080a051f0b1e0301 68
    0x18048046540300c8036071a4000d4041803813845064a40c8000c0000c1c1c80d4030303110400018a2207440010109450b02c121541448860380c0024000c14040000100303c8a01c804940c1011511039125240005445107003450141103400060403001d115103002e5030750b03100150515143c0383c040c950418041d01c4055440d1550b0044c1d505902060708000480c0780035010b0340000e4208403010b440d140c240b0102050113800064181c2c0c040010410004010742cac2564180207101015500b91000c8891850a5000c40c0c2c600c0110f00c1041042071005c901e04a005d01e8941c0508800500100248111500c401c9240e1300c83d0800c1c440c580c0800d00d40754401e09101418000c0e2412034030143c443d95445041e90b2a00260040104600d80840c061f0414207439951401040f5a802942c1c2c2f22100c0d0401002840003509501180d0844d80d02540100c0703032480080c074006400b010500d104c51754000030384000e03020301c03024205074580705030f1104c5004c00070704000818003603a1518040c224024440044101145650040c6117 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 940507625 1250 940506375 940506383
    0x9060506030f0912030f0603060702160b09010c06020f1215030a02120102190e0f01050403050c012105010602060708010519050103020306032805070609060e010c03210b040f09 77
    0x24000101c24090752141c02d80d1003a070403026160441081042c03255039500403140071044030500003d0045a0a0030403406501524500041146464240e030b8010720021910a80904040000c1d400899922401d250111558026000c5d9110b0301140442ca0131500130300052070101c1d8421001038400e035135503d4a10007809011340542403002158083c000340c14508003104010350740130000d103005003001c22111240d800441c1d484007503480e40d001c100000d03030401c032403001e04212082c00280040390300420705020310b05090802c50b80d86401e4000c0034103000100c0f042c051250b40342c88000621180c01040d203510030907069548200581e222001c1204045400d080203204409001c0705010550003503004580211005040380d041d030a44080d61016400b2800c1d41050031060345800b00304004007000104080c00300e90510009035402c1c428018100e1540309501810812542d0800040c54000d20344580c0e84010722000d800350015100c40f00f4003809403d6540c4e40241d141181d0144c0c12a00e604c02e4446142d80 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 940508875 1250 940507625 940507627
    0x90a020d051b180105042102010207120c12140f0d090605040b09210115050f0108040f030c020d060c0815010e0102030a0309060b0603130303060815040602030907090e0708060109060506 81
    0x520301c80b00c0c844043d0150302d060040c108000304445a010b01c0f01c60001c04008610070340100d1314030009040040c1680184050007034603a0500000d1502d554640c00d585a44205003180002d50a200b80c10704080c2c1c10700c20060203609054044888003241c00c02690f000da444013040c49a0308c1108407a03e02c00c0b0320450494500500100c82c00d4640740c148125191013032181d4802c8502203411031401c45654034001d02100003109000c002508202e040c0d94021042400d20500d245050b8032443c4000c99100002002c003c11b0710a00c1d021991030300d460080711a00030b0b074108a400307400170016201d4403003a14446940e440c8004164000e40c8500361116150340180d01550403d582448150f01801c011202158400e8a41c0303140302c150f8461001a62003400220410702c4104140d05001d001c8170f11a400c00340f156080b21343c0c0e1000140540304c51a4000c0d50140340141d507543c40c0368065051402c2e40d08030684032400c3c1800307928030b40400590350094800766000e41d070850b42d95040740d82c00c5070054414035411030302c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 940510125 1250 940508875 940508887
    0xa0216050d0e03212a0f19050712050a0c03121101060305070611120a08070801120f122c1509030a0f021c0b10120b15030c090a020d051b 60
    0xda450702a10400844191718030142112044180f6100c4445803402640d5101d0794840c80162001c00024405000451080e8442d4076a602c850f91150f00710700802064070013454100c01002000c10401c0382071604000042007840c0c507407926900611102003000001406407000140090042c80f0301d034100c95002d4014005280380c81c0050742d1459048440404c40d000d00219802c1d040340040042000344180d5503810a18a0b000c40082c14507003060300300d814800b001c61205000103030359a43d503855050304030f4105070080e102140120b44030a080103004003840d1580714220002c9249441d0903411540072202d526021404100740303100c1d40600190f280d81030380816624030126440640da0000d503030000e80340d045030f90114a1407181481d010703a01212000c0c442410001440031440c1404040d102026560922a499803107400a030310380030308907400d020306400b65403405503030410203ca0540c401034141d0036246418400800203412040c519a1014100701c001344954148010394140d00216441e00c0f41010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 940511375 1250 940510125 940510183
    0x90117061b04030c031506080d12110712020105040201080a0903090308030c190c060c0e030c0f03030c0d03150608010f03030507170d0b0103141e0a0216050d0e03 71
    0x201072000800041010440480410345540954000d9802030492100e80000009440111010f41e40102c4181e0840c0d0003e40403681d10070f52107039030540800703130210340140400d40d40c1c00caa2152110042480c0590f900170b00d185a01034000c5881030703000740ca400b80156a0300d4084000c2c0e914091000780028020a02400001c000394050f50704072110130a101e0800301d0700841c0d1a01840314110712404920300e041e82c407013080254000c01c1c4658180e0300c0c125410312040d40c003081da01c00e90505503a2003042d9907099030106850400c02d81d024121070301e0031116250600c1c18043d0040c8444075000c05140225800860752600448289040b80d0301c0400005500f4610b8904441c030360001001102c8406042c811f610000c01c111026002c0503420140001c0d4100200001400301d0703000c0c04481c00c41501c410100010028010010701c180c01000010040c0b40c2d8862a40200030301c103000c60003044886207407162041c00400602025010125120f001142400340308040d502c5078032106000d5000d0020090550f18 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 940512625 1250 940511375 940511401
    0x2010e060f1506030a09020d050a0506130c29161104050705030105130b1e180702031629011d1611011e051905190b0a0902030408030609011706 63
    0x2c85c182010001ea020005c1c0d00040900502800c00d642640c441c01003802400000d000d60364110342d070390200c10f0180003d5644c44e91303461003038800c40d81c581171246003414031074503201c2209441c24004c41d4001d0383c9181d0590404003a0549131403e607804101400c22112504240c49071b203000d409907484280c00c580c600010003071507940d44184000002d41702e80d0340080381d80301d245e00d0414110325142c204007442c0b0030340e0034806043e4492042440c480d2282003803014643c2c0100c211404c80d00b418811701c6086001d400d05000c1c40c5d20070310200303034846254500c0c01c090314010031203d07059031900c501c03c480c02e04845e50301101a9506445600418680e41d0444402d01e000c0d96189014030642030011035800d406900a403403001a2814410303400d51035100700702460180f046400750518a000c1c0811241c10800304d0001c5401041c141e054070541c0d00c3d5002d2140d5506c869040d80100b10511095640346010320b04450705400c1580c01900607203078080042508041104040301c11010319008100300d0b40d0383d40f240038031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 940513875 1250 940512625 940512631
    0x203190309170a0f110d080f0901030f0903090b160b270307080901030209040b1c060f0c1202130f120506010f0e060d060e010e061b091e040b04060602010e060f150603 73
    0x400380309854400006214040502023292400c5411902c80742c0b010005400e42d110078180c803003454075050504000030380001282081d184c190340060380b100d0545400740e0020f8041072024281590082c20801180c80c00070180d151440c5801c2d40303203400e680800c00c980d9607008001008000c00024801c52400c7c1d40310340d0140a00c81001840070a000c488000800e61b100d0b12181101d455490301044007040c0300d00350048105582e00100100800da03400040240034482400e9000c0303989800058280030300d0124202840500010080b4004955461100050a41c0c003d1001c40c0d180c054000002866030760080e003102101c0c0c0520210340d6940c5d40904100190280c80b01c01c840e0265940b00107494440c09103e07160540411100401d40d6051400d030070a03540440c20300c400300b5840b08004886164403522040c1003001c0312000c030100303009a0300002501801c4004001030b0050702d409030010380d25905400400d126915007060f552035451300f201c500c0c0b00c254200c0304800b0035080c0e1220340c00703641450320007164 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 940515125 1250 940513875 940513879
    0x30f04090b0a090c120e07051008090a020405010f1509050607080c120a18140d14070308030c0315040507050f0a0315030c030311060609040b040203190309170a0f11 72
    0x440070f501c69090104541c052120280080c090464041c0e2072442d41c8620700b004110200240106440c1c413000554088007038080c1c004200011010401a050411003400c2e2154010b0050060f03607101c0344010103030902c521401c0c148142c0d080ca83c00002d80142c0f800019078001402d003926010682e1208152580f010440306514411750a0002c084941d6401400541c4072980e1980c0c13010340d070015401c50803261608418000c1e1560031440c1e006540e000c03202510711f0f500295010104002800d000e040004541c0041c0101c00c001041000e0b09800c031005612409403070b41c0350246044280207100881c5c80850745040490310030091402800c0c94540a8020101c05241c0420848426000d000010b243c6503c111108598001d040c410150442440f00d0342d488004000c1405107002000074007043c4000d8000f40c0b440fa03000c0003041c295101403102e8404c3d44960305a807050680301c0d2500820301d00a6118271000310124419100e034041010030040e035001d401003203d00440c2425280c0003107000782d110b800c907 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 940516375 1250 940515125 940515139
    0xf06161703061512220c06030e01232214010f18020a0b13080a120f08040b06060304030302071b0806180a0b090703020a0305011e020412030c02030f01060e100503030f04090b 76
    0x940019140300c80a03014200c1d0ba070307004c032740140c001071258207683c00e040905102198a00303002c0e0400065410780399000310f0161039035501036642101640c51607004c2e040030301041100e2411082400054110108031400c019080040c410642555811902c410350000c2d030000310700f60b04015407041381e000b40591154551030007108569400b4807a10301918420102e07603080345c0ca00c5d10310107039800200390300c03044013a803c1444840c6002c1e625000ba440300141801d121391400320100341414401d60580d604075602101001281104c0c220004001710640300381c8042e4070400c400603460488580703221400000c0c142c01440640080e603100c12400c54024000903840c030416400101503952103004100440c010000040c407482c0c85c0d640020000e00b1064083c40c25401080100801010b44880e01880340d050301d022004198144002800c101149001a071f240d801c020010980414080000e801382c1c2942402001ca944e85000b0715841380150035000b08da42900344410840c00c48160000c6507280c4000b0528 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 940517625 1250 940516375 940516441
    0x200a060e0f070807080f030f0a030905031326010c020307020409111503011a0316030f090b0a020d050a0b0102030307080c042c10050f06161703061512 66
    0x714601140c42e44500859072040e40200910402804800301d05c0500c5d2001c1c504d848803c3e00c5803011072152031101400c066840414000740081441626030712020001000140c9a543d0702150300356a0a41c40c040d0074986012608501c0e03001403040030710702c1c0501d801850900000d9002c000080031800e0090310300c034803074102640d45540d603100301b00202da4000503100c2e280d506254401075585080f503031008005104205100d40900041e0403200b10208500c3d0200d20b00c01404100d0f405401c07803c0e4024007100a281c14004103034080e401504150fa4010f40401c4103540d03800812065504640060740540c000300046100c00b80310f08140b56000c4018a00c1a28041d50f0300c13841c55101e4008410541c19a401c4041c0071881842030b00c10980007a1413251840c092810b150020307400201d450041c904c20003000610b02c40c007040c42c40758200d50682220406036820008544480c0d00c2c0e008403031040c07144000320581301c1e0100600c0140c90100303610541c041d82560ba242c010f0b444498100d540c50380500c488541c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 940518875 1250 940517625 940517653
    0x1b0705010c03050f09060402030a12031d03040611070e01030b070c12020a0c05060a360806010807061b11041803180602070311040b01030b0612040201200a060e 70
    0xc0c1e840040391030707035002801e80b070110315020031010041c1c0141801e1708078900348005640c00043c40703c8c0b00d540090301c84c903900300d10b00002c0d00201090fa01250a00949424038801030f0700200141007140d030b1070346406020960301415076441d15030070700843d00815400801400803070140d602656000c0c8031410300005e15012521128520351800e000c030001684421118410405403000d424014031055030300b2400c05007000b8014185203504c1080c2d8211450006c0508820300100740350140700101d001c42c0301c600940300c040540c0c13900424003810146205003440001e07914810912050340c1d10f401c1080003e002850303135401510805240c00a6400354407103e42c1e1242070303a03d1003592100d038421f4454041e4440e502014105270440350b4855029074211060030400f007405400d003041030380401c540001ea00c0340c0c1000142c0060049458054206801058401c408040c2d071f08841e00a6000343c84030312184c09c4100106400c498ac01c2c450109a07003149202c900060320b2074200c0d860340c0c4002ca09440b0a800d80c021 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 940520125 1250 940518875 940518881
    0xa3902031624141c060509010b0a03150f03050303100b0f180a1d1512031806040b030103032016050616022d0f03120d0603150f0c0f081b070501 63
    0x250750240103140160014500ca403d1081c1402007506446450387c4d0741c07400d0192000d60141515420a0503120800001e5a5100410100281c0100180e502d000340c6c0301d041c132a90b69001103c14031162038070b501000c2880c40b0404141d614070310460100c2c0c0d03e00100b4030000742c211a07034a561141c01c01c49150011030f0f01640f2158541d2040c40c600e1358514503203001c07008084070030400080d00303000d00e103080880040030b0004000ca5403e9000c0300082681d460411f00403e00903c42c6510500d9a100044000b20400d81e03c00810b00703900b050070242a50800380c0b1080940c0b2a506010440041c0103642010011400c10b0405086000c0e00c8010003112081680c01080807030044140d9240b075103203101141d420700300060300c494030f4000c029076021b041c0860140c00b003640c610070907020b60703000340c0702113040315000d05141c00490166603c21110880d49802c01002c0c005088000017500c03d03a400c0c80d0503802c0741072141e00031a19000c4542d9032403820351122924078540e80c1903c0c080701c4c9000010800c1d140400e030240 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 940521375 1250 940520125 940520137
    0x30304080c1903080a0b1c0605060123070618060f050702070b040b030105120f07080c0111010203190f06030b040f030806150a390203162414 62
    0x5540ea0352107064080d20b04110305070080d1501c0c0440b112100c0046a4842c610310f40c42807041400050700040100016222049804801480d52071142402d0400606410290280e01c0c280c0715402001c140030350a01c101c030707610800340e0071021050101e80041201074000003e04009450031035803100b9036031500c43c140e0303c244615102c03803905c0703206001d9101c1e810400300300107013403ca081d6810141071002080340391106100311032141c00c3c4400d0780d90007008148090460640e4142c221844e155440d404103444221a00300107000c2040e14041d0402810180201c910815403007601110490380490054010220303440c20601007640d40d02c020001601209034640502d0040540a00d04005450001c241540003001180209030410114060018182c113650b05400c41d41051440116140d06c503407550583d00c1c190100402c400a1b10051503000c65002c044060300a5042d50035425020700c4a88000282d80706121f801d0151560541c9001020862080c0c06000d901d482e0382e000312403032245074081c1c00c49 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 940522625 1250 940521375 940521383
    0x81206121603171314010905060d0c0806010c0803060103091e080d060902070c090b0f0d12082d0c040e10170c090c031e0703090b0906100b0a11030304 66
    0x320510500140030502111010070340e840300c1c03611341441000c00120000f80b0805105481070740d00c0000685c09000c110000c1e10010f03109c2034440384101d80100240c50708420300b1000c9400400070400651248888541640d08001c1c05440c42c1c0707038440110001d01c144078081c0d80d00000300c1c4640202c903150031044c480882c0641c000c103882d8000a000b803c102c40e0b10354040c01a0038410082074000800b0798603004120b45c142d403400140082d01c000490400369810f4111680400084001800c011003048141c645c0146640c8001860f504e000791001c044580304a100a0707a0010072980c0c10802222981d581c0c00050700000300d06140c0e8401d9803a0309030304283e0312b25401c6c034500a01030181400c1d4440c0c81501c44042d60045c5640011040031520945011303000c03a048000010021714203201341a101070f2000c103050780565040c603080c203000300104020038040320742000c1180803510201c00054030380e0213130004940070b814842c9000000e02c8180e0001d8480d40078001f120300041d491540506c0610701c01c0d801 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 940523875 1250 940522625 940522663
    0x6080c03090f0f01090506090c0901030305031506040e09010b122802061810050403080a08060103090c230910090506130c021e03120a0f14100801050108060408120612 73
    0x85c625041e410024001e0070444594002c5012244607611401b0f5181100d40604100e666a15203030005e20100403072103102e5420034000500000c40c0b1002e807400034810b203400701c002c21403020408108070042512103440d00e02c981c00324104c00c4103a003022210445401c8403861012001500e5404144e40741c1100c3c2c1c070503680340d0405429805600302100404a500d51070328095240c28155603802c0032600a0041500c1040742460003d25a030740254030041c0300641090760700c2c000503925070f080b03415920750071400401500c2c000c07148091803d051494600450500e002501d0850400313484130000c0100501183d071101848404245858280c07050350600d00e000c0d8042c1c44d0551001c0010404694000e2025105600412855881c10051101150012000032000c9040c2d500c0c4bd803d08050040c800030344409241c1070090103c0c1c4844c4043d004201e422000007445160785c0d0b0120f00392500c030200c502030220326003001109e468080000c03032640e000070024600d42c2c60314120152149007100000000f180b5900c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 940525125 1250 940523875 940523891
    0x117010b0703020d111b010e0303120703060f031703070e0a03080d0b060a08280c020a1407030308010e220503091f020d0c1a040c0306110406080c03090f0f01 69
    0x40c1c184400c0c601c0c8130741410300c042040b00c8490703129940c40f0b09600390200351001d5080d40f51160b01c15601c604c0c0682d0000c08807031b15103405c852035010540e020b0300d81c14007003441d100700018041c084100300c1080341c0d0490f02418043d2041038000c0401d500c003c00030001c101508400040c241e503890310f00d401035030184010a440e001181c501c07008071000d464004d8802c01040c4424202070340c4c44425981e01480d480002d003e260319000b0700c046580c50109801201c0c034100098515110750004014100c90300682001001415050790079407100030f0341c08081c1c0059003203001031001910a00c0100d03001610400030700d203000c003012a602c3d45640101c00403140c3d030b000001d10401a2a00c04c2c0000c040500003c49440310009044001e50340d020401130600a10504070181c0d0709016030a0344030b8046400e241c030303506c0071860030746402030604110f400304551844c941003000044242c644251000d4403001d803260300305611402c40308041a08000d0808000d4461210100c40e106c1d0700f0f00a03074684071038502c0003240c528 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 940526375 1250 940525125 940525127
    0x1207080d0305010308030601030e01141501080a090302030405120c06040605032d15121207020a270207240617060f070e03070e01180b040c0903030e0117010b0703 71
    0x30032094a420101400c0200520100d01200f007101e030404400d08000038108800520039024045015041c1902038a000400140c00210001c1d0303010044c2c00d0b6200080c0c0d5030360101080490b07003404006001640144801d01035400e22204540801382d500c1c00310384880000c80002802c40e07200342c000b007002407000f005200c80507452181001b1f0394201c0925140500c4065201c803041280003d24100c02101c1e0050a000c03c0d032281d82d5051808044a07095484120419540c40700ca0791181030124040c40da00301000800c1d9900741c410a40280c1c41c10300c02900e12112101fa000070703404c101d60030340e40b00807120210100448012800c460700050700c1e40119405150000201c121001d8100ba040f4980003042041665000c82d98159842040760900504944005011910b00003484c0c000321015026100049030982400c65051510f00c01c0700380901c00e0044c04420b020589040b1592503022070b03400c01050000a00031a0035400750001858444840310042d6030282140f80c00b0380c00900860070000b0b046040c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 940527625 1250 940526375 940526383
    0x35072115090c0f06030209040b2d0411160b06030f0604080a141606150b07140c06030a0b100f050714211b03030106050712090306050702010b0118060f1d120708 70
    0x30201c4002c0d400c00a10704291403401c80d25002c4401000400e04d00ac82039980f82d51041c3c840908c002c04080d22090042c04450741b0944d424420746250720040001451864005403011324188560301600d250340743d66031000401c0c0c00403004003040c003c50704241290b510100c3c0142070b0070141003054161400d00c5003008002c4801c02c00c1c200f00c051460100c2401204000011a0a80d6600c506c03a0f1969502040e02d1a00b052400e50303980f82c3c48000001030203a0a0f09a070003d0034001021281d8400a091403002a50250400c0038824007040080c001c950101c1c02c180c0702c01d010700380c2120603241c100b01080b0000c03001403e609410301d500c4502050300c50780c0417001007220040381c034110300952441d41049806042c03070117035550050094020301c00c8881040e03c03503400e08008680c021414440340c1000f444c064081c00d0a1481140028421030404c80307629502c2c80900100c403103580715070781c5101c40c8010458105080100440455802c80e10510958940b100d598036240d031040c02a003d6075043c0f0841c5818 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 940528875 1250 940527625 940527641
    0xd0b06010e1203120408070c150306090203061309050f06010b0a1103120606072f130506100c0f020a150f0906050435072115090c0f0603020904 63
    0x64410714046042c20a4000129140c01c82c404084004950391858210001e100d000f00003232823843e5880000601031464840d840d18000143c9080c4161074441c5851412070004881440d807000012480d511480c0d0240d0064003864001d0b01503802a96412800f00c0c078110082c0d11142ca03c1c0c000281d4425901da00c00c2080c894030356a08003951030621644007500e42040080d0109105242c0001c1707030000c202038074001a241e91444074408818141907401d02000014055590740206c824540350000c0c02424487c0d248600d100806a58076000c5d2414200c84c00301c00d1140860b18030f50325040803400360760762039101c50040402002c0b405040b484d002c0020018401440b549003803102d00c000501c00507412005960a40341540100eaa45981e00010780303c1c40303800313030700181560088441c00041d080ca0205002080c0e0312407034250040391006961450341aa10000c0180030069400c8001402d170701e890300003204c0743d806480030041e45501c4034250004c00019501100c042540000c0700c1b6641d04103401401c8d6 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 940530125 1250 940528875 940528879
    0x140d0e030d052a16140a0803031b0c0a02031207021903050d0309112215060905040902060405030609030304020901060e130b060f0a02070801050109110d0f0b0d0b06010e 74
    0x400c04030f0b01d0820701842ca11481c07000502480038800c5072900b8004200f00d414022a000c031400d49070f959010200c1e20001700d0a0154040c1904090124003440c0c000110b9004034000c48051004840b01c404240300b542040c101035549000f5822544090b039010070120490407090050340385c0e00c2d02280304000492114600d004202c500d58070081022460100e210401000b95040102e250041441c104400e0035940710401d600200c0c0310f90141005c0f4403d8202c20018044880401c04103103141d0b404c0c1d8650465105501c0098852304c8203011034101038020207240c03480a0021400c003619000020f007800c004681030b882d10750005c0200015442c204503024010026420146000c0c825000032440400500321011072441e00c5281407150350300c580d0104e4840b043c880352603079107481000c3c030002c0d20307106d00c0d100c1c0e84141d600b401c0020400d401e5601c9a0000d01c43c0d00c514080c03819602082080c050480c4498440d0059501c00c40c050043c0ca824400c0b44443e480382c4103100036450120005081c12400000f018 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 940531375 1250 940530125 940530127
    0x6130f0e13050316020409060903170a06051003241205100b0108040b130c1223070e09010603061b1115180705040e01140a0213050d140d0e030d05 64
    0xe004103101204642c0c031a0384d14001c00030b450071103001042c041e06001c1c100401ea24600081c0c40309040c0d00a4940000d041160020030840d141c01c262a0b0a40e40d96004071a840041540281340050107640700790440300d5000425003c41a09014035000900141d00c000ca86600d650443e004024090050b0b451581c030284d010040042000002824494020002002e0242e0400402e005034045400740186540c0000d00858030f94869240b5034800100305005c81c2c001004841403200c440c5000c1a0402060030f0000400c406850851010604003014001c2012556100c80100119030140580c40072640c1c509400b9050120b00d40c8014013400c3c07055010f003110b03004818203881e1145d035200fa054010009500807104a040140000c5c1021500d61016511510b0070501c40f01c9950190825a24001e103401c80405079034420b00410300303034824060400b8034045208411b1117140307400a91040080d00450011001212244045140402001c00ba030089911070b01484400c0c84d0402103c0d4a0b030a070f03441e040e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 940532625 1250 940531375 940531411
    0x150b0918010605040e22060b0307080c0310110f04141003090f11060c030d06050108060612010b0a0c12030501080709090206040b0f090613030308101404050606130f0e 73
    0x81990284c0c0c0508084d050841d00400c0441c0c0d015680d0f41c41d140b202401c4051050f10303d1608400070040b0700b5903240680215003000600c0f49000c40c400a00c0040500a0502100000c5034030004055000c07496080e01c0b07080c010f0313640e180b4170034020f03001500d0142e2302d508a00341030204020101a09204001c1010f041032411400540d00200007100194824030f10009085a48001060b40c007401010b110345110120703504d0400020b680107801180c0081c0c840380c40c25141c040c00c0c00014401c00100c02d007505101c0004200b010038040013000801c0051418160f000c10f83c0e9200120009030400c03560010751244c2c018003040500340400c800034040000100011412031380401c03102c0c0914401d00a98100c041961000341041208403168802c1c010100f9030b0320040014988912281400150001007442001403050b090110800003941c80c03004003e4494060001008080d01008010756003105045c090804407069101480010b808061411401030341440b00c2d010980c0001010104095905048 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 940533875 1250 940532625 940532627
    0xa031815050a1812120903090f15050a0f0215010e090f1f0b180f010311060a1d0a080d0306170a08030f0406060b18090601170613150b09180106 63
    0x40c0d0f092460f400780c0101802c07206180c0030b0b50b045c0700c20040c4080ca603060610000070181d2008400c41915448048160342d01d48526009042c0324503a1107140101e401081035203015400b601c0c9000000300d40340b04844018140d14000c400c500303000c0e4000301808051109116140380b0034080080a03d030071000900c1c1120540b0441a44c5042c000504d0381c2c5580c2e42d0301210015240e1428280761444d14241215041c200100d104560350070910090b190b0594150b030381c2c0701c503141c0130044501d801c4c070564441070b00501040c0c0707030813803158412485a07104c081400c000610480a0040c1042c00c60b854030005451031500030b8028800c0b812143c0002c1d260404003501000030440d500341d035040041800e280030b150f0f40d686011802440140c21001d07035850b010900413540d1111041081d90484190b0740c0c0d402c03948914005503609036000700e000079003140d805d001505070709003e4004c440d00002e007071000c2129000703203030084880d40e16900451101070740018244080c1c2000403400c0503800d641c90440d11250b2400324 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 940535125 1250 940533875 940533911
    0xb0406091b112e2c01150506030c07021807090f031a0907030503040807230d0809011b0605092a060703030f0213050109080705060702060a031815050a 66
    0x31011203409880c00c2d48100d210fa902d4004030740035040f000800040007406241c01c2000c421130494010300200c0c0d01c0c00140604180294006070144559580c0c0c000c0c2058100b20080d040205002444402031002a000d42d4034608814a0a15450511101c80c2030108000b040112260400e0095041e08801000012a00c654800310481c0c00801c5400c552100002c45080c80c0310b540c0050503500c40414003050004c404652030084511740c02480b0100345038a1603c0504c1c143d0100700c95480100c0c01c04076008619800d00a140d13294052404900488200043e0b100d109240c040130323545159a0400c111301034008200020124102908640200c903141c05245100e81103036011030302a00010a07580205070181c2c00070a51245036031010b5442e5522803002094140e407a224441c00103180120024512001007240f805440d005400030385461b216800b48009903010b0000d0804266852a0901d81046d0386404084007520480f0700d500600d0003401d550058950150882484600c3c08950031404d040b251 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 940536375 1250 940535125 940535143
    0x60702040207050c0d060e0c010809300c060f0903120103030f02070308040303051812030d02030c0409020406020601090b4204090905150f0c0705010b0406091b11 71
    0x12005682d520140c541141001603e05400b82c0001002010b542040240c0c0c014207800b40703e62003102d038a00c0000004540341301040d69080140e8011403051511030f01c0b0500074505001d14110341035607107142c1410480d200d501c50394200b09103800c04c0003030200407800075000c00c0e0040b013031000441c101211009076840d505010712004040c0b2184404c055140c0707000b40081002103410000b0700d9110750f6a4240908158000b0340c9240101444600010061522101c03901c64090b0700c80081d8207040113a0300102c000d500103400c100c000101030100007445440d50008001810f11075028100c1035140c4070740b02d02941c110111907072080c02d02e545800d0480301ca00300682c0c1e01c924803c5048098840c02c3d03452100030103400c003590701401c40019001c0f981d41e030340d5045080d40510400441b19a901143c140954002040d1100c120750b0f620f0038041881141500094990a03001d1000003580e903050b1800101140e280c5d40c0404c0c2c22544424010502c2c2c6c001c00704d40384002040781842102080600c1050741c4441070a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 940537625 1250 940536375 940536379
    0x90a0f0e011512020f0c060f091b06040503010c020120180103230f1f031505090f0102071113020702100f050c070803031815040201030c030b041a090703020702060702 73
    0x84640c0c0300076034803c2c10b40000c01407104030115075404921009002c0d59102102000040c86550301080c002100070005c02d1141c083e00d809404c4152003030903038030b100080031040070781e101c0d400b804089940d41d000c0c0f041c986c04070301031b40000a80c80700c11103c00c000e030b5080d00c001010500c018001d0075820400c0701c8224070002803d1070006110310340080701880c4c004031244400c01b0321410b101004202d4900a107001d01407031300c6291206684010314101c4025580030300008182c1011006d01942602164020399001100c203801d680700039020064090890b08452800d80d02c2203040805200c0c0c0d401c084002141d801d50600055103403203400d4001c150140c09240914081182c441800b480140c81074094400404035601900c080a54405d46035035680c03c15540200c001e00c0d504407421840b840058034402070846007000039030b96a11500154001c16480380048103050b100c9560410542da94130520b06150700c1400c403c0064040d40041c090403501c01030072141850310401405025a4405094846180e41 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 940538875 1250 940537625 940537649
    0x2004114005060a1b050a060b030316060c210203010510090501390c150c02090106050d0213060c0302070e0709090509010b0a06080a0f1803052b02090a0f0e01 69
    0x20542c200d80042113404c0355030f80070340e0401202c0108a008241036031624015041800040e510404040c4c803842601003155a030442801c00c900014819003000c2040d114904194054407240382240c5207100d05000040c0e14103500000510030b9281c04410300c0340040c014034198182500f0304c03001910120300c21000c5004d8500546800203110f45640e140e02c0840c10084c40e1a60b00c1c140c0c4c0c9040c0c164000c080c01020032340e071809502ca11a00b44100501112960014000c1d80d05900e0f0120a480c140e0110240e900320a400700710781d008103441c501c05040101a0742e40c0d0f00d00d40c0011410020b04119658000d88100d02a01d002c1c89000e96101c000c1405417134200e440000c0f281c42d015241b600409441c1c00094100f85a402c0c0009c20a13089451140b040d10b0944060040c0404020b10000b1200801910304140038104079140110b0302c10b002600080744402d1142c140856034203180c12446a000d50501c40782ca8002a040c0f005003441d811000c01460b80d2a034520070141000211446800140180a903500c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 940540125 1250 940538875 940538887
    0x10f0b0a0e0f04150e06090c16050f0a0f1101030501080303160e03101401080f030708030601050d091209061b110303370c200411400506 60
    0x42c1c1c0d8000d640401d04024810010410548515041500240700e07801030f891508000030316a041850400c0e00c00c0c00842c94446c80d040d45080c0007010b041b0366003025100342c41142907a4403c0e0804000003100310340031342c0f40078195101600c2e081d0303609003280e0020350425007410700400842500205480e08170010a00d0100200c500301404c940150078082c5090f498440c03420480f00034560341e44000f4a034001c440000c00c90f070381c07103840e400e40d100c000d682c80c1c0c0c603240d0042000d07802141900010710b4020b041450a9480d24030221508020744140300760642c0d204010745424894903402018500081c0070784d0420700c003102021083c08448140c402d80252981e5403803008103c29a50a00894500d0780208417680154201200d003d5810b010032880300c09640303822230041c0f018502031109061481c0c2c4c400140f0f040c62240103007048000461600741034000c0d4032206c0ca000b8100700440640324240c03848510030003030b0000110030585200c3e0502076030500705000c0f11004d403141d0031041710801e40300184e40c2c03aa80c4030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 940541375 1250 940540125 940540129
    0xe1e1b04082b0c06200f0a2307030804060615022b081b1b0102030919121101020c011406030d03061805040510051311010f05070f0c050423010f0b0a0e 66
    0xc040c0c0032109910340c1700007070150000e030245000ba00c03d24419a5502070708081e6001104850740c072200c08001000820301420001a10446040341c0c040d00c54000030070001d41c0c42c000100100c1610000e45c1c003603004039061140c0703400d40002d4018080801a90301c02c020b4101c41d4054200c4a010740008213599034080c20080c04100903084410240080b00b8151403801e0804255000790030030344054146000d050703078025985405e0b403045a1150b070001e14091420f8401d410540d07501e82900c08c0b00302555001d1010542c1d05000784103030402c140000e207400307526261410400d03051803210707031801c0d090600d03000c01408003518040c0e8a40701800304500c0040c0a45480c20039503e08540701c21300800060406081060b01c007214880b40a00c140f1852100d201c011840b401503c0c90725509005c103001903400d001d044049a5480c442245441c050700842c072030394cd2901e002c1000d54040b143d0016081024642c0081100e690b080e01d240104003800c3c0094205080620500c0c6d03911452072590b0801c24a0b03001c0da00c040e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 940542625 1250 940541375 940541411
    0x30604090206120403322a16051206060603040302030408070b1909051509041107080c060915060909010e06040308100e1e1b04082b0c06 60
    0x180d002050140c607189a0f00e120412124222011000500c00c07141084444000302d0105404032141204400c8000e0600281c4440740c203e042c01154409442145001203080030030749181042c0c400d005000702040241d0b01d03502d046243ea01c214000c100b90301806207080d030301042050b0449001c441055a986813803e0803440d501807604000350a000d85c0c1c1c00055180364070740040c03040720308440d00d01040243c1c5103c1a13900c03e206214054200c002070b0000360711005103600130000c0d0040104005002c59201074100255040200c2c112101c40c030010b01c1001c558410400140d011003400010940715802c0000b0b8403c10034080c1c0719902807400000400d80e0f1b21740a400034951680300208807001d500e424140105040340607078460040e00d4410070b010488000c2444814400e042c0810890316200109500e000000310080000320b94503130401b241c0c0d100d400c204000b0401001403000402c00500901c0c40081344001c0c680c040c09076001200100032105070080341d00c0c00041d401450020318440000103030f03210 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 940543875 1250 940542625 940542641
    0x601051005040810060e130f120306032f0d0809090a021605011a03210a03020c06071d0d020f090a02090301020d0e060c0f040e07140c030304110105031902030604 71
    0x10300550004003403100417a4050021251003006903160341d00d4202c1240b1040c0080d8102915490a2291b00c03c0805c42e110900b4140da00c0614000070030303583c0c0f034444070281505100e2540d00b00c2021100c88202d05468001e20360400400c940401d140c10840d40c80181d070b1301c10f442683c0d00920128000442c1c1480d00d50540d0703d005210100102e0a00340d91070000c0c000e15064a1103070481e82c10381c5804050703090004d0f07400754a10a40d401081c001e0320440007408542c2002c003035902056000c00c100b0580280a02202c2c0c010707002915850580800441041c00003824807105a00404c02c0e42d10b07010140c0d03aa041c0f0308210260590340c411258403049000d102034490000341c603800d5030001409800d100199030000c0c2d102803481c0180c414a40f5090100c000c05c3c403d5450758201c259007030009009003020f40d0b034203603002425420031811600340301140b68666040410701d00c1745504040104800d02c4040407210500803400d1a086107145040c4020400e0842440e200806166020000074202c2c2c8440c0d0103800 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 940545125 1250 940543875 940543889
    0x70611100519060602010b090c0a0c030e03010914031b0102180d020103061a07050114012411072403152d080705031207112b061b020f060105100504 65
    0x45000c4c1c070303600c000e4064100e0106039409210710b81d0000c0d503541740354000d5803091101e41e551b50600c007442c0d40f01140c1f2950340c8100c05074155a10400d8a000642603002031744224040400303035031241201d48203918451385804480c010740c2d004004403251f80c10043d502c1080001c04071048940c2e0384080c00101c004040707581000c2c100741d84a91031091301a071600041d00c2c003944a5002840010b00020148020301400c1c0724071408200c01d485152440f03042d0807a0310b06454039030300d4280f04040c40f1030786082c41c02c202644000f904d5100b42d4030400e0a41e81c40081d0381000c40c0141070034002d01c0130001000c048600540b0510a103800d04800c01c0c00f0756102040c4140c05441c00c548030060f000d8594800742e0300c548003440b40a1192113180115a41007000500b0354902c19084150b4400f2080500300744144050b107185290688001107082c0042c0308007030084689501e000e61800601001e5046044454080003c2e00100f0340d1b100f0070b061600c2d8580007800c41d042d10001d40c3e180417030713210b800c205840c14099504000c1d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 940546375 1250 940545125 940545131
    0x170325150c020c040b06270d08070f031218021908010207080c07061d0607080d0903080702010b010e03031b0a0210020303060a0504020c0c040b1207060908070611100519 74
    0x7103440d030001c1c0300010301c0c000b201d0403c10740709190704102961041400e64410034903003e59990002d22001c0291a035100003814488410f030007542c406460f9840540f0485905142c404001c5c1455070004800700e040300701c07020410201049243c078608411401d18000c0c0320f910420441030304c092a40399914000c02c00d04000307540712402c40ca0300e880181c1200b41c401449105400c000074140c0d00c180300000b60f560f80c500d900307500d4080200c28084154400c00d010307038007203030104141014000d4a01c1004110341c003a0b5940d8515040070200242514400070300f03d41049140c0c1345c1d1070841e54010007205c00500840d070b0b800345550184a820790034020110000b03944040e81d070402c1001c640d0080000d6110354021220421200d848404000c03c03400740741e1455055501c00807000000341001e42c4144c400590083c400070060004100c400d16102e05504074100003040c5440800414404012400c00360a007810000c40c0d081a021b101503035030507681c0e102c100264a46000c124010070903100110f0b0120601d10074 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 940547625 1250 940546375 940546391
    0xf031f090e0709050f0c030414030702100314010501020105161d18011a07150c0306091a04050a0b06071b08061e15030706140405060703080117032515 66
    0xc42c1c03100740341e20405000c24146400910741c514400540c070f208000c0503420700d08517151038440705142c00d02c00301003120903c010000c441c0507075544034916001801c0781c0ea000c511640d00300c2c0c1d05828071b041a07100c181503a0420041c032060044200142c180e5015a01d010203e4542c8400c00c40c02c10300d520407032180c0000d41c2d603154001410058056505a542422905060191000740c44149103d084e5014055000341015031041d001541c02042c1c205c0f41c1450042b42c03264a91001404035414095800c030084507288034051395083c503000381980314010480810800007810f02107000341c81007244c010881c148038529546919508002003002d0b00c180b404031805440c18a60390740303448041388840780544803402d0008200d40d1608940c0500f480026024250040c0f40400503110a404142041203050081c08085800d443e1721016141841c000da54440f060352400a44001e250981854442d250f0001c020b45154140103010500d90701003030005503003149a440c1001d5000350058054250701c141401e0748 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 940548875 1250 940547625 940547651
    0x2281406070602041403061605030c030403030b0a08160905010b0d05040311060f1b0703020a1103073305040e040b070e0909010504110d0c09020c0321010306060504020f031f09 77
    0x4a403a017903016402c481d4681c441a01625006030000c55000c001403007080050760303040c18500910740152280c00c003c641099810009a420662a0440107043d403281144550014601c401c07400140601303041003003a541012141040b1380305c0d041510140d10745940100e010188a150901002d40d01e88054a5413400d04840c0320054040c103460085080700c0050503441224240070442c1d002d20b51603002000418040d64500b5540e05901c0d8045515005801000505410406000c01040411200042400400c4c0094040021030543c0c45007048800d11043c0710503810191207030b0300315400000d0000c09035240c400c1161501640441725401141c0501072180660054003d41e015600c1054151617504400d420b101d101d41d002803003d0f1000050000400110100d6401003103181180815030745403d400819001125940144000400380b4a00040050000307038443c62020780004c685c154984103110000354024003002d04001100e10000d4251100400c000c04520014042c80100303001c20541c0480c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 940550125 1250 940548875 940548899
    0x311160302040b040b0105190905060403030207090507020303090a0b09030d1b0909110d0e1603141612030302210c180603060117130611070228140607060204 69
    0x30080b80034034141403040c03e50b85030038000c0045808040e91001c4c18984001401d54a40705188011000e12151381c2001c141910740100a101441c029002006010714100c000001c40d08020a032030215003040c400c0c04100580865041001904101c0300502621032a01d443e04512030071070401b4229280040c0b041c0310b80006030b4241d40304215030301d402403401e565985090640e01100e03161201440d00708404035542403d6400020f02401c60300440d000018216105014012036401c2a140700d8002e0303104000b8001c041002c0385010004400540d0b690340f420034120505c2150741c0740241410f0300030503d0317101250745514030540c40901c2e20130301e0350341d007815210102c2541c002d80c05071804600f605524042420083c01f1603000f039406039a0081d210a00180f40441c1c6c42001d410300481c8196010200c011884030f01070110340c0342d160280f41e980c8003954070400c80000104003910701c3c1e03120400004132024601203103600480e10250100010b584240000448506c40e0010051480d480440e02245103c8018 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 940551375 1250 940550125 940550129
    0x905010611010c02060106050f0f0c030f0714120a033201060f05090d0227100e07170c1602150403020a0e09281a0403031a0f0607031116 60
    0x1c00070040c01c000361000701c3c0c030b4020074098080031a50400404804a0801005060115000c000203080c4000f112902d415503201104101c680031002c00c824051010340c0d00404484900d00c002080b8548500c41d141d01c890180b0300d0302400f455a61480d60f14040b900c40c15407a01c1c83e1003003541c0b4007820710041030856500300078000c0400040401c41c081c0c1001d8010000c607442079078001d0021041c8022070303007042262000900c0c5070908000c6103000c0e901400d40403a2260040c5003c0c400b03450014201000c403100f00704001c1c540310070040e00700f0f040c004902561413a00c3d00049516030715503075000d1000c8040079042034000020340240c0181c10484180300000c01800039240b0844200c0d601950b1540954603403002551014825040030011804032410210780c0140d0342008015004e103201c1c80e40302c59410f0500d22410b5450300305014100010140e251041e12000502c03540c40c0280c105000002c100c4807042602c400c0d0054500142200a00d8001c0000075807982d5505c2c1110300011340c0b828810742408440c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 940552625 1250 940551375 940551407
    0x50d1e150f03080d0203060616060b010e010813020118050d081305040b060301061b020a03030201050601030e0613020108040501061a0a0306121a0a090605070201090201090f0501140f0409050106 85
    0xa00400c202454100e07100882e40c203c043c1508005114200c00000e40c00502503a0340504108992a641030080580c00361781400f400e00060744103600c50000d4031012403450744a0400ca506800c01122034040120722400940a2900200c211181a150315820301c99410040d400700d0340d41100c50402107408004c1110110482030315040c80d03a0380013848259070311142000d1344094148018419103215448400400340b55141e1043d018515401140304070380203400c1034005035100c904122455030103014400b101d0702038000400c0545880d0101e08801c180c0c8210003410800410041400e114003500054090603001700b40c64211034501101e41c00f5a48500304240220b03041c101c0014915100044000205030408010b5205801001c11b003111490014010f052581d507940f6144c1c04600e051054600c5085290000184d4100600000d04115002e90095010030590031041c01542d92003156008229050740d10b41340c4520000d6072880b00c50155820000c0114901000054103691102c00c0388130810789 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 940553875 1250 940552625 940552661
    0xe0a2123010e1501031403070804060801060f0816030b061b010903020715021b060c0607031a09040c09150306090c03020918061501090e1009050601170601050d1e 71
    0x224000c51902c0d43c0d541c1c0d000d007545008850041020943c0b8292a108608040c002d5900d00300c0d9581d1049483d070070981000000a400d070740140891034001060307400d140110305000c0e24034a0503400089054a03052003100c2090786642182c0f40e1900c03a84184d0703900f4440c6441e89040a2000c0c0310440c0240145070069005125440700001e4010700d100f10956003140740c1d03019017a0880845048007802c180079001e41e800c000b0030048198070400078040d203802058950b801081c8400b8906e90b44610820302d00c10720348641328860612002984003102d400441d0b2003404040f44c4401003071503040c6404c80d182d00140031642040c2c001d00c2005228a00b250a491080b51740144548841000300c5d81c003015064001032590191001c9902c01e8039040014000f81c1c0d0514207104290303100d204100302400295010183c40003810014410060304d40070b2242d100e0303400e01e480d0b10740304034404c0442c090340c901400c91410320000245504800d4919040040c841010001c20091002c41d208004000d05103c011a00000700c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 940555125 1250 940553875 940553891
    0x12030309152e0915080d0e06032e0b0a0813050615040204410a090504060f110a030606090513240605070c060e0a212301 53
    0x59004103142c01400008051000d49907545068080c088141d001c002100800d0540054540141d000302e82404030002d84141e459403502e0002454034048094030b10502040d03032144100340e1a52800e0703e0740000410a0f41640703a10306405544c2610028540041801e100d04c0301096544113600149910b83d03290b6603065165440c009200c0c4402021640181076030880030109801c40d0010701e02d55945030000300010318007640c8081c100411003100e1449240244004850400190b003020182810080c0051160b50400504c0c001aa6250703540075283d21b0075a1000850705004013a804084080080c1004010900d804207031040360760400600000060f040c032030045502440b8803095804c441000e81b41d90500b0326480801f80240a050143c442e0304203c00c44412003401350307100e42c00004c21050b2296540e440700340c2015100c83c3c074203401180603c08031185920580c0c45a40044046401841c00f003080c080c030814021450054105002e02440700d03403210340c005c00030b981e1458050802500c0013000344031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 940556375 1250 940555125 940555153
    0x34080109030c03021603150504050c120f10020c0c1c05070f050f0409021003090f0c030305070c140f04110705010c03020d060f0503030912152502030c120f0912030309 73
    0x440d039800020f0821107a2400041c1d05c031038623000760b500548070b44166000460401c021400c4000b00214a1000b036000000721045000c050080e1070900a40450943c64504460600b65407050b100e003a4500072400f001c015141e200b01020021191903002050b209850b903900108040400c060240c94482c01c0c10040109144c039062040362070303055014120060000c2d815001741c0041840c06001d0322800c40038007038180001d49481c0428041c3d8802e88071192202d2090803d507185c1c0f006034010080c0d10b022014004000c0c0d40303400308001c01c150100c0300421041d1444407602c504d40200c40009013103600303001d040b450540e016005091041803010040200031341e074124410004445100b01c0341c040d0000c000d501c60a06000c2e101000d08010501151202401015001744c0307140119452010902007030140d0042d07110746028207a0940051006600b06071049041540f0340407452038110624100194024080e02c0c0c10090300d0a40030700074201c1d41000c40303522046850f03500032140c00d4002d00a0135a819504 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 940557625 1250 940556375 940556413
    0x4080c060705090a080f0a0b0c090d0f0501240510031b0305040302101e050c040f031103011503110915061303060f091505090a120f0f0234080109030c0302 68
    0x2160040007d10251540740c079201000381e005469650641000c00c0501441d880c1c615011240606c0742c607541c20f031148071703040141c00c4940c54012020380300c0c244558846013070b001044481c02da07030b0111501d08056a59920070381c0240407000c1a89180c1e4260700c04055110340680c001031266010340c09407103078248004002011140c03030034100400002c0e0740140342c5a10f50180d20840d80114943c1081e45000d80710104210000302036401110b08501264445000b401c1c00e00032190340b0400c00c000000f401d4115981c1081c0c08014140d054040c400d51070004d01c07110100407403588040006800544e03100105010308205001c13074002640c28608010030100180710611410803030b83d40008805e40501c0c44004580c0c0035000c083e209180030f114041e1480c01181c84010301c155054080d841d07200c400080504090f14800f0195402d50a6400525101c50700800d0a42c0602c00301c0d02003e0f2607034603000c0c0c40405021041e4103810900c039a41ca003d18601c10503410182404006010343c01701e5910300b0000c4520440 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 940558875 1250 940557625 940557643
    0x1706090609070e102d05060405100f02010b1c1b0605030613060e15100e061903060803040e07090e1e040203031b01150803070b0f04080c060705090a08 66
    0xc41d500405080040f2000c0c43ea10981160102e0003415031309564001001c03654071140d141703d5107480403d440724240000e8203400b20080406540072400c0516003030000e5110514400100d00f13002006d440c404046101707621004040e07000810312183c10380600c1911b0661742126104903548070180720300d003010040c100d02c83c5084441c7e980d01d0a2561b81c1d50303024000003400146101100710307154040400c0030907490001911490740c0e40d400c501e01c01d600c101000f440d140110a05401d200910040c850076403111011640d40c66540040924106802c2c002100103101c29800140749010125000c40c0a0000445075030085140e42e03611425a61600d4001040d0041030340c80480c0741800c510f80d07000304811260210380c001d00040c107882c14100c001d4050340d1403003240440060643d641e03001660703104002c50317020009064100d004600705030155031802c2081c100030300321103014440c0c640001c0801481e2001c03100702e50150410384580e42809503003c0d2040e0002c2203103911802d050100818440800140122 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 940560125 1250 940558875 940558891
    0x51f0b031c0c03020f060a09022806080903040321030b0a0b0403030f1215061803020607060506030c2e1707120f0e061902030115120b0a17060906 64
    0x800004622080e0340c51038141200301c01354003a464000d00702000c1804014800c400710100440e90f2050362040004112900c0c9a000c071705014034410f0000c450407501120701350350060074202d0481e107401c0d20079495030040707900003048868030200c00e100c00440c2a501c03841007083c81e08c080c020301030ac40c41044403409041c000d91010b036100348000c1002c01c4c426802154035541600b0070560380840c02a00d030b002d40c1d43c41000d09a03a460309150401946034040c01d07800d0f1500c1d8007042c010b10f69043d5030014219100b1341801030102c580344c00209450780d4043c23112100828004028070400c00c84440da40c68140100700321280703103621040c819001e0902500c1d2540820801c1000756850346d81c1c0c22016249854410300302d001965464502030841044d52103890b804806078402000d0a142c0885810740c00c065100388456041e00600042240307071501c4051030a922460b0901121001c001d0010000505d038200d11103030300031140a0001051000c3c030807035004001d0464140c07000d030360302c604815a80d00f00a541e002 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 940561375 1250 940560125 940560163
    0xf0d0306030b15031c090e04211407060b040b0306010e040b0702030a050304030f02071a0706180302120a031e020a02010506010206190b010e0a080105060108090d0921051f0b03 77
    0x400d40e400d40c4017089400450a0801450350742e00c07410704020748941100c04803a556038004400c03003112a682c50030001d500041c40c00001c000c0301e000541005020f41d000c010440d589881140b45266079940202240c0c1c0006402ca88036980e554441c4904250180ca09407000b0790070b48003103040140f0220484014171100d0b1507452464540b66002c560030301104081808502032024080740300050b09400115a11102a11070f480340e0b614140101145c5102d9140d050000c0d50032104000a0b80109a0b0000d0043d032000864840c15a540141c000d00304007100042280710101d80c03038003504499405441003103034513802000b00fa941d00e0010382c0d0b45c40c016101103910b20080b00b00c113608030001c0c0d000192560418903201c240d070b121802c0030911207141d64002c0c91582c3d4444c42000000e5900108036640a8004402030181007818500906059114000c0c10081e10284614800385c031118508600003075403000484482d21484c542d40809078480c0c100c080020f6050040d140024500001d4030001003107206000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 940562625 1250 940561375 940561393
    0x30603150606270e1306110c0c04051506210c0a0306050607111201060305030319110423010e1f03060605070c09020a0324060806062701020f0d0306030b1503 69
    0x80d00c18513000b003581c01c50940c2d5100000000311107004e6004007800a90400303403500784c1c480659003402c04001000b8002c40c0f0300410810b0310001d1034020540c11001717444450b903529041d0000780b5444044149030018040e500c0c02e2004111185004000f1500075036010030459458404000092096090152006128174914061490112100b449100c0309030000600382d943d0b655818210f4008031404650714014041020131007072035028000ca01c040d402d004074a0b00781005505c25500c600504000031014605038045880e9000710816905294000c00c441404d07041401001e02c2d00300e814044800290811f880003541c2802101a01c580ca9880406092024107041d800f80003500010008005c02d910b642c0303501840701d50b0107400d0100c4459986907407800d80c00c180d07000c1d0001d0302c0a0407031802090100310062000c83d2420545c1044400004541909010400102e00d0107802c0729a1107503034003c0c68500503080e40c0590041040343d12a104030001662840703218070b84000c06140c419011780101d41c4c6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 940563875 1250 940562625 940562639
    0xc090a1a07120e1005040503060a020c0d1b0213050403030c0305191503060905030315060a083409050306090d0c0209130c0f0e0a0506150a03060315060627 68
    0x101410a108038500466043c0c1c142c0009403a04100c0d601142c040740000801340901d0038203000780c44d488082d80700150b14226141d41d0503a034403182e181c2c480d0100180c02039482c07138000005000c001f640e6001051560445920150500201170075142180804e00d42002c20800d41e00074001c0c58455041e4004011181130303501d4080c8040e144204031080d440f030103040c001c800501203100d00007010303000320015a100c1c5000540022646104040c01e03114030018400c1706112907108031407552103600036100216102c5120450302200f20f510302e6030030150900c108486c40c1075501c00070120484034104c049900ba900c880d00010b40b17504074081c1c070400040000c0864005800c0c1001610b4003c0403040304e00c1420002529038461441c6550440410582035040810081600308591a005050203100708000d0501000061410507080c6240703c00d48004281c0e11700e014007941c884030040d6000b00c1c174583d0440c41e0610000050004d400760700080341c03a2001c411064240b001c1c0d01c0078185500e40f40c08904030309101c1c03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 940565125 1250 940563875 940563893
    0x402030706180b030403020c0111060f130816080a030b01210b191e062607030f060906030512042d05030f070e011d1b0c060c090a1a07 59
    0x12110000142ca00c0009041242500542c441da0203540580740c8000d528000604407100309032a207010382e11500c2444114100c0c0b0103403541000e207010b290b1070489440d1420983c54020329075244000201c11401c41b0510012070000c150501032903070104648800c590040d1240034002c0042c0c0d8040b004612101a4891150b00070724131003a00802404070f0441180140c1a007005507004503207405c0118808244042002c4003107801b030405170800282902c204801200905603001341c5c00105c50500c03000c100300b140a50301c4003269a50030642445002d46540f004005444284411103507441340017081995240018160340c141d980c8800e030040c95010300000078041c03645c00390741026140d0701080005070541d020084a81c01380110f9005c0c218052030641c84078003101059201d0310203120300100d81c21010351814a22a80031040e1484010001400110500d0038042d11f24123300138424a002e1000e017420b5400035004210085503000708107a00c690800c8074141d00000d000019a205000c51390008000c1e103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 940566375 1250 940565125 940565147
    0x7050a06050d1a030609070f0b09060a0e0418050f100e0a062d0f0605060a0f12020c0a0807142a01020f01060b0915040602060c070c0803041512050402030706 69
    0xc105041c1a080b04400a8200030040d06c074400568414070040007c0211620b02100814110344498100141c100110309103114108004003044103110581d5402d6644c2d600034491a09085400c2c0352120b402d2500301d9940d5001a000b46551146040542a20511b401601210742940740500008001c1e907480c180a0308228580030440000540c0b60b0b145d41c02d10000490300d51190031408212401f03101e0b07280e01140c0080e000349014800030842d100742c1c10780004c4449400c04040c41c10400303001205030ba8000134011110b1409140c000c0c0050101800301074409000c503680a403002c0c06100c5040d007041c40d41d0f01000d0b003503d00503034108004c1022400c40c6485001001d201801a02e039607400d451506821a850b40c1c000d074843d017001003a0200307281400d1521043d0745a44a203914a000d007413200103075942c40c00410f0600101c1c1c1c00a5501d0070000448400001008484d085940b19510f441c021400301d8158400c610009100c1c01c80301c03d501c5401d008860185d500600900216408e04000300c80a03c03142d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 940567625 1250 940566375 940566401
    0xa03080a02010905100902040b03070b0307050a0c1203050603070b040e040b0718060819150b03090304030c0806010303080a0c0f0e0102010e0f0303100f081f23010807050a06050d 78
    0x250750f1100c08110240102d600c110b000c9400000c0c000c885104000854010755901030203540441420b100000749141101c6c1c1114003828178684404090f1822141c5c00b02000c030051803e80751074880d41500b5015045540285002c0b0306841405440300b20050850090388a101000da45070008107004c60b8200c41900d170044564034007468800704131840c81141c1c4074984e00032000225400100103400240d000c04071100303650b000091040d900c02007104400e00c0894050201182c5000011074411201001110019580700c100c941d60603640c3d51000d070320303200244010b8010030700c40d038006070760b21702c4a00c41e9105800003130b260344019800c9014100c0c0c01380407041c400c50642d07580d54803001c40350100700206402000c42100450340e03481c0c5004503e081800a9001c4009855903da040c000460007043d112050520a0030907a00c1280c0c0d0700721a000761840b041c81e0304544590401c4008200403621465060321000011a1091036568080c40a040342d288944000200c05000d144034440c40390304400b16030624 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 940568875 1250 940567625 940567631
    0x90602070b10090605030f070e13140c010e3309060d0603021201022506090804081e0609460b010f14040f0e07090f0501140a03080a0201 60
    0x42a80d5000c0981400c2d103024104140c0e84408100602c002e0107002c025000540c0904102d200070301c0001d035200d58a00494424a000a00080304421204039071007400713070032000a0501142002150343c40e00c00103500180058860300c03604055041c510a003504070080111521402503001e00d0b2070704035a100801c0404801c030204034400c4a552450050a00d00c103e07a1f00c00152a032441c070410801c826500b4020003180d00501c880303012240100b030307400c920001c0c0f601502d804100c90318094004200c2c07004010315060000c07502180d1510005520340d005002d014041c010a0003503440982c0c0d561048503500030b00e9000d141d071816200860051254200c55504401600b1700c0c0741801d092101d9090191050304100170058101406003409895004041824038541224104231190855085140032140110b131180303010040901158080e05240015600341c5402c0d64464400802401c0e6250418a40c41d013448004942e042c1400d45e448880e000080c00100050703d50b5403505840d400a040c2c1d10300b0342d5a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 940570125 1250 940568875 940568887
    0x18090b040f060828020a050d08070c150f090311100e0d0b0402090c030906010b1c0c0206091b03031902070909241a01031a0d050d2a0303090602 63
    0x1102c0c010200600719682c0500801e1071242d54445070904c440d02124400f4000c0e495090260f04d44c0e451600903201c0c01e03100d01c848401c107410070146038401c1c540f00034000d256480700010461041c2d0400341c143c8040d0b075a841190798141c40116409095800081c081c00e080000f100c01501d00744610440031002400c2284c0100c20020000d0b1140c40b2404d000e54000301e09204200031880d08409150b8026030304000300d411400c140781015500e0105014005104200240e0301000104140c1d15282c81c280240043c06030035110300d0000c0d12400240d6148150744110f04003c0135050707444002c4040440090002d41c1040400000141c2c3d860036100000d00f5402034400216000301980501203155000b03844000000d04d2500082e04017191103003903140d0481c0b074551101c040007000e40411440c00d02c00d29010a1420251055406540c1c4400106078400803042c0101d0822902140e018401000e64503541401310f02714805130080700d594941c24007400c01c002d0120000078005c2d44821400c1d8001c19005040103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 940571375 1250 940570125 940570151
    0xd0e190506180103180506010303050708160309140406060c110607050d0206091009030813020a0801060e090c0d0506010303120b0402030702010f0b010203090d060e010e0a0b01031218090b04 83
    0x2070300c42e50048009480790784074030045580601800310002039202400c80701301071a450350303a05c484c010700004082000014910003404922000e1320780650380f41d03005009040c4a403130050310003001e038070802940b240c8000c0d407a00203150030310800c8115110703a120040d452426903a00100c0b545e10710b0000d58080700c18041c84000c1003080143c80c5400704190010100d5040850143d0720300461a903854440341d04048103000042c0c0d004520540000c2c406000215814040c40003c20341011500840c59561801d07100084000544016070702440281c0c080c0c842d0205888240000400700003806415588403400410000384241c4c43c0031b101400840c40041c5880c070f400005010b81c1d01c02ea0f884030040c1e45411506074001e0180c481d440f080d51007400194a48007001d404107210180410001d01501da40c1d40c00301d1000c601c00c4d0010080c620b0a0382c20790380d00546902d00500303083c800380401d541c002d600b100c40301040c5010320b440c2501d4901d0905100100e03850140741c030000c0c00d040d805840e000b42c0c5444c40ba01840e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 940572625 1250 940571375 940571377
    0x306030313151e0909020a0c0206030702070e1006020a02120307021507050105070206010f1215020f300f1816090f0203061503040804030c15030b030d0e190506 70
    0x74014840503402e191404500040c18200c0b0b00c3c0b4000400b004a0107840015508107002c1e02c1100d0204401503110000500c0c2500d1512005030701071340000d0008104194140e01051850039200541c90b44001364036242c0003081914014058000541c3c082ca04480c090300e0301c1c01c161072100c600003044034580070003035011407403810005524225481020918a04014081c003d141d03022041c2e00c02042c0a43c03500e605442c90080ca403149074080c1145001020610a141401e106034007c0181c00303641e560940503000c01c040e44200c040700d0511110004074481108150150808500304044c018520340b180194082004070180c64180d078101ca80c124208030103400c0c000440c1410b03c0c0c030f80091407603203050306040949040301c9400700503501c100200111640ca002e41d040181c0002c2c1500c41d00e070758071407030984018402c1340c00151004a541e00001035103403143d605641d01501a603028045250610103145d503131448001c113840460700c505890149070405001402141c200c0c5100000c80c95078410214140b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 940573875 1250 940572625 940572629
    0x150319060b030106270e10030602030f0a150b031b090409050c01090807030201092c090c1005070308061e04090c08070f060206070f05040918051b0f060306030313 71
    0x603001c000c001008015007000c5400c0e0340d043c0d0300f210700a000910840c0c0d00d0048184d402010303003003001c04000c241050007450490700a140e10031001c5640341003c0e550401c0d00482101c004505508155003c0780c410b540d21140720450704c0b111b0800d03080d929040e151071070040010009030a41c403028062512269030700e0050f20720060042c0302504503070000d00d00040010486402c0708000360711600c01000140da01040000c1101c4d40c0c450b070740c200807540504c0007034ac605035085040c2c0303600c2070001400880ac2c0045545181d0b42c0044509600d03040c2200f81c107803814080c0980c01340100d00001c000070358504040340300c501918011500c141c00111208009421121007080c103480c1280480020b02100c0c0e000c20414005e040e142100482461800c00c00a65920000f8004410008820044082d981c0180e0590740905403060041c00360500c034102000000302c806005840ca07209901800c0711080c0782540d607981c0340802400b0b40c03054410380d8050000c943d0010301740340d415100400058140100030f1200d200 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 940575125 1250 940573875 940573889
    0x2150403020c220b04061409090304050a1d151003090213020f07050c091b0a0903210e091b0703020c270f190b03030d06061107060e15031906 62
    0x48200200810f01e07044601601c2c85034016490010140b08020501d042074900d640d003100c1000d0150350b800691811801150301c06c640003000c030203001c60b0740e5141e13600c14600760000c0008104c482d59182d100341418400b03403100d160003410411800c1600d601c640c0240403080d0000e00b01c1c0c0e13106030910304070308100d03400368010707800090002c00c0e1001040018880c01000181c00c0360034640a0a2a80d40000c0c258071076146032076840d100040c2000c858cc001c0b68640011500152440d40144034480d440780d00b40c81c0da00e04540040c903000c3c11025649000010f00b030180c03d5407644442140d103403c0e18010103902030482a0150312580c2c0d462862591465030b980f852607041c8014400442198a400000100207080c2101c080179107402c01010091526800901c0b1402110202d00950050082030841c440c80c44107080383c2c1d0401001080c055007003020035007103090040840c0c00b05a40e0b610708480c00c0c410800700e01e901070481440c99a001c82d5540103075420220040030344032a121210a824101d070b41503803001c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 940576375 1250 940575125 940575169
    0x32a062802160503060610180b0d0b0a05180703110f0d06060e010503221703040308010608011a0f0a0302041809060609110703030e03090a17190302150403020c 70
    0x1e4110b2080300054001888181d00500355418444001290102c000005a080100b50503914410074504107208000f4142110b06030754891700004000d018022481c0c083e0f000741060000060503090681410082d449100f40000050703d42040c220060200c007a01e9145401c1b0038010203886415280043c0440900c810340086c403075260103005407000c2d01044001d410301400b402000035090b0081505040d8001c0c000d60b08100d101e05240c21311600e0742c03e04c0703a041c800304080208010107400520182c143d81c815280c3e006207a982d043e0482e84450100341c0030740302400a02810800c1c0c03c3d41005800f25400703c1c1005401c0170384801d81c814040f103111407080c55054a48410600b44806441460b001d4030180343c1c1440f030712040460781101d40c440c2c048020101680c9505c4020590014416150f00a500600b9820110313940d10710b40800209445a01805009807000c003115026100340c1070041075810f401500410a40425030031038032074010700070380550040400c8a5000d68030302880324861580e0086d62 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 940577625 1250 940576375 940576393
    0x4022a0708070e1612020d05060f03010506031207060e0d09150804030504030f020f28090209010207060f0c06091202061303051c140a020306032a062802 67
    0x640d1612039194062611030b041042d007070100c0b403815039007564849501d0480c0c011151805104940001449000c100c1d214400314100141880c40d4000034000c1c8402c80d100988409200105400c0b200180d80701c1e541039104c1265012010603100282a100780228400154400640c541030708018403d00c0c004009000c021050108044284058108170f8007441c0c07482e651324165034080c00c140b099000241250365a036421404641e9000b80783c041c1000044c09025199100c640091880d01e19072b101035541a00242e404241f0026910a5400c0400e0581c0200841ca29103a02641c8001401000390304002c002c0e00b85a002ca551409580c41480c07045040d025400403000d0003e0414001403c548030400d10f103103064000c650b011081d036401e080588a820041580640e00070300501400b42d040c1da8100704c40e0200300f0b8201040d40038600c03505081d01074a1750840d1031000790f148080a03518050000c1503a20200d00d290822401803d0380c020030607060b110107040c82ca4400c0f03048410b0007101005074007661078 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 940578875 1250 940577625 940577707
    0x106082407030b0d03031d01092306060a050d0302101104050103060605030f07110c12011505091b030402121b130905070b0901021903030c080f04020d0f020402 70
    0x3490390700c0282458100300700c00325540010f01d11040c41001030304041d1a8290f091040074410303201c00c1c0b04012078000700404052407401340b492010380c0c0369100000f142d00c0e4880e20070310b8001c00c24510681c4001c00c061400c50603c810840344a080c2ca009404500c01c11480082c2d40c400340c45403080c140c40483c002c6441d90b142c172000500307803845500308a0400c00c050003448800881c1c1e1120741d80010031418155440400403402034a40b200041d44d9a40c410001c6825414000d0194081503203c170349001e0f007081c0161654140500701c20300759000d4044110302c0da440b601c082c0c1203001854000c3e100903c1450807940001c950752401101c0b480780800190550a201030a140c4a2110030700b01d4084c4209000080e41512800e4840312180f2462194480000d1280402d038802e12800c0e03400030001c0348090f80100e546c20002d000340380718842000801c0000002c160760800f01c1103141e1003154000c010040021040d039030706082e05003115080b17800503028007203135080034405585030707008041003100e244000c0e40101c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 940580125 1250 940578875 940578943
    0xd1805040603030509040504140d05030a05011202130203100506040305030a090501020f030a0309081e0c1b090610124205090403050403230d180611010608 68
    0x482944128684201000000e410000790b07101404116800916550b85050038405440001c0c01c030344150144521400869400801648c083c02580c001008160307240c96944030703400385814010f98480c3c00061641840d503400d400035a4425804018108243d60303072004a8110b40090f0805c170380980011402e02240b591000103000108000d2009000d007072040f403001d6450f445040701620805071a240e5440c1030207140b000b202d401e144880441c210303880390107558150680080c040a0200d00236696040700402d000102142030860080940d200341d22440c042005186200a01d9030a10036640c0c904490800c407440780b4407880c8000540d03841240510940c083c440002d14200d05402001c211031510103b807080c0741902981d1041d111403040362154107059070303180240c0e48000c200524140189141462255100d0340b01c0c040c10044901d07000c604042270700c400c0c0510141010901c0301c14803c101151040d1181ca03c2c1000240000031002d88501c8568101070403030101b400b032540181c6000c048408018 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 940581375 1250 940580125 940580129
    0x120a050103020609040902031e03040303110c0a090b04150f06090608040c06050f070f060911041b030b06070c2c040309050f0a0e1f0b0a0804170c0d18 66
    0x4104500d41c1940d0024805010311041c2c0d50050b65150150b5045440c20007040d60050008005542c426101e60040c8d540d0303511a000480006031886050540100b000880701e20402c00107194811aa041181903c002d165070141d0a80c00740c1c4138400002c00408142042000c0c114502043c0701d103034201800900580c80d1503015004002c540310030070000c104c1d00480f000603038242d46092a558548001a6186d90040140c0074013100d542c4030640040080301c0d48550101841500c03d15900110242048110741c00008250200d48110b0103160495100398018030f0010001030589081400310748a4402002c031075007000f503580c407a0310102000c1c41c0141040b40f000300a025815516441c140d41c0080c40052280318060141c0040c85500c03856075201a0100c0c0603284960101b0240e1270001c00c105400b0b8940d1100c1800c182c1000e001250b00018441242c00c0494580c45841c8161126650210720b070340c001c0390206400500348050350006800f8010143c40c040e490b80c400c0c2642c04000c10002c82c0c80507075 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 940582625 1250 940581375 940581391
    0xc0d020606010207080312040615090b010f030509190201111b130204081507050d02030f060906010f021506270702070803090a050f13021903240e1005041112 69
    0x20301381004000781c00403c54614a00c0c454140c91039840d20f1038404d000d003c22a08141360f80f020410003096a15065014082c02136090340c0d000f044a00d6a082681220001e541144842d00310703c0310340d01c0003001e10400c99119841854106119191032009900b05440403140c0d08280c40142443e40e000c2c9007114075240c610301654002c52800c1c0c9001e034029074400d01c03010006008060072001601c414000c10a8580d0444440004d41d44c80c5000341c0081c03401d03070040f00e0081c40340e40d818000c01d500c0d51159004a01113051a0001d203085000c500b1904404d05000f8030181c4d00003090402c0c0c542c01e54115001000706684a1003003003c0741040ca02c0030741454410303080400319078010305c860f00300d50b510190340c44200c41059811545c200040030120720b203000e041840c259071030b000041d864002e130300008040200c503016603401c02050302e901d0040c01c40c64a803910f42c0d00c03a24003500c00903c03280089048960b00014074140c1c0356407a42e902c0e40803905844156048034040303040171400001380005050001c1d840590 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 940583875 1250 940582625 940582633
    0x4022422121515030b0105100c0b071b02041d060a2a02011d0d03111612110607050415050c1c1215050f03060103170307140c0d0206060102 61
    0x400744003005086051401802414508032002a040ea075540b2540000340c02c5041c03110a82d44a05204111302000e00c21140600c98003c070024405100321540c10307140ea8090081c0340f203500d4100c030444d5102441c40300c80e07564034400000c81006a807070384100c013240025a0b47c1d1054507080c050082d403c0403070040064107040d082807200ca0f4410f1155800b60912201203070080c107007440440701207004040c40c141d140c104003400f074001da10205d40041d85661445441d46c1c24000d007400301c40c500c0c046010b0708000c45500c2500354000d50014600c0203101200c000f452a000c070031800181013107440c09e041030711014042440080d040c0020040c4000d2074038080a10b0918900d400261300c0095914110007403049402800b80e0004100d0900c1624a414843118610082c40701c0c1c213002d045010414418031985200300021115603040e401c000c02e885048a40250251041800c000b42a00712a48001d00031020040c44112800c400300c0500050241554500010400d42d01c00103000391404801804d102c2c15544 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 940585125 1250 940583875 940583879
    0x180301110a080f040c1508180102040303050f0702040b0a17011d06160908012a0207061b02060706060305030c0d08090a15060e01061101050109180b04022422 69
    0x504002250b4001044055008003039407103042560303280710190084003051070b102c0804450164081081d9022322400c0c1c0c001101244044641c40c00c0740320310b2100074086a000d024072982c00c01c008000c0c00f0303507e0002c2d1000c143c034a06000001c5010303030203402000c1155003040c0b0190003203070244540d1038002c40f002000d500c1240012038807a0307202c8006284a804039650400241220f01c50190380c801480c048000740603003a64501690001c0000708680c511504d203072281d030528280f00150100449109441e88141c10300c00700149981000d80b51010782c0c1026080041d40c0001b4110b119080055024401554031a40030204041c204141e1403000010040020184604e12001042c22124640e210106054260048071540301402c00d075030164110145020001070815003000c071291400c40b0950003001240e072944090402c44110284c41485440244001800a0032000d0a550024002840300041d06405070301c402074a0300a49403120103540202d50418811003240810801c0250480c090b00f41034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 940586375 1250 940585125 940585127
    0x70c150315090203060102010f050907030314040b030712150e0711120306061b01090804170d0c03030902040f05040c0f0b0316030b18010b070b01150c1101090b180301110a 75
    0x1084034002d4000d100c0c0d001001c1050f0740e00035444075002d00001da40511507441c1c14144e040e1908001c0c0b1040c0c001c036001c40d900b80c455501110440d41076035050214981503803555a02141c5034554481d460241d2562040c4203195482c411240304000c0088180c0c0d40401e203082d9000902ca030540c00d51604040e4080d03c043e66802d9034600660fa4000c1c800d07641c40392200d208682541c4003d0a610701542203528000a41041c846000d00400a403081080c4004c200305011104941c0d500003100c124001440045500e000a80300380c003d0341c84180002e002043c00e142111529041768010340e400c480c180c0c0e928004001e6100c040400784c000300140403105045162200050301d02c80a48050070041507034404d5000341070382d00ca4101e1103042601c2109000c0c5ea40c3c48d400009030541c81050f040e10b00309640000010302501102841030031003503582e85d0340072605543e40c5a0480240c4026600e06110303500d02d001c1200503213440074000c150500b2050441e2140c3c000140350031034510441559000c1810000b15801c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 940587625 1250 940586375 940586411
    0x30a030f0e1f0b0418052a0906040f0c03050103030e040908030606031f060536090a02040504022b020906160302030d18050f0c280902070c1503 63
    0x4140740740003400c444001d051102c00101501c02540c0d034814900103100d00c0010001410180d601d119170111115841030000112108181c100201c021440320074902c1c100e8206200c2d065003183c0302900c046141900100780e102550f103508050000240d0350001042810742c0442009245042505c3c20844c842c000e80700c001c1c030b40c400202842d000b0f20001000c1b5000640c882000c03400c0c8001c1d001c903020724544441c0010055403100c505c8091229040720b1045000c04d00c0c0d006020040480d480240511214405005041380300802054480d9030a0000007a6502c03140010110181d1540c000e1001c003a0304080002d03410301034140c0440c058030521800d000707a1124021030704c2c2d40c0000b480e41402040c079403400302c1c6944903440d0421101c41c14444203206c9441c000e4100c0c0000c2d44502c0540f01c40340c0b2070685217030b518a0000031701d41c1d21181c800d031420b5003144c2ea00f241c000848095000e41414546401c04a801c2e80d00c009821629105c008508000a80400203144010700d25490b00348035401c0a08513110340 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 940588875 1250 940587625 940587643
    0x20c25060914030c0a031a011d0f190509030904050a140c0c120703030203180c150c0a050a050d120c050a0305090312190b062a07080708030a030f0e 65
    0x161841d4001d214120783d01005510600e000042100d205540c49280203400c280a60450054a0000e07030004502000400c4240c45d00c03040006901c4000e03510010310030304554020380041d44600b074602c00944d07640d0340e5004036881010050010740d84d40c0c00c1d103018042140c500420396185140380110340e24001c841c074000c5940022500651a0301c0f40c0c06070910504126140d024084101340000e414010181c0540165224060200da030004500350110a07e8039903c508060a901c901120f4001e107054032441c0160400090500455802c480c0e039076181071800d400c1c0d1605480343e92254403c03403052a4822200c8010100d06103050004000340007000d0007a004103540142031507120360000d01190070410550341d100c01c1c1101c0c00c44c0641403054000320101010324100300003e081800c22600f90402d05c040b030301038042621000b200041414003900000044185410042c00b600740009600e60040007100054150074020710340c3d4844190002e8103d4a044020180f07050400c40e031401c00080204009038 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 940590125 1250 940588875 940588889
    0x906020c1906143604050405121b010f020d150e0a05150310060e0c0f190212030a0b0901211401180c031208042f04020c250609 56
    0x10140c1c3c1c5400d020496401644c04c3c3c105604640d03a046410034864080601862581c50b0240900b02452402e0006944044030041e2840d0b000030000314254000c00010000310601c451442590000010040d0940340329401302541e164021805200c1c1450a22850443c1c83c208074228104038986001450b61020003030480003141e940b10000703402d4180c01c03040d04200d001c000342510f500007400c01c0224003c109034040e0750144032101c000500c01281001c02c80d180d00710aa00783c0c1342000c90040b440b00011030b002000c64114024080c48140c280312a1b0003450182c00c0c0260003249040d240c0c2c2c14440b0401d0140d10045d2080001d04258001110504448404580040544421071a9200e043c2e02504a9900140640400180c2c0030244500903003d5016248503c801c41008000c914040700c3d1840c05231009000000e0280e01d142040380a6000340340010340c0c138603940c003110310b102c40020101e820070045044130390400c5104920304056902070750702da03001d010030b4050303407a0400500400400072409901 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 940591375 1250 940590125 940590137
    0x5090a0b031906120b0901092a0f0605090d14030708030a0c020307020d081b1e01110f1213020619030e06190b0a03060614130e060c1809070906020c1906 67
    0x81b0300c80d90079001045019040040c000404681c402c0c903407140c40103c0c54481841444010101e030083d426511036040324841e9403103d0421142c0400c00c42c20317042c90b403070446200c1700b1600d03010110102800900b500c140136a010035203a1801086140913589452900e00454204100e914010303944e503c0c40c200525085040c0340d80341c02042286081e8080305800da50503500c0380c0c0c09060140301d1034100401810b00814020701160380089582442c6000b4a40c6031400c400080c485850080a50081658820301122950071384c0c2c00c071350300411075951203541d600501a90582c0b40c4450541c050051202c10002040102282d142140800d00c108665803041021a525100d25034515950800040065504541d040061965500c1c2c00020700450204d00c40c010400c6160440000c1461300c144e0b0315910705075010300705d02c1c0e44404594401da8003c035516519010500380308038207078960064051144c40280c4503180c506041003406480c6c05074001300701d44110148146008041c010f404a0412241141400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 940592625 1250 940591375 940591381
    0x5190506070c0218090609011a0901030303090c1a0a1e0c02060315040f1a06040602060403120908070f031d03120d1b02060708070306030506150105090a0b031906120b 73
    0x4081907844ea4604441102c240d0602113507050104245015500180003000711540b40001e0698051500b1040c0c0d500001150041010030f001c2d030481e0240328420402203040c00e86400c1860700d004c50070b50590001080c0400c000d80100d803c865441e4001c110b120455501101a280c014016504460002d0140c0c3c40400840c5603d45640201501c2c0403000b4014000c581124003404003c201c0508030b6002254008113103d41401c20700d046405a40096000c1c0510341d84d80d403000e590021503034611000c072540d61194600803a42340805803103130600c500100306505120782001000c2c4e481e4081d0b080034a21051300000d0319a0350008a07224901c0d0b08844107503e6901c80c0754000c00601000707954000303090000d8004800141e0100b40384d80b00380c01d00c2d00c0b81c10b80340d15900300444c210390030707800b00804c45d50003a40454000300300c11005041d0080d051428901c0e0510b100045601da031056808080808800f20920841382914041810010880001003114514084c80c01405805469000d08401c0080000c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 940593875 1250 940592625 940592629
    0x4121202010608010c050c01050106050a0804060504051c0809060901150614092701140901170c06270d020609150f0304030c0201020f0705011d041d0105010305190506070c02 76
    0x1e800601c0c60303e000700489001c8150142050380003d804c64125460500045081809a803d036004030b00280e940b108103654664540c0000e2202400558983c8141401080303403041d0b00d00818070ba40107503903401c03500782015002c0c5850110701a209040b964100001da81c0c541c0c03144038083c401c550461030002c4e00d1360b41409007801c841c403400000ba0380108492903e001200f00b0000003518400340714000102d1a030380c90550307103010380c0f0f19604240e00c241c40c2401001454101c8204010100703a03041941c0320040404000341c0d4a601190100c103000b540001803d110040441c2035020700942aa0009545d003019800945603100d02c00c0000c1c81000e07190003441982a503c415281c64060a556880e0327642064207010b40079241e011401c80c010b1044a07101c03102d0101c041462811107406855246004040950030494209203581d4990060740d43c10140e855000744142105035002c01c2800001e0550450411034200841045100382d00c402c2a004103000510000b882d40e4420880e20b003400c9900c1c45840 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 940595125 1250 940593875 940593881
    0xf0615010c14031b07090203070923220e06090d050a1b0308220c0e06040e03040909050c1909021b060709060306051509040504020607050616140412120201 68
    0x4007050b240c0b00119480001894000300c030410001c81038101d4071040e80e5501500203911013103928a0010352502e40c00c000345a082d5101418801c00304c910400d07115166408a0000e1079503200201c43d16441c01c0003000007070924810640381803882d0740034250758508802401d80e24070010904400708000011308081c018800e9520b00b4032013101d08442d08004400d4100245004029100320f061a000a0701c074103000c0d0400820342c410645c0c048034640c0440e192640c48200000000c003015041901c8080801c1103000600c02400070b800030728800900210141840ca2904004699441c011015248014038400c4200d201c0300c111a00b5150260791040031300c2d123a1100e078040300c20708201c40c8101c805200d640340d08a140f541c04c2d039040307960401c4004e035603004204903100f92082c07810710018208003020080c182074011980c014006403000d464035000d50b0340d031072910300d04940507424001140740c04010301d580320040003125004214142e0600b424101c4d503542c00b00f181c903001030401c92800551041e441c000c4d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 940596375 1250 940595125 940595153
    0xd02030f06070203030f011401020c12010b04020d06210803130807020406060503060f030304060f1b0f0b07020c031c0c02130606030f0b27130b0412020f0615010c 71
    0x103410380381d850070b021401a583e07030800d480840300a42e141c1c0c00030804071a14109142030090580c0106900c0e2070100900850300c0c5204074049481d5201d400c1529903849900060420101da44000110702c0e113400d800d02070510414805650041004240e0404100c40b881a80c2c0c105820007109407000c1645c5c64012460b00c1070200c000e4120303040220015040f1740000c00b449c82183c0a555210a0303046c203074101070304d92240e4003404010038047c000001c00c0a2164548004540580300d0440c1c4605070794440001c0c00b046e0b807008946141c00e800810100c03540c140001c601d42c2e00c0980042c11300c0002d01d801d0062148520a1400c10480e41c0d412590071f40d030b80c0c3c6010004010301e071001001113549580c0020007600003000a030a8090070264005a1400c050704207401ea910000805001c6104081981c4c64055000c0c24014141c201101000c002c148622649806144a5491301c10943d00c0100d0282c01e0410119000d40c46411a00421031045150390b40d100740b4042c02d10b0200180303146480c107804c41c0701300c1c4c0c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 940597625 1250 940596375 940596403
    0x60301060c140a2906150301060e03030417011e050f01030f050c0d03080603070e0c190c1b0f0801050f070503130c080a170a1b060207050a03030f0c0912020d0203 71
    0x181c58500c12000114048010800c4c03120b0310180ca03941c41007480302051001c402850001010001001150311031060019400c01c014203991615585e90143d2880d155071214541b9280d5546002510314401a00c00050174410a10240050310340b920400c058024140f00141c8043c07202c94852080010621070240d00c3c401c02081911402c0f0b242c14001d01400c4102c4405000b03109000b400305020b000608650b10178480200c0c1c00b0f01d0900740c00212604031002c040f04e8810f02051f445030200180c00c10300703a20152400c21011180c0306145c50151a00308070540d0042015901d00818070400b20b106005080e884446410032603500d4481040c02c2280d0b200290020b00308610032080428507902c04a0800082c5002d007802c0c1e44084442c4804955a110310410a800320b40204203400511f03040152280c03070940959001030400d9069210b8606013001040110000303651840c8240c5220424031403d062000f541c43c145020b1400d110000030079014049001e0711541c0c030501040c00315a402c000b40440d035016 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 940598875 1250 940597625 940597643
    0x10052d011b06050106110a080d0c0c02060a02030c0c010f08130c0f06091a09031902180c0307090e0903040b09061e0a020c01021506090a06080d050c0606060301060c140a 74
    0x541c14002c2c02443e0a00a510000e45200c000d00b0b108000024100d4090b0f4103c0143c03403031b210100b24294000e01e40001001c00348441e181c81240036070360f40406000f616a13140c024650b02c101c02007031a42031640b644a01814060a180d00a080d030b648242001e43c0301d1030260b0b41419030f9085060a1100065550140c2006031042c5000f20700302d980301082c001155001160346001c03898500002c9107038021001e02e107403d0381c03200311080e0b40ca030006211458454006031802e003403109081c000c40e565030350484510301400d6001080c09007081c4e02c5003604005000e19043d5000a0401c80c00c0700d5142d01c124070911000000100d080340103540c81004451592010049143c05128214032042164002c3c41103c4054020b55a03080e1083d40046900c0145050a0600c41c401c2da0721101000403901024190900b011b50700c100101c1c41240400c02102200200d40f601a2203003060546a8078090000f45800d00818080c0010002a42c210580c0380b0700c1070784885c0c51a600740c00100014500415841d001d809401 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 940600125 1250 940598875 940598927
    0x14070b07030f110f1e011d0a3f0e01020d0210020d0209060a020105070809071d0415060608010915120f05031c050414030a0e0f0d170310052d01 63
    0x65014020045251000028012412004400c00c100c034444096000f0036040110914001841c2140a1108074500a00f100703027201a4010a01100110f400007050b4103100c500058049400044521005100344020311aa402010b002334607081044403002c01240c02144070084030031160191840c08002510541d2034500f0944000c0c041c01040d1142c2000c42c2c00400400d92409011071580159503217500c00340c0c640e01500500300c0c40c07004014000e0f1352920b0705008d00e050729180b50140390005c1130982d40d800c40340c0d410a04400c00f12007600254810a03218501c04002c6040a181540761140d000b441c0c4400048203401d20504602c030300656080e02d00e10b51504000000041c4e40310502039070152041d20450039580c90000d540e0320038801002e01040500c0c911072004e00c1c1800303079032040b400040c1c0109800311030b0fa914500308142c2520b0a042c1514040701f001150180201100c00400b02211001100d5800101031410388803410b441809120305c1d90300e052481d900956485070a02c1007c91905401d00c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 940601375 1250 940600125 940600153
    0x5040b12060103060b07030e060a050409051021021c032d14090f13020405060c010e06100506030106050a02010b151e0406140904090f14070b07030f110f 67
    0x40400c641182c04a4070300103001c1035100c00e80c3c00340c074203140d41501c50107016081c0b01e0800005820044501d01044420040441d950b071a81c01014060140d088254602c1c0b030404d969503961a20004050414040d48203010002d607070351084001710b105000c0521444110310742001c4039540d034203241214600040c100184000c21400d50070722407101c5580e84599003844c840c2c60b02d00706841001d8110343e1015511119035014541100c2c0c4040a00c907082005203016a14000700e007041d04440700e040910703503440e011000000340610000e584508055146940241040d0000e44d4500042c05401c042045c08203482c25101d0003503003e00032683c00105030100160b01d03220034900a612000400b44c52710200010880c891500800391000d40b0303000c2d1280b0022007030030785088115411001905603c152110302010100340c0995009031100d0050046a1481480030249840e1411591201c100001e00b00811030110307034000c003210303050b07800c1c0d00d0a8003603016040c403214600860403000c84014001c0d855040c42c1c00d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 940602625 1250 940601375 940601407
    0xf03070207030b0108070b030114010309060606030911031203040b1306090c05040f05010f051504030c06110f0d020627072309130b130807061d06060a09050705040b 72
    0x80340f0030540300c02a0781e26007a5240c4c42d203a41d0f118591040070700307000620a106003803c404a035508107240000d4501070b0394540c9016150f0503406480426610400b55062082e01c48421a901005030014602091414a243c04511000704094815003168001c40c194081103960f01c40f18640049007840400c005040030242845c661081c0e5200d903151081c1e00104940b14054203040314400c600b14140945007505020380d250b0551022038203c0d00401c004000150400e1095024010907500c081428070340007002803801c44000d140750f000e5800100d409011b1640021050791052134401d400b4100c9040c05002c1003261400a60220940103148002c58075840a0140589081c0c0c20202500008904003d00818200581e40325071803405c61031002e008171780c10000b942d4200400c3d200043d00d8031240c5c1c468000c150004801110159224080910941e4035852002d41d1005440050104e80c04c100c0e0001d40021024030640f80465164000240258026001e0b05c0c0140602b4100c0381d61181d410f00c1c5080a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 940603875 1250 940602625 940602629
    0x130b040c090509060403020a030809031c0501080708031903020d0e030d0e0601120f080f120c0703030b09130b04021201140105100c0f1127090607140904020f0f03070207 74
    0xe94500780000f40750010004506004903015006018013440c00c9e101140c02301e000400c2c20100d84402c0100541c1c091484000151000300518000b5255051038062414148940d00030b41e1203a005205504a0b99907401d902440c81120b401c0050399100500586030180070f02d0360341c24025003c00b2610320f04102c0d440c0c110903100da015205a07100d5030389901d4008000f80030500041c1c124051520346a002803070310001014180c000d030907840d0824001d1003410b805d14104959540c140c040125102080503003600540711244822a41d0313500d6443e041d40141114003400308042c0900664802145c10340d201e2001c0403400c244110003d1181071001425504414000e1142500610b10410000c1d541c5200358109200320f0750101038150042040d403600c1b000e4045131000c0503400b024a1001c8103d13940006809501d108103001c002070323a490200e10300d0341018402000102405901e41e45030303103040004401c0b00c1140c40111001a2200b01c84039141525000d18440c001520307600006101d00c15400140c8002 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 940605125 1250 940603875 940603889
    0xc0b07120e0301021c0f060504060810050a0b010806040213030203060c040509010801060509070f02010b031e010b09041e0f02040203042f031e0c030a060c090f080a0b130b040c 77
    0x39901d0440341494200c0c49202d4070780b101d5200d070800a10302485a80c200d8010301c4860b0341c0c0403c03420703150f1001070300b1102c2540c840d0000b80e000c4003000590034075600880c0d502c400e42c0c1070108003940d586c4d400030b004030600a0600303100702c1e4001070a84c4190880c03030703c51010303540103012612a40ba0200300a441c0d40d02900981d0722841c9180d00026606034140502800d940c1701038155503494840100544070440b60040314010755403160045800e6440400c0109502804405040b107040540c9121501f11031100c0d0005002c0c804200401010900c400340d6030071400c80024030305000b084581803103400e803882803c000354094000014041070041503144903140503079461501500c040f48440400c0400d0102e030301c1d9034240d040341030055280c011a503812401f4041d02420349220380c00c8000001d0a0100c84c0c1d004807030709030755002045000c6502c40c4001c0003500a1008a070056030600c1c2e61075944003da904000c1c46181318000040001883c4c041581c1800c1d0700c164400001d0419292900f41507602c4d0140c0d00c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 940606375 1250 940605125 940605137
    0x6140411030c0403060e070e0403120515091b0c030301030c03120801060909051017011a0a0303021c020304120308010e1e0f04050c03030706140105100504120c0b0712 73
    0x80100406081124050300c00c0b41034452a0500e16901c15019100f9400c201032940900000007410300d40c007030b41d007502c99442551528444c50b141d07a65842152005015180f0079a5110014022500c2da40c0741142c00500b8043c0c5003000000706803400245105101d0541d036180004000042004403c00c1d40700241ca11440c0c0218098420490466607041c1c24442c2c0d400103510007908102005066110a40201d944445000c0d02038545982241c1c01c0d2407244000d0040c4e5680703100498071646903203c900061001c8540030306c0c041ca9900c000396210b80d03800216618041d55000255118003c208480c000c0c854184000504006800e024000203001d05c039032115000103400042c00755008101403d08900254005040c903140ca02641e03c0d4070030014000c90fa5880303407009800a95401700f000c0c11001c1e02c60030740400c6024000310030074200401a1f1149000e00d200c2c02d800480660420240c03001e0f03030001124030003130014070300384551200116480910690300c0040c9140a019480034991a2506540c0f505 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 940607625 1250 940606375 940606391
    0x1e0816030e121f020d0b1e0f1e0105030a0b10170601020102070807080705010b1507110303031626100509161409010309020301020d050702060903042103050d061404 72
    0x1036031180f0494a810112401c0c0c000082d00980641c0d010b0914000b13070840004120b01200041404603110a4410103d040e80b200f84448520317041105900441b41070342c15a90341801d14850700103212402070418103114020002500121032135000800c80e0328000d110030b200710000726014008c0d58404c0401e144801000d40001c0f40c55005000310380c64254020307082032400382135071503002c4550413035041100c071035488505210466503504015a11911104c403507d9480c545890190311307800d08907089034042c0d0818010002007141825423030752604100d0500b48011007505410340200076146918a251003050400c1c080d01074407003c01c0c9015650309440c40307003142d01c2d440c00c962007621142e030320400003032a2200a80810400034001d070544040c1810003203a88034003a4000390030790f00901d0389912001c2e0381e90204100700c4d034104005900170115401941c0703040d052000040b04940045952114000c3e4803e10b5010140304504640c11106108420000310307484a40c1e102142404100d40761140e070410b030740 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 940608875 1250 940607625 940607659
    0x18120801060212030406050c09030a050106150903080f0307020a293702311211220e0708061006090e0711030c0a1e1e0816030e 56
    0x48a4400c1024030140c1c2550745941d2001b02810f40203001c2c1e1204030b0144800750907600d0070414104a948910008290a41007244284075401c0701d940d0391041189201c010808100d440b000c940c40164000301196803070381e400e40242d00c0d00150b44001841c100158450142e0780d0b0480403584000302d940c103030b25240d0340c4640000c0d0421290324540f0001c0c410880c3c02414940c0c509400d02049150b4841001d4100a82080c1c070442c40701c0352400580400302d004081c01102440251140040c01103403032007104264580e1204031060880c0d80203140540202ca01c110000c0307840404d44050011680c0c820301811040000d100e869a4152064a80070710501000c1403480c8400d41702e0b0702c01c2c0d4186581d80c3c04101c0c90314192000c000c0003d410070050100c6081845001c0c01c1c10300080241260200c021f0080a5003440d000c40c1c1110042e00c3c00da01e0000070750748d00002821110b40b2400d18521940f014425100909240701203100b00c60800c1c1c9400c0002d004c1c2e03070405801840701a820340c42181c010060100700300c2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 940610125 1250 940608875 940608883
    0xb0406031101180f0f090f09050304140402040b190e100c061509050f01060906090f06080402180a0902031606020a1209080d05030105031c21181208010602 68
    0x40240220103689545280354410481d0741c501e41108842c443d030701961000e50140b1418550071446200407649410701184d000d502901c52aa0400310b42003100c4615621466100d014034003079003052440c0c0c0840c01c540b03940c030341e01550085c02920a07290f684000c160407400880400c180404042520381940e1040b610b0072602c001407601c6140c4814201e44120b40e0342c4401440c054a90416503011598040341e1484203200d040e02c15007100c2c0c1d10520310750410307001801001450380241c040000c0d0307a07010300c07444148110a0080f5000340c245002c1980303c502c0000c0c05042807810314500d00d91140c04001c100102e64002440c1c09000b80c1c2907600d04143c00c0c0084c042604240a044003580c0024040310001c2ca520784850741508141c6030800c1015110308483d800c2c800050035040000328040700500081c0f4080c024001c05405400a10804480d020800b91030744110202004a1040001d01400d01203210b030030250012102c0803503440c0c00ce0585c900940c1402403003c003140000c082c800040b5010340001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 940611375 1250 940610125 940610129
    0x6010306050f0d050109140c092a030c0c100b100516031b08030a060e13030e01080912040f061b050a06020f0d15240801091812050d0b0406 61
    0x9000c24040624007028030039081ca000c4000c4840e5986c50b00e0780004a0103400306881d51650000c040c007100520381e82005100d01018099521900c02c188902c8180180014280046100072540d0740c1c1300c0d550960051514041e0010001d03090040c0744548032040781d2071740015541441126403215140c806201102e040c0120905182c000d401001ca26012901030005c00b0300428032884c503e03a0a43c009c3e81e61009030f41040d41d2811030162205e50a2040c0c54002764030a40c4880e030404514141d40c0d8584006002c0791181d0001c506210084001c5140c440c0c060102d0544103800350051940c981e607030070000703400302032620424001448508106000b044e0b044000550709811000030710303001c201900c4280003075000b03100102544804008003d650701e070602600300380c0c0e00002141401d4500d4000b100c03041c2c6810314602c810099420310740300c91054208452038191440108e00046403000110420041c00044c0c030090702c0c201c010014040950b038403500520802002c18014844000d0030000c1c04140c902074 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 940612625 1250 940611375 940611379
    0x603020403021e0f1c020906040b0108041119060914010302070201051c140106050703020115150806030a14030a18030305070204020d11030c071a01050d020d110919050601030605 78
    0xf06588030119036101c0030031060300020902401c880d00341c800191000a0f240b00c07060541c541034034036000d528104030000da202d10192810b1003440a10380000b03081030f400800007040699030140394062500d0326030070340100e02007011807140001d89030030014007000058800d08014a0700e241c030f20f080c0741d4824000e55403290343c1a16014109008480c095204a504011402030b40d6580d5038664403000a03420154020700c00c0e915240e540b2400750400901b580c0140e5103100201602c1c2d074003000b50031541c020341c4c8907004451504d10034980b0f030341001134203112a058000e424602c4170308545020b51808002001c0c0700e07603e900d9491500740031081c800400c8004c0e2102a001c6807003072000f02c4c05428260014102d02d181100002042044c881813080c032030704299810540030300c0100c0c055003000000c840c409240707040e00340d0a01043d890480000e002c0c034a0507500a0240502d03032181c408003c0c95001580000a00400704491460420503040640405540c11b5a0650078840450a00d500070700c252000d42c1c1c80 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 940613875 1250 940612625 940612639
    0xf040b0a050904110307080604060311010309030512040b06011e0f031e09030e190e0c130f0e19050603070302100903051504120908030703080a060803070516060302040302 75
    0x50425044825041010410103001e01042140410360301d601c5602c111030102034141e07440741040800204030b041c000701120301507843e20105001041030b244180300b40c0c080034070703000c505108035103012121030040c030300c080000f20500300521040100482c21544900d6082c1e0318a450b15820710901d49903c00b1813070a200115a401c000109854442d0300000c011030341d40070704422502c5108104400300d40c0900002c0c2c0024210081d000303204d260a9050040382d1000a100c3c040003810f00034540c4030801c000e00000f9a400000861034800b030b60722a0100000c2168091289804d540c0741c071580c00c0d46008480002d0641c0010090200142c810f04c610740c01814041c00521076a03045900340040a40389602890921090640000024004020030005441e44901c1c042803420149001c110124900035075a0a0200141c000e0081407070002c00e4490307007505490601160340b5054401c4001307103070f16041000300303000004005007844800110b0f81c0356000210440f0343d090b036a030f00c0100c040780124040251b000034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 940615125 1250 940613875 940613879
    0x150516050a0801051e06070606080f0a150f090209011836050106170109140a0b0a0207080f0304080703090603060609050409051e2503170d0e010203090c150f04 70
    0x10031082c8500e00c0644801c3d02c00c0d100c5e80d6100004e10b95003102c3c104680e0b40c0d85030f0380280043c140030702040001c044000004d00207c021a55500e0003041d41248001040d9070b80c102c050000d01642c2c01007540c0680142c00c00303969503152003400b031484c0c446d8501080c41500703018800070268065031800c140c03041850710002c3c00440c0e10850405c2001440f50565440d900c40d140460183c2c00c04944e640a8800da42c00014141840e2071b008003a0444022052500d4000350843c07070100b40800034440c8e1180400e84010385e1807410303250001c0703a400707481011400100c0101c1080b00300300241c00100002c034001d0302d910707410a55990301102941e44074083c1c80000303281c0c29410401824140c101d65005449a419034220b020700c8418003414203181240701c03c89500040d0003990342c0141e45205201d004411804c207000d035040da119541c2401c0c400704449217110300000d02c4644c404551f80100c003546441030003955a400d0007c101555118580c02c1640b1601400144060802e40c2400b1640b084002d085c2c4582414 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 940616375 1250 940615125 940615129
    0x60b040f0b030a0e010218120123041a0705070201120b0a050d02040e0111070309060e060405280b03180f1203090f030c0303070306150c021507150516050a080105 71
    0x10308043e1100d400541c6440041d8590f0b20207002905945544c44100e00a5074460380030007518800e42025845281d00d403c4501c0e281040c101004641101124030000254865103803c4a84500e0300459036010300a2000b0300c51800d034440000c00e41c5900036a20010304c051011901c83c01c4840b842e00e8258450201c41c8108031030b00707110080300085ea00080001401c803030203c00084c01d407980b1410022280740d00092000405421030500409007006280101603140004080b03002c0348550300a07240308a542401c0c1e03800d22031110422040308800203160000450750b4000f03006042c3c0080d07031441030103030b24080079603100080003895045207851840201004200300340e85170340960000c0e01041c3c9038002e40a0310401054104009d18070464030303800860b0f0340d14202000600b260320715049010308034500c40b0501c01041c1e000548068040e0121030305500741d9141c440b0344403203104016000345045103d000c102d1b10f443d13403544000d10548000c100804001e40c5410211a5881b840b0708080202d03502c0c0005108034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 940617625 1250 940616375 940616377
    0x171506090601110307060203010e160f08060d120801060e04020703020303150a050a15020c0108370c0c0507080a03080a02030a060e0c131e18020706061701060b040f0b 73
    0x4501810b240000d100e911001c20b046911905d03080e01c400750000300400240c070701b41d90500e81c0b2010084c030304030020f80d00c513400402c1c688000322142c0421451001045032640e0f074081c07041d00390758401000c030100208a000030745991400d01c50742c0041250002c1d100410b0400e802150545c0d0741c154095441d680d0307800c568406e150407031110903400240035030700464203841c0c42080f4005803016400d403d1b06070000017802442c0c9291040c3c098104010351007400760f00720040460104140191301c4545103071a0807010440720b01f50300040c0b611581c2c2088402d503111078000340304a40203400345090300c1c9050340360700c2c0903940c510852600034001504240012440c0401d90302a5400400c845004198203503290007c100b07098044e14440c596590010b4243d0381c18100b09459002440026980d51a01e0545501c1c0d80c030001142c03044078898282c0d0f640202e09400c0c55411103119a50082c01040100e03200c40e1121502c0c0f000d5840200c0340c0d840e140001c64030b0f02c000001c4d0303001c440a02418101031070078680c0980c46c03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 940618875 1250 940617625 940617631
    0x30e040614240d0e0a1a18010204051e0f09100306110c0627030f0c010b040c1b06061706070914060f090103090f080a0f03020304020d0609051c030617150609 69
    0x38a008501d91040010003828480c500350700d042c0410006410129030787c201c40380c1d03112440184d0f0f0784100410011500d4102e202c00c1410b020000600b0040040804038038281d054004450b4818041d10401500304502020041641e0040c0c0e010001030308400b48000c4688100c403400c1107951301c0a0000382c010240c110b4001440302604024604880b007842d4842c1c5136030030400c00001c80301d0000c55a0500c2e008240f0440280e18400c44041c06288018107014005001088054901481c8011180b06101290b0002c100a24a40885980380019000c10795200c6200740c1d03e02c4000303101c96900007009083d14075040500000105140d203082c004520a01d5a81d00c0380f00d000b811300d03868482c081d02046c0346045e01d111041c0548100d580e21941e01c070005204900910700041814414001d10001d81c444000300b058050f030104c00022119950309080e0f190003400010130551607071410000c1c81241d40740d04080101c1d000030214128400c0c00320b0016407642424085000e80c00040000140b1600d4074000c2c4a030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 940620125 1250 940618875 940618901
    0x605090c09120607090302150909040b091501031110020d09050603040311030c0d181d060402070203030d06031110050a0f090b07050309090705041d04030e040614240d 73
    0xa03032400c4000b00c45007841021a002004a10074078000c00c10b50503c0306000b00348044261a0602d400341090000740403000280000d044820303140c0c0022499201000b0213961b4240c08440c0120940e940e00d40307441040048550507000799400c400c003001c032034000107840d446803405444155000d4100014441e403500028400c2d400c118810b01360411100091004100d000241313005090f0036026440040d004400d402c400c01c403100c00490080204035001110442c00e41035024500c000c40d202d0074001406405041030180d4580800210403001c0f44e00d41c0d1042044903c140b00300441030342600104207584072205004408240c003004001c85e020320429036010207010904120220030f450b1504e640141d08004800c07603655100084111151034182a5554030500615100d0720f02400c00c4440f010300000050a600041c0c00d0b0f002140800d07000d0351501d5080000944200a41566068071007100c1001203d036900400c0f00c210504951886c0800d2100b24010100c0c0c0b036803800d828400c00170b00914038030b180b0b56 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 940621375 1250 940620125 940620139
    0xc04060e011806020d03110306030717120f03092406060304030306081608060108190803150405130b06150301060e030c090106020f06010f050f040507030f0f050114040605090c09 78
    0x14000d808414150006441580d00900c61600c0807200901140c505480b1442d000005100308503c0b2b07034000921500351544440941104072030096441e142060010308000f2a080100e03c03003110103c20701c0a913100e004400c0c00c48110501c802c0d544280754041c0f080e600c0e8104668800034546007091002141c009200c0d04d000103076035a90b900054140788001c0301c141d481746034007882000b01310310070031801e4050220385001d8030003603001101c00c1c0c50a04415800400c0124084000f500a004400307003580c440c0300140c0144003a140201d0001c8802080c920200c3d201c02914000c03529034107141c510440003903100c0072740c00d15690924400342c507036240362420994984500020031203141c40c0e010750b0900034241c607001400311070404602603060510581043c0640040400304102c2941c0c0c1d5000c2c204d1030201681d0004880e21903002c04c4028240381c40d102ca000908042d45500d424090754892412100b1808040c030f584d0007500204415120350b4400c0179405110031010030291b00c50340d001061141c00051803a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 940622625 1250 940621375 940621397
    0x60203030a1109151801080907050111100f0f0f0c0c060b040f0905030a0f050f04180e010c09051905130e0f1005010503150702061b040515031e0c04060e01 68
    0x508038090210030364945801c01708481150401581c10011100400d0034009082d140c81030555a90b200940f046904010000004000e0b040d018461b0180e1103807080418000380c0201000034015226002c254200c0314540001c0c140e90380d2007031203500615a000e6031106507178030340c40d20340602a21030000483c0d40540e40311003001d1074152500c5400c02e0303644a0005180c44105148001c1c0903210082202020700104010380110580b0380d008a60540301c0400d0212400440c4607410801022400300a0510b5031900300c0c281c0074141c2010b5000100c5108540703010524500180080b03501c420b42c81150340000100c40042d1050b5029000170481e5800c0b05c0c00ca4102410039440303c1d20b04243c070809161034640c0e41c001445241414401641404168143c041b030b00e041003074000303540b494000c201c14000d10800c0e07a5480211207120803a0000e241c0141004810002044074541340d0f4800c5d00c12030b00f0072008891860321304c0550000340c0d20520a10030001c0c20f05251010686a460980d407182d4100a205265 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 940623875 1250 940622625 940622629
    0x3270b09040f15140f040506011b11090a02031b19080402061e040905070212030f0405121b0601080d051603030e010906092307063903021006060203030a1109 69
    0x14030f8024100008101030020441050106221881d803415010b03e06081c10004e00e66000b2140d00c92558010200c444940824141405c03055510020303680d00c84100804d010b811225900518041c0e82125034801c6200c2d4201c1c09040c3c00c0c401d000c0983c3e0120185807a0700d681c140555030890340240003030079080c034046410302d030b5400d070710703802c10b08072800c1034003c58184100c40072071140c81d621900500007455407102c1540280070b00d010003040b00c1c0300c00440c1c00000341041428001804585c00f0150600d8650481c01391b4a2040e2401c00354071001d503c07034840009090342c0001802030251949031141ca26101d43e11481044c0901201002d40030300d40c4607c4d41c7c40a4040900c105484a40900000501025141b4110050f207281c484030b1030078648260700c00409040d01140710411500d032805d180702103442100314001111328441c5040c100896585601c28111940d0900c10300c05403080d400d4502c140ba950900c0d4007194514060040103034014000540700b2061a40420300120000c00000d0a101c00400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 940625125 1250 940623875 940623911
    0x111e01050703030e1c120c05040302060a0e210f1504081e040e191a061b1b0a0605070803012c0406092904021905090403270b09040f 58
    0x103600f48021982d05240c2140c81c0d80071181301c070180b0034144180071031091f114008040c0d004600000e0706c030320313030001d01410607500034001e4805c101400742515061141c0012044c03008a070102c0441c0e010301910050412250021884003d980e804102a507641e80740c94594000d40d8005404289661401d079600c920f800ca5014080d100528130614401c0ca9450f14080c040b0703a5403100d24401040605128401d41c2e80c490346003030001090410f0760465180e80740084180e4200e0f154040c3d03c0070368011b0780001032101028664004881c501520f01d1540e41c0d9036030004596910a010000d441d00381d0510040c0700520482c903080076030301000442002210326800d00c49040103025203084031556030303910350302c002c0056400c02c2c0c00b80d4010381e074500403e00400d0040d04660000052009200d6910b40d00c01074211588107481801820300a070540c2020721b07181c6009441d119076001d041c0010000007020000300404410f429042d0341d0842c540c42c5c14914442d061001910841c000d1030b540c3c988036040d50380e8450b02c0c20 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 940626375 1250 940625125 940625143
    0x5030a0206270306090610060905011704061d0303040b011202060a0c080417100c0306061d040e0a120e0306010f140d0503300108060708250804111e01050703030e 71
    0x40905111f0611101c050b02d10300755544964103102d51034100b0030141e07030807861007100c2c2c1504040305050b650341c61500c5001002d001600e0b00707080c0501650383c1e0140d800000030350f110318071840a01d80c150b601c0309043c41c46a504920000d50000003000032200d9103114403590003841d48600102c6060a88a04440095040c035041240300f980c4032507a85459002140030300d424441440c10104941c07800c00701c0050181d000314600b0380d00041e424601d0b00d0261210303448805204480001d54040c003c1500c0d04c1c0c0000c030909541c040002d085612410f010785004140f041c102c0d4180c5466400e194030704024a8104803040301696130195800c0c010307101045090000f80200007500140038000c07009002003c1c8641d004030008288010400018000e01d400020144c0c0c100c042404d14072019903550494151030a45000100c1440314040d00f049030545d0407501c1140100d12030721a40340c40e54580c10600103d001c02020219006202454010442d40102d000700b200600920300450b81d2640301c102d0340d140c90481d0b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 940627625 1250 940626375 940626391
    0xc1207060b270a0b011404090204080721030f020a0f053f030402031606030506040f050412050a0c051516021603080a0e10030e0705030a0206270306 65
    0x80c100e900003880c140d45400e8100076082c0382564482c2e41082110b0080500a040780301e240e584424458150703009403228070000804c0200b60780d0301c035200e1b244540650014800d400c2e584c03081c0030010503484600980c4099030140c0e201d8804e0207500e0381e20101d6840c000d405803d019400341614480100e401103645a01940c041d000400a024072201154040b1504024501992502030501980062458030140d0020540380080e51607442e1400002d042036642202080740c42020840020b2103505038011178130800045604104c10070380360081102380c0d80304441c014803008030190083d0300360380154040c08110040b0700d050450402160307150b600d0110b1107845245205002002c00c4010310300c580241d8140d11031071024200c5020003030b014000c00ca0302800001d0000360041242803041d48203c240890381e0744002d244030403094507040044c0090107074802c0214140103a00e80806c240c1400509880310b83e902402c081e03d07110385402c52040e0304200075440c10030400d2142c44003a03251750401c681c0d0f026042c1c0e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 940628875 1250 940627625 940627631
    0x204021b060f150d1407121a070f0221390d140c01150603090512041518050a1d0906150405070e04050907170a0f080c120706 55
    0x8940c400700c216030b40042003640c088484002c40580744c0c4030a01007600566000020070f0211403c051402d080c0300c0103400901040c3c8840a0040c244580e940b14100d00c1d0548440d046940e884c3c594040b5a80c0300701d5103500d030140e889503445040d0951041141c6500b404c1081106040c803200c41026903800c842000700700c0c540d00c41d01424031301400d03203401c1003500c14040d00e00600142e80804400307402c5c0c0140300001e40600101140007034002500307410681c14070703224050204d807190311068058010598401c0640f0b00388100d0700c904041c1060b1004031001d80b01114040ccc46403a041e14003c88001c3d5000e20b8240030300848400010310342d1980002000a0300300c41c10301a4035140c0481c0e0340c82c8441d40003442ea15840d8480014043c14900100d43c40198080555011900707507100002911a003410030049074010789007004002c0d59440100b049402c0c0c5001481c101c0403645400301507a0344090300e120240100c1c03540b42c80a07001501307100c02040050400b005440e01004c5403001d00a0541000a0540b09251 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 940630125 1250 940628875 940628881
    0x1020a090303030b0a1a0a0201090b010f0617070e0d111302030105011b03080103061d0706120f0608191a040b0414010e0d030c03060b0708070302010506011b030503040204021b06 78
    0xa018010341c0d0000409403000c215243c03811b05004040543c0c0304840c1c403074120020b15181420b1007034002200442e048032074110039594850420818404502ca01030000f03090032718100c0a20308524038507019001c60780d6005507044064081008c001c0e01c03420100d82003407004854a00315120107141c4242c800070014010b88a624000024060410b4010016214240d4441100000707400c40a034606690700304c1800145040b4040c7c84401d10860711403134400500c514900061044e9200c0c900c41c8102d85507400c00e01503401d4058207801540d07464001c1e092150800009030205403442c00c401c603080f40c018103000100e00c45481582c41d825900351820307207007400f0003804c200503c004100c00c0a040070450000f00a880c40703821460383c88262110400d42016201c49800040f540312341c0100010300ba052140c15a5014640340c9111150700c0104101c1c055400d01e400030301903600500850007065010188000d41d100303540c1d82140c2c254002030049034072507070900905001000b00c6125158880701c1c803005101da81 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 940631375 1250 940630125 940630127
    0xc09050703150b030403051818040210050408060606032802091f0c1502040504020d050901050a09170a120c1701081902060c0a0812100605030708190e01020a090303 72
    0x19446203054034101e1002d031800c22450686104503035010781c0510b8100d86554000b0180c01d000044007603030b01c9e40409440340a86800741801e03511401580700f2285203140e0301c2031280c245c0d114003941c4500105034202c40005069418000002c6d0345c00250b031204a01d03020a903440741c03665101d401140410f81d5a011904500c1d90401c5111854074101102c50815500d010010040041c103580740009c08804000c15142445c26080c1c064401034103008205541f1600d0403c50407004100490380c482056003450007041980030305104289140e50440700002103501442e041503070f50384c4514141010020103810b800190340f0544600c038a4100c0699403500c1e4a0f084031a41c944850040c3c1280016070840e41c0030b03145031030245107508a00303a0305840702038680503807031291414029400c60183c10014005160946c407401c3c4d020380d40c420403202038141402a03c660040700d46010881d83c0002245c0080c000c41c2450b41155101c1040940a50010901c841070b00ca0f8507080e070300301114020200d4001c43c0c09000701 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 940632625 1250 940631375 940631381
    0x8070b160237020d0b0a0c0306050402091507030504120f1b05060d0b1203070804240e040b030a020d150612080924040e0105100302030f0106110a0c09050703 69
    0x1004180c1500a1054518441d46502241d442240103040ca001c0d00402c115181c280752900e4994000b41913242629003030090b08041c212040c08840064a0101d01140038130f020310030b41d586680f000e4400c1d42c0c5145d26500051056000850507401d0207014080000e04c0680b0100c1e00c15014400c0182d410140c81c14070345980038404010743c800c42c05080c207078280700c0707601ca07142944c020445401d000f241040c0e400740412010800866030810f1800000350200502c46000001c4c021a504098840421191a1403507004003081031a4500051111500c008191400d0780003015148401020b50381c0f014010760009050210040e81207401e48625101d54400c68210f104650040c40d801c0c2000c8407440c0d86940b00c0904d8440c002c51540318030180b091803944030b1101c01c03450307000d0468101a5903885072550148544087c007440380c0d034850080c400d8115041131013802074030b000b05000e5248542a90030000281c8200e084901c8284691145040c100c02044091803000c004003c140f00020342428007613001016 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 940633875 1250 940632625 940632643
    0xf07020913050604020f0111070f05030d020f0709050c0f2b0e030f03070e060715150506030a0903030f020d02030f0c0c070306110d0c0f03051014090408070b1602 71
    0x800c07403503610301404501c02045050340282c1c1202c100f081c9501c3c40c03005850b8885a01e508424900c12800045005081d00000b0000e9400813411902d11541d1503400702d0b51840c2030444140b0982162604110f15000c40d00700b85e40190103102c1e0039080c43e01c440321064440c3c1201c8001036280341c2c1031000400c1c41d0340c80000e8218410308900306001340211419265901d00c942103001804110000000f940144102900118a4001001aa0b8908082c102031105101d1011120b8a0502d054410020034510004241c102c802c0900014116550314900d90002c00068006405140d20f50b400c071003044001d0706c01000c1400790b13400c00507183e01305090b000c441210000e00c2c020341280304104800800100086400482e5032000b0040f8460307520022280680c01121400506641441084015140c07c03054011961050ba0b07400c0143c2e42c0d64058004801b01785108000f024080011f11003040d041c100342da298400d0103840c841340303000106e035104203842c00b040b11841100d00c1d807105004280303503041c481211 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 940635125 1250 940633875 940633891
    0x1290607120f201b0d0c0315240303210501060908061302060304022b03030204060206060a060f050d060b0c010608071d0106032714160b07020d020a08030f070209 71
    0x542403d065030650b94840c07001070304480350000511940c650382d0329080111010780d840700071056030540d02e180807003900b402021006509803c00114150040f01580121a46540d212005a00d1071841d01e0603510042100302c20041c06242109990480d012030107814000c2c0841e07602c1140c0c0b18070b070007421810310f5001780010480d01c44810803d000b6940e03d5003980d40041d012070b030000150f05000409010100b0004040c038131881c20020324002e0540541c00342089a120780c09540c02c2e80d803000b00b0001e1459807402902d01240605907000c030418440c07400b0744007001d035102d0002565501c4e004002e2898100d46251021a03444840502503a00103100480c010400c140a20540400c0704014190307003501402240209540c6001c603038954900075155440c4402188600100107900e030509041480186000d03c5452091000c00480340c95402156400c9501c401036690030703d60141c1c20030801800b40f4100743ea01c0440c070a8003082802051008040c0840014a5180d51324024410b1000c02c24006044417 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 940636375 1250 940635125 940635167
    0x10c0206180a050f0c100e06040501080903040909030e0906030d020703060509030417010b100206040317061810091803050d050a1d0303040c140f0d1b09150801290607120f 75
    0x842188c079004151400d03190242081c00007a40d0381c440182c51400b41c1d9101d6000e150500c40304109050304071544124420064030245c040366910310500d6919030450f012000140d00c44401000490015800301c0d070406c01101c181ca103001e54465800341c1128400b81c0c0e181c01c1d0b0359100d07841c42c100c0c40e01c1c2040045441c0d0351300103402a440c2540380030b042ca10344202c1c031410610142d80012644c0c0d480c62441584038031000d40014450501d0281e201241c1c207640603042d5643e1034a1401c030710b40005080d00b007030304070790550f00e05103403442d030304c4240028110160640c680c4584442d2a404600c00c042030002020321044015500c901d8503040540d1700c1c02441d480001e810000c580310040540714180138a522050aa606255805280c6007440c180c001d610b01d411041c040e050f1010030300300416048400c114007002d1a0000c0c00e0307100c8110710b08071494010f0018841d031209010798104181e8407606425003600808550404180c1c0d02e50308c0c41c403820f007503001001a101c0c40310032041581240a030b8811602c02d001c1c1d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 940637625 1250 940636375 940636397
    0x30d0206010806011203090e010902070c08010b06070f0f170a030605040504020a091a09011d09010e0d1b39050603071b02041517010c0206180a050f0c10 67
    0x6503c0d510180952003c0151030140401894069001140200b0b05055850100d41c0d6458408009400c9200215038055202d0000140074038140144810340e000140070f10b151801e1b130768032028a01c086605c09c503040380a000c2a40e011810152524031080301c0d400340309503640c1d070312840181110a070380c000d03e101d1441c203c18000903840700441c4000f42e82d034855001a484541048503542101c40c000d100f1342c013100000011550001540d000900c030643e902c0004090b07200c5e4108982a20741c1c0c04c0790011582e00610b8a000120301c180c81a6030861410014401c015090382c8565a003441d0f1021000c406204101000d00034004003080c18000241c00c102e4010018204000940c09102c094000002c115400216a200c0d0040003048152558000c0c41001119021402da801142d528490700c590003612201402d51140180101303202101258054246541c5180c01400f44402224a15089110383c484400010340100002051003840d4001020842010020011821902c0e030107442000b05200d55 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 940638875 1250 940637625 940637639
    0x310b04030305030a020d0c0905040b060f090d02180c12150108010902090604120b0a060f120821150a0f1a030a0e060403181406070f02031614030d020601 67
    0x1aa01940d03854542596240c81e566a6900603008880944082c2454004150119508544c01008072001610140301256900c03082048601a01c030070344100c01c0c4100414a0785180c000114031807148010301c003410a00ca450343e00c3c1904c500440f81070216000000e40300d41c0225030310f12413035070082c1d069807104d4081c0b2000700000c14060303040c812801e80380d402207440c0303202b940c884d400da030058004c07160269503807202400c1c007680c1c2c2c103010f42d0b41c05201443c1407408140b010700759075400305584c40c02c1e5440d0111020350b900d9032002e07445070040f8080500003000444103580f20b007420a01400d40c04401641d242c003030108011010486611001644145144c100b0010b0710b194603811701081941551900c80d40d846100c0005003081320a681c1d010b0080c4402c0104158000f003840c0c1c08800c1440345152115104c40c89204e007100755010813607100b03000b4442c04000035041c1450400440c409000d94554843c000581103254417180c1060b5503040521146071050309042259400040c0070340b00400c481c0d450504 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 940640125 1250 940638875 940638877
    0x50714011706030c15070614060303270402070f0b01050906100804080910110607020a02090109090c030203010f0204320105210f042f010c1403310b 65
    0xc5454541c1c80000a02c1a6018040081c4800780900080039041e00343e60400040d500c07201c011110310f8178105084485104802000303201e504040c00440c80c10180088141c90b104030045400001082480e02e14115210b90025141280c07084022042e440e030a0b00d402aa9444141c00650049200d1020020301c1d95440244024108803400d2030307205a1118201a10a403146c80710241c2c00c00b1600045691071a4080c662030b140c1988038042d03c00c1512120800c03600ca00d120000130b0b61180141c6c0c01031116042540c80780c00850720410200c4030703082da2030340841e0035074078400ba20151b281e82c0840c00f0800356091401ca210b240e500b0814944480352140350a003030100030030710b145041004c04204010180c024604861126403134601d62016454413801d1601010011a021140d03003030702d241001030b2604160784001e07844403850132001c500190b0800440300100c0581043c0c3d10001d050301e20760300650b000e100a0a09059a811745800c0d2507041c04648030640000742c0c014003e02c0311500400036410808 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 940641375 1250 940640125 940640147
    0xa09080d020a0516032c01081501022109030d1701090504020607080301081c05030f06011202041a070303051014090402060403051b01081608061002070b1605071401 72
    0x50050300c0e0b584485003103506009a02142e620f81c0103203030380c8506050700445041c00c54809441281c13003051721486081d4400000c5110b031400300f4101c0001c0703540e80c11034040050718900c0c10b1048911100055000e00608402c0901c11000c0540000741e200131410103000341d1220f060785e42072a2400043c220811115810705200360f00d070341a901d4010604540d14a01290220354119055544a5840784411038451503000345440300058210158010f0301c0c018015a0b2048070132126108281d40c5403401501d035a4901c143c3d607801141c0c20003000c01e03054581c000610b100050605021f40b00c3c031903864007608580000d44200802d11030350794204003110800031491001c0d00255040d480e00d4440307102080e118060b50b00700520313501481000300507000c080c00601100d10710903a11554103440300550071030584a0b00311114000745110f070004240d070424546840d01e20714144121030046d81d84070701c040c000783c01c903030001c08075425a0744602d800d003e001c01182c809082014051800d2040070400a80006280 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 940642625 1250 940641375 940641397
    0x61002070e040203030708030f101a0702220c120e031303060c09031203050901050a0e0a08071a090307030e0102120301180e011109181b130b0a0c0b0a0908 68
    0x2500000b411514280107032546140d114007010386a040c05c100c243c85860040790307a0004819801c00c0041e040e00c440305018641d0310107108140c50b04034150248081c10b0045040c03000700071071003c0c41d41640d049c80e104909545045645140403880c000350004180c03607401d0303048040795006228031108400c00600c4001180c0d4001e030b0020b80c180e8400340c00c1d140401141c1c0042c0510051241080c58143c15400c1948106880c8000304503554803c0d50301003c5902c0420082d00c1503000e460080005515a0010814980a8107000100030100d40e0b0407c80d001c0201d41401d40d5030030201e090000c141e0000190120343c04c0c02d0018102000141007000700500052040302550110080b4410040d82c4641c030100151150200a000f207950111002030305600004240b40500036100316035080103101c0d012a0b01612044243c40c1c00e14900c290140400d8001140c0320725003000c00b400019020345144000c020585482e1128002d03801c860a0441c41c2c10b400800000e0541d041040103c00610300f0000c869051503e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 940643875 1250 940642625 940642649
    0xf080618010b04020d1a2b0305120703060302090f09060c0f0d0f15052b031e020607030606030c200c04050109020c0606030a081911031303030806100207 67
    0x51900d03024280100704070740c001e480090b191142c1e01c91908070034600c507420140b110056008105001100d98107000d4030030721400689000503101021228600020700070b1810b07504000745041192085030301070f522000400d641e0304040086043c2021519441250b03e41182404d1429007441a2a23200091585034952030004183e401c4080c032006440828182c01d100304030392041301400c0401012018100b000e07a400104001445182c9440e480d0303182000c0c950ba40c1d0f00d03c003011111403070107600d441e0100c1c1030001d00401d028201c1003000c00a00c00d503025500515060400c044050101c50b00f0b500100105820404824219500151b00545040c40d00403644c0030003098810450600d0f00040d501039015080c10000100c40b4800c3e0090640c94100b08160382a030388804003050364451047d0002408603105115140442c03000c00545080b000d1141461501302d1502d0102c6403c0d640000d001c002c07840041d1100b8814594400d1000da4485401e980c41c15841c0d42c8a14041d642e03039098818121221303c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 940645125 1250 940643875 940643911
    0x8120901210c02010608071217070602122805220510060b180a050a0b07020402090d050f0c0306012909041b020f0d0507020904170c070f0f0806 63
    0x4050880070000d01444a001c20201d000960000c1c042c02e02c0d4400c90751603124401d00071503000c0c001c00300b11245030380c0136900c0303d960160b01014808a40100c00b064500c42d80c00d0005503880c21b14125861712400881001586105910b1184a070040305000740d10303819841d003020000b0719000100f1300026560a500c035008032100c54604545001e41c02440d801c0801e0501c00c000402c0d1010001400e02d88100f43c2c1207541808070407050120164030781c8601c030b6000b400c0c400300f001510000c1c001404460300203000545448070007004a00c0303810303c00404484646c8440c1c558000b580043c012205103030006c4003d003110394584169440303041101c0da10b0030b02c045219107440b19440400c500710f0340358240150062000822641103141188011346c42c00e4054007600c0c40618140e000400c49290318501a16403178200b906c15000d014000c203008000722403e540348528945100c404001414050007008000c080041c208a102811940181e022030702242500300140030300800400c41552040150080c11600d039 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 940646375 1250 940645125 940645157
    0x9181e02030c04060611121e21040803040308100f050103020a09080a03080405100203070c110f130b030f06060d0807020a1a03010303111c1112030a060e0108120901 72
    0x1041d004070343c032620380b03880010140d4000d0884082107582e01d09482d81f40002e00c00304100c622500403032024211900c00d180e0650740c2080050300d440c01d2007881e8410920001c0381441008074060300d0544449502208000401d64840c100030762100b0109000d125652a250341030018007032500401d8141500442c4102010b4425130314a801000e14000301c922030411070a001d844200145c805540d03601034407031960b428941e1030003141d000715200c0ea20800e018180313849074650b40480136441c80c0c2c00764600030700941e0303030b0745030251101000c01045e00010b40d040e40f081018540181d01130003c100340c0000c0c00308a056910205c0c4015055000305040350303909410b100080c03a460107a08400e20064610801c3c2200d03070004400395050380e106c1d480c2d144c0c8030108020340c1555a02d4018222190105d0301349681d80e55885004a080c0d108410707012a2425031400400c00c0c2c80f900100d5140d66010340d034940c02c01800791070313044407401068014040c050213207140d440c1d46114481d624101c1c1c18000002c813144010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 940647482 1107 940646375 940646383
    0x705070b010302190914190e2a060304050d0905011b120201020f1611010f1403090715020d02010b010e03100f02130b0409181e0203 58
    0x142e1859081000f480320741c101e8100c01c2d030059840007a1341d4180b4010b80101e0351510003040d40c01c1c949490103006003180380c50309240d8130342440302101100001146019030042c41010902c9031255440d121010070f804d0010854000c08004208800d004001c02c5101602180d503846000881d921001121507594407660340300350090a1040c4c40020703c1a1031440c0b540c811500025040801411008006800254002c82d1003400d407501d14080022280c05014480c400342041884000c1c1c40d40c0050200a9596016441100001c007040400d902040020020219102c07134070442c60006070002c0d1510700b42031102001d50b003002c00c1c0410640c000c4c2205209140e01400a1a4000c3d074040180041d080c0000d19200403982007111910102c1002150000f40000ca00d0b1699503610709040882100e00303080410607000380000da02400200340350544081c0710030a0442044800782800040e043c = true := by decide +kernel

theorem cover : BRFrame.Cov 940467625 940647482 := by
  have h0 := BRFrame.cov_init 940467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 940467625 ≤ n) (h2 : n < 940647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
