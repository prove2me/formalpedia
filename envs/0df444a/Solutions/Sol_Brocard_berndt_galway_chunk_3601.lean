-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3601
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:08:14.7969+00:00
-- url     : https://prove2.me/submissions/a28cfdb8-d7dd-479d-909d-f158e143e795

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 647482014 ≤ n < 647661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 647483264 1250 647482014 647482021
    0xa080109020a15120906020702010306081204051c06020a021605010507030215060a05120d1812060e031c0501290a0c051219030b1e040209040905161706010e 69
    0x3e00502d01600c0000d402c4c02450795010110800c94020500f000f846008010303074440240c8005021502290003000082d400200300604235640c40c41250150b603030032900000001214044001e86c40490203004103c9800411640e002c0741e00040c0d10400d8203401c2003090821078440004481e01e0085403c0680180d1240c9407420851354070703400c41a008100030308000003907919080407650981000d80585890382c01143c4540e4016030000c00880340491011030301ea00c0e07030300d8210140e801d01c0780717101c02a00c141d41d40c0720046c029403410001c658880b024000ca264141d180c400102004080921410340441400c0307604c02d080c00d40784090780b00b40c00d22450640e410005140001c440c1c1e030340c000c0d40840f024800d040682c0e2103034510a01034006814014107040d0070001c012401070903514844403180c002c010b01c004500102c0c05005060f000c100c000d40c3c00585031415400080e0180c02e0302e80d0050300c9c90050310f50200b514007010071000e040e50700780300300c08103a103550503c4a59039003402d00c0303008003186003d40031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 647484514 1250 647483264 647483279
    0xd021e180406090c0e09150d080408060903070317090106031b080c060c1507110105180f0c0603070e1909050108061609050907110610061112030117100e06060a080109020a 75
    0x2001c0d00800c050269541c81011031020500c540c08e14901600c1a20300803808002d011000c108084d8841044006103007081d0f850f07580680707501140e0010f01c0050502400041828009500940040d90814240c012001400b0088205500140610b0130300380030b450000d8400c0e040071400c454000040e00700421105614004145900784003070a10010498140700514112000b40210b502810f0740071100032044884000441c40d04000e03c03244c3c2001d4004444900845d41d526046d40e620402d2400e25120b0b109044001510b03400c880680c0b05041d800c01da0001c1850001c5a00043c10303602c60400b05c0f4101c0d110f164100589904006d8024002003007000107000a08151915580025035414000d0040031904070960404208031130007000c1c008416420804203078000141d8000c581410080e200f00e03005007120385c0580c4014012078105001281d42065031017010803850181005d6094104032542c0c6171070b03c1d43c6d151170302512541d12501c1040303c0070660744418800d804009070b004059006080c5040c04 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 647485764 1250 647484514 647484529
    0xc030809030f0102130e07020f2a03030c010e0105060d051b0114070b070807090f050f0a0803030a0f0b1c0308060102010b190e0a060b0d021e180406090c0e 68
    0x103001d405019000001011480c00d00282843c0107500701540d4110b805c00c1c01c8681c0b0b110f0000d08031801c550140302460b542107408140c810721007103200c00100480b040c016200590140c5e454503150148400100190785d00c0041d4040d0214510000c001c1c42984c8130401040100e4034920800f030829000301240a86c810000c0252040b1068103041000010742441d5000d5450b4201040a0b603848210790104011254050b072031903805905401c0c05c9440500303104041254498a000e540c0c0907080b800c00c158115640d03008050014039506044075941d260840c022405040c49062414240b0708100c651074662030071140404400085035030603280c041c05900c040310034010190003541955680c607a03d42e800d4076040388410301141107011450501e0718100b075105500c580240b55407226881c08409120307420219046400340302c560440503032644a200402d0034252900d00d004102b0080024002500040c150203038051460101c4007082816502c0c00ca24040d10f440e9242000090700700001c2c41039605d407008 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 647487014 1250 647485764 647485777
    0xb0c010e2107030e040203040609150c1d0a030203012406030c320307020d170403020a02060d140f0610030506130e07080f0a1b030302030304020d05030d0f0c1101090c0308 75
    0x50071348500244030021800300d0b030054409132a40d689a45a03102409602034541c0320054020804100c01078980900034125001c2c0c403085820410302c00b246480700e988000c4060041d54000f0020014500c4044001c2259014a030717a40070540425038000036598000e200e03a8102c4c003415203c40740d41d07400610213003210b1003c43d000c541c082d1240d0b10100225a030705002451082c1c070203400070301d04202e42d4007024118800c0203c2000e02848080308000000f503001c2119400c42e941503622548070114100580302415a000b0440c211086180c02c008070304158030003442c000d00041d260110022594135084041c0c0700e013120b14503040115a507100d00f0041d1954400d40840b03040c03000380c4808c143c46401c0e107408e18448080c1c410751130303004178281001d03c04031800114008841e00385040c40b20745135541c06900c07800000c00c081d101e0101e65a800007881018001c484140d017402004024400c0310b629054000e0110307022140016001c41002c20790328071305101d1943c0f11500000c003061542c5c031f140d5501446500c0013 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 647488264 1250 647487014 647487017
    0x2919110c010c1722050a050603011d0c120a050f090105090d050f09090a141e010b090406030b07091e0e0103060b0303040e130b150609040f060f0b0c010e210703 70
    0x81005440c0807400700384c1c0c080752015030815502c0c100d04d44001c1280d11019900079901c1500200010424080500f103030a0a6030000d81d115085903650240c805194040ea04184000422580410510103034a50000f8401c1e0503600080c42e8540365400428225001118030114581c05000c4d0200b02600444c003030410407600708a81031800340100003240a201098544070b034007644401501d01c410b00e943d501e15500034601c415500c03201c2d0025121609101043c441e00d44510030001d5480e0301a1070f1600302001868014000880d00d06004400400c0b0820300d1151158204459030185240004084800c1c103c8030905411001c81e4250344505000b05406030240303138140b1041000140091840e03000a106d504034031781400d11000c2c64100a10b00d0b540042c54092034602c41700240da8a561414140c0344841c0e0300352400540d001e9002140c00007000190003d29074002e28030000618185104d00030705172403800a009001c1c00d409181c940703607542e03544405c00c40e0b034134130b000c1c2c035020690011005440518000d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 647489514 1250 647488264 647488267
    0x1a0a0509090907090212060f01031b050a05070210120e210d061d1005060f040306050411060d020d1d030403080d180c0603242919110c010c17 62
    0x4c44194100f01c0c0c2c08029028000c102403010030549140503489030880d29000e007270030300500c45080441160703141c800d80c2c504140200030400ea1102417180040d00c058a5003d0042c09404080c11805450900400c09415031a8108a0568610800440c00c0c04044415880414140b488080785110382d8110b5080c41c100c4c995542d00c001a03011141e04951017003010b1111025850a04c9035259030340200036017086004100420002c000c4901e00c0088800b00c90b008400051103444514140c100b140303507081401d1b0711034004210441b04407200e80c003c01d45e59580301c10030801e00080e03403900c1ca9200c0100100310841d401c140010800308512500401205545c0e1030000350159210302002070b10301c0c218900f616200712110040c03007a00c0d014410b8800b1456060308078045031034100c11107021315441c2e00480e90400700c40309a6220344943c03140d20070001c4991285203510340510b0030b070718000c1c000f4070b00c8501c0005400441d980614007002c0b540e01c02c0701006030764003c120521910f031005500020014804400c40 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 647490764 1250 647489514 647489519
    0xc0b0c071a01090b030f01090503030f040303140403020c120703020315041a01080303010303030c020f07051507020627090412030b0d0b091c03060b041406040b030a061a0a0509090907 80
    0x1040d5406010b400c403c1da00258501e0300d842030500e000b0910707900c540d00d60b152017580d001040c0700100340d90f0b00101403601c00c3c0c0540d865140c12006003402507406000301d003000041c8809c068010442650010080c0c0e41020305000d0410065603c20091201a42540114201d0b880212401603c1648240500002c2100c100000002d20102c24240d00c180801c1e0404401481055030602805d00500354a02c010424180006d400c2510350b001803003154401c04101c0d0840580e00b80b4102965100c0ea0020080f03a02c50118840694690310b002d103990481c03030450300c1018180c0c40d008085a00550704040d1848540c00c40c020709a000303103e400921070b80000001180e10015680c0d420321485421603201030444901e0340350390b02e02c0c0323001304100c2031080c07605106082c080140301030160b90460342100b107050b40819100006c00c0b640d01c19138104c400d510344004104640351145400c20804c8581c0c508417040342c4908081c0726080307400703007041520000304200040c10780d80c940800c029410100b0300d025180300d2603 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 647492014 1250 647490764 647490803
    0x100f090b01140c0102030415020703210f1107060c02030f041a1201060c2001020c010503040c0519030b010602120904021b0f0f060f101e050402070c150c0b0c07 70
    0x4001c10032002880c3e400004100c00c004c0c10161001231401d00ea0025801d10b451960050b091031400d107681c0c10f1000240c412143d603180c068020025070452070078100070140560f0030280c16540f00b410141d070980d060000d030145031351001040300d507091401174402d410141000101c002c3d00c07262010380c80312104141311f501c0c445e208c0c050200340241943c0c0c860804448071840e00e400d101008041c080615144100003034a60398000c1245000e9210910b002980ea55031403a00c05078a0342280c1140b07030001912400d07080d0001c0d00381180d100303881c020040000c80d60707a11030080340e40d4001035600d025a05001c1c04550b0480c2415005440401140d816201c50f030080b45504c0c034500707200000640f082c1e62101c0245016002c06012054205100d0614508a07280c0f0301080b00c0c0322403c43c420101d400016084403c11204458009405050010019503480c00d8038281294440024094001c0a00440100100d89801408880b0400b58040e01d407080c559100c400105880e00030344021786004203002803000652 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 647493264 1250 647492014 647492017
    0x110a08090d0510051006110a0201020303150a0305010504030503041b051e2404090c050918040302070803160309050d03090504020a1419020f0a0312090c0b0d060e100f090b0114 77
    0x8a03080e54860074001d190040080c0000718542085005400c64440c80c000762f41d002c01100da02a0003452800c4444c103884d07001c40c1c5010001d910240541d440c0c401400f0070503034400001d5004500918040b01d089130105040280e1500034070440307a20915002008014454060001e810003000410b0190043d00640c01c0030075280c00e60394290b0340704200140c2801290610301c90701040500901d010fa081800b282d012a00c4200c0001c240500c1d0044140020100b520800800c0090038113181540d03110300701c100303603480c0c0c0d62034688089001c95040c540c042068106180003402094040c1d80d11000c05241800707001c0298090a400e5040000580b0350711142c1c8102c030014561300b00b03200c1c003400203c03081c844024201100640d0081c00e54011101c404c02195115140480703030805040c0016409031546001202044a42c0c01001c0c085400700e034204c00140e06500900c03c03074900840c025915034072a1001d441007403081c080c503602c540100b4024000f00d60264800c100390241270518034054155464010f205 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 647494514 1250 647493264 647493271
    0x1d280212151b0702090604050a021905191103091009091112150d080d02070b09010902010306080607140309010207240b0418080c0c0916110a08090d051005 68
    0x80400da4014440c1c078000c2d210a014800c040090a0380c140030040e40020f03045080503040314071941d00ca40c08104610b20310f60440c3c0c1070006e003080c10111060b098501a0094200f181c800c0620300440c2d0010540a0040c1c0c80b898241c901f5002640c5440000010848900d000440506c00c000c03286001180e00015403050203020604090166240c1c200d506403800c0400c1d00030440c14603160301c45a11880c0303484001c5940d94040c0c0c0095459200c88041e40e4500c028060804054007142440060110490043d031020003418000c3e641401010744600200390380301e100b6141d000c0000ca0000403001540005809160030810440002d89400b0f40c0c0c1c0c4541c1c4608020b01043c003060000545d0207407841101d40b15420714024140c40620a01242d001980d01c0749a04e5074000d8070b0a1340008411003400402c0c00051250800105001c0c11800c100b09140c0206507120131a0020410121110081d04400160700d079100d648015024a80080307102445902d000300702c8101e429200b1585150603200160054610 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 647495764 1250 647494514 647494543
    0x10b1203041a09010207051315091d060609160c15020318073c0e06040f0504020901120203030d0501080d080703021e031008030d1d280212 61
    0x1c541d0b0030205205940b0500c0020942290401c00c800030050340c000c28644100c5404031014001c02540410b4800600f04421504034800c02c2e4507000b1544400760f5100e004458256a450840c02c1e20301000140c1d00c20080e13900b01c0c0d004070b01a00040070304404016009105103d40340800c01c0c0c200e1a03807003040741d4030b10200c0e41c00c910350040100b1411030b181d5400380340c0c090f04460040201d5803800b0300d8640c0050000b800690b07008008203086100c03440d58100745404c3d802404410301d141c1d41d101c03180c0045860079194944a2070031301c100103030211198056507018a40080c24045164a400d0080e10000306004080360980400d201c602d02c8004a0320078607000f0541c2201904600181c03440007052064000c144206141c41070115000395210280403181c038500340005290b403920740c3d0042d0003951020760b012640038403002a5452660b040e46e00070021150184030417040a0191003145500e03140079110700f88480c00d242d001d4503004030a0700a418803984c000382420303000000c49450142800c120340e10030310 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 647497014 1250 647495764 647495767
    0xf041104030f11030706050324030d020106030302010c0903080d05061f0207030201021207050615060c10020c0105100e16051201091a0402030c12090c0405010f0614090a030f05010b1203 81
    0x20103000701c5030110541a0f50403000790002500303104d030290a40c0000743c10300110780d0387c2100310b40c1203040f0309061041078a40281241c42e40780064200901903c607a001c11030044d420600755408070380c0180c041c0400c1d41d600041c10350501c101400c16400808001304155445a4103d2040004c464010b221080403500c0c2d034040c040c1d090560002a00d00200030800170f4082c0070403c04000810701c0480c009400c40c100b00c1c030764560b525080740051818002d0810014503405100d0542c50a0340c0750380d006024600744500203100c40d6035560030b0a89603a9540c0b150006000b1200c1c0001c0714001c84060310074408016050044c00d0180c0ca98201403c00801d0300f00288599994590300c8480f81c02c59000f0003846411a0103528600e059901c100e964041c00a2940c0e140e1245008165a02014082c050440070041e204001569480d00c1d00401211140f0481c03002c140c43c50300005c00c0c0d01c4150115001960f0240c1540382c0b0b1382c60759680842940d64000f068485541c0e560b60b50070581d450042442c401c0e4020030045 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 647498264 1250 647497014 647497043
    0xe0c13060b0f0c0c0a1d060f0a0603020433140d0603080c010e0f2a15120108030c0705060913060602070521070605131e030c080d08060f04110403 64
    0x20740b82038a4400c240d1711460f0f003044200b0800461448136503042c12401c480384000c2c0c6551002c100c2d041b450082d0942c2c000142e02c0045603107980341d80a40b04031504480424516600300c1100203c43e2040700e40030341c801c0400304100300d900c0d0107109644454039607256000d16242c4d80701c9030f201c01c5520640040711006000504030241a109019480311b075105400900406400b5842803961205110030240224029228040e007400c10bd840006140364007074181c992041d140d0031240e00e0b503070181c4004890f190f20381c4008102d4030000015580300091a41c01003101c0b60501080201c55080710051690044460448180d02950760041d00000d00d1103400400c03d86040c80c0c1081320300041e201c007080c0d00340079810101401d198002a24000c80d100c5041c096910f90105100b0045014070341c100c510348500b018009504d4030b074088030600c112030061213410b000e0751300c94000d181c95a090303640000000d150100840c62525001580341c0c2621002040002c041d10301840c5011a41c01540c000c2e503140b034201120707 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 647499514 1250 647498264 647498287
    0x9110c100606030c02011e11040e0a0213170615040207020d111507021507051e0a03020c040e06070815130221040803070e0d060908030a0606030e0c13060b0f 69
    0x480000582ca0b00007480581491150180c07c048003403035070120141c0342c040e042d517015080d00854000c0c29030440011501d14103034503428069407001c84030701c45860360810000390000304000e066141c6100c03030011302581d0b15005180b0300c0f000d10341089650711a03420046840141d54072240f400c101480380f004d2880404060b800c102440401503183d0941850400400005035550034800d0045140aa999900c0d12a01c0c2412880c00c18110341000c00c124122071034010500c0300017203180301c6600c6507088840b00c3d20b04c20144420ba600c00d1000984a90111020440741d5012301c2d0100d0b80900840303030100244d80100c00040c01c401d6541c40c00b90241398001501d2010703400191141400741da04200c09038190909940e140d1041c0700c003d00c00d004100310801040c00642c0d603040c0c500790290f0400c5080c0b10319a4a0708200940d6481650916038480c07400d4800a072450207802002031100c40800900000e510060078800703403240850166900c0e076510540414094000780203484070703502a65883d91200c8000c01c9 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 647500764 1250 647499514 647499521
    0x30f0a170f100f060e190e100f06031119020f071e050604050a06120b090f060108060a1511030f130305161206111603080601031d060109110c10060603 66
    0x43d02030f444182020b024a40e0450381c4a40300a44c292040c2202803940842000b42e200c1175041600003803030300c0c81405044841101e030079040d19032895000141c00c0d079030241070f421a20110681c000c4480184007884c00740c007400c3e00d40402c036030083c016a9802901a03402d00e08042150300201e2a92602c050840403141c0da003540300c0302a100c160703101c1d403815042500051843c0076900c076580c10444600340390b040c00c440e95000310030351210242648055043c411001016080c046482c0c6002030181c400140b02c070710b09040250202c0b8880c18020894081c00c0d5400c44182e00041c1d015200c40c4810400140700702c6110009014881e544500000d2050862416904014541c8800140004041000c0c00b402000c02100c85c4103a03402080001d94810994124400d03001e03048050340758400b52446182410b81203500c8a1203100d00b40e0b82000340c41c15a040c00440baa034140c0050885501ca80d0051048400700d51001c000c000644540c2230030320783c110108524103011025254690b0351102c00c1081515003600 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 647502014 1250 647500764 647500769
    0x211c090f080f0307080313140123100509090102250c050603100501050a030f0507080a111e0d09050a153c0f0207030519050903030f0a170f10 62
    0x6000c1d06500070b4840784155079005081019040310000408074450384812001460015800b40c0b0f604c0d05101201c284500030094010f0124103150418049034800321101031701440b544445110f41d494905110500c40d801e10f000301501030541d800c02284401d0105c0f045000401e5205601800d61902c151600001c948040e50000780120350500912081401108400e000e0b12020300e411900d61090712002ca0280051501d80d0b2541403501003032002d56544040b880d031250998101c2400f8234104d154aa00c500c3c42404c1031201084288103183c10440b88410003480c44041040d40440c1740015516554103000001030201c60b15000b0714501c14a0500038010b2a49011840518207590550414502c1040c01010480e481d0227022204e03082c00880700c0d90010903903e582610464860303956181c0034007035130702c4202c03104001c8038640c00f0842d10030f220300111b402c00324000c1d01460901806040f0040b59030890303140c40042c80030b03150207288501c2e124810329106880d40042c400c03050420000c46082789042d41c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 647503264 1250 647502014 647502029
    0x7051206090118051c020a0b190501050303040b070308060402040e162a02120a050105070c110427060209130b01030b0d08040506070c080a0303021b060402211c090f 72
    0x29003102041c004142100481e003201032040d0401c111140482c02c2c1f4840250013000c4240a0007032040300c5540c00d40d807007010640c0d030404000b030ba601c0c0c0c02015528083c45c07040780701c54402005900002031140c07d4150f0041c2002c1c201504064959490307280d016400ca0303204c1c0700401c07180803001c0c1c1d0682c006070000658004494000b401d1610340c44981d43da2b040e01c03002a010b415851820003603010100403e001190700300d0000c000c40c1c1803141c5c2c004c01140d03581e00180c80c044c03802d030105c5d0060703d0700c1d118500410111941c01071990962141c4c84202e840811025982c095080c04503154030348452580241c20204584c0010b86000c503480094206c0c2c0f45419001e005180c194100c0c000540c40000319410b0313600440d4507075105c0360140b42900100e091500001c0b02401209100b008043d05030f0094021f454203040098140c031400030550303a59800840340a54420b0650001c41111600030310045a0041c40300c00b6550001b8070300450007444c50741200c09400040c007000c0104090320050394101c2c0546080d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 647504514 1250 647503264 647503301
    0x804061e08010e0c0c0a060603030e010f02010218220f09020a1202090103060b030f0106080303010e090f060103061d010911030105070e06070b0601030b0a060f0914030a0b040203070512060901 84
    0x4003501c00740d441400400704030044d1000074000c10708440402951006540c00754060000c11f4481c50018000b04880003c01c2c042407002c801c0b140034038010f00a40d441501c200f4030000d25018a41c041185407580104940c0c0e990314164000c8020160500440c90306122070900820020240e105000110750381e5070182c1c541b40e4814a8010050762404c0d06581129008800490540402c1000030f080c0901c1900d140c40d1036182c0780f0001060070001c0b010f13504980107880c0010035a42e1740740b0255110000403403540c43e5a0042401400003959543c48400e42a503d1141c2c418080d00360301410f800c5945907102a264001281c7e04e00025250902a69511400f0391408134911420305011550b2401103c200415641c0000c0c0010310b16480396110300c606090040c424070903107640750006000c841c958007056001401003c4082881c03541d030b4082005900000d0000d250f4616180c491003004007014000f01d038140a207000004060f5a5181c13201c0b1911070000c05458103090000c405400c440780e640903035005101 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 647505764 1250 647504514 647504519
    0x806010306060813060b120601050310020a020718060b0307020109050d030e0706030f090b18061e07030903171501020714060f070302010f0525110619090804061e0801 73
    0x24064640b541000700b1910805420640c0d1614a0180c0b0440e030040d0f4002c4032580c0700d015901c1f03000540c10304950302502556480b0540c048da41d016031017604000409a4000c0300c0811181c2840001100c00c0d0703d4803034001903400d07295a41d101c0c165100380e0b15100141c1d110000c45007841810b00800034080010f0400f0032001003040a0309454512031300c1524181640c641b03d41c6085400d9421540c1910347c090401e00b10761a058015004203802d542900d42c0d01e11482c0005a001f404044042c907505802401c106490307591040124082c0091240480401105101a020144807901d15074000c0c0d100a01031f0034404503100009203481c842c1d80c010003c0407400c020410481d114039040304d10b0b50f08801c0c03d42c4e60fa84a641420380c05810090595400c503440e00042003175031103c4403000c0d0004520f0032151654070804c0d032070484402d820024803000300d070440f40100b03142524401d203414000c0c00301c68010891903a252100a0303d504140c2c803540100d140c1242c40036180000315140e0380070751100e061100e110750 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 647507014 1250 647505764 647505767
    0xd1106060a0608160e062a0c010804110303090405010f0810050606040306110f0406261509070c2f030a0f0f030504050415060f14070605061906050a080601030606 71
    0x4002a160b154240401c01d06115418484c5d0301c40280d40740058820f90341c032250b400020300c2c400d81c01c081c061014100030032082502e07000403c0484e88000142e54080c0c203a1540e40b2095100e05114502603854070042110705051744844c0542c1c0e0007000d4404070030070300510b010301050910380d002c800f10080c10b01c0d000400456a03510070948050f40c0d04030900041101903c586c41400c0e1041e6010142c0b003000100f00043c4031640704111040c07294000c0151200c2d80c08440a40c2e2044009a07882540e14440c0e401d10001402c0082800740d00507038a00d4441580c0600f034444030800120050f82c1100f1600640c15040070002c1120a103510710400d90040882c080b43e51a41040c2860101e40200307482030131940002030501c213206903805040d00410030440c0340c900314110040c030040e070710480000c01d81600c8000d03807003401340d402031050110706942c41e440d0160f140e45107401060010006a80851030700101082151412800741c0604508c0e244c07641d035414010006400c40308001c20107410141821801e00505 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 647508264 1250 647507014 647507027
    0xf0d0210061a0a0512010e0a1406100804080d0e030c010e0a03051c1409150f220206070b0702060405010621030807091e03110609090609090f0d1106060a06 68
    0x8081c5031007070076103c140040045800d8841c1440c009540c91004001054034000038800d50b0141980401c10882c0f1b403034004428031301500c11140c8560194898403d00c1140313000d01011584144610f01d528980b100740d1007001d084504c40d08000c00b29600100d04103146404c00d03c50701c1032102400d00140803080c5903940080203889100354290110925101103180b103002074201805a034400c0044a0661400303c0d01a81c2d903000041107030101400c0b45011500100d41004c42c0e60148003030194650400c41c00d1a038118603043c800b80102d812242c100703c0c1ca0045201d071401907015002560161a083c10305060a90079a500e40e0451403114045180307403582104030820780e00c840ca0b8107090011050f41e50980a9a80850641c440703242140480200b0139044c10341440803044d00d01c03c100e101d200300b010b041481014061190030310307040b40060002c00c0d66450600c051941c80607000c011a814108403406180c14078800d041b00c500801c081d200c08a440d54014041281d010005480b0407500c2440d040303000700003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 647509514 1250 647508264 647508299
    0xa110303040f051018180510050109051e06040303050424050702040c02010e06011721040b3a05061909050603030720011103040602030405090a09050f0d021006 70
    0xa00840a807040810340280e5006030442e19400c05d5810460355501390071561501e40300071034011441c0400150708400c0e8000b084060314010fa4910f902e003402c00060040e61601c20b41c4001443c480031890084560f20000108003951207071755010b45035840e0542e02e041d02c1c601c0030201e80c10401c5180f1010b01e4503901c00b0a0700d82d01901290b011039401501c02043c2c0c010030389600c07034002c00c0c00f0700ea0010440620200c064140211198104ca4580e0504081e020039080d040c0380d6003112140410040202c1d215401c05800e040c1000072803911481920404006180c1c4123508074030105000303020980c400201c2d407003070a0340b0171010781c2e0034084181110700c1c80c0a00c0740e0b18000c03408815510f001080940e00e0400603200d9440c2d0060031845425002c0440d140d0360a941801e99001540b07000900117141d00100580b0700b203500540044d82082e0408040120b541002024a070901e6604c82d091340c01305400700181036201c0e10180141083c200c8015009082024030401d000c882400c0c04000c01c150078501d401c1074078 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 647510764 1250 647509514 647509519
    0xa05010e0703052e0f09020405070e0f010f1b03110304060906030605040c0c02040f110f03040210021903050d0230100810090501020d05040b0106080f070906050703030b0406080a110303040f05 84
    0xc168905d4082c600050a15140180d0030514203000c004400382c02500c60300c05050f00f01d5081d442844400011500f840000e5a080c000071300019044000008903000c07003203924424240039051521101d80c951030b40d04140c1c021400640d100c0001c20000e5098800c50014000590f024058110031503009081d10024041c0240102c0d41c6031188200f1003010380c84904450024071030350340d0b0350b1070040c9900d0003600180e401381e102c2ca07200c02010020900000c1c010010180325485050000369988003070f5441d401c074104000c0d1440c0c00300f205049052203104500c02c55a03081e8aa000b51a0a08a070400c407681c0042035961001d44228041c004924001008401c4194251011600c20304138500b080c064042c000020030b076a401c1c50f00388400c00c440d0f10100ea05840b107a40c0e070b40d1840d54071100045061101541c608002c15500720017440441e1003000140392443c080d0030003007010300c620000315084404c1c541c01941c6c50b8012007143c80c1048a02e62155100e640100c00a604050400c4a800c0384034140c0d1240030f2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 647512014 1250 647510764 647510771
    0x31806070804030f091802070c0e040201020c06210403050715050603030409090807021801030b0a090b072006040b01050406240302070219060c11040212010311030a05010e0703052e 79
    0x2139540e01c900c0c102c0010307100c0104121454a40300d403a100181d00b000004403400c07440b650005c00c01e044100a04c41c481ea030168010552025450280311003039000d21034102c046490150180081b030146901280554030980e81c050f500d001c41d00780201625408130800108a041105000455800100395030980d8540c15000038200840d00e0019082e1080800c000c3d081800341e180610b003c0e4080502c181241d00032003041c0f51694587c288141211134508005010240b4040402c0100c0d10402c50a0005603000407100c420003c10007403145030440071201200e4000d21000140100d040c0740c0a5140282079400001e0b4000b903501528205485140d41c0c01c000b01640820402c06540c0d0b03480045018201070300c00504040d4543c0340c01403c050741d02c1d00585001d074242d1001040d80c1828405c071803000000e0b081142140c0d0131940c58480000203c05015407511806900f00d001c10000e225040b280d002c0e600081c0312140c81e40c41c266003020001c2c40340d8010200304002068000b07441d01410440100f0501000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 647513264 1250 647512014 647512037
    0xf0902011e0e030f030a02060105030d05070f0804031e03110c0a09051308070b010906141807050c010e16060314280c21020a09050409020307091103180607080403 71
    0x1c681100b0788203640c50b40340c441c800a40c610244040020059400984e0076552140e88402c249955545d0120b040b5000440420011021511644502c801c85206003103c40c0307050f03500d032560070344140c1642200c011010000803170790803d80c22200d50b0180c500144003401c1c0000c1c010340098480c940c94454200f05ca80c030b42001485805002015082081c0e12031101d41e114a00c604001107904424003074030208905d050000b107201c400c070b140c0441508500526605440104d16081c411200021300301d54280041441190303910707042130040031882000d100041050f131140700320300c0045407000d43c00502858a8840d01249108403100c0f000c0d0b00000c0c00b04806410001e030340340c010810a00c14201d03203440f403500c660200c0003030b0702100c080b80024640d40c40c184001800c90110040f40704648003a0301044000f10204407a0802d81c010029150004058031056a03540d090b244c207072001c4640420b0000d00000c200461220305500360f004100341d6200500d62490000310242c0040d101400260601002e036001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 647514514 1250 647513264 647513267
    0x1020a061a03030c0706031503080f07030309150c080c030c0a11120d0f0b031c030b180a0c0f050307090e091e0c040c08041a09100c020d030f0902011e 66
    0x8016400150440e9a5913080c1c0b0312054803802d85001c0c0f61300090a064076051422815014401560f4000c81c807949040c2007030400b00c2861b40701000440501da00c0700c1d24030f0041000c81c400c034140b81c2c2d407036038000c204c01d409424014080d04005003022022034007401848030424050054030710205050915000440c412800d240c0b501d90680c01414a00c0000074403a039495034030790058414481031520500082c1c40707401c101926400a407100c80b1100c05045170000e0700c240b003608448100000036007203640408405001040140c02283c8080303015844203024040d803a840100145500c1e100e191a07811414041c0f401004100700e4411001c4080461010407158101405007a8060309d20a0169039000c850003000c03034850200031840751082d480c042e940c05605004441c02803040b0781c80b00003240c50150005409059000143c0400e01900c01d049000890035018441c0301c2902240340c00504e01c00c41c0c0c510000381654071000c03428034402c2c103103554040142d80051076109141c0843c00401c0300500d00020 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 647515764 1250 647514514 647514551
    0xc070e010e0c1b010c051e092812050d021e0c04020a03020903100603050c041a09090c030d02060f01050d11011d0a030c1e060804030c020a051003020d0509060601020a06 74
    0x1c06040750352030500d401458941203c020800c60840103103104400902200361602402404445500320020300080c034420602c0310504045c0540340d200015110f42c031440012074074484852b0445007a800b1050b66003049404100760409041c0c0c0b07a403403104c0340c02c884904a0315081c9000060b070240d40c001c00e5503400203001e030301694101c120160840d42a421240d10f0304002c2c10061006607000e01a020068810741018007808880c00ca22404c040c203030010940a110010034010f0070507025005000c45c842c10707503409115862584081d64018406401c011651081495040e80705a102c0c141d4001d0180c0010300b102d202c076224010909048a81c941101c01603041c4401c248000c1e80c1c0503003441404020004e0710149a02558446080603c031240f0301908042d2a0007540242c0d00810242e20000e17002a10628041d20b0341440580b403c031049540d00080313298a4020542040480c3d00030070002c804480c03a2081c0c0c0d91101a00d070041c003842c140000040c7d00c42000f0603014005585440001150000000c0c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 647517014 1250 647515764 647515807
    0xe03010207240b1c0201082721190305041406010b07030210050403200307060204060504080c0109030c18021c0905070f060203030c030711010906020c070e010e0c 71
    0x200d26510712181030b1207002c1003a2041ca012081c1e146001d01e04111400c0145154800c00c00141030701c0000180b03a001540c1e43c0400512003c0101a411744c5e418401c2510f20f8800c43c502c0b004002003035552018004070109104003481c0e200e010360148450707072001c503001140c0f100c10302c040d00b400143e6884038205810046400302d41a0224460b81c0000a04940701800406615000c3e03402e88a080305103115050980d0000d68000d40044c00850b5028121b0080f038407040c11400002c42120f1405a0980d543c42c16a0460785c0110082071020400b003191007810f011200b6441024070b0b2003035410f0704507030f07030f03c65900020b00500485050100086903214101d078115880d46007040320025a01c4103890409010300101c60f4201e5160003038503c0020012404020201914403e03000755081d42d0320316903105265000203100700704019014100800f80c0e1020311900034090301814000d030b40c40d070241d20602e182c07000c554007039140301485100400580d156001700c1e6400101110540360380e08240302400c2160139894 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 647518264 1250 647517014 647517023
    0x201e060406050d0b1801080c0d0506040618051507111c08192c0607140306040603140a0c17030f180907080406150302010e01030f3e0306030a030e03010207 68
    0xa1920540f000c080d04c501c14129801f50301162003000081042c8410061080c5004115500c1000414006000e5801c5901c1e084200002078250300310544034513149c503100f0b804a40342c1c814801709000b01103501050003000c501201e00200803200c50b40c850418004450403202041014143c00f14500341c40d072401b02e4480b681440c405002c1030143c0c0700c2600c020203030604120b404490a201e103040059000c9030383c3c0d10420320f0343c9680c1c0004030780100b450f2040e4402071440360711644d107510110000340100003049000d03982400a0218000501d08040503000c0f0790451082210b07507104180d01c0e50b40000498590003010642c45e40c0310442c1e20116012440c450b01a1684010a80204503040d0350101209100c1c0d8040c4005000e00740c000c201214075600c06020190006d5a181b80480381540242c20103007203000b0641d000515130b20200711143ca50364600074001c071011640a0300c1103070522055014842c3c000510503081c65420100002582d91611900c014188008075246018603a420f506613468690030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 647519514 1250 647518264 647518279
    0x7030e010c080d0c122a030b0a060c0201050d06030605090105071812020d0605090d09050603130618020a12110307061b0516030812091b1507201e060406050d0b 70
    0x3c1902c0d050800d6012044181d000c1803c0400e43c01b1140b1070300560001a00103082c0e4024181001400c03680c00c0014201603050100030041d01004c094a440340c4001107016800000e542e090111407142580c1000c3c0400c010003a0b5040000201142c04e0540400c80c1c1c1c22060742e99801c001e80c80814031010b01c10300301402d443d281404201483d0404510101d1201051b40c0d0031007d2a110020014640400e42d0403290040710010420700054142e030000e0000380302c40f11350340041012176001440d082816000f01201e004104800000c10402036400005044105c01602c001800d00c46c008000e00442a082c05000d0742c0d41000c50144482400800f500030440c51504648076203030709080c81540d1101c44507215180d00080080c5010300b021424200c1da0b509101000c2c0c84103081e20810048104940d40884000d07001c11030306000a810b030f0194240c0c141408a400b00c0364102a0401160040140740300d10249444900426550380e41c4048a0170b6645074140079440d0841096200003c0c140802220380000c078 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 647520764 1250 647519514 647519531
    0x903010b031c0206010608010f050603060402120405071805040f060c120903050a111902060c070e1312020604031b1e0317180a12031401090207030e010c080d0c12 71
    0x2d600c00044030142d603902200c49030399880400312a1038209201d8001e01030b00d440c3e010700c002c1c9019002540c001c0303001000076080084600c22400c0d5290185c40444080e4461a0100482003105544000d00308542c1d50820051130702d902c0b40c81440c41e036100014000c40d0386a07003d8403040e000b0f900f440020407500200300300003105460040c6c05030340840711034400700d60400c40408035a200010080417801014142d510200d41d650300744000c80c3c0200e481c64105020300b11001c12a10000705409101e00c608825a0786402c8844c100f2060048000054a045401100400001caa003114a4800381410a508110341080500f80a210031040a803148800103401070444c080c10780c4654440d16000000000f80407035106d204030440845013541a032281600700d4a60907012485101221841b007030303a41004039440042c1300c0c0d075a42d0300100740c000d65082030340410941c042c0356000610306610700c420b0801d15249445a1568001c0b4003408207224a460b07159501c031901680300d0100c04034030000d201030a000404 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 647522014 1250 647520764 647520793
    0x30f0b07201513030c12091d01180203010b03041104110304080909010807081e070b040807030b09031309020a1e020a03030506060304020916022823070b0903010b03 72
    0x800b9144a0341914103140302050403100c0c000001000b9580c0740e195a80d0180c950756990144c2c0242010b083c045c00000140024440301054261440184030750400c1c0702ca40c1081400303000195090b0703d00c095940b051005000803000c103004c030b0303400a80041200901c180700e140000c01804c030f082d684da007100741d011003404100500d401c00b0b01402e19084950103c660b0700c60840b56560f40d214031441c030251f803180c40580c0491600e01c800c841d0700e113144000d80c3c0d0344540701d40314100307681c0c09a4840d5045130b0015104005001130700c4965504091100080d502c1c062043c54504405980e60040c0e29040d503001415042035070040400d025140817946200075505900d16002e5101c1c0c103406010784c04030341404000b802d64544103086a2080d64000c002c4401e51f00c48200901421203180d049609510441c4405012034010305084410b08444000d100e402400901d00b03150808450364500700c1c02051941d008da840e48001c00d181003611030000307400391034480b18400a809070103600e0029815020300010707a001e1a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 647523264 1250 647522014 647522023
    0x109140c160602120f1e130303060e0f160302090a0501030b01050d09060509100209181f081b010c03091503110d0b0a06020d0e0d08071406160306030f0b0720 69
    0x348042c080c5001c007a5180d15103004041901589848030000510000311040c1f100c882c214480d81c000d00d03002450544be44c010070310403002645c124400909440070800b0140b00703400c8805801d03610f07180540c02c01c0d03c4100072881c1c0030340d40d009041c141074a070701c58180f00703034456019121408409041441008a68180340e0005c11041e604820795006010100d00d15190130b000311400c01c80050070080b800b002c000044a620503002c0c086402c0f010501e01d0444451800c55029005000142d000c1c004441c1014690700b030700421010118148101c04021001003900b10511100310344041d840c5482911803120202d0050803030349840780d40040c020900d01030b480d0640d40280300d0275a0076198145400c3c0c69000503070741c449500341c070600054074242d07034510035080008045010900c910001800d00071903990309a0304002c00c040d07029540c1e000b54104146118040f071056101c03010743c20200071407402e61b100c11030705204194025100c0e6000d000444c070341c0c910484404201c1140c415a9000780d422100c01c10303845 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 647524514 1250 647523264 647523271
    0x1b020606060d022703010b04020f090d020303041a0a090509090c130b1306030204063c0306020a020d020106050a230f03070803040602010f021602040f09080301060c03080109140c16060212 82
    0x791f20b4000e8040c5c0500b440d00c200e60707005400d050340038100315281003000b40d071110600e41240c042c0024400020080c14410350780c2c0e03041200200041e15101480c0000302081184c1d80040d2160521300c0a01160010105840d0303481141901c0c205099805100c50314003400907520700307d40201c0c15425500030804146d212a041c1d920803601800015600c0003405044c0510906803400d0741c0c02c600021301c0300000d64036040c1880c4c04a6240600a036500c2d1074035000c82c1c220844000c00b68000b04030103e07640c2d81c28840e6030080d1200300d505504c0c0d1410083c1440340351641440041062110520b442c04554880040d00708a160040072140480c1d2608203054481d0050320443c0055803c000c20000485003e0090740c040080d00074810b140812243c00308009440300030288901196146428004213000300011406031846803101840c1c3c02e0700386401080440144c0c040070809282c540728101d4103242d507050315044070441c403900b62200079a00701c0c1c0010321150100204200d20021f1804a84401c40000034070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 647525764 1250 647524514 647524519
    0x31e050601080708030a050c01060905191419152103021e0d0e041d0313080f061605160c062a1214070f0203011b020606060d0227 57
    0x5a41e0b101c1c0d9050741c484640c00380d401150014030071181003034403410203001444074810010403c540d9580c2d58008442c000d41c0c801e411000c4486420b06c0d401007170300070000c10707440b0f0b900700491070b26260030b0161200320746600700400c003915202c02081e40c200d42d0644c5006030882a003804000d8145c0c801e81c080c0907180c0c040441c05400f8840ca4140e86c51071900b1390344401d00c2500090104406032041c00c90711803c090034220f0380503586040000030300244207081181c074a0032000840e5220100c80c04070442c0c10702a8401c5849521a0407500301101001c18050b800ca030001d00308203c04075010380c00f50b40b18064491407102d182c01e201006020320115400e13040c00c9840719228404082c2c150303420f040190528840028440f9640380710032000400b040244229030b0070510303106500e403080b002e078008554000340d01518803640420100003903117028410307080600112044d100252120501c041c0d10b594000300868440c0c200414510b40c41d030720707540450740d40c09500c0440e0706071000d84202da2204c0e0030541491030b0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 647527014 1250 647525764 647525773
    0x302031f12050d02071202130e1603030e0a050d060203040f02030d0201060306110702061903150816140307031e020909010e0705220f02040819061406061210031e05 72
    0x2203d28004250300040e560b110442d52000d08160302400441e101c183e01004402c0d5075041541c91040c1c05000181600f0401c0c07848852040c07031414010003004c130b500340151042920340c01c1000a03545510907004420f501020250701da40e941d05220340310341c814880107501405100320307455840341d06510010503244600c004000e6545141106400c0e801400307c0290011743c03c202401800c120208000100d6030185004140c0310700038980581440165070050006610446684078045400702c41c54000e040f44003056181780c001000001d6448802c2e100c080c2c0214020f109401e507070400e01001c001c0392078015014500c541010821140240810b10103c0c0131030140d10004190707440c0c201418040b62496001c0341c540c1780210555400185566a00203507001e5080000017100c4000780003192060092a501d50300b450b005041c11020b90f1030100d41c2003568003e001c1003000980d039100c1550302c1c00a80c3c9030790803921b50300c2104103c07040000e40c00140c001180440003011021707403105420708151107801500c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 647528264 1250 647527014 647527033
    0x1113030c091811040506030c13020a110a020105120702160f05010215040c090c0215011706090d09060509010c02040e33010506030606130807050f0118060302031f1205 73
    0x8000020300d40b20000c0003040c0484050f601450980c0046801c03100007010f03500300960300c400081c0c245080c41c0001400b503401140341748120750018101c99481d90400c0107005180103d60000340207203d071002c0710014101c460081450144200012020003c0300301180c10b00d65140c0c02036101c45050b5100c2d42e80140710310150385004101e003045480c0140d40c03014400844500345040c24000e003403610790390000c61140c0b548000c02e01b421074081c1c41c020101c814140a044110400c82c1c0d0030324030010200c010341e90107060171404142d84090074004482a51801e2034a42000e03800490b0044d01100340a94014241400250a200045424094160403400d1301481490401440d4840318400180c0d9007441030300c2c0010000340c1810001035070b100800400e20383c0349c0a504103410040f109942c1010685a0007200184400d0602446910041c813090070310048160020442c6002080719003c4c000400d9008808200d05805100e0074100c0c40d00881000c211054a5036104052601175180c155013510403803990 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 647529514 1250 647528264 647528291
    0x3012d030c05100f090509151c02030c0a060f030c0c1a160c08030114060c030a080702070f080c040b01031805160509040f1704031211060a0204181113030c09 69
    0x400c2a92213407601d0786a030081c80c101c100305403030000415502d1207812441000031540e035004043c00d40300b0500c84e05003450300035034014146424078070008240030303406104003800002c0c1c00120305401d2002c14500814020200d50b400c891007030100380020002035a804442c566200829600d61044000d0103515021580300e06007280c0d041d00c0d0550240081c4c50420050201649035480e030158010090b106c03511300300d4080350007031469000036840c60000300c18005001c41c0c203905000b2107008140e410340406100e424080d1103925450401017061041e603586d02c81c81a6070340a600b1080e103a68a100744404050b80d0ba0516684409040241d011841205100815a4500f09480500950300070700044280181965800b4a104030840c260811110a00c400400188002c0034190a4034450b13850300c9841c0a8001c4052070002d000d00501d118900611041c44081031300c420700f1184040079070001c5905444140348034558454071104a42200b01150044244540b98040c0b41c125007481104010100c00c1600 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 647530764 1250 647529514 647529527
    0x203010609050f0303090a170615060901201b01120606020619090503030406060905061206060f0a0305010e0705030f010c0503131a0103051c08090303012d030c0510 72
    0x39400032640d003100a000350300b0b210031802010200a002c492074120f058000844074035040d401000038400b5114003040840007404150b410016001d48086019044400540d45000c0c01c98204e040110f4409210040a1041803800c05070620000b601d054549481440c030059a04062103404141e1010300038200018070310032441200c4503a0301a01e06900c0b000ca2014052121348c51400e6081d446040b0070012030070510055018911034400001d907940b07800c11020a4801c0101020300c5407031300003c9048a180d0108500c0e03030181c000c481c841c086418060018685100541010f4000d45c82d0902c0103400c0200014198250781c002c5086801034182d590459003038440c540c1c2c954001801c180302081280e240315141d224228450b03690b405101110100400d094002684140d41640c401550a88802c01010521000100d0391904444514044d08603964a10045c411503100140040c004601c2c402c0c010030300c61a50b24000c204030700079680c0c4e0030051081c3c0180e001c0c2c588a074202050801c070040c000c04 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 647532014 1250 647530764 647530769
    0x6030e0616050307051312020103061410050a11070f06080f07051e09100e1512040f050a1704051302091c0203190b041506030f0821010b03071101020301 67
    0x1091500d00000c208040703400e0740004d03280c1024410300f4804240054044141c03840500b4036940c0c1c0e42c042d2003240c000101582c04a5004030b140310380c181003c85550721120421b5000c1740321400c00a542d4a0600c1c41114110400c0e007440c60340380505407011a82c200354141900c111280380d9207081041d180c1614541e1400c000352109404540100708503408110035001101c9483c2c00c9205260801c4620000309006444102d0242c001035851b10030702e10b091a0840c0403010070360b281c801d0242070505e43c42c1c82c0f05031808041e0001e0a06003c09c00c00c01c040120402c984004650320401c005017a480304031851296070003500a440c402c1c03c401103803201c1103c3c0d601c243c0d10000401000207914110422107048003904e0800240d07090700860b144907041075649100341d200306101c3c10310341c80103181c1070034080740f610700101401c4803c078100b90040000c6541e01d00314240e01500035140703075170300d24402d80d640c4140040701c1300340001030248000020b40486010003441c810500b540340d4003d0190450001d908030310090 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 647533264 1250 647532014 647532031
    0x90612020420072406091b02210304080408011404061a1e040617030d180b19021225030b01120905030d020f0405131e0203040213051006030e06 63
    0x340001c401040e000060100c02601c0140c2c00c83c0ca0703070400030b85582039072160b412130b03c201a1500828080c403015004c1f441d08010082c80981140148110070a02e20840c00107045d5106034044040703024095002c1c1103400070300e8501d000308190b0380340915480c11560b0489003600c01a1500040c0800443c0001039442e10b024020280104401c000c24100032642c020704e800c0d60400c0d5140c0002c529120240181c03c00400301c1d90003035840781c030040104810748400c40d540e414400610780101c0f0015160003071301a0004009034a82c030000c00302c800c2c1c80380240035181c40d21f8088500b00062052800030f580404480b50400322881c110741090701426426250341c40406070002d1200c3d5690700307440d85140c1c02204064800d4040d64a400828010001a85c110301e036001030001000030100050301e002c1070884040329054000b032055848000c2ca00c001d010f40700d01d42c81a0390ba0000000f9003159540f0f56034400010000c04100054103103602509003882150044602184ca810101e8464000024010f842607641 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 647534514 1250 647533264 647533267
    0x2070614090405070507020d0b061504031707080f0a031406060c07050411040815070f09060507030507030e0910140a08030f0706060e010305031c1b0810090612020420 73
    0x101c00900009240040c04141042000c2c400c540050352590180d02405016281c2403200c0e0605104100314003004260812b0003072400c0104000182c80d1103040341112256485003601c4100f14180349110788180b040d00ca108010008500c85101e401d0b600094a07a800144c0c0d01c2d565966440910410307104020322491581d201d808104030500e010b400070f0718042c00c400116402d1030b5440b0001e5140180c000b114030003000c86c200030040c085600045600b503441d09850f0040b5520314000f0042c3c00c0b840ba580015080040c0094100c050601030301200401c1a0003a2101543e49803528201c1d00f84095402000109040c1030360686941c0303000303503480c8192002500554686420b08100000a5001050840380a5210032000035034911321000a802903002d00051030303a48500c680a101c0c0f050f07010584950b1180303004141c00340d0010210b90b1030040100b6041c0b000f85502c0700d01145007000166805000040d0034040003040700041003130290000e910a07101403085040500d200c801800220310f80e0180d9440 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 647535764 1250 647534514 647534527
    0xe0c07150c1101020417010b010201021204080a051b062e051306030c0b030406150f1517011202040501050607020117040f08132c01090e0118050106050102070614 71
    0x100369001400c1c00855082c60b03007001c01900005820f980040c0d0048449401381c0000e030255843c2030258282d401c00c00d1000f189050f1008a00e0700c40d0300c0c000340001d00048808111954107a0080088424041e00850b03552a8680000c823541d5603500116240c0281040402146020212103540600c003210b00146441c1c06500702400d204da0400c0b50090f510019458100001c08249284200c00c0580342644003d56030b49094280301091380c2c001c540507641084030710801c100d0311011801c10000d840d9260b0b503090710050030140858140c210800d290f2484000300d000012030307046101c0140c20480c800d48003400070342e03a15010041280070305c0700b010340030901003414682105000940704c4da1017845251104114103060b140c4010744d0300861858144004902000c0c04203a01030b41001c1c440e807450f01c0c80d8403400e80d070604194008403418469441155119001d1441e00442908601d1418079003101d9101c04015a040c51406080f1503c0341a01500075000045291442441807050100055500f10b14018 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 647537014 1250 647535764 647535803
    0x3062d0906160201060f0b1b060c19030902030d050d0f0506030d050c070909080d06052707030e03071515141507062301140a1226040e0c07 61
    0x49984100200f19541c61001081c254207900d400805080840010390b2103c009543d64800c4d580390096080c1d00f603100d030041280354403a5500715111602000d0b6940489540004168050b00201c071009605004514410035040c2e44a13003d03001c1401d07164010700c40816401400340403240150380246c0c0640021030143e5225000c2c00050100c03488d40300c1103e039916600c03500242203a0060008580e20346002600030320064050180700050b16084440d0600b916402152225108024840c8524248820001042240650b01004804c2c00900036607650303006615215040b124465061035050f480c1c0144018900810740364102541d4941c00001c0c514bc01c410100101504503120081d200e883c01c1145000280c90b9008008020a40402481070884155441e4070480c00c141c0040b02405d0420700c00340e1640d65400440c4084910301402c0004044172810f100f400740d103552081c02c0e100700c2180d242c0000111603800400803502d01c0380003031640b521042103691040c42011805011581111400381e40c88 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 647538264 1250 647537014 647537041
    0x9060603040512040608100504110909090309040e250e190f090501020a0e03010c0c1b080111070c080712060213180609050604020c03030f0c0903062d0906 68
    0x2e018034111011035481c42d00100c6a60711941141000408035070521502e011191000720103080100e40a0120413040348042040e401901c0ca032f10b00c1403144201092881100b80211074003000c0140007405400000c6000c035954000840403032448004888800c6542c2c00001034103026245070802181c029150a190501c81494050030304180c2ca8bc3d480d00b49880701014801d507081c07540304e00d00241c0c880040d84400340610720303044207003170003039044c09501c11400d0b81c4804c0b01c80c140d07a800650014210f000201611204056400c00b883c298644000b800d54901d004001c0c100302c030300c5226032490315a115141c06450309203034401d010660044010718000641030350054242540307843c0200c13040755903401d15410803605a5140a49044d69942d090140126501402d588880e0540341980303441c02d020107841e540d10009041034400b402d0340010a6107000301104440564900404403001c60a12101c1d14455415840306900600e1500f41c8440e004a80204540e2160700e180c1c000e003030240d841c03890b90041c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 647539514 1250 647538264 647538271
    0x122e0c0801051504080d08070f02012a0302130f0e0703020903190f0b01150207230603060607150515100210050c12041b0b0c0c0d031b050109031d09060603 68
    0x3c01c1c005004c04034020b42c0406c500c06500205645005880c20041c201510b8810030720034810444e4140450401540c45050b5100b0408100c0035050040a42d80c00c400c070000d010f88001080180011302001850002e03000c1454281c500c502501d144a40303c10000703808920038144510342541043c0b07400807130a100d000c2c4d051042c07401030000d070700380741e10b1581c0d94100311809800a40301d0840c0d8100d89000540e041240300c2c09049551100b46440c0203000c004001da403942e00c1e180740b2402c000400a05d00392240c6050b0b450f0300754030903e0038030028982c030941e40182034102d030710aa91855204c402c690a10700f6010b4030314000b805401500e5580d10170744140e4003a160081c81c03072550101c2000f20601e07400502d005940710b6401042c003502d80d401c401c64241091545917020b540a04014441135402d040049422a0300c42001c0341d0b40260f14001d441d0555121012404920160079006410000c2c80010740105112500c65074501941c0f1301402141c99001c04a4580e845d000420000029040d05040d002144c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 647540764 1250 647539514 647539549
    0x408060f040c050d0308090d090e010e1b07120201230609100b1c0b0d0302061915180617100e100516090e0c0a050702122e0c080105 58
    0x20b060b114008034200100781c00c03044001550480420070050803e002090820005140c091580382c50300c885d000b5200c2060180c00c141e00d07107a10101700494a4004813400303024504041301c2e00e8107038500744030080125002c0000c01650803d4440c90380044240b2000c0c0851031116000c0e501c986680b005d03c0301da6203000300844443c0b119048041000e4003580040c2000040c511405001e0f03071801c1c04082c0603240c0349104580161111301c2c18600080d00850010381c00180d200c0720b9004040c1800461000c0d1000300c0081078031f580c00100100d12006200c0711070a058501c2c410074490705555404004004100040c008000e402c00482011010481e4200085926007801200d60340d50100c1e522100b203500550300b010013014000e500e50112330300910494003d00500c20180e075285003582d4007800c00c0c03082c1c0349040d040001c0001c94004650341c00e0075024038107403800111510b101d04035450030844190088142800ea0091292281079001401962a900010741ea400c0050f40b03018284400c41c4200802c211 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 647542014 1250 647540764 647540783
    0x60c03181a180301020d0b0319032a12080a0507020607020c0d02030a0b1503060a0504080409050606070c0314011109150a0c06092001170c0c030c03040b0306030d050408060f04 77
    0x142c540d401d0000d02030a51384040005640340c500820140340440280c0310380400c07030502100002007a002101e00c01b60900703074000c9490403040144d80742c0e00c07140c1d5100002c280501e900250406240d0000c502c038031070f4041c80801c11180e00c600d1b0060703030b0f03d0340c08454000c0160303c402e40b142603900b1b04641400c5614070290485085030280d903654112003204031944411120000d481d0310143c0313410001650001481442000981819100e540d00c6100ea4081d40ca00ca5840c5d10100b0100e49400040310100344d00030590001580d16807a092609080c150746481c0e04d507080c022624501e804030402c43d0a00030000308107030107001005103181102e41003515850140109101c094011480a0003480c407400e00c2044404024208900110313818a203161055041140c08104401804040800686c00c000c5642c5c0d101c1d29180604802d1f855480b403800d90080d20b00012400084c0320108501540c081c00781242640c071442e004c9601141d8038062441004981d80c8a000450586600500441e81090242c6502d1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 647543264 1250 647542014 647542057
    0x17071509050604122109050f130c080f060f240f0d0603050d03020c101109120c030c030127020607080f0901140901023301060c03181a 59
    0xb042a003060b80400749806010a803001002600710014581c0303502e003d20408003040c480c0c001401300d03426002e29406072615441c2840c2d1541d848103000b56100d032802c42404040030710500100101c03c103442000400030284041100c0380f5091020150640c80600282c06110000c40c0d01c03a528226600020006542000700c950010b40c058000c042c01400c626011401c9465407034894a0011160510b504142c4144490004000041100300e0030f03d000900c0400c000340911801c20f8144101d1120f0b680c0454014168810303408045039503140d0210460959100d240c4400903d0300b619501c114011403902c0014040714484a00c00722210500d0000e05094101030982c3d841c0e02680c1d0002d030156505800c0401c41110644c0d11680b40101d5045031440ba600b020001000070703544d03000000c2c4603244d000311101148612242281812030500f56070602680d5546e440303501501c5008250760550000d1481d2400c0204401c000d034070503003280c4040ca0150403002603529030260a0f04801501c00e0318034040090b0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 647544514 1250 647543264 647543269
    0x18020706091b1d041a09070b040f08010e03070201020703030f0e040c080609091f1a0301060b04081009120c0501020c12091309080a05030c04030506010b03040c1707150905 75
    0x3038505054440500386806401c211002c0d60f48088507083c1241c00c94100f00300000a000d0b07000c02542d102502d209442252102e806c80d83c03c0c41c02540000001c000e010030300041601200d00c403d4100c2d21010003c100e504d00b40d19034103490703115940c000707070142e8400641040060300c260082d000e0314503a840c010030300c00710220000c0c2c19105410364103400181020705005480c904044991741140f0318400400103400c8074503011040c0607801700d047c0310030b9a0307034920300c0001c42500704c18101402009000b0400c1f9a00c8211a56058001d4082d8284034400c0580c0d800c0c1050041c03013035003225604045ca841c019a940807040b0355407004a20100e580b5502488104001d5a08200074000c818900a0803510380c08044140303c0c082e150b0411043c030050903c1d080e40089070028007100d00021700c40c5045507481c1d07503001184415126551004020703210301000022050704c1d00c0c0180d40614401c426002146079548251444407000820100b00c94222003004c0040e1903400e25002132a540909186511039501d200 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 647545764 1250 647544514 647544533
    0xa0506090d081b060124020d0e060904060b0d39051c09020306130b0f1806090304092a120612030206061f02060106030e1f0e0c09011802070609 63
    0xc1c10f8601d5441440140401080b800f501d01d0100c0380741c43c0507014816840707402551031851125607814007241d5a868406500c2c0e01007143c04c145000b070024421142d0702e00c2401c00542c070407d00c038481c252402a1008003011814141058500c41022410420302c00019010315070b581080c00009000041228640e014201e202403e00d44205600004082c1c03c0d90046c9410700d031000f03011034001e0484490b60000140b0700200940c00c82000e1711f10580d65954481c042820540062450020317118030340810904110000c000c0007942e0a401e4240a40040c04603903000c8142011504d030010403150f0404802c039403090b042d00452920300300303011483c19514805001c081d64005025401078104004001d0700d030a20f085003c101000d40320648184101400d0025164081030050104040d25407803003800c0100c0c10025250b10080311540e1214040303080521750010600c0704038000d41402809010700061810b15805812100034400369a0020180c02445009605c0454203c90050f07842203060302060f80c0d8075 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 647547014 1250 647545764 647545807
    0x9090108100c050a050d0b0315010e16030c12090c090f020a020115031109090f010204090902120607090909054e09040c0e1e010e0a0506090d08 63
    0x4060a0a000101d050038259031140014409100c01048542e8050307030b20a04840e5942c404220008410a05070300180c2401c2151807201000711400001080c900d40c10604503010b540000304103035281d040c1c14410380c1903625071500f03c0c002c0b5100942c0d6032000c08540e0800b41500340704140e1110481d4803900004101c0da0381c40e10f0850000c1d40400d81c80d491640921a1809110550500e10049032455844420b0780d464280030032301982051000c514041010000d0f184028440b600075510390340c03558861801041c0d51042680324800d4030110902081e8089902e50040e0f00990b141400e450404401c00082d204002044515101b4002c00c04480e11034800d01a2024961450b01c441d198113034088410a64101605220201c00720b4040c0d050340c103401011640701c10000d88001c80e1501c806401502d4090a140342680c1040103100c0555070b00c07120040d00c0c4031504090300d03664005402c0f0310902a2003095030003215041a0100314074003061800c403095100d6a84180c501c907203407000280784603031145c0c1c01c02d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 647548264 1250 647547014 647547029
    0x250807140a050d1e0923180109090c0e040c091d0102040801060911181e030d02150c0a020712140a080408011a21012004030b060a03050d1103090901 65
    0x1001e540030140015a004c21012110740740030340103103082c403002003941000000074a08030040c0d641c20005640762264020078120700c2c5a41c0c0d1304e0030741e0f40d2040c5001605241d1001c4402d1105144040380f4070a107a40c80b20f0069401840c02d848490074952094024000803200d401030440c0f0325000c1520b84001d000510103454081e00200fa00e17450310541105454a07026402002007050145540190900a200500c0e02084034130b5101c5080384660100602179480d2916014001c0010360440e0341e40004452a00b101c418151400a0340c51741d413404224052010b002005800c0440100103e904c00b00c940c02c5210f00888602108910b2040c035285458407142e030454110700045404c00c00b110080c031074410800710000001603080c0c801c00009201900300c0d26284228196012100b4072044258131254410965400400d0064071070310000030f19411a00c01110f140c40036030002802c03420901d50304800ca03540180105040d46c82c3c074101745c8400304001c165000a12040c0140318640c0d0310301d0f00c0203000b0040c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 647549514 1250 647548264 647548277
    0x5060a05091903030f0311040f06231806070212190c1401170405120d0b2115180d050901021005060906040b0a0317250807140a050d 58
    0x100e0078056040c002c201c241d9410034040804001090704901c04401001c03e6207000100c05540e03031800c03483c82c001c54000740c5000b6650580403600030f8021444140c0000c0c04041c1900210101142c461035110300403240c500c2d0310301c818682c0b46604009010b04205480181058034286105a68902d0070152502804000500314030000502510300b0890340a480000310250b010b034114400038001d145650300c0254000907450020b81070001c00d0003d0880c0e0300d14214070f180e46009142012029012500001c2c0c07181c11002e1000785200c0540600b040c01141d05405880c0807031003401301c2000150000d01100112440f90f0540303840c40d03030500680740c0b4044030740c6600d519a58218002407925084101d16106a803500c41808080e81d41d000c03030694890300889000c191007102c640420744030002588002d2400755600c4003140c0c054402d101410f040b441041c49010b1781c001c010307907494001084c01006040c6c10000c1140c0e00200d600741560007000c45480040b0f4160f0380e180d80e42c843c42d0640c5903150600180d807 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 647550764 1250 647549514 647549527
    0x312060a080703050303070509040216110f03031810050c0718061d220f0b160c11010810030b0a0e06070f14030901110c010c02010b100503041b05060a05 67
    0x6103540395a02400c51500281039041c110b90351244d99200c00782c25401400170110703800915580c2e80c0c0444003280255003003583d500c101450948503450340600d9261040c4031440c0380083e1801e000042e645044502031174000151010802d00c1002418114a8002c016017049800b0001d20104203110007826022440203452070351020b448102c03101d07600014a10a50a40f1280c0c007600302e04d61301600007419035484280b4420319130101d10720304000705000705070003001810a010b201d49060400d218145080c0c4403901d40c0b1001c2c030115400440500300603c040c4503580c0c1580e080d44550329650748072403040980100a9100d444400008200300c030032100703594482d1000308944400b403290982100203820900d04090361600c022f009139000d6081d904c403454003c80010440c01094000b175070310404404c40b69a0350070f840c3d5015406490242c2680c005076080099000e01800c042021030103985107236994070b0454032280d584450000c1d422001c80c0344091010004a036540c1c8080042001c032081d40c031410751718170 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 647552014 1250 647550764 647550769
    0x50a120210050406080739050c0a060203031b13090f060e06030d050711060c070e0c120411010e03060c0c160602030f0313170304150b100c0f05031206 66
    0x58035801d60904001c4184401c0100c1500b159400341c01c035040303082081480d010b41040f1880b04100c1803000c200c2c11070104959500101404044044a004400742c61415114a00384002070b8814400d21005910800002d00c11b00312040085101142d005402451700c4080ca10031580701d045a0400e0403191707540c0c079120107989030908c1110000c002c05500f400d1503245c207000003606c400d66400688248000016124200310f4001051600b02600820468a941e504030000343d55211034052010700200050100345800d0110060b94001d0f880e04414480303d03502c035074650349220740b02040f450600140c4030012819a03000d000261041c0051011180c1302e441017440c4601c2d081d041e5100c0107101071004414022540c2c0441103804030303640310072040d0390794484141000301c100e85404081c00c1c04000c0541400f8030480c00c1c00640c040c074015202c80c003000301900307541c804070780440e40c49652040c1641c01d101c070324a0140154040b040d0213800b00400743e100ca03884260a40c0d0201442c01700c00c005d0381c002c001151 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 647553264 1250 647552014 647552029
    0xc09200a111c030b03060402061615060303090f062a15050103110a0b040e0f040f1e0c09020a1e02030d0e030c01050c0c03091c05010f14060301021201030b0a06050a1202 74
    0x31301e0101c008010174106034001c540039101e042080240ba030b5000100005002c00700c0000c0310901e0300c2000410000380e490a00507d540858000c120f40580c030f888002a00c2c034801e14444c1000c05484982d400340d85590b03d0201c101c000003403011101400c2020013071040c6049442035500850182030141d0fa981001c4042202c00e507015004811608404c0c031080c030004820100c81680401d9400d041e06040d119403c2c002d20a1644581c000c1c44518031280d98041e000b554650f180d0001d1186049094468a40c02100d047c1c0c0110010fa2002403d007980302209680014002c0c452182280140d07840c00b4a180500d005551a4000002d4907900024403105080400d03c00d183e80003003c5103001c0d06100d000d9084540700d01c2981c94561041c000c40c1d061030102c07072681100c04401b81c3c1c0b0100800900700c03014441005407c0a942240303204071140001907541c20180200d0f07030030170700f41081400c580c0e00f15070364021804005405001d00503581c0802040548030003602c1c1c0060607150800f0810b0040510401800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 647554514 1250 647553264 647553281
    0xb06090a0603080d090c0f0e19020903030403050c0112050c030a0c030b030f150f060d06020703020102040902030a0c03050702060613051003020d150506011b030516020613030c09200a111c03 83
    0x42604000100816104814803279000b034180424114040401c05042010380200003440364517000c00200003041040008a040703000c4c0080e00c030a104c869403412032000300c40003103a1110701034a04200041e000070302940105118030a40c20700049040703225011034074021a004818520b80d0000515a1010250b00d5a5a501216000ea003a2203840d00d07070041500240d840e01c0040c442078000c644401010700070b406030350190528882c11901c87c80c1111003a03002d4000c2030028000300c1d140202085a031840420b12600c1102c0203854004500842000b2900030400208009030781e41c012900400165030310b2042010450242a03007207000d13070f00303005810101e40f0080c0955040c4004c1420b000c05519840310400c9030a5054180241c0351555180100780800b503240009522400000d42c8090f1068a0761098082c2c03401030610300e54a0f62982c68510865000500005031603404940c240c40c2c0d49070200c01040640f000d4a45090300020312070803246800303800d12489c2d00d08509202c0c8449440e81c0f52103403100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 647555764 1250 647554514 647554529
    0x30c06051330180b030403051207020a11101e0c030207171f02070b04080d060914010e0c04030c0602030306011d0109030210030e0f01021206010c0b06090a0603080d090c 74
    0x1450b911518801d0000a04800050003084111403024505801800000f0845128020750340d00e400d1800a009a01814000e060000a00040b4400c03070300c0000c00c00111036216201d204403c103840c0030803a5041903083d80074100011090448110402c603408043d2190140d200c01c070001e1002d10b4084e040c41c409420a400740380c01d01d41d080020020000c0c642840026034444405840e034400d4103440644140400a0b081003c29000e002c100b0190030001c00c034030042e0030070812510b91100380b24000d580129288070b41c140000da005100c002c00400c07040f604525511401842c0035929928010f00100c00c0c2e002e0809a00080104180f03940c018594450150f015050190001940300000c0d002046902029001d84036400000002c00d000f40e2107080014442000c0301c1c0201c45008a0a020b0740c41030203400c2d80d44081102141c2954000c140c03640c17600398800d50114150b5500014400d16400041120303000c16255840000440c00890040501c201c661001050f080042d007002c80c0350410b942e10840 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 647557014 1250 647555764 647555813
    0x111070b0603120d2a0e0109060512010306020c010621050c06091f0201111206032512050a14011a091e040c09060b03040303050f1e04030c060513 64
    0x5101c0c0c21080444403000d0100c0e80006800e05544811022140d070b42014071300790442214904017084e000800742c1c40395070090f60365800c060303220142203d280c004c014044c1e4180304600018000105190013804080c8030003000010481d541d070300c0c001d943c0f1100303488031842c0740e40c24848002449000d00c0340070103049081d1802803500203e4004070780e01410034245204400c62180303110020b903100390072802c0f00c1b542280e00a0740b105441c1c661010300b1f900c2a101c0501c139104080c0c1c02c280e40109d10b1032000310b011240380942c01e454680030700d40d094102c081008031507074081e0400c0e080c0000c0f00e420a240c0c060146800004501d504108203d840d4100b102a8074850700d8451f040004070300800c149090b410058151007812921030740b504802821060304044182c50030807801140044d0391002442c0300340d001c0d640c14030031900d581004110081c03054540c040180c0c3c030030700541d8282159100540d000b62080c940b15904030030075201c0800300d40b02610440700000b500c03140382050206225000320740541440408 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 647558264 1250 647557014 647557033
    0x100501090303050d0515030d02030d150b091002030708030c0c0c010305160c03051b010203061c030f0c02010c06060f15050301050a15120c02010615030b0904230111070b0603 76
    0x10308203004c0c00707900070192515900021310703007240001c80404540010307046490b800049040030391a0b4204a030070001075490030071800300c6c81d0b22290b410405c88a505803c545080c1600d0284000612045050800c0d84810010000080c828400440c49009104411910ba00310100304034100102d99028604150805092104200100194520440490518098009035480e0540340c0b8051a043c020503400700552807505410103400440c41a1401c446005843d40c01104c40011f40003004c10280000c0d0038075060b481c0c0e060280c00c00e0811035005040440d10001c155039100d05603070564100344180e2481d21000c1080c2c13111015010114005030914038150b40c10000460780076070740b03031145807040403120018080c2907000d00410170050650b800d0034403988041c620003901801140c0b1501c07100002c25031440103090320030322505100c0203006090a0032500c136902d603d00903001c54900c589813200240c01004030b5150920504e00180044900341e0b40ba01c1407800d10061401000b003100340a5000017040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 647559514 1250 647558264 647558267
    0x60201150504051009090f0308090a080d05060d02120c0a0501090308090411070b041212230901230103170c06010911040f03030203091014090f0f0d0b100501090303 72
    0xc00d02501c0e42510300060301d40da112110015244594426070a140c540412201480011403000304020300030345600c525501c5542c002c6907184404140a000742c14248174802c03284019030041e80c1c020800525504040b40c1c81d4001070320042c0600344200c2654851034011a950920020400007445c09003010700c080e9146440780f13210761003540e107068482d0f070703540c0a54802c3c6c480440c240c880103a00801e0310b207054680341c903000d050306090400a4001c0b41019101d1110b0445600442d0011385c50410882074001f2131049130805c0080c00741c4922010354940107110000d0340082d04030f03004440b600926445035491400c04541200e02c01d64484132007102001030488106000a40c50f0465044200004081c1c440c864192074a01035034005e10a50100d40c10000140f40d070010241110390800ca131008042e001d440030a9070040b400c0343c4540700c4007405104503101850002d00c1c009240c040a0030340004039a0041c00280d15050045041b03501c850102c081c40001d50210500030080c28003820800c01706415600c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 647560764 1250 647559514 647559551
    0x3390a050d1d01050c011d37031107080f0c1c03170a091502030702010b0d050712051219021204080714060d051819020a05010f0504080304091401060201 67
    0x2d8090600c000050800d000ca0400d5100c40d1143c3d0180724010318000d20b940b07101d501c4515a40312103c1150021611403d041201115000f40d140c0d2903c0d5844c0b1022290b81c2600d85800100262209003c0c9a000041034081441035161f112840e502414170140b40d64100101510030a4174081070499050301c10001a40098480085c00300000040215548144455028210b4502d0040554062100518281d4415005540138402e82c0d0000e2220111904c28841d00342c400401c00307401941706407020402c1884103404041e1060186042e1446031408402507511035203c0701071010002d9510010b08a1907a051143d0700380e498007403111600d030900d02445955181101c0c042d01c0c035000162445040d41340c1d5407108036014915001d4092040b464401c00940f07881c40c0310810040305000d501d1b04034030f00d03041868090344e01c20307802000d00c0300540c1800011111506000021000c2c01010403000c540c1d8901000a080202000d14011a9921210312404268241a407150042d60f050021b0340307038010403000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 647562014 1250 647560764 647560817
    0xd14100608060a0b0c0114060d050c060901121805070b030c042616090510081c0c14061e0106120e0304050a0e090c03030a0203390a050d 60
    0xd4180300903240c00d00094003441d0f15a001907080000020440441a07064100000007a40041d01c49a2655000e080c00f110314454580240310b17400c0401103248038940071b80035003608041031601c0750304049890300d440202c07034105c07c04040e003000b802e600700c003007120801011014044945070030b400d6041040202d4024003076402010107500800c0e1440b00e11002c0000001003541400e030031038402c110360395080c200d041054055000b000341000c00080c26054090382441c200c5000c84000c0c2a410303018024031019000000d110320801c40c000d000640801c000e40a88030100b204400a80100e00704500d0610120081d000800012004135004202c410b03008122440c1c03240480c1004501200200d000d40d0852149800c02c660100646102144c109819034955104071a1101100c4005488600f095a03030301603180104016882003042044040048000310320700118165103001b5451026403200781c900380c6c020000340d55841a5001d13020312004000320212000c1034180020101024070084201004a4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 647563264 1250 647562014 647562017
    0x90c1a160f020f04020d020d062408040c03050106030b0702010b01030605090619031b0f050d0803220f030f080f010305030316120207080405150f071509050d050d141006 74
    0x8448065480322180756061581c010130855031071010130b003940001e4201d8000c1500d410701d4071710041100340d20384503840d83c03480110381103070100241c42c1d100310703100d11004000700c0e40002d0000c80000020800d004441c099485204144031a2070001002030859851180aa04040c2403900c02c120325110b80c5100da170024400d6815403c4808944131036a4811007542c0004d1201c080685a20018842d8607080c02c240c5d464410070304240d640d6841040154030140e072002c1d02c160307010408214203240130300903148020420180540000c0403500d844011220214081d004101e40c01d070503412081d4403070556544140388042003406541141c0318140e80b40002440c01541603d803520b80c00341c49001c0d00328654031591144055554407414908800a600940b246034000c0f40e040600110108a02c0c060341c803c5030070882c600e4200580d85c3c641081c0100c40782d251884440c2d80e851100701140040c8a43c4940035003545503a90b03542d0001d040d03c01100c0c800003411a184444200707001c842132100401208881d0b05 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 647564514 1250 647563264 647563283
    0x41509020f090402121b180c12040f051c11060708010e070203070c170607050307020604032607110f030a02100207020f0303130602010b1c02041e090c1a16 68
    0x1c920105d001d43c04100031001d107502c9421a545e05c1803075038518412220308203440c111080c650b0441581d610754401d0761542c01e061030902c0074203403410301c00b003000b03a01c5030144155542090050b100c0300e0414242100360100800c05443c0000321740d400c800c032041d100c03224100801251030301c40002404a230040c0640144d4007550701c0824143c500c200141d60780141c000001004081d80d48500c00307414014110b400004c2d000e5000040c01c807030300070700c1a603104042a4003c0d1043d0341c1d49560486000c0e0f0180c51000010b56902c1c03450b400f08251007103e0344035600b2a21030401f400c40c3c40c0007543c0b611009804142c9150310400040002540c00300309848400c00289016031a8401032001440c0d9840c199400d82c4c140c440410302c01c0c6a4100300c1c1907042104d450350000c000003841c0c403040c0803558124510280250201e00395400050506601540c00c114003508583d040c1d06034200c1627801d4440c10341040c1d8100320100014098522640d1402d0121070200140d1440c2010710000c00e90b450503c10000380000c400d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 647565764 1250 647564514 647564521
    0xb030f1b0a1d0a060203190504060c110103110c01021b0309150904090b0f0415060506120406150b04030b0627101d1806010503032a15041509020f09 65
    0x410a042d0418032100400c01e501294403008002e58075005083c0d200096190340080d41040c5010744100c8080c0c660a541d8010042e20644400101480080c3e800d81015680c07040d1940278080903001e040760940c06000541d9400701100390000e503020040014129400400c04102c41d0341c1e844001e80c40070034100703007800d4a9515013000a002403042480152002c0740f00010030541410031b07185140f00740c1c459503094002e070102000c00e00840d9542d02503a600031400b00001c0100b1100c1440359a4458402c03440483c0c5100745600d0a0042200759000c2e03450f160001c1428010030440c602e10f43da02c12010754041c1d824030f152050301002c00e404052000c0b040880c0002040903500c4140c1d0000141c44056490001c5203460608929a04002c4640500c500901c21031008802c6010949504035600200158142210030031030440d07030910441080380702c501d0200e080d0f08001c0280b1000803c611101c090f40442c2c030b860705086442c40a80c80b210f541c2a4074103c03281006a4030b5031511654008c0070f45a1a0142c0d4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 647567014 1250 647565764 647565797
    0x60e10050706050109020702090a1b0309050109050703030810082a030703121e020109050d080604090b04050a0b012403020d09080714241506130b030f1b0a 68
    0x201d1010003501441c20100081013490054004101051080c1d0341640d080c3d036802098012640110b4102214455004042d141c003803194118482e01805000001804a4a0390f00d451420446a000302c010900e62030030014440c03103d0f5408801415401c0c050203a50744100e2500d0020b03110390344400a5116203007036208103078030704010400c041c65005154520701c0808140c0070b010f1441d800c40150585413102c484803c1d0a2040c019070100d154007030020414016203aa05035102d19000700541e401c955601c5070100418080d100c041c0c041c40c01680070344580e1089c0d00300f809030000140c01c0100010b50700c4000c0c00d441003003107011080c41000f518006807030300c081141c41d1000c0c19002d00b014001c0d59002c16a5410b20104440021002c80b94104844009002003000d00e440001200c038100c1c26110300000503c0011151201c80305004003d0031545080001d40c20b915594007107800003032000c00040104001584544081c0340c020300a814414210502418640054800c110b03902040040e40c0403892241c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 647568264 1250 647567014 647567017
    0xf031615031e051504020a023a0804050f01090f0b04210f0e0a0b0d1104120c090c020c0607080a09080d26060d14030903011a100207060e1005 62
    0x82c8041c0c000ea044081d005510100a00010740d24600f100401606031807503454140308540301002e20b60041c003a5100d0750840c0043d100c1080055500d442100c8512001e018203260300200d04032850307180c108650610303080251905041d603480c0c07820707689809180e4010400304891400b402d503005200480c0d030756851a05034011046032521403001303215086040c0300c4c180c20001c840c0748200c03036036103420b42184082e04000c52810329100c1c096001108000d0300e4540042078100303072640750020f040380e0b140580c4c4112508241403e500c2c1550703a84849802885001c0c030030f01039802c00d156103100414042034124001002c42c4115400100712150000e03e0007109d5000749000c00003010860103440504841100242c2a1030078070b003038450603500c11a280044610800782007070140c400038010500302c008660300d01c12204552510880180f00c1071000300b007039660900484d6400d258490420b04401040810301c9511070049041c201950010001406005d500100382c691102b001c40795070a501541c1442034449 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 647569514 1250 647568264 647568281
    0xf0c09030a0b0603060a06060e130608031305091302030d1d03060711070608010b040306091a190c030b10082205070f0f03050307030804021513050f03161503 69
    0x1070040c0d140c200288200340d011503200c1c1c88164141c0c1c1865a400002100302c0c0c20b58000c0101040801414034483c0c10b00c000515000305041d800000d5082d04c4051842c41d41c1c12590700f4a01c03195030200240700345d0504841e07254000861100807010500c0c01d5001a0300c501001eaa41d108100031010801d0300c04000045d04451040083c00b40c17002818840001070884102c04a100124802c0c240d002071000d02c18014076048030650300c603540c2000e0959036031101400f1110400d54580c00301d42540024000688030719070091618a40700502541a02041c1c13054403142005007050528007d000e00302030715080c51082c160121841c10716032607940d0404bc2c405103c0707440040300445400041404c10407c0005141040c0da106400071020b20380d0303403d801e0b00c00000c98040109650002e001c50300c0000e000326041c64102e44002c0c1400d41031429403250310001c2d00b02c9800801d07403800841c0704000c0ca003042155884035100540203420002c00210b0410014040740c85406100322507507403054112032080e07000500d13 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 647570764 1250 647569514 647569519
    0x20f09040920030d0e0402071704080c0118060804021002240604140106050403350d050c0c07060e180717010801060621090b090d0917060f0c09 63
    0x248240a040c014215400035070312000765042c0c2466100180f400160307140380e08025a0b42d40107412408030a11000c1d402040d13049030a40f00001d4920711f0111210050800b9080e884000d00035402044001881d07003a0f245486214080418800e1020a6002101692083e010350b40c6217000150000708900e0621031004c070480d101864071380d0084035001082c10700d010300c10441d0140941d40c041c0f95050780c12182031050344045801007000b080080c5404034803000313000c064888a0304860341c641041010004804507900b2082001035440686102031048503042140545020700f0f0080000200b95180c005008100500044401130900d9948203c0b6400700d48981190303205041c20078480107070680194104038240f4100c0c540000c0f94250b0148500e4044914950311040d0805840d040029804280c03000c445480b5201d154400c04200005541e034040c01d400740080981c1c910211005003041000d40000300f18001e800da424081c0400080c0c4180c02240594003513000c2c0c0ca5030404806184242c040c3c1e00c0c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 647572014 1250 647570764 647570771
    0x1104050d120909020f070b0a050105100c0507050a060f020610030507061805060c01051803030f0a050606071209060906110a030305073c0215070e01030905070902030901060b1c020f0904 81
    0x743c0b5280c1d000509246c03032081b1002880ca40718002c0da48103a5009000307143d0440010202e690601d071007119152840d030300880a40b00d0060b12000810b1080040d50403140101d03111000d034812850b410008150700400b10100c100181d4196a2481c0c0c640740c5030b04c40d54040103001d55102c0300403d81c0903494030003004014401035a070022628018040c00d4100e9080c6090244003035800d403000c801104681c811119281c41d10341a0b610019403100030030020b002190402d0083c484003000400e03501c44000d2840d09900c4901c3d1444c9440001080195541c00c030100f0020007119444119400240421003d40d0504012606541d0354000b215840203800303c440ba5400240340340d03101c40b02c43d8415013044805090b106c941b03220880300180c1c2c0d140c000c15000c8242c49115400900450703c1a908032050350b5051401284002c11500c69603d049116041102762035030000c203010010780248224402004000075440c10899000346d0f4131020601100b80c0b100c1207070001049142100e01320100e40c2c0c2a00000c0c03042 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 647573264 1250 647572014 647572027
    0x605091204030f03020c0d0309090504060612050601090c09051f020309060f030709060815131803171e0a0504020d06020a08060f12070504020d020702120f011104050d12090902 77
    0x49090000640e064000d4003034101d00980c0d50911f05006003041303825480707070090986480c52200c01400e00800680e0047e40d100c03c0807030b104001180c0e05042c1d5000303c0050409505100f00202114454a9021705100080604002c01d49034114204031607076007030f0028a0714580160301641544201c0003010b5000e80005442e400707503030485000c0c60007984507a407441440398850400703481c81e40080e5485003540002030005082d40ca040c41ca484d041c0305003030380003181d604028848900d02c2540d0000450110705006556029410082c400c00c3e40003150740f0b503401103240c07a030420202408004d0003400e00552290000b07015911071803055000c46510040465660800301c0004040e942e06440701441821703200e80400c07651418032413840580b030707408001d03003909858803017000029801101084e030300c0c90702400144050395a8a02c15101d0380d26050103010103858071110300e03085807050001c80003000e00500013071200e900d950f2a803140f00c2e0383c001801c0306100b00301c102c00e60b00c0c4015a0300242c0c0c1c031400007400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 647574514 1250 647573264 647573273
    0x61e03120f070606090b06040905090c13021b0a0c0614120403030e011a060301150c060c03021c06120305071b180b0a030b040b0408070602071109070e030a060509120403 74
    0x1c00b9030500a01c4100311283e15038054006681060b00c149a0058081c00700b40724130403055100c0c0340c11098140072626111140f20204090101c3c0b8008401655804540007402c5035845c00440006070515010308916880b80d174400180c200140241c1c01085000400711516009040445035042007000800640d450306240c003c015003c6039500d980103500b04810b6030040c5210040307410210310024030711825a8207101b2a0050704100c550b408042142c0c000341100400c6062191580c4080c1d5580c1c05642ca0a900040300000d80f03c29454a0020b0728004041044141c0701401071400c1c1e92624103695109050f041034210010b44048082c5406081d040000d42080b05809000301181e0703510b828044403c002c0d003001350b42039a6100c0a81a6010140010000b5060110465101d407141c111541001166114482240c00c00d0808131440c1c10703410000400307032400f07910300c9a2110481c80c1000403042010301081d05d50304400e0006019548560105920500034058200c0660325148003e8075a603407400d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 647575764 1250 647574514 647574517
    0x1e1e09080703110c0d060c0201060909080406170903030118020d05090a17040305100b04090813050a050a050303160503040938010c030e040908120f0601030203061e03120f 75
    0x302280800c00d48050343e0b40c0103402203510130404c0402440004203409903190707100034041040080045550700c0e1f001080201151003a041024040c5501588460410f80058060000c0103220401c0d00003607020800d10050010032a0b0641e22740c200e03440008420089040043c1c0a81030107001547d0034007042040f8031304000380117042907015002c030f200f150b030030326400310501c0c403031030102a000780c0202580310010002c64000c100c11640107800007444096a031190704654020300300d40c021030309100004100030700e00850014060141150700301000381c80d0000195480c07084040800d40c1c440b4001001080c0801402134400424a18005224145604c4400091904145040e007034114401c1d41621002c0d0300000801709619040e120862002c580c0d48042d107010354201401940a03407a410711000113075402018084641000c1841656811300080d4881d1703084008120604062042c0101b24266032140358400c544d050130450724034840b400d100071a04082c0c41800403902e1520018280c4220b0000b0340 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 647577014 1250 647575764 647575777
    0x90f0913120516060e070e0f070e0319030f140d0204050913020102120715021b0f0a030203030112020a03080c0c1c051c180902040501020f011e1e0908 66
    0x610000e01d4500082042d9114019006020ba0026012400000060b030503482950070744401d00880b000f43c0e548803507154900d6000c507000780c403001404040c80f50442e00032110811402c011070151030b42e070382d03a0f041070120000390320780150402a0610382b0101041c011800070301c000c8524040d195071110041d44850103903215115141c0614001000110300d9207250010312002641640901004074424407000565044208103440503e448054031450300c50a2001b414010380c0041103052605090700c1482c00c2c00700c24214071700c05401100071340c0d0000c2d901004803415520400c0000c0715004441c00828540d94454000415402c0006015400c003400040c004000010481c0c82c00e4002a81031950310a030581d4541c020b029070b01011142c603941e0401c0e180140300d4800c901d8640e64280c4e8085401018200c6544103e1099500150034001c41d641070043e40e0141c5100030007804500942c0b0340140c1c4403414864100c95541d40d500d030340c07168591a030390500004410050300388041182810314880560043e07 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 647578264 1250 647577014 647577023
    0x13060216140a060c0311030703080610031b050a02030d0609020d061d0c0d0209041404020a08030f0f0d090f140d0305011508090c0d031115010b040308090f0913 70
    0x10500000c1c91031410a20350540d4030082c011990151800000b0307a43d15001080490603c00398201d042d198040800160083c1070003581c68100074109207083c487c1c0790750203809480402d401d181801034840010550501c04000c3e628000360713102c41140040b030450054025280009003440c2c0700107500c802c690040c10604c044550100286540c2e00f02e02d09120380342107483e14031481d21200041301a1403080260881d004502c1015141c40c0c80b45001601b00c0785242d05410703001e8070200912056041443c0ca103c082c00e10080298940203440b40c8007202806101c14400300c080e070000380000c1c1050550400e00b560313903100c07010514648892608220010118012403c248590350003903200e10301c00c0c02864122520360f002441000001d031070458407803500800003000d911801c201000c2d6502d940f0000070000780a0b60b141518080300c41007043c01c2c00038140c0840035a0555800600803039201c03004079800c031390707001e0700c40c81d500d0056401140e24072200d07420141e80900d5030000c110f0454580801503086a126 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 647579514 1250 647578264 647578303
    0x7031a071d1e270108010606020f0715090f060c140304081b040e012903120901111615030501140612100509130308100b180301020715140108030309030d0b06130602 72
    0x207620b4201c0c0c0e1a040207000030280e51144bd0200200384c010241d05800343d0032841e0445c000754558448c0403440080d584000005130115241c80c042c03046c00300d44625180c1004000c1c0d40352915105406540300d11180348204800c100e6200d4040360358950313016000300d00700d10000f0300000070031030b880a80c8202401082041c03441d441d00c030601c00745000304070454030444008005003044944d900440305458941e94045c4140b2542034000400c0c184140075100030981e501841c008010003c5000302a104181d20031418040b01c0b0010181c259100c1c016220040031110b0030101301d85d0307203008400c0003018541c485500114031030240460304507400000c4202900a445110068545805990a08401d485001c00401081c000364040103840c0341c4000380c400c80100090300b44000c0344c440062000b260818400229659040b480381548024000c03401404114065402c2d0320b0032013180e036140d220344051160940d548061a20260399404143c0300f02d144d0b05214a43c04589440019542d4245d50274190103c050 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 647580764 1250 647579514 647579519
    0x70f031401020301230d0204050a1e02130306020f04030c06020312161e050705030d0e06010510080601051b0a1b1a07120207031a071d1e2701080106 65
    0x4050003103d040350400060580d0035901760481001c003c00354103c3e00d91200c01ca40050015a4031401624015010850001740c5041810714070302c101041c0d1502c011107503006009020660310249a24012039400c03540141c2e03070b424482c485446521858000900c041040007006c9002507002024104080800c00d10310340ca511503500c09c801e03a00c00c59403100e000400c92040502801c07102c1c40c56448084032428120f0802d1100d6964500b5900311b80918142c850392201c00c2501c881041020f54018141602c00c0500b40b14484002081603070020036103414017000050400d440071480995020360941507090303a100801c07a14240c05120401500300d0b5400ca400d480208407050b054107030200e1404030400d91407402c0403c0e82c82c0445100b030000a8030a600402d0310000c0400c121407801e1320800090010b00000e46003210010b4500c0c1c80000074458845034102d41019161544513101b000e5041c20092002c111101340d00143c14041840c680c14041c1d0280c20600800910b4142e04034140c5071000002c2c81000e8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 647582014 1250 647580764 647580803
    0x90a0603030822032d020f0705040b03030f0913050c0a180b070201081e09030c251701091506080105131703090c0d08220305060a0b0105070203070f03 66
    0x10000460f628042c40382001e584002801510020300d03100220740482440c5121a00c00c81e10500100030b24000b5030400501c00088107028406c0c900608004c6408000c0d4149a2021039603c0c06a002d8003203600200003040c2c2002d60310303820078200b02c842c450028403a0b40b0300a5800156034008107180f00c0403480b0b0948003401618800105000d0f078060061103810280d851700111a015006006294102c0344c10f070160b000e4400b990311451140c0d030010010744e5140420a0601c1c50310030a00007007803003698007400d0100702c02c8980c4140030071a0440f4442501e070950f102100c0380180345500c0700421700b03520b50303014503c1851181c02400840704000c00800599440d280d0b140001510500f00800c0c00c130704101c131294120880d9000c1d50b0004401000ca80c070704521034000c9000285108010f6a6a590124014a03d46601a903000c07021040c6004413040f180341da59040d40d0307540041d10f0811000d4950386810140d07441407007900c03034850b0010121040343d82c1d00d54117010038500d41d000c2074400c000b01304100d922030b0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 647583264 1250 647582014 647582041
    0x605031b12150c090604050301090807120f0e0402070501140411040f1b0315030c08010203100b18010e0d0204050a20031306050402060702030604051b01030924060302090a06030308 79
    0x1d0b81106050040c40e40c500844074541d60010081542c0401305010100d200c2d01e0074406c0c8151980b003440096a030f00280d0822104900c4051005003c20030351054105451341d02841d8228003102c02d03500540c80c0c041c030740740c0180500300d1250144d030b0b00d0003070310100818080040b0301c4441038082500e081114480744d45802c0296901304107000d880200341602089408d100780d009685010b00a4a44040c00b500c9568903203200045500c200e209079000b0091004030b110105d0800c00404103c40c42520700000400d02c102051030341c001650500203112210407513a15150008a15998010410032842c0361030301c00302c00188000351703000b2906510662600706101b00170382180c0c06003650407041c080c0a030031540d40e40090320300148102e070441800e229920042e01c080190034000d61241d0042d19402000411a0240421040c0c403241010708081445022402412806252018954070343d8542c2c42c940d800100507240650000350009001c408005002c01142e00c03030300c142d0b8840e40d940407203070b147c3c0d00200c400c3c0e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 647584514 1250 647583264 647583283
    0x230409060e100b040207170f04030b180c0d03170c0405040204081f09020112020d0908071416181a06070b0f0a050c09040207050c190501110307030915030605031b12 72
    0x16444407c0c034a200b4451010113000003000d0415040e10386900d07907482d000361110a0350b103a94004601c55548030b280342c044c0a141e20114058078442d446400b55140185541640301100501e5031030a00840c07440c01100301214040c000180080d5542c07591108400c1d661f07031401103500e2502d050304d1f1105c044020240036100b070040c0c050b9102c0020700c000820210081d441031b040d91002c1c9540b070000b440020000005801c040b8081c8000d40307101e10301803601d03030305102031000aa0004e1800080c1030090500d02e8030072210b240b80903100081c40803451840013031b61008203501d1550122001c19008100022440c145109158092200100d03849800a1406841d01503034074013101c92061002c94914103141c4d016141c440e01031402c0307400102408c0b020490902c40c090700c84860f10400001482956008900c000400b201140214500413041d20010440740c01805013170290480301d0100d10216200382c001c0c0c2e024203070040560307041d40301c030000040510a040d40803a000740001000310030720f000041040b503030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 647585764 1250 647584514 647584523
    0x70905060906220c2f1e0c13091202060903090114070b04061a010c1a0c0c120d061202010e090a090c080c011404230409060e100b040207 60
    0x1041d803121810068075204920300d82d0041d50310340708007000760f540da402095880090754840108010507644018074490141804107500d0500035840c0038040030000304408030840341603071000d0340703211a07041608102c4c01405860348811070700c0001c0d40d060708a901c03c0001d00d11552000e0030f0020003107400d80e02d40701c049075030300965001405036204650103038a2401d10300740c4c40c080da989443e5060f9a4040c1c02081584d0540e540f0307540300480000a01e480451155003402400e1401c04081250b031511904403020600b68003161300a80815243c603012410307070300394090f0107080d2000a45c200c00341807000d4000c80403074015075090043c00110748440079402d036040c2e90183d451210481c5400c0c01c2c00704c0c1c104042d14900e0410307940e40e5a8001720f10380c04028405002080050300440807000c000621541041c40c4d0014056000c0100308a141c00d004151918003a00351030aa00d0010003200280040011500107480c003400c01c0020350f99072502049040c1c007980c1c51141003100311318071410f100890003440c50040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 647587014 1250 647585764 647585779
    0x105061c0302030a0c03210c020d1d06090f0d08090a4b0b04090c0509030d030509030708070b0f011e060c06110a050d11120f0601021c1107090506 64
    0x10f138403d11030440c1180c042d00078202080306001d5a00004020101644184520780e522a0122061135051100122440c1c4915020a50803a008056010781058a104a208010001d851502034940c01c44009003100e00900340d003914100c5082c10501580852202c0d485140640c0011500e0b41d1504c02c195442b41d211440e0520295401001d101100c818008a007850545c04950580c04051001400040c2c0308039000541c9641c508641e05082d01c021040c00e0f003c0c40000d014210080d10001035801e0751443c40e140202e03807602e68184190442c81101130107800d10718005084000d00541c0d000141c001c078190040d04101d60390b10b1800c0c90301c8510703e80950442041c0340c2c2d81002a00e100f6000080c44a0003240b0001380d4003400c106541c100d5111840120110700c02054121b4070305010301c103204441c1c032620030316850050f200071501c014807002000075102120380d0000c01c20316482000f088006407071b00382c9444000300c40c80380b01803d0074510300081036240c89081c80118030305100d4018240070761005003001c03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 647588264 1250 647587014 647587027
    0xf010305060108071a070c0812040905010e0103030219030c151a041b0e030c09010e010806090304051323040b09240c0f130b03010504061401020a0303050c09030f0105061c030203 78
    0x124120350080d04251f0f0f4010f01030001060129051221047c00c00c0d46560442e139440c80e1030b11000030744405a0200304070078180d0004001185c1c01049450103554040d4404814541510381900c1103040d40001a0a440202800c42c0014036264014194441d803250020301c2e0915410820080c0c880e0380544001d04407049030f0303981401d8019001e0303450ba008018103441d203000001c004150018000d9010b4405034841c4001000001d0b0180700180c0c210b181000918a004d0505c00490710102d1803400070500ca9a0700c3c800302c0b4138100041241d00340200740030211006810103040c0b00c00191400e46900c659030041382d00d42c40031110f58424219008048003005030081e07950803501003840c1c11103148004514410454000c00f0304552140e071000d030404c0089251254140014070044810700c0d00320f44401800c40001c0c4006a0f0005011948140e041c40c000c103041d900d031081060540a0007004941602c02c0c001090f00b4100190045d82c811607051b00c86081c807000710760700c0440c2051607500190150b0010000c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 647589514 1250 647588264 647588309
    0x60a12470f0f12010501050f010c081e040b0c0a03020123042003030a0305330d06060b070309090e1606030203040c120302060a14070e0d0512030f01030506010807 71
    0x1070100015005102800840d580c50100c0c6400b48555a807410b141d40d950010700075854041560340d0090003c2ca0003a8008056940325409407284051030300e4900144a040210885008116009003444840050300c5451171041030341d49481c1e01d0000c034095403d02d52450344412808101d5145145045d8900c40d0316201c03501d416144419810350340074642d006500390003203920200000c1149000e00d560005145c0381c4850304400120a1904501c024000801074640040100300c000e10032180031038017107064010398a0540d00800040c2d201c95404013000c00c00409150300480c0007000c60301281001d03c00711140702794454442890603903502c64440d081c50280450351196010f55480340c0f04403035060019454060741007041080f003070300f10010b030301400400076010480c0c00750388807424032400300020a044c44030000d003020002524a50190400e4032001040c00020403202c90101d00401802e95a0309103540103914000003408183d405100d0306000141011002600b08215041e00c10b4811090349907005 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 647590764 1250 647589514 647589529
    0x1b030b060d0e071706090d030c08220507090b04050a060f1208130f05041404110d0503070804060207150503040b040602090f03060916060e030309060a1247 68
    0x8405240d220300782c00482d84d00960038030506031405140090000d4940a10014544800100070f80101070802c4043c0d095aa04600c105811440c0c2c0c101086003000c550190b4440446400800b404a10454200241c901e11541c091418882c00780c0d800e000070b503030b1040141705996180c0f0401c001503030051000c001d120031654803160281d100301c0300d0f2881c02e0040042c8045503440c5400c43c86003410100e00400151a10384102d1005c3d1552503503d86103880d00b40c860f103820140c4215194010001c2180090800c84d0500c2260403041e13100c0103c076107450320340c50001c2d600c04031801402c880c3c2d0b030308068034000d0070300540070346c0c0c46580c0c00312607040c8540d1141d41d100c0c00781d0080020365402041301440c041c000e550900c041403080d140f00d0000c100c01c0c0c44000b00030351840c08990080c0103100045003020344603280441210601981605e52070f94840500d03900b00c440c0600b9030780341821685006c80d0030b41d203126420760356404540564561921a15203200520600c130841c0d022040459049001d1034490903d00b0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 647592014 1250 647590764 647590781
    0x1308030711010c0302040f0e0f27100b01080609221e0302010902091302030304031b23040f2a0513090204050a1d070e221b030b060d 58
    0x10307001c4103251140300c101e8295489080c0d01e0f004a5000316017403054400290440d0003c5c030001100d04140e0400c11010400b0f804083c1c0840d0000605401c81500450841455080c40c00101c007207c0c52103003014000c2e8001d12845160a00041e9108040780091030200503140c09803d10b40d007040c8482c0404541e5803198007600038110340300041c0f00c00c410040403600307141085007070090f00003090388032144c410071907000030090811145401c062607400240c0c50001c1a113094030b40c04148080d05a180c95a2501c5082041c4c0c0190002500000b051600c884030700034600010b5000c5d2418000010060021170a03114440c004a4921254528940d070001c80c22105005104203030419030315001084821a80381203d6802c41c1342600c4d00050f08100d682490b00c01c1c600201520340d481e100028050760020354115001c1c04880411007252001032495403141240f558003605c10b40b40b00911011012030341c001e4030301b42a0300c40c900e4201b0140030140d10f0286c010500002c100400c0a8030f006c02c4c00c00b00300300804442 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 647593264 1250 647592014 647592017
    0x618020a050d150905071d0a060512192a090302090403050706060b0c0a020307092018030303040b06040513112202071a011a0405130f110c010605060313080307 70
    0x80c3c0001c0203000d41c071800307001c0c5c42c8990b148124580d00400302c5c68481409400c160280c0c0000004020485d8094195082e022030403d00091135151051184140803140c01100c070380e14a40700d280519480c1644414030045990551150294100c00043e910f524072840041d4120b407480c030004000074454002014402d02c030301c0d00002d00740d03200d08000b000798000e40c085e4442d65100228203820341c0307020469807000f40300c12071041c00034100c06100140405150406042641c101050120081003102e581603803580024003100d0f22890075041030348007403005440c0780d4040c80c502004a5090820402340144098000d10f649050460320b500f40f000541e040e060226003505945046d0303c83c05202d000a1092502442851684210401103107000c842c0690111010442d4030042d48030b502e418009460403900119031540401c0025105800900080c0c04802c120900d8040803120b590002c201400d10400b510008200b543e840f281400824403007510400c03407a1203040d00410006180000455201026 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 647594514 1250 647593264 647593301
    0x40f0b060d050708070521071a0f0d02030a0e0303090705090a090c1e0b040f050d030e28060c02030622020a030f051009030c0f020a17010618020a050d 66
    0x50b03448241c1003949540150030309400540040109150200d0301e6059509080324082882181107402035803140325110315440540010488400002c5074025142080d25158501d81d0760400401048002d503c121080c0c4d841c40c0c1b51502440c0340304000419203114101540051000d41e08000411546943c018210748a564688140707000058400640100910246030602300c00501c01e8a404400000307508501c500c030700280420050383c0514080d01d42101c00a9403131444080d07641c28104d40340b01440c400680c21400080c00c0c0c10708044408800081120400c640380d24807a1120002c03103070761984500c041c1d419841030300883e8802100f00661182010001c2e1051103030030380c0f0750120b0610701d001d40c0305485170340b130810102c1c05004041c001910110002d5104205480c1c1c1c6950103094508450005403081c0010854101152142c8401c50003030401d24602000b104110500580a84142c0c007035010b8442a00010328581125402a910780f01e400781c80f000e0624808a1003180100001178400300308940c0c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 647595764 1250 647594514 647594539
    0x80111160605060627150307021b01021507051b0111040605090a090921181e05041107061506081807030f0303050402040b0a0f060f030f1409060f040f0b06 68
    0x606034808030001d01702052101d0694400e00c20080310522805c03024400110030010807004690103e000340185042850520b900e40042d40103c5c80e000074a030040203c048210144006950040041c1a5640a10383c54402c00da0034488a5803e80c7d0391031583d01c030741c076100b40b0003400340a02580180001d5080948015030b499039581c00e40060711002c24050382e40380078410f48058036142c00441d00561000c0c03801c08a0003100c03040038841c0c0048241c400c40f88200c0c82c031116040000500003100e8000c001c011f02c10705c85c903035191201c04255846050200e40961034041e212101490781050001110b651f9141e07001140d4502c0b0006654420054084400740156003021000402c0c104201d11018000c1d900080c5515062060008a238021458244120800d000400900710501016400da560914000704512003841c42a07001d091405900c003126401c0103803401107846c4030610944618500e0044610548583e14881a0030205503806440d4110080130400820385501089401c610040c0181c01d01c3c62 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 647597014 1250 647595764 647595787
    0x1005100f0206180a150606090f1a0705030912030a092103030c09030618020f09040506070f020f070b070318061d280e0a0212040b0601110303100801111606050606 71
    0x2002c061805c43c4a9451034140140ca40c040400c1d005407080c42440340c5070701d0820040418420100120080100c000284d078000c0020600c15285c10600103485001039601c0550115107a8110505980002e4404c52001421242d000e01d0040440b848209840b2548c1e1951800c4001d054800c14420501c10085000070000c0d505100e40105080300c100444813244607881000f40c02d20685003074912620101040c4808500045841c2d5001202400d00724a0a8440c55090b030400d0b1002c0d01d0108240103c110000c1d101d4102001420304610a5459218400c103040a48009080714000c0d80001000038500348121100100b185503075440007403002c1603000700c0e081c81030015881040c031000041e085002c00c020281c050000c040e00141920019400d0028021040c010004c0081c0090312a800040220300542d0003460924852201c6074140c4e40c1d6490035528900051401d032069090540c47c25202c40c4103400340106480c0e501000c1e5803504642c8549407030b080040c06c400340500c0e52003801000380c5900075 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 647598264 1250 647597014 647597033
    0x170c0c10090201090603060501081314070303051201050904050a080a030609020301080c1806060f03040c030210050a0f0207030c0b090a0f0602071d150907020c0303031005100f0206180a 81
    0x108060004a080407080c4001052001142d024800b4036003055001d0115a07008400d80754402401e0007500c40b208254100300c10456454040c1641900034882d02105159110008001052170780d0594521079a8a10921890b40c13021a03010b890303900110300040020302910020f140d591403915004c20099101e108030400c03640280e010700c42e20380c031503111b004260034082032000358211034030240e05e0186048404140e66204505207241070b0800000000d040020110098000e50f8000d040345401204000c005040c692000d004680801c203d103009038842c030701c006880000da941c010104900340b131500c41500025001003004030790210500c200822280780c080005801807030700d43d0083c0340c210302d400780484000380401d403c00054501e0a0410244080c1c219062000310419a4128000d40d034070700f4202d00744200703d02122b502d40400002e04c0744d4208040d4071a4159007080b2503a200710345070040c01340c41682400315a940540c1003000000c081805c500715102c60b4800f02415100b140809a40d03000a4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 647599514 1250 647598264 647598283
    0x80c0c04060f06020f0c0310090201230c070e06010e09060f0909010c0e06071e050a140607030b03030304120f0207030203070e011e1d0c0706020d0e01051501170c0c 72
    0x60141d02c0e204100b1158100804a480949440503004c1d903c124000b19458140845d02024a01e40f103d440c00b0440e4421b184c020268003c551880c544554200480721a03580458048021880b48180105103011600150b278010803050310b4081e00440490140300545c0070041459a10504418201c0100c0d00c5445501d8819048032000090918114501500028007074543c04d015160500210000070200020f044224942e0160303442800103d00d060391924624a10041000b000600914040a400140c0700d0041c480e42e2000c2c4204852182071542e00d0208560140091400c40ca0703203080540950a15100b410b018410b99000c83c2d00c0741c010900d00503166106130904121000100600c0100450a481820a041d1005074142c44c110380710a02104540640000c01521408640510011401c0b00c240c0c035413004c025500c030b21030148003a00030100c21b0344440040d420310000490452070a04500c040301016160b050080c12510a4200c4825000f000a629030b0303030801c00b000700300008124180301d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 647600764 1250 647599514 647599529
    0x108150a0f0e0a0302010606021b0405150d0503040317030403120902063001060503191a040e160611100b04020c1603050d0819020a270e06030c010804080c0c0406 71
    0x10742403044c540282140d0040d488441150060f41c0048194405c0c120301a0410004035000f040b036031528981c0c88140c50302602e0482e404181d0100c042c0070020003001078070481e801aa11280030f0048440041003902c412940240041c40d1160030048400306030303002e01c202e0b0f4009031880c0d05203000010314014040c1004c00841d19100b009505042000706440745c0760250000b842c2080c00c42c24032131440c004044425a411500c3c980702c225000d084000c0d80074456071000700038420300c1031350541c4003c01c0d1211200c00c01d60210011024011074054090800b100362030107108010aa8204403058040c000c2100003861035010350200501680404100000039500000c016170041541c5103103049440c20303504c440c0302000c0c07250410070890440402c01e146140f241e5106000b607a100c0d004081120100b008040e203c252103294400c00346009d21500341002688c0703601585000c2c61300c03480c040545d280e4008004500042c0c0a0300000c00041222016080b111125012203800e4058030000600307582d4560850390 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 647602014 1250 647600764 647600773
    0xa06020a063c060506210105041b120e0607031a03060408090f04020f0c070e0a1109100c05060103050304050a1e052202120f0703021611060714030d0b0105030108150a0f0e 75
    0x3508041c074030006c540101402c4808200d1980380381414001d4085510400b0288941c140d4107550071034a540020160340c0320742003079495501d09294050014010300c1d404049842e201c01c060340381030800181090260740c1210066040151280c10408a45071105107160420b130280403003002500080058945c500044001d41441407d2820040003940010400c0044a050442c0003c2c028803690031190741e80340c20ba40c3d6680030880381c2400d80d044180c40100600501c00ca42c000410302101102600c00c0d120212903000b21103a403100f0344012030b1400c0c034003a810a6000d2100700681c0c81c221203685001402d24500c03440b0300040300d0128040381c020004100d01c1060f11400c000c08503403200b401c07550091080c2070440c1040b681e4080c070340946d44c0c2c050300201950502c92101c0003075995401510200c0c3e0b8090040003040445c00141c6413250802901039152506100b203044d010f600490641e03068500c41c0009080c0c41d001098140400b400181030040d100e0f541c0c2c41e03400040b0030f45c2c1c098840a0341240c002030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 647603264 1250 647602014 647602057
    0xc140301030c17030f04120c030807060b0906061309050702010e070303020f0c1e0f04020c01020c0705090c04060f0309060213061706060a022a0a06020a063c060506 72
    0x1a002480c0899009120313400800c240c486003150442982c06450101004100484403450b1034680c01c681038202400a40000c41c21600300030883e0411136080c3c1c81a5041c07503494461000b8840a80a902d000ea0004401850181700200d2158000c2e0390103030142c80081218021141007030704010b1560000c0d03005811103000503040784000c010600e4a00001d560100000920500c1a03103408815001203110f5002e5401c11840e966981d0140e07403001d404040219600d90782e40403030307564482c618418240100d68450018104482e0003082c0c80071a41a61034442c102544d100c82280200300d0410100c032510b60030700140d0b4060559044450140255465040c102000c500001119080040580380320702e80811007811000e81c0450400521144600ea40d44000f00c5076800552011141001c5608403544500c0028410b81c00142e1191140c0501030402c1402130300310001c04030011510100b045020f11101410102c9030683d00039a40520700140040c41c143c80314002010b5500605112070003a03042042c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 647604514 1250 647603264 647603279
    0x19050a091e1101180902070303090b0c04030507090b0303071403040f090f0506030d0909180b071715010206160c170a02011a240d06060302120f1003060c140301030c 72
    0x2110309201c2c0c242400801c01d0814902540d07660b800740103400300d07940c01092610070540203801c00d008284d0b2280c0300060b645008132070000107412600c8262218810104001400c10700c91044075140040034018500d041020784805400540c1010309031030520003003100003003250034940c0034005400a407401040560f14455408241c41004d001c00c0d1094001c06800130a050b040801d101c00c03a0100400450150303043c1010b044002c8910300090109695241002811a4401d1442c055220300c159090481c1e180c041c10304004010611119000d80e11840101d00c8203000c1341c1e18255020042d103494540704800380c1c1c46505480458069403c00c43c80030032418080c03034082c0110050345000c0456081c644100100081241862112035140c615501d0902c460000c0380e071044a10305001e6500501c9400c0d43d13444010002d511840c40000d410581c071000c180c000c14120951400f405401800f01140da081d52280d41c014034100c21001e00388081070400011601d10140039500950140403804049480e0000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 647605764 1250 647604514 647604533
    0x206040e0a06061e1d0301020412060606180b12220606051c031d010504030f0b0103200607030f09090606050c12090d0f1e081306050319050a091e 64
    0x3130003950340707210510145090340302070080ca60303404603000c00c500405884042402442241c2106984600d5112404140801900f000d0101c80d1039070f442c810010141440b05000c6405400b580180090801c1004410928050700710b401541894010300400c0030903880031a0503d07050802c80300f80761114400c101ca031a0048008004103c0e0007081c054804441c1c0c2d00401028252406002c580c540c021842c010307910a07403d4034095540401490300c80c601e541000700d40c024003440211920720040180074564030701501442154032014140500709020f03554162900c1c2401100902007104003000010500614052100100f130607451b4903980f000303070120321802c010600001c600003100c100700c00c0c0708a0300d803180400400780e040082c0e0004201c440c0b604a019072040c0d13108500c0203040e0f50200c0e0a0054100042c11020081412030050aa0300c0b503094510b4001100e002c1e804412241c448084003229800c1503511030000d100004041c00300750390704c08640c10310121000704a12800c2920040001405 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 647607014 1250 647605764 647605787
    0x15060d0e100213170a0209010602060a1a01080112020121060e0906070c02060732010e0a0b010512010e07140108010801060b040501050d0b0a08010b0a050a0b03060d0206040e0a0606 79
    0x11030551a24400840030800f45a0902c9204110750880481c81c014510500c40a0b50641e80100010801e5035074450007540c035001602d00c250800c0ca0304c08200c200d4000e0385240910548181c503502c829a28100c0301b030140007131040c0180e0500140e0004200000d9035542d0880c40042010170014400342880070a0b40402c81c010541d02e002c0c4d101d078062100d00c3d50032401c0b0b040649e50448405540c0c4110380340c4105035803100104a070b0240d41100f8080040c82e003108042c6c3d5082d0120008100f4000f060400365078441d007440c400b51408007014014000c40c10240f5050000c2444040040782190130350505915101d4142d010610046204a14002c1c40d0f0f482a400c40c0188200c000130300c85181001c4d403221040c0702e640718050510a001540140c0d501442c1c01c0150700c3c00006083c0d5888a80d40c03c81c0038081c04140f559903100d51565400410140b0f804107142c015104004846400c50743c0c0e10040c071550503289041030342c0c0620280000511f1110200c00640708280e9410041070381232500c3c0000d0100c10200 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 647608264 1250 647607014 647607043
    0xa0219080c070e0c190513090b1f17180303100f0806010b0d0b12060f06011101020406050714010e060c070b07030506030c2e02061906050a03080315060d0e 68
    0x105024210b0034200aa42e1120102007841003000c410b20011b5602c1d00c54181400540700e0140d000040d0314815601c252000d40c0181c0d0107100610802c00c0e05680c1540c001c1404011648100203650340d0300a14070b150354000c13001c4caa400d03c0c5008084007d45150000c0301c1c440301107040500c05110002c1c0c0d014509004080c41d80043c000d40d41003401100840c000d81a4640d42c081d41c41c4a802099070f59405a031002c0b81080d407d642060504448121200c0000c6170007601050160703034120043c082c1403003203a049136a50340e1451b040414940e510001e01c54200c030310f0034040d0342341d1000e80280310043c0030180c040c21719481815030740d0481e0b01d0140c0d03072800020704c038909141c0380c0002c111160f02c0c08283d03042d103001c0c2102c030791017045290510601d40c40195601010301610142c240d15000d6000180a40a01440500c0c040402c210b10b40740010303554940181508400030b00020400921041c01568020704494417510020001c2000f2814903044552441c60740c070380b6004007081c0514107101904158084 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 647609514 1250 647608264 647608289
    0xd020706020d08070c0b0702060f07050901020d0509040912090303030b061804050a110a1d0d0305040b071104050a02040510031a0d031704030206071701030c0b0a0219080c07 76
    0x380301000c0e4980001c0403061081c40050000102c25500c2200050000342c0d0001082000d8100baa00c025581c01046403030510010007840403901041c01802540e10015050f8002c20074038000400840710354100300c031059001070300d03414210000364402e00f80c01082c00413561040f02992450600800303882d0070350322203030107a4010000d800707035400001800c2c01d2031b0710151008906510b030843d9902c010000920b03280b928400208244d01041d6100701d82c50746411b40e5400c0003041c101d0f0103003048a0003200c1040200441d80c00c004c1002003e4400010700981d50280591240400c0c00c2d4001c00c040e030320201d4203a00e8150313000405000a2400c0808245061524902045105481100002120750425225100d001800c14480405203d0784440e0716a010444d56041181001c0c43c3c003a41d03a0505903840ca0101e160000040011918585403d040302c2d0030800314145a0315048115034181e004042000850046403035003001c7e180c10a64500d0124450080b40707075150400b1117a581040c0043d0801c08582c001c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 647610764 1250 647609514 647609519
    0x9120301030b0a05150306092109101b0b100e01060f1d12250b1602040507031404030903052505090901090c0b0a0e090c070605060a05040608030c0d0207 67
    0x4045164582c003c07800d0782d00080c1038441c0740c1143d003002c08041480d42d052080108000203c9004110760444680c101d1a1011110358205905014000c500406822a4a800d0942002c0340301d10b01f04070003680342c0180c100c03410301c00351142c4109184c1140c4a03c2c600c01100c0040065000d47c0c99260f005059a00d0310f8500f07254102d200034801d0b2210040010381d04103444540344107661718044000900301040071100e00425420164410901c954005041c400c001400064103000100403030b00c0d2460344101020200d41c442d0f00308001084090003400401d583c035a0141d02c07000e002c0d0440d500460194130b81000e03140ca0351411518003060307500d08d146800310100002d404d0190f04a00301054800440b650680b42d6180a24230340180100000607001d0b150340d01000500c8282c0c8001000020107c3e500c8a6010040c03c0601c035900c602a640710f10120f804000020218409034007464200301c00600c2158001d58500000e42a10025004081c5540001551200d0000100030300081c141031800070705102407 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 647612014 1250 647610764 647610773
    0x907050c0613033b03060f011e0f2303010b030c01030f11071202010e0a0b040f031716081509010611120d0e060703060b03070c06020c06070201050912030103 69
    0x20700034000c03001645081c0d0b40e003010180521080440041100c40540191078442910100d40f4040704a510030076a40d0404a04141401b1903400e10030300003400c4443e9107900c0c10400c0260301f81c0c2d80724203aa01091419011030051083c41c0130600500c0803041a410302c6141ca848100070090701c4901d184aa8900044071807940c034042545601c3c042c09090008004043c12010405130030141c40380c10701c01a00259080822101c0758405180c5801540200030382080d2030344456030340103c80005044689084c2c002400691081100742d0701c24428a0100305040081d44440300201d02541d45468143c40c0040d880d81c1294000002a445426840140311400c06000402c04803070042c0100c03010860021500b44130058104404005014601c40d89551000c0403004940200b00c2c00511841c240108008510080c0c0b2a0080c24250340240034014915121104103a400b079040310782c11955103801740000401c0340b0041c00030b40d210329a01c1d00042984e01c4d04030421400d00b99451400c00d0f0200c2c01340014001308 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 647613264 1250 647612014 647612023
    0x1507080105040b040902131a0409030f020f0105070207030f050f0d03050a0c0c020d082101060503151e040e0a060f0204080c01080705040e04032010060512190318140907050c 76
    0x888184000188480049a04503042060040c80c075041400e1000310f0ac2015484031a11100341300e10b40c2501da004441d99242da090380d07000e03210840180d100c41001c0c0082070390400100040c2e40f04500b1140b603040680002814500315070400b6001c2941c1d03004211508106001e001700001803407400940442c007503400035010300310f00d030406800004045165150f507032100d41640900e1200712000740d015a5164001483c0b84d00031140010211881e011004d4181486200c150074010803c09980c90b807140d0000f0b000c02003100f650700d10780d644583c4046002203661407142444500c40c00d280980e40314140b0000350f207001008801103040040c2c48080102443e801016036045d50510905014940c03038600701100d882d08240e012044119040d00b00000083c0d0000301690949151641804135581d180c040203003c54081440c4016900a803810921200201c500d54105c94401d007010314042c818840c2d01c840140c030a030007903066100301c1840c00784645048181d82ea4824460b1600d0392400300c4116041b6200d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 647614514 1250 647613264 647613289
    0x507020105181507050102131202090402010f0e120a020414060904120e10080601140f0406140d02161109010302060f0a0e063015060c1507080105040b040902 69
    0x3100d40b45403207003a50b40341d0601c42c0d0b802c10320700803580e291007031410028002e41c011491190304907007151000480501c5003019001c9242c0007844000c65945d035800640c3c0c140d001c4d0880e0b504000440381020010f5855610700202c20102c80c00410b01d13810f00344180700480c0c1c801600703104e040703002c003007040b409a0301c11242d83d50103948040c0d5071300000445481911411542c21a11f94040080822000070701d03230040e0300d14802c0c4004d9a0b0444203a0307400503079240f90303c80e600000346851010807040c407020303001d9049251030608000c2e40034036025240a640e41281c0083c9440c0203104130307038001c0c4024330144041000041004866081c3c3c994555400a06984203281d0785440c2c0c40e401090089905000e514045e41128003d004035560b88003130700f01c06075102d40083c5882101034260f003210843c1401d034404244201c512522418098032007000700316281e00501c0420001d8403900e80704003400b02810500900640d96525001c1c0707154149010441525401c80400b0300072450008480056941e50498211 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 647615764 1250 647614514 647614537
    0xf0e061003020306190f081506030a08070f12050c01050f0903030c181c0b09030c1005150d060203011d04020901050d15090b0f090319032f07030e09040f1118160f0507020105 76
    0x2950049031505000ee48402600640b00d42e04102d22401030580090043c10903400e1280200400d6a61078201801c408080e030b220200742d40140300103401d40340b284c0e005180007030103000444440010040016030401c81d244544c07d0700001c0161480802c03e10f240700c1030f00140c0ca980038508028000c004a030b906d075a4000c14465072034494001c1248004841030401c44040042d00b0340f05010040c0c148180a0b500078410002100c400c00384003603c031031003450081d002e02d900410740880c9910380010080c006d004104240c9083e43d15841d00c500c003400314460820075611619104074103141030000e15003403540042c00c6090b1034000308039030041004c0001c1002075000060034006080041e0300e2a44003008110304954000e5020501402d00701d01e0900050b00100c0c0c82540c6014101c0404c8040c0200c125041e01c0062100030014100c5c0002081300401e060b0b0804042d100702d691441e00100c0042c01c001c280c50100b0201000301c1c0403081d49511400e2904e00c041030f42440d07882e00050307074002005c1d4400c0280805 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 647617014 1250 647615764 647615767
    0x1918110d030509060c0a110a0b0906030c09060a03200a020a03030e07080a060506040b06040803040b340507050a081f0f02070308010f0e061003020306190f081506030a08 74
    0x304060042e41502c49284000e06466242d076030f1000c65564850500318141d480031110b06c0b080070783e480c00301080303000d5500c6c0c410400e062000b90f0091004c0c03504042d0403a440400c05024072411511400301800c031100003503a02049010b40914107042ca0310400b0000c542d0080c040044490075a000a50146059410301d000554a405c2e240c0700d80c07c20075030790010705050044d500281d05111441c0c01c450302850044908005003940d41d001c11125100c3d520804201c2d400a1000b00404988030028040c1601000400030008445009005a204451005a440601d45150f5009220040201402a003000d5441464403810300b07100582d034051a070044c01c629101c403040594480d0140e0081c0c507281444220542d26000303070b0300c0c0140401409014041c001c80b126600041c1c46040b29004070f019030340c040c014a03000d040d03c8500300d000c2d40c002090250485017004002c07010348003070020407000b00950098041c405040c20300150803c080c0b056101c44410040d000d2001c00d540100c2c5004080c0d07840303c07405 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 647618264 1250 647617014 647617039
    0x10203160f020f0f0706140301050a0501230f030103050606031204120c03060501061e030b090a0b0105071a1506030f150a031509140105040c170312191811 68
    0x8a1602c01400c00001003030140341103103d01c4c000001a20300540703856803074a481d1384909007100e0b06c070b40c0024400c20364480444d0310704211550042d4107030302c1d00d4841100c0c4400503071891051007245500c1214803c0500000000420501905125058104200300c001e040d1503141c1720016907a60091b401b60418807a181d401c4401003009071402c8500a5a02070070910041d0785d6584050301e04100744000d601c0c0041d101c100c0103581031082c8101035022000508002c80d6464203a150001401184c2403141402010450840030076101003000c21580c0d030303448d03080c101407920801c20300c181c824400120380200000d00c04c2c8004e0392080c5802c40c0c1d1011712045501d000f2034003840040c01c10031440d817000d0443d5012a43c84401175845410945541d0b0103010340341d03038605040b0040381c201c80003150050255071a41360240408080320110000d6110940700b120304003032004c1e92000182c0c0c0240c132522035201403000c1d000c05c01d0000740500d1410181a040c015440e14054480d052078030313400601036105840c1d51408 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 647619514 1250 647618264 647618267
    0xb150d110123040311090c0307120902030319030c1b0b130f060b0a0b0708030f07090807060e120706080f0a0f14040b0a0e1207060e06040f0c08010203160f 68
    0x41c0300511000e84007102ca044101022034540c1d802400f0560310340b05600140001410540701e028002d050149031103280d990b817101d08031a0310a414141e9450292501d54031000b503a01000540b494258100d1a001c1c520b101d080302804540743d41c25a40c1c10f00c86076030144409415000c0c501c100e440d8114680308815554603103040d1307400c4a0304070700400002440460710148295648401e1254900782c07484004580c4a0b103040c0c00500400100404081d8204001aa400203002869130001a981048030080e6101c0740e80b1414002d85801c980005400c0e00d801c88410302c0c00031311074171a505517200604191803c10030000c1c84482c0080a00c0140403079180440c0030812658008450f44407404000c005140c0c120300c0190103440d060344d01b074480c00e50110215850039020312a10b181e800c0c4410050454071040c001c608402d030040383c000e50b09607503201c50181c081c590600a05109501c50000794000140c10700e82400c40c844d283d0050700b050f070310500030042c404956104481840003541007030404100c00d59030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 647620764 1250 647619514 647619527
    0x1f060e0405100906030503192d120e0d2d05160507060c020102160e1b130b0a17190902030102090406091b140d0231030b150d1101 57
    0x3403003083d884c0500000900401201911000080b00400d061010368210110b6094210718000d805000e6040350f038a6901e000d1a0903003154a540381082180d004d0f1280202084604118244505030000c40d40029400c0c0c0c031840c0306482034034a41c1c0038080c0c02c100300d80403480103044240744018005c0c002043c1c10b82c02e8514035815081d55218044070390040c0c071080010404042c10f14202d000d84585030b00450840f1002e0103100641d580c41600b004103540d0322050180e800c0c1800c40803445204200b1410b0001e140c408c0c0c03076030081c100354192181e1398580c85100030401448000140048a03801c2c0c10301200220000c0e150080c56140c060100d02500c0c3d0b8000a0b0080c416102d80c60f91142c030b0824001602125500802c400c061001300a02c10400004c0e011785884200e081122104841001140155a40759002c3e0a1003104641001c0f00b0f4103500340c01030001c0f0695841007004040000c03040080084545005906c64140c44144401105120100740c1101982400400d245400088036183e640b0404 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 647622014 1250 647620764 647620769
    0x60c060714040b16060b041e0f0e060a14070938070c060905030a1a0a151d07051c0b0312040311120f120706150e1f060e040510 56
    0x43d10a03030740c0d800268128094080b44c6000702c07080ca041140501d030a1070544950740c0f013079035208070103104401c0104d47c0700d0090408120080c10140e54266011040b5420060070340701d04901480020441c0c2064851414490028014001c201c003500c1c09200d902c2287c400c135208107965064105040c0d10b40d080070720828500d01d0021965103c04946c1c0c1d000d0003c880d880d03904588645d00d413070082d5504c80091648640c402d41015196031040565103011480f800386c040e602a401120000e01d030f400c9244514040340080c2d0154a00d842091030032047c04070324110803900004c5505050380f0342000b007105021b245122590040d010b0b543c401c0c2d0500c258078240070300307003001d40c402e280c1c143d4468507407030710340d05580060309640d000c1c00300c0c1c0803142c1d620b400009010841607003080007030501c24034815000320f07d41d02040086500c1b9444640010480c600800c0c01006041e0f2591241035510301b2a0080410034440201081c4482000c5030420001c2d4003c0d5800d046880151400705c0c00380d95240603407a070105260b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 647623264 1250 647622014 647622029
    0x504170c1306050607150908040803190e0f06090d060f0c120b0604120f0c0311030607020703111e10050703022a04090302010e01090302030a030b060c06071404 70
    0x44252142604020442590380481111250454046070034840c040340c03030500905401c1001048400d010446285101424010b01c4c0d0300812245c0da1940c841007aa0455484805258000f044101c0384000d449141c911141c5e1034540881c40d135a00c500040e1011210240d400e000b5135000849180715219051030249251700f2140520001c6540b200318801482180d82c11000156882c2c108004010180070340c0202000040006e81441c0c208044a542561100e000322421785245002c00005400400f80000450013121200d810038401e80a040c00c04100400c2c200071904280c00038800544180001c59150350309a40d1040403010070000c601a08070350700000b40e8421846805000e500754070000418140e840390b801d8404640901085601d503800e03013103010003402c100010030310345401c2c40da02a0160310b000b0320010444502c060301003400c40c0e5202d40254016080011891101c0e90180903881088800381c40452410392030008442e1125005481101002038a9208481d02c20352f0a05550103800301 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 647624514 1250 647623264 647623289
    0xf021005040c1401090b040501030b13061401090b12010b090d140c010908061b28030b030c0d03080c09030c182a070201180b16020a05030a0c060f0504 66
    0x10304001d0705040b140d1190510540404541d0751865214841507000c403540b102c21582864100401580600070f258141a00500000c000c9501f01c181402440020840d00904200d0b61b034130a8001802668a81c10007160007a04001000307540030541e5242c0c0c11151642c2c0240d4a50b010a400224000c0034400060560701880e070b4003018910000c0f03a2051030300c009813140301046682d108181e403264030031603421039601c0c515030001f10303040800401000c1038102c0c0e80741000e4500c541510a40040341d541d61420002e907544890a540342020440101d04100441d1808010390b42ca40d002040361100802c00c1090340c4012a502c0e4550320100a0300080a00003411040811304c4003001012400d0202d43e8000c9a001c0b04040f001190848022100c07005941c2074880c0c03500040d03070019203a5200d0340862024a0b2841407001840c003038844060a042202e40800c601103204034010022860b0440e0030541c400d03048003010340001f03050380d008030040303d805041800380c803c1c040d4010703142c9001d0780c0e210051980c0d0707 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 647625764 1250 647624514 647624521
    0x9060108101d0a0c03140c0309030417030702040f050112080f04052e0309030c022101150504050c1206190b030403200f1b04020405060a03050417090904030f021005 72
    0xc101042c9841003038420410407966152480172800c2d913030340b41c28180d141d4807650045115500c0d035034011030307000741c3c0340c0222480d065440d541030400c40000c400c01e01041d007002c280402103103014050151350a100309803e01ca254100f6103054a40001414000c0c00054001003405501107071000b9a801003070000e0580d105002c00300b5540312850300c04c1e05401c0003030001c6652024160b000b0300c030b04c0144540540d50280003003030079420f0117507400041c03040c4140d00500243c0030180d4242402100d6165009091240a01d0b2401d01800191900584801d504140900000c44080340600042d5440300d811202400001c5503010101000340d0503800030b94403110000100001d050300004071030342d451140c0d007940e850700030f00008042e201c1c1c50105030446c01e904640340c40c20402585c240103500081005000524103981c0d00e00080b00c40e8090744042010a0322003080005124850390030842c44d1000e040c1da54940401c2d84d0004940d00320003071005003840ba00e8403003550001c5c800c01c0713002000c43c0400c50420181c103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 647627014 1250 647625764 647625809
    0x132901050102150c18043b0106080706030c0c212a02010e150a05031009090f060506031e0d09060c4704110d030c2d0308160c020906010810 61
    0xb40d000324444103c2e01c01321f8240018443c1449170100311901080034040070703810701c10203c0103001244050030410032072002c0b400c08540c0400340e20444081020f2402011215043d02811200c0295982d059031006055030000312425800100401da0382440c00c800742c00051400501d0701c1c0c4900840b160801000700382c072510250001d0003140103444541c0c0320301d941d540d54140744042d14441d101c0100b990140d41012000200c243d000b05400903001001c0e1401c1d400c96400001440300307c241100d00551002a203100100e070450aa40c001e00b400e4038212542406c65212118140c207001d084045841030031040040c088100145a118020340b00450250768511503451584001c090ba025260034810740d002c05100c2c80c1c09a4444051945515000c0c150400e5484180c1d2026941c1c0008040c40c03214000702c156903120b00c0844801e540300b9250704465040c999000644020589541014400020709040140e1354002040c0d41c4440246410009655541140c0c50b05540c254001702081e650380e0b60400010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 647628264 1250 647627014 647627081
    0xb010e04030905060a021504020f03010903031a0f100c15020703030906050f191802030a0305130506040308031f080f01020d0b04020f03132901050102150c1804 70
    0x950103695402006510b8904012545c4a0343d00048003507400f24110074600450f0910041d8050300040c400054031140c60080380c00d40b140001e0440000ba0f485c111001c08001c440302d00402130100b41c802d5100120384001103284448400c801c0c00901002002c034000b0050140070001031301d400310074155110040c0f450301078042c100e000b0781100c10b42d05000002c1c803001d0b08031040324070894017100078600c40580445900010100c00000c0038151680c07001c8200540c030b003000700418845c42075807034550b5800c4c00350b05560781100d50b40145101d403100708410800b0843d00760580c0d42060703501c0c4001da5000341868480001c1c04090340601101e01641741402502c05066015110013010882d0138015941c0e660b0400c4201c0c4103c10602c0808441880420913165054144d007000301e2089a02482c2400460040d4540078280c0c1d00c0c85050040030001400385580c180441444449610419140c42c02c1411000c0380502076404502d9000100e40301c4440c80399581e0708140060703104034502001c00700c01c030210500030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 647629514 1250 647628264 647628271
    0x1e0201020f0d02120d02040e1e101805070314010e011d0112061503062408030a020601050f03070b030408030108071d010302190803180f01030c08010b030907030b010e 73
    0x940074001080d108400301048000c0021140d50260608034882c080441c4d040c0c1145032180071450382417001007042d181e0380e1241783c0150f1040c9403150f8460350708a240411840002c02c1d854800b11000d02c1001000240d02002540800c0c5400105140c0d0300e40c441103004211181c0a03406189072800000380500c210310440d4162030141e488048106050202c54800701428411220300000d5000c01c040410b1942c1c0c0054102040407d560442aa42e80c40b41c6098a0b00c108214003a0503003c00150381548103010480020051a0099030a1400d60040a074450f0014810b160007120440a14601950144a4400900411044903449003450f0400c84a280c00901641c2d00314400c101c1e0200c2c404071710140c0d642c0c43c504038804000060f801d5a0034440001000c0018460309070041c54081498501440900303130700c004051825181100302c0d800c2141d0214000c0d40103040c545082100c1a20a5000f0002c5047d81e1008074020b54035100c212449107001890303440907001e1040303800085000260107644030300 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 647630764 1250 647629514 647629517
    0x103051e071e03060e01030b0405120a02010c020c012606040f1503020a0e060604140105070f05030d0b040b060403030c0809120d022b08060a080d02100e060702030906070c031e0201 79
    0x591a9000d8143c2c2120001d01030714400b100316000420000e030220a030698081d00c14030548000c1d10000074120135541116a280300580d46848550400990402000700351040928200f542075104c00c2505400201000128001044540000e481c507182c9802101001d102e1a100b04481d0810200810700d14842e0b0004901c80d881c440c0b000a460044030072928040c2000610641c41d1612f41240240303d64203402541c0d0502a0a10507440070409000c5000074880c00b90003c4c554410043d5000300445030050000c500c1a40340003004040b0b0f49480d015141070f80d5244c140400000e06034106605140580d03000c09500410364005030204200c00f00d80650b090340e4a400b01c030842c0b160003a4000700b150039000041c00d404d4458241e21000381c4201d5050360400e9002c0c0c02e0000c000c2c1c540300518200b12203001502d02580c403000400a0003002403007041406038401e0041d291074100302800035124400c405003180b0440c0045506003d2294907200c00e002540e02003400b5402601c1803110b0034110031210820703030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 647632014 1250 647630764 647630807
    0x141f02090f0306010e07080a1103040b041203050412050906040506030c091c1203090201110a0803060102071715190e2116021003060315151505090103051e07 69
    0x40705040c00901036050758080450305100341d50b15081120501d9000300140c0c0116150b400c101803d42d2407000660103140030350003146040c58941845803d40c025030014208152805040001003140482e0380b103591000c901c6e01998030403107070700001e94901564108940c0590004107200d94042044020045268180e510b2601c3c01503802c400a0b0301e144441020b4494480240182140b030311030741c4100d103220b2050420201068400b40c041e894481424801c40f4010400006d11040c1d60f0108007602c0240305a0000306102c8240c000d0043d1a5602441c02c607005041c0400030850710049111300040010284400300309118540c0304050f52520502c0489107413640c401c0e01d80c071284810400700c5401420000c820340c1e107a200d80d401d0040c150400c41c4500c04047e96070b0408000038141c05100030070b0508007600420782c0c00c2c2105610340c030071040340e002000076142c91030311030840c5410206440c00500c00b400e00140d0b0340d992002801c0451040c00c03070108081080e0040100503508040c8203c07600e4240d501c4407 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 647633264 1250 647632014 647632039
    0x801080a171803240f0c07020f01050408030a080703110406091e03080f03010306110f1c020d0216150c0206280f0906150501120e03040314060a0e0309060304141f0209 73
    0x14200c802c06d84150b001c805082000c1805410410030040710510103140c09071820b66664a400e00355040103080c2d00c0001c8a203410300500700c4d07050251400f0500001601e510b01441c11f840039102006502c20b40703e0310300140c10220505882c42032000c0003150007115165a55002942029265009000894610f8030f40b0b1111003003074483c0400d40710703691030501c1700701d03d40f03c107440f4080080a800c20940a03000d40070007685004090030300160020003011501501d1043e16850185003c5100c00b070440b100c1490310300d42050095002602c250046084440324011900c2440e2038040c880c1042c9900a42a0400051000401c500e60120017080d0150104003c03111704010380c8924000644102400900303d00c2c1403800500c2140e000010748002c21081f2450190340303948a442c1e500089044070200d070459410000c0d51400c80c0600d044901c20400558035002852000810a0002400c040e10240c15100540820030007040003800d54210348902500340d4298000c09406944031064035406810140100d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 647634514 1250 647633264 647633281
    0x30c0e07080a090312090c030c1403120a020303062205070e09070f05040b0f120103081b011404030e0607050f10060f080606010c02031009030f0801080a17180324 71
    0xd151009506a0b04c40e01505c01e502d41e084003501d0000401e580c0e43e0b4204000100080b41d2110240003050620110f0f000051103e04042c140641001e4000e40c00303c04100010840d41d020080320750103c8103c4035003101101041d8081c00d021120011a003a545c9418180045190041800040804229804011750b505c61408039000c045000098011800c07e01080c00307100c82d9500544040d01000120303134100071030300da0f100c644034a00b0303401958082c9000464a1070000307084c000310121442c0c0c81c0203103d01040b41d158130096950040c0080c04003e03000100303d030203580c1c0d1070490700441d801070200e5a4588268540e03030b071035030000e0b1440c00380c00713150140000e81d9256041e082c0c0c0403208244050070b1156110300054901c0d003a02c40040380d1502984d2400300064016202d1000d549002e6038500400329100c0701d01504a101c182c010858683c801c10b4500d001030950020803e0382c80c1031580c0b0b95120068045000081d141a00c002c82d414080d8074010107001400031440125801d00e64082c12164485131760 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 647635764 1250 647634514 647634521
    0xa060518010905070216030c031a0c16061409010501060207080a15020f0715050a1d0c010c2310060b1c020708090a120b3d030c0e07080a 60
    0x34400c4036a00580c004000150980d07000650066040c01070742e1048203407420441c1c68940d680c004032911b0383c0040b0144144020b80d510340c2d90703000c5070400c1d0300074a0a006d0083e2100b800790700c0740300c944151046100e06c1040103039001101400b1a040001ea41c85c1013211425010300401d010f040c00500c180000000c01031307000034401d4540d41e0080344108002e0303c400503a002035400044900c1c03015404109003800201c503000107016100d84040009147c1c101034407288190356101e032414250820540001201c00400700d104c00201c403003402d200740021a585048041080e40710f442d618807200480d292511442d000c18181c1d0b40840c1241c2c1000303125142c103013940e03450045402d080d0024032100242d4000030305690080c040c0038082c08a5605010071200000c03104c045e1038120090403041c201551003040091907080b5044101542e1040d000c013142c0c0065440b80d1512070300c019500003c80b5030030740c3c0304281c445144041d581240c0d0751705280da22491440d00901080d00d40c580087c04000018907603004920 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 647637014 1250 647635764 647635789
    0x9010305010e0132040f021017010602150c0901031409010c0e06130e0712051503010c0f080a0216060e0307020a0e01030330061502070602160e040302030c01020a05030a0605 76
    0x35010307055080340c0104c460301010001e00403101c25a681c512031000d0b0344c0c0c450701001d03100d40c150f0f030700c845640340148940c541a4040e8005000c2d94481803ea1800501d9004401c0d41720180c41c081a0f03c035005100101e0140c058039080b001c0300a940d5060050b50241074004000c40e50b02503c80d4451590a4000e0011520800100c0901d03298001800d100d002c0307007a2622500580c403031410001c1d031032010459404440e010b84a541c02110000b080d55030605082c01807001b01c9080e414410328440102d003003d4481c000c021f2004c1201603000034005408040091202203c5402c1507041004200c2d9131440356032507205d100168490507205070300150f201440138045040c0c0394140c0e2a8640c0c102d08903401d5000c00c0580c910f01c00d46411411607010301da601c0d8810b640041a11105584222010103000b030308100043d04420110740180c00802c0c0c021810800d610125900c500c01c44500307688a060480c20f40c021104486003c1d40001005c0c6409070f0322038051805440641c004002031a600d008000c403495035030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 647638264 1250 647637014 647637071
    0xb0f0f010c02060c160f0b0a0e06310528050d081b06010603061a09100c0804090b030610030f0b04020307260d0e010c080a02010b09010305010e01 64
    0x14155002948500151007405101505460800404040050400940b0380b00345410070034000341081003071a1248030b840200916010795140280056000305441c0c1d101021900510000070454880c070102284030101d012603011541711b200350400c6800540e1824482c207071003402061602454a04244969400480d9605910085a181000707010084000d14003d1303d800d4401d006602c441c48070812070010303464a8001030283c6605103803010302100c0464200c1424014104501c1003401d0070081140c0c4026000c407000031184054020803141c40c200b040004160030000702d40007503082855080481c009004070181c5406079164412079241e0111403002905640340074007980c020802e0300b602e00da0014006810b403408107468484041c0b0850b600300207021030220402040900d10000e01140c0d400341d00502d421078440f862200002c111a10101014208484c0002ccc0030403407038001d6010782d140a20180c0b20241d1907a4030300300349000707000815191806500b00150a605003005c000c0148448d40d08 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 647639514 1250 647638264 647638279
    0x105090d1d01050904020304030333050f0d05030c1c0f1218240f0b01092606010b0a080901050c040b0a02070e0a02270114180a030c090b0f 61
    0x390094001d049008245060110030841d08945849034002184142d0090304c011510210b48124140315106102d0001a81d41d80100e080714414074062080381240c4088603050591408031000400002e105500100188000030300d9030b1a94a0116210350360100b0200c481688014814068602440d0820603a000404500f1868440d074800da010078035000c8641100706a00510f56520302d0020400c1c0c14000c012100305100a004981900580a211494120078040480b8110000e0900605030090104041020040599205000b5403150701d0400d0f2804941071941e5404101d440f0727910500601c1c00080c820400940030043c1401107500804249454519046c90140c0c0400b6640015150b0720860107402d800281090c0c5516409000705a00308005a60381c1c0780105154010680c044100904c0fa41082c0780c803a280c0e040400441c618820708156580c5100560b940000348800e003204a9010791030440100134068400c0c410303030070b031a00c481081100428440c100a0007408420025511200 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 647640764 1250 647639514 647639537
    0x301050105030c0702040c03060513020f03131a191b020a020f0a0801110d14040515040f050d080a0c02190f110d150b04050c1e0d0c110105090d 63
    0x20580040da070080f818000d43c2c0c00d0241c240e001600f41d03030f0301c1102036000907120fa00170310079840c005184c40c0308a041c032002146007000c00c6190301094040145202d520010703001301c00040c80748400d00255004889015403106113495048a000490b480c000e0104c2c5600d407051658480e80700008404001e01190020320241000d6400c001c83c0d0502d07909200d800490150001403151001d001c0d0550b8089440d5429848444040c444400ca42d0036640f58140842c1c18803d01001c5040230031900d0901c000c00824040c15038840c101a840910720400040440c400d120341c2500c4d041c0d1005c0118010f6001d048140034118010004030381c3d4149032101545c80d002401603020000c0c004a602e010a1403103006202c00013241030000420303680c0303034000549005141c01c606000a91417441013440d09d90b0300711001c00039400c0910f00590f09000c0d1101c55000d5031019030401071161018401d440c8a0180038409001c0020f6045009001c2a5055040381c155820300f40441c012610200300380c201c0c407245036a070750071104 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 647642014 1250 647640764 647640767
    0x102120705040e360705040f0603020616051e15010608430207030308060a0f0b032a0c0c0d0f030f11010204060c02030c0f03060a09080f030901061d0c03010501 70
    0x9110a191140c105822040510304a621060511103a2114005d0048940740100303000c00c1d01c404005441c11203141040a00060381c0700350581d403031140b80074040c481c0740c0720b00d152892410303003842481500300d15103030684604140c00040440302403500301e980101d107907a0360800351741501c030586810140080ca45ca091150418150140c5d00404144100d82842d01a402e002d07421013180ea0040c60044c1c112032410f2040c903810620040d009442500c46400390f528004100300c03030000ca130107000310720b01c40000410710240621304039072410150b40c86645843c02e0300420018041c6c0c04181c050001d8019841d074004035203460549030404030f070404010b280a001940c0d040380c10302144c40015041c80a80355000b10b4071002403004e880500340686801b81401907900406150081e0000c0303440c4140112001340314592804506a90030507034440303010807620854940244240201400f0382400180401000b43c0d10078150050030494441000c0040601d0506042c40c0710f030102140c00f01c0d8401420001000f465 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 647643264 1250 647642014 647642041
    0x150311090702190206070b090f06010f0b04030f0809031006150201091e0f05070603291e28060f0206070507030c0804091a0102010506030102040f031205090d050102120705040e 77
    0x261000389900d1400c1c8841e0340e2200c2404041c0c2301c440c06035021904171100c1140800209001d0084112003003400c0385090744907900c9100300e0100030412401009000200080070080e200c425000409803010403481d505640006c05d014440c844055903950300b18035506006200315100d481c0c1110402c240040181d1403090240b04d40c2d88100c40400c032030001c92021413414052940501302c59500440c000040c14000c54003c02d040740300d03420f540c00a0642c0040e554030b0f1541c3c1d400080ca01034400c4650b581d600d000500035011701d030780c92003118001a86000d420030282c0c64101a14490b845190a01103483d0007269912000c076070316000306004001184c0441d020b1201a50194810180716150170388500044098907812840030f4290b18080f90001c48a68082c041c451340481c0c01e900840c20140780c25000142900d4610015000c00482d1100e01c000d00d22500864400410250659a852000e490958001c5d803124850441045034000030902440c0b051701150708070707850410702d80c0c05a150510382c1100d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 647644514 1250 647643264 647643313
    0x201300504050a021507020a050109141219051c020106030c180b060d050730020306040b0a15030f0203040b01060302160c1502060c07120507030210150311090702 71
    0x40e4441c01d01528016035500c00c45400b00d00300c452805e03880b005948140040d16005400ca41c1c1484680b580600a00aa00100c84030700300048135180b01e08018060007a003401c020600b0b105404002403c01410310034002402202007010101100c4000c8200d50100d00f00d407907034040105a81403610307041000000400f80607115060054002800101c0b03480020f8450b0b216400803508070703458500304420150030a10803001d031400030380103501280c8000003280d052000b542e54800340680c04408240b4585595101c1e1810740b4014048980481c1ca940c0d10000a4a4103c03c810003e810a11204404880340c02641d006035804040b0242d030f6420241e00350060742213011504041161b2019890200d4410303041c2030028400c100e54000261003c2c04001d04041c0010845140c0007000c10603c4000380c4000310001c0c400d8443d00d09944c0380c280b80d140c120300f030080703940c0d201d01801d080046013032803803885c2c40c2c40004403442101c001d1900e4202800348022100c044402501580180030740c0000082c1c881d500c0d202 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 647645764 1250 647644514 647644523
    0x30c080102090d02060f0f0301140301051005090a021e040801091e0c180207060609020316081603050c0d09050601061e020d03050a02041a190203040305071a0409020c0a0201300504 79
    0x10001c2481e800040c0b60000d9122b002ca801c900003900d219420280304403600708a91201e50303c071260420700440c900b09000f030036080013194005092803481240c40d150708090440038201c180d6032030307407011801e02a0100d50010b9400e14200e9040c480c0c02c088000d14091110381c080094001c03286000d401042c00c1c09004d80e000c605613001c0001d1000140140300701400782403413010058880c01e0000420300341800300000740c02480080000c1c0a019001d070502e8943c042420310700401d00390b840189070303c2103000b2030140100c014186106e60040060203d05103068418540c2e58801d580b1071030001c013910080c0000c9003000341c0c1041040042c124030981010394014140c007005450281d03a9030fa285210700c065940d2502c0480007007080074010164002d0300035069242d100941c106400c0d5240d85440e04e1091155083c0f00d240d0b20310400400d842d4000340c6004010b0310318119210b1300c201201da0b448518060b000c0380004c0701d01d4081b513010444240c0148071520fa0100381040484101200001003001400c00d69 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 647647014 1250 647645764 647645767
    0x1b030f0201080a020f0c0106090b0a0509011a040e0c0c060609071e1b051f0b03030d050a09060e0d02060705040602030a0e030f0d0207230d150b0306010609030c080102090d02060f 78
    0x104070440040003851286c0d02c65000061051034280101c040f902e010360524072030100404c08120560700c01c5000c0741900e003550305038440141d484140c44414400c50f0b000003960307620343d01008418803044020301503203080401911480c0d40e902d82004056002150b05c10003185510003204c0d00c1c402160ba54000480315420002d95000040c400c1b0043e50034130000c00c40715940807140486a000d902d10031540e0703103140b4803810312110460700c002a0b201d0107149e41c20146141c3c0d807c0080e00e6640705800041030181c105108001981c0b1610041c0d4a80c08000401d001510a500200c0c0d0564440c00c101d0b41140c00560295092202c00c0200715508840411400e91502c00c00b1010800034106005040d020320803a00102083d900d0700d440c050154409450810341c02400b11514070854486205001c0702661000d03d002450708003a5503000184048580c66804d44160300012030100d030401501c10580b8060404440e031260b03a6000b49090707114100302c4c1da40000d2150b12480060402c9005030140015860085 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 647648264 1250 647647014 647647027
    0x50d0e0109080c1b030a050a020904060f090b0603190302100e0a210206010b0c070308160c090c0212030103051c1e050a0e01180513060806010e041b030f0201080a02 72
    0xb8805900419248203464120074a4440c032003002010310395807510250b01810300c845494540c1500c410f100080a8000c48a0f5000201088060341c8585140b0994000c1003000f182641006109000100d86d400e00a2290a115115810f12000650002d40e40f40c0c0c01401030b030b22079005100141282d0101410701e0300ca000781c4800040c1008072440e0100392001e00070b92500d001408000d103805010380c40b0001b0306c04200300a01102d4130109010f42031700d4000d01d200760349100001d1401c2601489034000b51840c81c4244011a44407115000000809095070841d2300c0c241440044050901c000e1100604039800b80b40c0d4450244200099000c02e81c1a0341010b009210024140d403181c4010f2800c05000680001072644405802c0900a01c1614007845d007a1101c110035466010541c0320382c05040d02c2019850010000e4806d26000b00e0007502d0244c00307454503549c2d154140e03291044140c070200d5900c0642c03040801c01400100000040725000040700d144110380c1d030015130729500054080500241c0810a0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 647649514 1250 647648264 647648273
    0xf07090606090e044205040c05010c0843050c0109081c020a0209010e0103051c08071d041e0509150c0a020a02040c0c05100e0a08132c0c0a050d0e0109 66
    0x5601c5c5080345801c0c041000e142030715018002c00c3e41c03500914103008c0500a040301241003a4181c91070400446410840000c0902d84016401411059404065411210004030b510401c10f51000c0d14842c600300e403c1442c580005549201a50040c079200e6404284e000560740091107100070056001d00564016018a4000c0b440c4e01c0000d801070000c1d0348281c3e0041003003010401080c0c0c128480411035142d54415440c0c010301c1c070400504148100411004c0c0f1103030061000072450b44c102402002000312040c1918070100704002c030780c135100740d0510304030000c0d000000202d2240984d40303200000420341c1ea15020070841c280c0080a5010451052400e00401601c036413203080018581900c4096009009140640c540405041761998240c140503080c58440000600100c20341d43c05050340d83c44207a00d100312605041d10b03901064002c820007400c1c0b10500ca500070018a850034a00700d261180da01c03450b580c0b4040c410040341c440052010040e410300d000e4076905c82041c10302ea0500108104d129500e5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 647650764 1250 647649514 647649623
    0x2b02070212030a020d0507020904021905040501090b01080105030a030801033507050613030801120311120307120209030c1203090306011707090e0d0503090f07090606090e04 76
    0x504044640c80020011243e0f60100022589400d0303624100d46455015404505d4440010b40000d00851300341d207030441e01c403da202c003d84c0035180140c0100b000d5a940e1000d04003920071b09a049010600640010031a4280841c1d203c02c040c1e090384031940682d20307550740c0303c690303541d03c01400100800000000100d01319498090202511202c41c1e1a05c030582814210700701440a0107040c409400e0320054800a9000b804803070440f1401860100b0581c0c1509050314645c41e09404c056207801212500c0c1440c811540103503000d50403d5441c81204c5405440d030314200e128041141380e05511040c07500c0d05a01d016480d001201107140c0540c0c0c02d1503a640080f03468540c007a0800c0618288003a4110800306007003101100405002d07105000e0184003084181d03e940c0c0c00e42e0060200240000040c24441c02003116860415031001190704aa07519030a01008003c540901d8000906650000424200d0031210f640140d800070a1924a20002c0c4010b0b0010002d2078104a080344481461000d035488800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 647652014 1250 647650764 647650789
    0xc0a0e100f0603050a27020112020c03030a0e0705010c080f0f160506190c0c11010915050301080607030212060f0f0a0b030405120423041104090914032b020702 70
    0x3c03400b00c0d040c10050301d8102a101d0043c948072940d404452401c0c80ca1540d8070088055680a003440344955020a40d02c80c0030340300384480103e4520002091190000c0399a0200490840c000c05880e4844c0d2035100454998910480103454a001440b01080d0020742c48020301d10b030452182d40525000540e032600318518070000055071550050000c00c0114450705030010304850360184100448404140701404040a240c40a4181202203170600d10f564010040900503000d903071600c549250f1036201c01400d9910074024495107028400225080074043d000f0303906060054410070f801070b0780315020322103c51b511a0000350702c804800c0f80e4600c00c1d2030b0280314001070b05190f0611996440c143c1401840c0c5005901c8c009d81c20701040000708042880c00350404000c00c01c3c0421000d100d280980014040c25524091702d2880200003800200c0e0f61055000f680c02a100d032602d08410b581c01c1d000207842e8040c1800c2109140309280880d20300c005171003450410b5174a4410010700f00f19042e00490031461002 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 647653264 1250 647652014 647652017
    0x409030306170c031507020304060f09030f11040f0c0207060e040608031201140a0614030603120a200f061b0d0c0c200f04020705072301080a020a05090f120a0308180c0a0e100f06 78
    0x4550715017800d0080170480f04475081c060100c2c10b0b00c404001d507203d200748190420420140c10443c007a50300c5401c0030340104043c904407911400308041d00c4c1c0c03034144284100700c440791010441001c2410324000c018219006a15401d0420400c20070018107540010403a40d811700440c90031001d20740140c40a007181c560543c3d03a070300c041604444921103200030802e01020383e0b8482807510002c6000010f840e03030b1014051860616182039072610403058069203829141d01800d01c00415005940300b0403411046004145d10021001c0102d00c4815100561011b51b40003014400c518246040a8004104181c881e40807600c04c2503503114407104540060b40f54041407158040c0d5152150385c060b136040d030840b03031180c411880e00a10a40180c541d100b0000501e000c1c41801180205940d20702000303519803000c0905840040005203402440128110380c0c0c440e02900c2c2941c0b4203400a400210f4010100700a000b2108581c2000d0b04401d41c05c0b0000c0000c031041400c4440425041c00143d004001025079 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 647654514 1250 647653264 647653283
    0x509030d110c030609060106111608030d18050d0f05210117030a1b03030e2b0302070206071e02100c03121a0409030306170c031507020304060f09030f 66
    0x6401d00d42003076200012103100341d001200b448a0700b080814820b0440e0081e042c00c004950540490b00e00b00000d00300440007131075030500005500c04001c0000e100b01402300d0310070849a24003000c880c4405296100191090344000c94220300c842c0038101c100e80c0707190141010b83c03c100000a030f140030b41c2c0c4807000c0740b00d200725010010414800010881c02499039200050b60400542c080010320355800d80089001d81c3c998404118141802584031811102002d0b09580720303c204004c05182c5511041071181285140030180d0039071900ca8820754503035560040031640382c0b0719030352140d070007603100324600324640c84003600f45000507038a00c01240c0460003551541060103a00d82030203441000b800c021243c0090130581d0107202c4076103000112408001c2114005024006030404030020300141e04a20841181c10410001040c4001090f403446503044085a07011800078100081c1c4290640b00703d40560b0080c001800003600a0200a10a01052616040c1d03242d5030b456116800c06a40c500756080725a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 647655764 1250 647654514 647654537
    0x619030603021c020d0b19020a0503090c1009090f0609181412040501080403090504060906081b0108041202010b04110a020120030106050a02070518190501050d060b010509030d 77
    0x4103040c40c1d8600d000b0300715141d8404540e80c0c02017250040031420040041d41c80f400019004041901115030701c01c5510381c215111280e4803000f400b02d900c25900383c45e00b4841eaa5000d80549400000e4010142c06966100041880c019840000e09810906942c886480702004104452544235028580c15001041d17400d4400c40c0c1415000051ba81e0300300d4105400040451104024003000c46048503000c0c60600c0c055521418200c03000600d80e00040c0d840750511000084000d030913003086042c0d9481c14107417a0502034204641d441200800d40309400b080c4108001804030700440d9002c90014401e00010070300c500700d4800a01102ea0005801400000c0030440d246015824402c880003503085280c07248001c48500b90503180d60105225003000c0100005024411034805e21022004001c058403218001c000c07803e107541608400c4650310342020000c00300e035032000402d0190f039049035405040d10303030400c88640380c2d500906000024923050201c1000f080c58562000c100c9248a201e055550341028003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 647657014 1250 647655764 647655769
    0x10203041211060c0711061201060909140609062b030309060b0102011a0f030f0f0714010813030503062701180212010e18030403030801060207050d0b0f06061903060302 74
    0xb8408003004482e50701c190100158034410008441c1710542020403500000d91000004d1418030030f031107003c44919007102c000501c464000415009035180e410050000030801100e4124640c01255031030340c0050044042401420445032030301030841c0203000340c0c0c80703032001c2c6a004035400d4003d1021800030340c0d1000040180126403017035891840003480280821000c014940d65032420040c40e5510503a020350f610109a0b904108a002c020f00a030180c80000706041e484544481a6101e010440d11640e50645c18540c4507004580c0718007500484008140d100f5201162607410041105800c41100d2030303c0032000c02500b95104c000094034003031252540c100b0711101c120903c40e203000f00e4000d0044c408243c0d110180041c03941502c0303d840f08094640c0d40c440203404120381407070030080325004c00038010050540c0041c2440c182c98180e0205c40a048d42d801c14490340310500d98028080781680c401007404d5000180308640c0107000100301c0c6040c0b110b940900101c3d0007010100201003980c500c810421070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 647658264 1250 647657014 647657027
    0x6090d02070e0609190b120606040b030a02060a03021e030408090102070602060114090604020717070b06030c01051c06030c06030c14181203070501050f091e100f0207050102030412 79
    0x40c110900158071a00302000404d008180250031048903d40d198400d03840c81134580e10501a0150040100e180c812000054070744541e42510b134140120b0500c00402000d0500042031a1021b90103083e0915100c000b110840081d089040015820080388140c4100b20f01450055401640908600ba666440d0600068034005166104c9070940d0845401007082e001c03807101c885c1003447c060b11802015910000028000d200b6440e0040c5845001c0040e0388000d09500082c119a600c104880801600d502040654400d455840580020010840080312400c1d200d610744150b01008070111f034142d100d41d1249540030f1035130051000280d036081082d6000b90702c460b240d419620b1460070790b407a046d4500050940d10303682404103405008002c44d100c400f100304204542c01ca5410100070412400d25030901c440d10340d07054075081c909104803203090102c0141a02c25001d44c0806000a003400d8001481d4000034050847e801c400c011327070901060b07010803403e000030340c810391003402c0c40d410b10005d2000107842c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 647659514 1250 647658264 647658269
    0x1d010501020f070b0a0e01020c03011d0607050f0f1810030c030609060b091002030d020d05010e090c01090e060604030b01032a12060f021923071a090f06090d0207 71
    0x280d200801c00c0044c0d5040070103e0b40c174184d0b030b4a00400b00301c00d030301c00503032420002c40c0800350558030300042081081080740100c502500000169a10f5484144003101d060040003601d9194200c204005085480c00b40004e00440700c0c0320840e004000c0424002a90583c0941401380110f41c403901c01c1c84000c0e03494030540c0f014050b01801004240e04040d0003203804c1c0540c501481c041c1d4030410910007080d0003001620700c0c48200400c290751300c48004c031800024000030f204542810002c03801061a03078001090034001a02c0696907082014035007a1703030400310b00c0c0141420b90455401c200c0400898100c040441c082c502500181c40c10315100e8a0028008802e104c9004071446101420721542c0019205076014640000d0003140340070814040d107000b841550035503103c43c0c0036507003102c0426400c01d6210280e007140f031918086119001841042d01d2207110401481d80c08100d00c200325040132601c010b034000c80140100c1da541f00036840c110380f40a80991b21084540d100852107070b0350300d6041001001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 647660764 1250 647659514 647659543
    0x1e091e0501051806060307050c0307030909231311060c0705030d080403020318030111071104150b1617070b2e0506181c0303110301050d17041d01050102 67
    0xd0300e80184507559440c403c0a020306206800c000089a1000c1c03140013a01d0141036030a056a60383e40e02c0e072a0151034000b02d44249907105041081500d045c03107000fa102032400c1c03410703581c4106a41e03a2420223072044880260440d41258160018510350320799002400f07000303c0b0100200f8115080100b094034003041c581c010010002c40f0020407000a0307005c420780b90b052508140740b6400b6121940081d0260546402905652001151280900840303401094100c00142c070b04000e56040101c2d6a00c1000031409000294081007103001229259105444034660259000b05150000450034000a91241105845001d040c0b81400821400c1081e9070300c07043c0c40b211211900c1003101e000116610740500c40c1c148680742c0800d4050444d1070b0294100e00031000208031006644100100ba10303e004035600c160002450301045240304903141041384e060718401003001031440c034169644540402600500c1c001500300303100015242600301450b842c0301c5400307400380312651b0410000900d010410300b80c518 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 647661870 1106 647660764 647660779
    0x7050f121903050a1b2a09020f031e0402011e170421020f1b010c060f050103020906031c142203170a05041e091e050105 53
    0x1450700d4a920324081c0d0a003001002502c0c200c01700411210582004440b0b004100c040035505d500c07484020b0740e000380c86a07a00e105070b82100942c04441e64011040c801e802c05508003010561420803484000391900d81c0009005003d140705002410b0004201c403440c451060603544188000c00c030303402d440c0c0d041a1030001300380e075100041d0150300c407480350303514007280d20125030030403180038010003400e0b1440b5061040e02a000c002188030f05101c020a0380c080010120301070310400f9800041c0c006059031560060000c0c0c1c49004107aa40b00740c010000b0804018021800300012002614040140c01e0f00c15098520318400c03001900e07042c0d0208031b801c1d11030059115001080d40d00c03410b400b5501c290b01101800035400380e07084801c0410400c0c001407118aa0344001058900c00f001010150142e0b140007410448100060344491072020419000b1040c40c0e502030b09004240c2500ca0b40d = true := by decide +kernel

theorem cover : BRFrame.Cov 647482014 647661870 := by
  have h0 := BRFrame.cov_init 647482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 647482014 ≤ n) (h2 : n < 647661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
