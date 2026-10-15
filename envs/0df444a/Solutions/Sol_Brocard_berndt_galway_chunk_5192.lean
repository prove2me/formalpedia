-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5192
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:03:04.850447+00:00
-- url     : https://prove2.me/submissions/b3fd3a53-2c95-4959-8b5b-75921618f338

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 933633093 ≤ n < 933812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 933634343 1250 933633093 933633133
    0xd140118030503010e06060408100c020f010e071424090a0b180103110d0e01020316080405151506030a02090a140d06180602120703050c04050a0608090c21 68
    0x303a05501e6040c196840c00c003948541c1c0000034400d0b508084280800900b8000800c0100340041140c5404103c6c1b5140700c000030324041c1d10041c1c000c00d070f81c1001491580c5840100d541c60a40b580485401d0001c1d00c0c04000c108400800004000600b11031100c4016110480020b040c0041c421110b1404c00303580c5094804c0503000b00304883d40d051200354840c0c0c00310340c001c0c0c0c0615411018a0a168180840624404203e840800300d180259400200b0030448e51039283ca85200000a400c1a249070304068a46658461400c0a051030f840d030300c0c402003910011007922481d44080020310040c0d4910b040e180f01806900400b990b24019144070388081040303510300a4818001d10301500d5901f8141058070351030050714007a4105000700c50890410408610203000034200480760301c24000031030030110720050440720024044982c3e8403040c0424021644c60f02c0320442114410b00e00302030591241298142000041c07080700b540a0555102400310071500442004c18580001c01c0d540201c0303420440250807 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 933635593 1250 933634343 933634391
    0x604200103140c0a0c05060108070f33020c1f11060702100207060608010504062004030816031107060315051c0627060b0411070c0509150d1401 63
    0xc42c41400c006410820194003918814107180f51407980251180c03560303070400d01c081e0082d241c580c0001e0070170700107905003030420302c000c013144000c8420b0705007040d1f03100400010300100c2c40174502c45007009500c801c2c0708202801034080010f0585044040c0114410a0451152400008038140c04252075000d41d0115a5510840304c54001d0030648202c1043c40001350320402d42103640c9695408003240d0400d0034424103110341c0c41013074002001c0d5240400b03600da00c00d51981c007144040c4100400e20004682c6001e44810860200101c0c0c224891440c1c25600c0c2c1a1142d890207081c89079a00014281d035142d0040a40c9070064041c0d03071319003a25035060021400e42280c0c4541c032010303040060400603040d80d12181c0b000445500c410181000c41413200c00444000700d0030f07181d041e118010781c40305207824410200d0040840b40440c1c5031078850b81d02c083c1008058465270748640b07a05000a19006102103034a49050b9000340385402041842c40d10043d0744c8120840000190300c0c1004000c0c2c0000c00c1e160207414 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 933636843 1250 933635593 933635621
    0xc16150e031c030f050c1b030708090d15051f0f0303170c0f0a111501060818030d090506180606012007051309032304050909010e0604200103 62
    0xc0d644071128140b0302c8001c040000d003055610700e05508001101d00ca6140914a030007045583d0701c4c40000c1300c0300a180c08810110058008002c0c0c100000c1444049403003034882070324401c0844d41c0783d080c400d14007818041003001d80e900b81410001104014031000340031000c1e03c03003228106901d8150701c2aa454050000402242c035911480da400c23081000400c4d440341007009010314001042003206501c3d000324a02001042e01c1000c0349002c00c41c11702c24194990020046029250303d0310800401504020300019410384040259030007102c002e100b103e8450350845414808251185031141d61070ba0202c400b1200c100e5595540c41150002144050048205079100403c50300348819000500485103411842d91260350320005140c1c5400d450119403a41e0702e00000303865030705414007404045400b000304044d1a0700c1c04484030380000b04800d41e015110203032030444160ba40e80c0c2c0c04e14010304240201c4400d81c89000d0802c0208207138505603a02e4030310320100c49134000f5914001034080d01d03650203280d90 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 933638093 1250 933636843 933636853
    0x1210061a0f0708090d050d0306080d050711010908070b04030209060904020f013f0506040b062d1323060405120a020904060608011505060304170c16150e03 68
    0x1d0021190007070070305180500c1d002d0340780c041c02000003000740b8071a801c22945900003642c1c80c0d8803140c05114200041c9660307005410385100e140001040c40c8a18100244940b00d000030405803640302d81c840c40b01030000c101c101c2d03031f50944440f02c1032042c0c0c100744812441000700d00001046810701c6040140070b198081c0c15001000e05507c010f403580c050036914125249803405c0504001302a40360108100e5900d04180b03450a5024044401a1107000341000e000e181070104117003407074490320216210111040c002d003482400500d01c1d09420607078035501e02000100030407000c1c1101d140c0844002280c03034000401c4444c0c0c89041a0340303407a813103070078034141d110005100810017401c0c8030000809192110081c0d400400440d8006440c0c9042076a06803002644d80105010b501303000d11803240d40320ba00c94100c010142c80c00d400109584070041005100b411200ca443e02c441d08100169101641180c0c1a260340d910b102c541c0c20100031152050b80d401c00d41020302c00740500d000d004511844440500648 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 933639343 1250 933638093 933638107
    0x7050304030f02030f0d0512010501020609060a0c03020c100c0f170f06010516030c0201020c0d05070b0d15030f12031109090c09060a0801031b15120b1210061a 70
    0x1d0708066280090382c250180d0111283c0341c00090003c2c2c1d1b60481280c40f16515400741207840000620141c100720705540c007075030a00980c0d076000154198031224880d80800d1050500404502074080c1c981c1c403000070701c1a003003840382c0d40d100e80e0000f001e90025561124200c04403010211050031005215145075070703007040440e8140140c101020f9004106062051801070040340100107058421016030000b4118a0b64504641c1d0501075400c00c0c92080b0341d03128460940340ca0b901e4480d2400e100708110484001501801c41040782c020b01031080c0007912034502580d80c0c5c1080b2580030b000d0b01301250500b00319060112214028400d080540754445011400e1003186000e110520201402c0401640014090801c1710303941c00d402048000301a40c1e405006500d1458414400c0c128150004a801840e1209000000080c1806102905986044100380e0301c15030070a0014400044003c1d0130028148401c1022140003030060b0b074103044d00384100700c1036549412505607400d8100a5010b03544041040d1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 933640593 1250 933639343 933639353
    0x8160f0311010e09180d02010b0105180f09040f060c1404050f010c082a030315011d210c0f090601030b120102030a240e01170a2f01050705030403 64
    0x451200010b041c004039a075040400100c0c446030480e441461203100c1e1225130500e01c401e205000d411b500c030740024040302e43c2c1d50b4006001800350403c038003150008007800b40d1050350340002e04070400c840501000818105414001a0f25040c034405071221070510425801c01c91041c5a085d2107a84494851400d15040004002d42c050421040c141040a013491070340c0407800344002094808100e20750351103196224080e01388803612805c0d000801c1e400500401c4254401e2003548042207200346400c040120100144407214043c00c80c5040d00070320805039442c0c0d55002102c078449200b800d50201ca0607003000e14108081030300c0043c00590004490700c081900d9500980082c21080301c01070541d403d6948105040c0d08a80084505002a588072441d621451082464044400010107910b05503541061004800c3c0c0c441841a0070b52100088843c294240c2c2c144512240306030b110100c00c1d0340b051103090390061000700d204641040003407052041019030180c012944050340c03000145040500c0d54540c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 933641843 1250 933640593 933640613
    0x201260703021803010f0e0c03061e061f03020a111906111c0207021504080703030c061404030c02031009200103020408070902030f0f0f0f040201091a0408160f03 71
    0xb4210307280680300b0038030410369428007607600c6840c00d851b0005001041d13051141c4c603004085513828000c0d00054103001400321144400b12641c5800c007006e00c0282c640002040d80d03031200600c20034a1132a94076011544982c150000e1018010030f54a5174100c002103100741e502e03914845003060200062000b80000241070b03030000c61000040c80c5d01d850800e0030380c400c98001016603c20b2509115400540501149801d0008548101902c0a680c1c2414104051582d0762201c6010103000c2c0207061440000700283c40d080a2108940303030800c0c01c0c56040c580b0b0068080803100300e040b031080c02601040340c0d003001316203e65105107402c0345111102242400e43d40700c1064881d203441d81016020400481d00c3c140c10840b070801428807041c016030785e1034400d1080f00c075880060501c1480304a401c0c14029a1540b034080542c02100904088200c0d84652005807034106c1a0340c0500c41200c00b0319100f010b45980080580101d42482054880c00307000f00003ca1118100d034050078108006c0d407401440443e042d441 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 933643093 1250 933641843 933641857
    0x801080c01271805100b04300503071106090d020f030c03010e030408010e010c0801030b1819031403090604080f070804090c0e030f0c0f03070f12020126070302 70
    0x20840c0c007940245440700e5080400d8001e4100c82c20020a070028034022880b807107a029250718084040c3c14141b214820300c45c416440b1740030039448000e040303509070350502500380d108020b06210969a03498614101d40c503a0800481513800c1c2100c04003004050502d9811200aa10700a020381500e01940e401c0042820005c89229098441d00d42045048d0705e0911171041c045140d07400a42d20b541c0b4040846080d190300c81040c208030703410140c7c8844400e0300018604e0540350b0001d02000d0547d905030035042ea90400d907a07641580d01c590000005070181d03442e843d0b580c0c180aa42c03103130001c00710041c070002180703c00e603001c912590003000024080b078040c00250590222010f02e403444c1030250340740c01b002c58015402c020700b0700350b9464120203450341115808200301015000707004a01c4030305290a446004115000d402051810881a09a03406200e000f01502e85002e2090129446071900301e50074000807000c80c08101031810850800750402c0e48405c5005a401c0c0d604080c3d030b62881c044003e500801 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 933644343 1250 933643093 933643127
    0x7030b0609190e07030605150f030c090d050a12020d0507020607031b060c030b010e010f090b0313061109010e0a0311040c0c060e06091c020a020609010207181406010801080c01 77
    0x1810214403c0d00451007203005945984d40031030301604003130812002514143c1000400c050402501010b03003801001c0e6544800c0c21107826454049000120305110f0510800920764000e0702540001c00c43c1800c0482864032450742141d5601e01e801c4029100e5215115010390b019000b0300407907002038410307080003511040907080c080d510f91890b5198400e03640d07502c1c984030100e9160000b43c030595a00c21b2145108460074605045c1c51152180c006d0040200f5000f0080c40b00400000112030303070460140160601d600c0740e070420040710680420010350300000c020500081e03c007124150185050610001902e800505001001c1e82200400004100543d0400d05000c0412040804a41a84503180d8003001c0c0d400a07040c41d1402810300f504080590a0441400f03201a4060103400d50001d90442810750543e0340c543d507841d101d00140d1030020700350b02107510441c071311f80350800500c000c0d008002424030501c11140d0310b1300c95400540d4410000d0007128010350000061040c0e0750b20403007250107449611 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 933645593 1250 933644343 933644389
    0x4050d080913060923060f01141305040506040903050d02250501050405060f22050a240b01030c0c0201052a0a0201080a1401050112110d1407030b0609 66
    0x180001c030b007240002102020180b6038072207040062190a01451741e9620030a00b030b9140c154a1540c0d804402d99024142e02d01a0019150f5031604c2d9015501720885c1401103841c150b241c0b5005e501c0c69401d080c20740141405642000301241d403a042c1800745a5001c0c0d4941c4a003270a00710b140da4130704000d42008004510307800304050840f41c09150041e4803403000c0e0041c80045064507041c100180740500c040c01e884048030034003040102d10f014104045600074006411200b0010080c24801e1808150134009440b0b0180088500c0c02d00000386034008000e03d00300014401d41d0740c560b0064003100c03480780842000c940071403180801507105500400d1000c045528074000380c500312a201070503a16494000916030307c50300d8100103568000040a43c020301040b0140710f9019043c109104128061040905100c1c2820396140070200c90380141c07101386004418941c0320003c40c1030f1440074081ca2078115174940065004910143e2080c007660100d60005001185401104410700c4003007000b1240030031000100e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 933646843 1250 933645593 933645607
    0xf0b0304080307020a0602040308030708150604050f01030b10020d110303090c40060905160822050a0201031a09011505070b182802010804140604060e0c03030f04050d08 74
    0x1b20700c0a400914020f07414191249040c0002078100b40d00580241500c0c0140d03070030107034a60fa8080c01c88040e1542603540010309000c0710010790180100003903a5600c22645011000519070004034810840d105070b451041d00c40900c0740e626102d100c00e4071030072601d800418a80c0300b035050440003070542e281d0030002c6412502082f0008070002c0c10000300c4d04007880058400100072a101c3c05003001500b110f400411140c1171640c0d0812606030200c4036070050212400010300c6021b095204038000011000e48003160041d10300d403803030b02c60306420400c80c082890701c008070b0140d15445540ea588120068140810f41c3d00344400200c0c48120055803008001c0e0812903400050b05000515004140c43c3d84000c1981c21500305441c01c210003aa41c2158080c0c6042c10700c19501102e21803038400a40a0070840e69584031400c1c00440181031000812091007000180b104004441d4001c2c030340800420140c4403554144410136480b40b1408108400000041c0000e0101e0702c0e01819452000d40f080c0da0031850040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 933648093 1250 933646843 933646853
    0x1c0e040b210f06180613030521040210050301080a110307090f05160503040c12050a0c0308070606050a29040503120a0906020c01120f091704050a0f0b0304080307020a 73
    0x84064811003160488000010601c2c401c0001e039070840c0442100d005000400d00515544500040072094040000700840060502650465180782c40450352191008100e00300390220850035038089004051201c84400e80038410402e403030603070f0103104c05016840d140792958040742c0f181c078402a6141c09001d00004403403960784181d00d05100e4a000101d80c2d07160100084045c0141450081d051000810401000400e00440082510f0b600382a15840380102d0519606d050212140100f00300038160010040c0304134040941040f0348500820f01450762200c4c28821080828400c840000e46080e800642d2014540042483e00b104641c41c45c4c1400e0f507481c0003a1824100e0083c18880700000a88444866070185403d800340400e80002d00e20001810f00081c450281100b02090300c1e070766000c1d005401d841941000911940040f0b031044006000780013944240d1052040354400d400c450b01c009458001d0162040c00c892891764004d046940e05c0d2200c140680c0010080000c41c0201010a0000f507 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 933649343 1250 933648093 933648139
    0xb1b12070f120e0a2903071e03020f070312051503071502010e160806010801110706090201020a1a160207150c020111060c04030b071b2414091c0e040b 66
    0x1003035500d52241d5020600c5126140040c24011600801002000300e100d070044060160009002140c100300231504008800902031000401001c010001d1180c2c18113900c01100c140e50504644204040e0f19540c03164013a0f4022650390580540142c41c007040070040c10240c00f0f40110a038000411250b81707a00d0024180301d03c2401900d00141010800d10a0140410040d4050400031008004074141440031031001e0162410081c02c25440e1351020b41103900c00d000c0311030310701c1e40300e0000b12000c20200003802c1c508004441e400381340303011643c910720030510001c0c4500480d00324500701c0300b41c850004411a02032000e280181d06003e640c400e0b800d0384990403c032482c0301e42107200d001906d4600b581703011401d202c80034144204015810210a03a002546010000e10b1544013458444454856184100c03c40002b0032403400c003844c25410701101c040d4a0101c0b0710503c1d40300b0a0302c0300002c0d03040003500c00c820340d0f18004001031040e100c10982c0d801c02e9807112488140081440c1480d2051110504442c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 933650593 1250 933649343 933649349
    0x43110303010b04030b0708091504020a0305011439070203030906030a02070506070c080901030c030e0d0e1003060e0f07020106051203070c05010819020906040b1b12070f120e0a 77
    0x2200001420405d1000e03002d403883d04000c06103090102070912010080d645c4035040e05901450002001007011956000e04640055a1140003804030000384500d00014000884601380c944010a048854030604500c49012941d51000142c0700b030082d14101c442c0c20b4214501c12a0580310412030503071950356040155104000c0d21001580d161214035140b410118050074460a000c1c0100c80c030000900c0100564000c036400b0b181c00a102418030800b18040e043c0518080c080d4015801c402c4500d0340e02200c1c2c0c40c0c8a40c0c00381d0b0100107401c0c2046023141240d6a91240e25410b10042c03011440000b031000207190040702501c0007046154a132000a402cac80903011580956510000e009801c0101c244600c0c801031074242001c0341036140c00200c0d103c0150080c2001a40c15030300081030550340e6201c0003514003a224100400303807900035a185190302089032503801d070503502ca10b11201c00d01008103400c1b03400e0164080000140c00f02980c0c1d61116240851600605104102c4281c22444c0c590110401c01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 933651843 1250 933650593 933650609
    0x2040504050405030715062706090e07030b150102120a02210c0105060411030c0c010608032b0c0c020d050a1505061201110712050705010c084311030301 67
    0x19841403032030102c0380f4122111b544c2e240142040f00400107a403c0030b55503521184012109240158008400070042c0015004407141e54544000c038105030000184840c242d905c10704112009031520740c1038660000b421248207005902c420b01c000550a03411011340412066070040711504035103100000810b191141c5126105007000c521a45001b03802d02482d60051001d0700c04003c54200240c840841d444024248240004001802031074610254031010082c030030b11040c4c13038842401b5916058207009840c001c00301401c1c590401e4103501402c2c4035100a90b01c0a40303030341441d20440e41c00d11144061055041d605409400800000b05180d80501c0c4400401c0d000300040904e0a0000c1220422800d4000f1845030303d840d6a0800c441c03c180125a02d0a03003149e20140c4040c00040c0844aa100d1100000e109500b8402c00c444a00d4100d015036000700c00324528000740360301f1180304844509840c904203070511341c00c0c081210300c0c0b03507030200214407072400745010038400c3c841c658050715592007039000d200 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 933653093 1250 933651843 933651847
    0x9080d0c0c1d0f06190905060406050109080a240f0e01060807030f020f1c11092d071206030c08010506040207122d030e06060604081e010204050405040503 68
    0x100181c41c0300650207404802c150381004160412980c41e200d1006081d482c0e003452180100f00c582e9110f210380d0101701c6030f00c2c940c489103a4542134414003600090b6406409282040c5000c5901d600880702d003019074184100514505c2d003036482e001081000900420140c1c207ca404140064010f4014210100d6048401040035200c00c0003080c21a54181d01c1107900340c011038030a200041030014442030654048403002c2c00c010703501c400264011490b014a441d02c803000c0544a0801ca08003070140301421b011190a41680ea0303580401407400d01802e821030103140350040d504152404100309940101c11880e100d800d100070740701d441081320400d400035a100c58500b501009802401d01809074414800d40b0207604010481e03540c1c544240707080541d581840b80d052082206000d15589003040c900d0005041443c50002c441c1c0074005000400b0700f40468040c6100148a0b41800011542200c00a400038002c1d0b44000a1092510010b0038100c641c0395002c20001681e55690b000d154060741c000c0f40910303 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 933654343 1250 933653093 933653117
    0x901050d11130609080c060d0e160806090309361f0f03080403080d090606090c0219050613050f06070201020c070602190b060105090409080406110705031c09080d 71
    0x710640c1030360f02803c00c102c0400700600411101140342d072103001c401da44040d00e50b16070021300005400c4001d18926240b0411420b003000c3d140c015042d00803a04200709550454454100590f280c4c401d501160f50041c010a448101548000c1c440141c0b01000d0f41c00c080d6607504003440c0b20640841621004c0d60401c030907090b541c43d0350b100343c15080203045000c010070170146107a868a42e540203a100280a04501040880419001d41c000c0b00040d6406201040041c0d10b641442d0001e240e4106140e00510605800482d041e844644c02c1c50401d40000041549540301450003a2041c00e03e0021201c90080c50054401c042042100790300501841d000503803505901400d0070310b409100c0d4041d0046511503c0405500c00345683c00700940764000d007501c0c5496840c0001078030760384141c0e0340c0a50424541098002844050b5010304280c82e4150340d964400740300c0010700f07940c030003007070180640c1604418403803c42d1401d0781e4100138242da501d081c90364409903079250290a281d51900e01c2c1d40400c00b004002c03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 933655593 1250 933654343 933654367
    0x90d02130f052205060a020319150906080a021e121501050108061801090b010e0d03091404020f250b15180103080315030c100c0606080c150901050d11 66
    0x40c02040003d03030701841411007503840f090b0b80e60001501d45520f032030b40040803450702d00f410710700091440c041c81024800ca0071030603210450819070740f00d0013181b00d1808901207216000460103010440d0010301c40500c44038000e03518500380c01c682da14181d224a102c0b109001852080c09440c4481040f04c2a448456242800140c42100e0040c285481840800d59213101403800d2012603041d40c4404800084d80075174030300141c0301b0b140b01d02001580050004a90313002c02d0b07031060a08040c3d41c00c0c500008040744d49081403000343e0060880b1689640f200f8408140000c075160f003100e480d00c40c1100b6002c4108620f4441b040284030030b942601c450341c01c00c1644401400d045078032000840450580350459032440d10341d04d0762408080c00c8445000c0300c0d40740c400625079040050805140c0010080b8044141191010b4200c2169240c2150038904241001800341d501144135840700c80050304190100300241400b444030f074440141c00d4180300b4180400d0700545042c2c40f41000c1c2135107259161395605010000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 933656843 1250 933655593 933655621
    0x1a0a090b0a170a0b06010c0b01032103020a0207050f0402091c0b010e0411040507090506030114040b060c0705011b0503040e09010e0c1018030501110301051302040b090d02130f05 78
    0x3089100d9000211842c5101d0030010311500301d03035089081c0f00d070f25850301001281c601c811008081c100b084064004400c0c05000d00903460a030782d80c0050707443c91041c000019000ea0068081c0100035030000ea00400850030880001410382c1001440107180c031140d5800240304000c0004a89869403a582d000c004002c024408507001d0a000c07000340b9007500d400d0b50b40c00102624210765030301640c2c031100400c610b14050f56140c0007811300140722944940e1680600101804002c5040d4816424000542500c4c20042c0480b541c020b01400980106170800f0019a8944000b131420106040001d240101003403090028001070000c80040f01840e080c11a8038600756000000700c907401c1d0300024030000460303540d40c00300c291036a024244540050081c3c141c580007003d86a201070318a500301440c060101410000070b6040c1c50342126207664450b1446410f00486c000e40c001c2d9565074030200301e880e0462402000540940f48001c14a000d680c44001c03000040d182946d191425480e100c81c207010420203071500d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 933658093 1250 933656843 933656849
    0x41e1502031519210f051b032103070818010603050c130b09042306040c0f08060c0d1806180b09010b010804060c0e030f0304031203110d1a0a090b0a 65
    0x74900d54041c2403021001084c3c01c02e8001070325008030130080e41304100d84942098400346c1c000c41964001d880b4405481040088000ca0521078003600c8544c045050b110844a6075958001c6016425a56545002c1c0d510003030142500662100204e85442500000d01921000d148901c0140118481c1e10013444a40007409000c0060b050600d04012000c1d1150200580e0007038001c1c000248118841515654010000000d03841038001e42041100340928841c400c02290102500c09401c241d0718001582c540405840044009000700300540c0b0340580c58004800c00c016018058a1040c46030f9160f00407030310079807504442100e40b402d04030706012840c024654000000d10090190140c0200000d00820008000a2685e0396440329121428404d003108003a945016007107420f00d44203404050b0b40c4c0e400a1004840034151400100549403013400f4950b00c0026159115007058690325150b005400c61700c401480b82d0360081042a020342e2a42101d900401c800d1030002138201d004400c3c007c5180482d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 933659343 1250 933658093 933658129
    0x73c060c110319180b030105120c0307060c021314090c03120f13090c1d03010c1e111b0307090207030504030219050a0311090f041e15020315 62
    0x80c0600d00d2141000c0704aa070700b078810050103480748605040507a00d942000c811304451926140010980e480c071600114180c800441c0c0320240190740d0402590388004122403a0b030907800441c0100030403402044002c0d045407000380380d07003118039034041c65004845a0640100300d030300400f418031242500912038908404ca0039805060300b40c0c005011805c0600c2800c0000000c0000015084a40c0b0344921412014002c0d20b41d060001c2010054002c0c070b16030415400d18444e0110b1003a180c000d2505204202407854641c50301c0d000b02c1030314112542d0403c01080c45030140480c07081003000d402d03000d208900c03a40208080010454981d44141031a10010b600702030b004c24410031280c80400c2e000340603542103940c1200c0c10084005400010800407400c0d92115405c00c584a4010041241020310082601c400340da0740c4045a03144220706001e8101920003800000000f4441800040f98407011110b95000d030000824916010b44113038101e80c0102c502d0f98521b202c48800c103c03949050800506051050 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 933660593 1250 933659343 933659357
    0x31b0b01061106160e03011e021e0405131d06180c09040c120c15170903070c0303030209010216080606120f0736240b073c060c 56
    0x3030001380c0d1001803120758910511802000c801a207640c2508200000310741800649040100c0f01c0d480f4020707402c58000540c00031544a031070184850710500b503408583c2d0041c542d41340400301485d0b038402807014126020090030400004c0040d40c00c2041054001e400180546180070b030043d44040c100071403a84250310804e08481804081040c0482500c10340394452418902c1800a10300601034044030b80c4070307540c1d003100a042040100c0d004201e1013420b001d00c1000301c44503901e16040c0d9131280709940c170041401007000000e001081c0701ea400f4119061041c0110742d0320340b0b82c80c0000f2820001c81c1e0701c0181140d003c0000c100f501d0030181000c81800482000400c54a030031014095214407060203a156201c01003034400000e000c4d104149584100e001c0054a8440d01c054003a90107841c3c003456a082101801030602c0204c06040e0f8610200c03600f05100368100850781d51405e080d49040c8070000b02000c1d26480ca00854096543d5a0b540010000404841205c0c86e26054044d101110101c506208070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 933661843 1250 933660593 933660601
    0x70207090b0d0b0612062503091a0a1d0a060c0215070804050a0b13030f020607020309010c06060b03010e0709050102160308070c0e0a06060306080703030e0d031b0b01061106 76
    0x1200ca14082c01a8400c02203080e60b5900c030089503c0013000e07680c9500c03c0c0300369014804046118810007c0c04080b006401c94208031080701541501d100c0c1324010001c01c42c2590940e2400e541e911020f4000c0600b46001c100090318062000c0182c818840032001600044d240030300f000355920030b500308540c003130001d854101d10905121110700c5004042e0340510104400180030403c09000c00c0c10000c0d0310100c228114100300744402e54544031030b02c00f00c0200381a104601080c40c00002c80510030f1184e60700031403a00e045100111076442000d40101c0d04162075800100d00e4050075005103002e440140a1062185440c032001082d07803005030701c06810340d045502c2a081d0001d0559400b0309494000c0241c0f80d4a422920700740c0384484850b0700800000035600140803642030715800c4a800c80d10303203540a0041c9501c0d101515202e2110b840001c0210b01c4040c60807140303043c1035040140f0b083c02801c1444504e042d55001d0445550307035180031100075906000500000d034102c075900c100450004d009001b5450 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 933663093 1250 933661843 933661849
    0x603020a02061015110c03030a0306030b09060103171b060a0b090c07020108072115090c0201021206010311040305010c03020301151e050c0a080403150501060f090519051206070207090b 81
    0x86558010444000f1001c801517a0030884541c00804c003904599451100c030744002c1c0181501c1c00f00700d0b41601448041134200b000010364038142c030382000b444a2030344400040400c2590101d04081124468900304450803942071040074441d891150002c02e045100104000008600800800801300188200b1000d40d0780000d01c2a442400c0d420141d0030280d090180c0444401104180300ba03241c01c246d002c01c03400309180040c81c00c0301e081f180c060120b100c11a10581c01c1c1c2c01400d0701602c144a40100260301c541c07007900041150241d6211541c54591a0345881d130954031312445c080d000c6038001004100803461013031507141031240c915041d40c04010700301e81b5003040b150b00d00e0000b04004000c00c00007158802801400045a070090406555550760b14022a20302c0c4030341a5440524540300c0005185030150340f01915011459480c4205142864100007155281d164603004001c04514089034903100c1c151000410030240008100d50310305010024034008568100b40381c114104244d00c031050b1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 933664343 1250 933663093 933663119
    0x290f0a0311071509060c030b03060f2502160f0803070b0402060412050606030c19060302031009020f0c0601060504180504022808070506041d09160603020a020610 71
    0x2112031402182040035a0106241805420006442036031a00903001407a18903500c03506a4500ca03507010300054071402001d800b01c2c2c070009105505078002d040010100d80d8007104255109810342e050710188150b0710240d10100c107c110500300940d0002003548030300403440d55464010007080b0b001d0801d69003803031540f64403801424801031035a043d60f00818210343d2000c05850242559119000160000d404c0482d42c440041e180c80e03010b400749662784445424400f5000400500b08041c81d070419240000c00c40081d840200243e07041e4110440c0400d405c003150004048480082e800c03a0f4580160445d00c0d800c000381a886007084c4041001304102e441643c40c0c80380041000403200054541c1da50002c20f060a10f00016183d410403e40806405038145600250039a108031040b5203400e030319141131041c01d10880c021040d58400c140c0000c07600400003111943d00c903695105070354035a54018032050049166800c0300d40480e40100700010204c1c0d04000d01ea5019041c640e40041e0341d850300e041c205540c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 933665593 1250 933664343 933664357
    0xf09022208070e24041a040c020c09010806100510230304060f0e061b0408030706020310090b1804031e09181814070b160201080115021c09030c290f 65
    0xc40e110441c46d02c01c4c1e8031020064918010241080c48a4031042c03000070b4540d02c120344054800c200303200010484d20000512144121686c042d02d0910030304010410908480071a0340c0000c20144200e41070750074a050081404488011095940b2400c1624100e02070f1442c400310b400d00e65182c002c0080c0412400108075400c4030081d10489c1d03c1928001c19104944980e400c1362620b4400004c043c0100805580214413400300c0060f81d0709c030a610b50f1041800c0e1125040082d5201991500c040381c0c6803101c0030a43c1c0c0241c400d080c400c80c1e1102130029401d00e410603046030804a85658410402d0320404181104080c981040c2007104031694640b842c1c580340540b0000d0030058940303668105140c020806d10300500100b400c45512503460000e0380302a039000311030482c0050804030002a5410101c3e00c815004002e940140000e01c2c01c4001c3d20b020300507054002e80401900c0c02000003c60350070101140035000c5d50303658141c5601c59000d800603422003000d042c440420100442498440e00700300340d03460 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 933666843 1250 933665593 933665599
    0x50f04020d0b0910050108070305011803080114060904140609090111072901170120030f0604110f0910051914210403020c01090f09022208070e24 64
    0x7450b120140100d11340b1001d0002c0241d4246400c00129a5170350006c1c240e81224401c80c001e00086240c28078200f80c01d28400001800300d49100018010b10003c4881c80c079000c02c01400c100d0a2007821400242615903401d0010890341c0c1c000c05014280c2440c046c0c4950050020009003d1071308803c80e802075a10401d100a082008041c104508154036008100144219040d1081c01561280700140444c403580c10b011580b90702c0e081d0700300125000c0c2c2c00040c00812070440107906550f91500c0c41880c080009040039801030b6100c44011510907041c000d42030b40c4000382c002c01e0b1965080800d10907103480c0c2c41d1120080c884184050051940c084002c0c21403034900f407505101001000e075050342940101c40004180740c942201c0004005540700343c0e20f11940c025030072500e00c4103580c4015283d2041034056510141103061042c0720100700342d0010320400030700c01c40700d00000080c22048070104441d9044007910b81c000340c008100c0100d0180d000c0760040504400032010034020303c405881049100704483c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 933668093 1250 933666843 933666863
    0x702040609060b03010602211902070503010c091806080c01050a030605060a172503020906040b040e0702150906011505070c0e071b020d020132070204050f04020d 71
    0x454540303400c1000201030500c000c0c02480c0d103807001d0480603002402604c0052107100590708802c0ca0445c2001d0580e000a50701e6480e2440e079008054a000c11450740704c082d4484c2c0c031000181520300f44a0b1804000c0c40b50790380c5401c0350800d90081c1c60b81020900c04220740f814280c0910516002007034004600100b400c1030b6a85255a1401380d001d0b1555900059100601103203240d0305e25081406001607010364900c07022141e55188100e200000a050080c0040011055903104507009030300500a1403c003c00560030306944100d0540c1686c05a008100d65000b02c00900007103a03010401e82d03c081e4030188141110380b2304441d0841d640e83c014030032180300007a50301c0450319032800303201103a0380950003400c10f80083d501c0d200c0c0c004001006440325800211079911981c4000c540c4c4598600096004001950384c1c0c0303003a001140c0344408120590842a1306e4001708826414001c9043c803c000e02d50b198079100d04440c01000110354000b41514801c03070005c000c2100503520240c60080a40d402b00e0205 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 933669343 1250 933668093 933668107
    0x1020a300b0d0b01060c021003090f02060d240806010e13120c0203030c0109110f030a060203061f0206160518010f05160b041203020a050a0f0512040f060b0405060d08 73
    0x1000206002c8001c0c0420f844040046405030b40304420b03800c41070080d1000415002031010803070440355000b002034440d14090143e1001850420010031519a42c20008207681420303032120527000d00e00c1c0c11004004104407104000401050040c035006003c0d0500704c01203840c180410780c0d44107a810310000d090131222000c5005190040119a0000d9005021642c580e0040750555000f000301c2c2c075041e22000c1170103d024004e440c09001d14913040b1009409442200c1807981c410001c0c3d003000e047c0c02e500040d1102c0701c1000b202d543c9560720b0304070603030340c000c01c0075051220780540350500f0b690151080000400a1005c125440e0b000d411807080c080c070b00322120880840003100c0c18040d08076112800a207075048002442000c500b110300480c010091040c3c5e02001034025012440381c4040030010540501c201804c0358000c1c41100c8803d03885040651078034094984600c500b9004480c00c5901c40c01040c441e0090140901c81c000c203a01c17041d0b404110704e0400c0350000c0d6804044220082181c20001403035 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 933670593 1250 933669343 933669349
    0x70605070303200c0f1f23040c0e010806060a1401122c1b010c03050d0501150206100506091c1506031401142d01060201020a300b 57
    0x100250021005408401144075103c4802c2a40454041c603514070540035042c010390800301d1542820348100e000f002d207219080d1001c101074044171942c0d038016101c0c0c491541c0c00c0b0205008030361059105400420b03060307040400d50b0103c204181c000407000c0d400b41c0104032040d164042544243c605801041e042c81c0707844001268000160303a0304490060a122010442c2c1c0c410200c00d038100315208480710802519020000d0380c0d5809100d4004400b1000102e41e05154040c5c503107030705c04501901c0c0c0740780340c15203503140141520000e0388146054840d0300a0541c010754184055900b040d41c00a80401c16403424002034040c0c010400424070442000754101c460a04a410201c0410b034406d840c107118144091429000340307003034481580c611a00c41d121a440d0541841407404615094000300826100e6086202c130300005c1040d0549407580e0658444552100303546000d0003440309500243e030f11040980010401441c1c1c00c10415644140e5102c0d0001d804004024501d0b02088900054520071540c00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 933671843 1250 933670593 933670601
    0x1b0906120c03070312090602010b060904090212060c030a0b09060109091e0e030702040b180a0203060607140106050a0531090f0b100b0f160309051e03060117070605070303 75
    0x112681c1841204030000400451420000045d002603c5000e00ea954907541a404d03030300690702c01a03220201b040a20700600c2d007540842103060014008503042c0303102070003140c03a114083c3c030340380c0b0395000c040100000c0464034003903440c1c0c003103040c0c4443c0d10b1410010006000c62a10b8050b98804d2502c481724901450079003a0040310b001c190280500a00b42e0148802c0d44907031107640243c0c015820000c0c80141402c100382d800f0405043d0698000082d0780385107006000f90806009151b00070000c20007000854003007a00707000510b0941d000020307100c0c5003908001e012429075102a00800b07042455940300c42142c180d04c1702c1920510301e006903881c0c00f00b20990003000180301c0100402070070054a0180641c00502c180f03c4d415a401005942d519484109441c0c0940d06200400e40010041c0e646001810305c1c1030a860b901c01d050513400d00c0c2c0c0f0717080040c012102050f65254242081080904642b408125050051410070250480c480c402c7c030710580c84504a001e01d009020000581030f082501c2988 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 933673093 1250 933671843 933671863
    0x91b11010e031201030b091204090b0a1701050603060114010509040b03031902030408071a0f070201030b0a09231e0c0c16030203010e1204060318140f1b090612 70
    0x1543d64500d184640115500750a01060301c62985450001c1c01c0e40c84005036054010341d034240e0403800d06140c00c41640c05480b80f11203c43d00000701600004a1a20030582c042503402454008101803030008249440d00c80148c2c448004c050803000420030070390300a01125a015030555003c121000300001203403462003010112103c8030f0104203440038071540030003e40143d03407904064858503030752408018100c42034a1408400c4c0541004594504403c000041c000c452042c1404582d044400b4001a14940582d0143c002907441e88000d01d509007a10680c5580040340c1068890300e414480f450500d01d88984140b9a281d40c030000c0070070743c084450700c140c542c007c4000c403c90b80c02c89041e04032500d401c030252104a010b582010b903031204400012442e82010351011061604042c0303060412030203001c4650a20700e00200606a480c0890110492003a100001500800704800070000161402c001c07003505a4a440b50340c00b000100d41d8030f42044c25000501140d021111001200c1c0e01810400d440c070b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 933674343 1250 933673093 933673121
    0x3122a1e0303050103120e010f05030a180803090c06131401050d241d0a02130f0806061804050a0219091802040f06060e0d0807021008040c091b1101 65
    0x54052401c2650503085141624411540704039480c00510342a03400410800203130340410040d40c50300072014411000385078481c84000b008903910b032180030b050801c031040d01002e4403203000000c00c003c1a03e804200001041c80140c8541d49071094800c150b1003094450f00032120405684c00f0307075803466031040c0140e486200c07035484c042141d0303007040002e0004400d080d14034200c100c40620001a014012640034404902100c0711003080b07a45490b61000250301c2131002d125680f0f01e0040100d105403500d0400c10141c0ba1003002401141404c80812414142800034000303a01001010000060000b044204100e54140c03a2040340041c003286110807031126411030070940d40b8080482039940300340d005107581c4034020384040182e8011860a4416150b0900030031011a0000c02c0034a00c5041107064246c1e0300c1d024502c82030078020168001503008070110001e10004100351700340030501c01c02c1410340c001003842010030015600007600820300d85c80ba04814005102c0c3c444100071900303c0070f4000b941540060 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 933675593 1250 933674343 933674393
    0x1a0a0e07020a0803090705090c19030504020102070b130e0a09050a0609020d17190206150d06090b0c1b16030f02030f0f010c0905030706080117070b0304060603122a 72
    0x482e40071586c5407100d00c80d0b2440b400c9190049091414023001b02e5018000503c0d1841c0c282c1458035040c1d019001c090000c80c114412a080098038002c0714000d80440c0280ca40b600c03010a20305213030b07001c4440307000d09036085140c5000a603100090002176190221640001c0201d5441070500005907110b6162801404070860036800c500010743c0c140c020021b491101d4040c002028803003c080f85c0c5e1742c008a507c2c101854091560345144c0c035080b9801c66040780710356404120070900342c0c0e40c014208810b43d040c002c819000328071035035902c1030f1031038045403000444010204c1000c01c2c10403806007012480058105103404107280d05549003400440540140f2000300c2d6041c2c0030f40900b060090101028071000074222100c08030b214a400310315035044400e240d644c40c031a0790030840c640d45030040c54111481c8074440d1000008a081d86840998403441c01601c002410f1842e5040408020140708030202c10014040701812111801305808a03507078030141901c01540500c0d2420010b0000e00810100e001c001d9 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 933676843 1250 933675593 933675601
    0x1e030f0a0806090a1a1525020102151005010c031e0801091802031222030b0621071806030203010906050901110403110f010c0206030f01091a0a0e07020a0803 69
    0x14014050310003903e1083e0315680b600b411800300d4003061040315070002c8826200030b2500e402c52201c82c00041d944040e5140c80d032120340b04c038054134510925820214a07182c542d415036030140a2080c00c2a40c25841681a01c0c040c4000b5604d413203503004a0703050040b004124400e16126480c8140c0000707406211f6000c4180000003e07069030000d01c01c46004605080b000d980740500740b0754504000d82d001e0010400c01494070511411900f0000364028499060013410f0b40e060a8050490000c600510100000381000c10621114a00d8501d0003250841116129602c0300741c001802412180b5009907540810a004806400b81149502c040e51660030b2108510074018654441801013807600c008010450061850115034000d41c4406416103952035116215810b11001803d0103c105141881a8034050380c0004c100307030002e41d9030300ca510082100501032441207103d10780303600107408840300701c1d0106500010380007182070017801e0341a40d4507800f1505c0365000700441907001d9800280b081e242d1070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 933678093 1250 933676843 933676847
    0x80c04090c0c05060a1b021614240a08100311010c081306050c1504020a06050f13030f06141023121c03050c04152a02211e030f0a 57
    0x103007050780d0302c2c01b10036a8080008240009050040c600c9000c0594003207525040e152108180c070b160810360000a0340540d55075061018030140450070326019281d80b9192040d0008004200003881e10007401c14400c3e061000c500b495410440004d02481c200d029500c461901d0f040c0c070b00400c0361004030b5500d498000b09100750402c02500600c40707040201e50003001865071030704207020f0030386010790030403040c403000d1006c544140c00074400364003c040098540110312440140e100079076401990007182c00100c58080246601400c9201140d0305111007249c00c241ca0392500ca84e143e03114040c4a6580c100903204d00c0303842203c1e50500504000d29018500742c91110403601c0e032103903460040759900103007081400300340284a064080c80c0072000460030241000c00001d660000c01d203c2006120301c240302d1a0050030911465602c01c0801140c03551038203000c2c410300c544242e40c04c0001d9031100c3e9101000380a1071002a44075082d6240c115200c806030036650031907040d8494101c82c80b014a00c0041c000c82003507 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 933679343 1250 933678093 933678101
    0x403120c060623090403050301170321061306081207050708060f010620030a03110c160f050906100309020a120825020f010503060112050414060106080c04090c0c05060a 74
    0x42d02500d4150750140c00300208215103400300c0e0011b010036014001031200341d0006800d50580c100950481e4540704200034030901c2c100707100c8a42c3c00044000c20400c600b84c1041052040c1c0c81521740401c0c4070282c100b01140340c4809122070343c840c8101012801d1814130104122060007081c030841900c0060800341070040c10441d007401450085980240c4c0d1522410400c0074901454454201030360509801e240101c1c054000b141c0c22a04000d030a100992520310f040c0009480304010000c00341600b4038000502410101c02d5016074030070001030042026030346620503a84460607040c41d000030f00b6035044c400a070400c4501c1d00011425504800588100690788004050384c8120341c1000401081075481c4624034601444000d41162070311070510100c0d40210091600200c0c14185202184070403070a541c1183c0c0200c07010749440802c07803043c8010010900030a800b400a52420b0222031800e0121420340d80b18500c50440c1c0c1a6031030441c2c0c1000351144801304c95540d848030035a01c0c0da0402c3c0701d543c03000e0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 933680593 1250 933679343 933679379
    0x320409050c03040314180d170a0804110f01021002090d050d0c0302060a0506010507030c0503040b0d02120112020a1712030c0d1d0a0b100504090f0b010506030c0403120c0606 76
    0x40b621115045a020344010700742c1ea050402d06107446d43d0100c0e0541400803001c00504219414080c00070700d280c1007500342000c1c0c1040152982c428416184c0b600b441c1602030ba0115095000751610280307000d490760301040111803038014220240c1c3e551600804100300d006540805030890291042c0140c40d50f510031100c0308540d010780e0032225603866010f4000c0480749c050b00c20b1408144200401c0c3d0000303001d8000038203c0c501440c103590410f0f688150340c0c80160302c40c81500c105150300251002204c9141c95519001d451070081b05030b05100760394041900440346001d00b070440c102c0c050312000112010449074a640707140400e41901c074140f0052100503a044a01021101410161040000d13140d1280000030203210000400f8100416101d90b6400d101c00742030710380041c40c4a800480c09885034042c03c035400380304904900352a8058180a042c2c1201038020501c140300400910404d2610b07403040d01c1c2501d401c503401c10b400b110350000c161555644481c0c000c1101d401e000c0c0004e09140d88030851419 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 933681843 1250 933680593 933680597
    0x9010c0203070812120f010e1801150f06080109050705070212070305122701022d0a053405010305090a0f200d080301060e0d05070801050115320409050c030403 70
    0x700d03142d1b0040801d505500740100d08022130f1440000e411050340809482120403800b000080c5600000c02c071804450036a08908600403001e501000400d9002c03101e10f00500300c0b00c0c0d040009003010000200640308542d00a4410342c2c6c51403c40e040301106000180c004e652000850b12411817450f002d416980003c2007040b001080c00c40040000054031000703081070b02e03050703000e007180d611040a981c0c009924001c020351a403040c400302007044034007000142003241c001d2006144807c44100310b40030300c0e0054803900001b010700052012601c4007620707181068901c2401c0c04141580c444102c80e00e00f0b00c00c2940075005040400464051142c0f00c032503400d90b18070040f001c05038a0040702c1444210007103407a0041104108100400446200300f250a400c454000c00d24000205141c44483c586a055080304a0700d954450040140a084150002c181031260601c0c20141540f4000f045031080b031816500540100243e034000741c600000d0441e005440d01c0f000c100b189050000c9004887c2d0411601280 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 933683093 1250 933681843 933681877
    0x1020a0f090b0a0207051909092a080304060c1a160e04020403020d080a02010b1207051e03030d0c110f150a020702061806090402121f080309010c0203070812 69
    0x14012600001c80c1c500b400c83d40c00600c071403843c2c2414000305000e03055144811005031900800c000c0d0701401aa50300c90f008207000a501840e00907586420b80c04001515141440742030200800d0301c0c0801900c045403d0390620449080c0c46062111002c41c10100404000100c1d00410440f0b46d400165561906907640d5800c01d01400796061004900c00c60001170750010110110000240400c0300500b0040040d10000c140000c40c5000f01c1c440000d0011068516001003500b44101d0404281800346681c0306200320f80d4400c90000820344901c1135100f41c074112500d804410f9041d60041079a5420145904200c81c034540c07408c4070054455070721801c3c502811040e003010944002d00c90007543d40894008140c03500d8444d4841c803550140038041e0807a17402000a0110300380c1c59480b84058079849011f0040c11601d407501180b2440ca09020394400700c950302d9694030078401030388008150b90041000f03082080c80282d00e80002850600c41c2d9000c45001d110740c8001d1f60300c2d0f1130f11070302404090a507050592 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 933684343 1250 933683093 933683099
    0x6020307061b0e061b010c09090b0406030b06120a02060f18030a1a090a06294005040c0f0923040602070f0302030408100501051f090801020a0f09 64
    0x803460355040b00c0d1400c0041c500080415481ca801c20040002011245050030a00c1c01d0301c500500356010040c0903c04140c10080801881c10240600104004200c0e02002101d007541d0f190380900c7e50151188d402088142c0b901190341d90304002c030704e8032550020144da8581c652203844400c60360016200d4920940303c03803c2d0401034100002c0c0b0100d1254007481001d102c424606118540710030041a0b80d15900c02d5506a10120702148190600302c01420842d2540704280d804406d004402d1209150207400c1c09810100d960003800030065400d860f460f21b6412810f100a0300500c1e9941d0b10380107107600c038500f0082c082040100410001111903a02048810b5692007042030b049030110820400124102c0348031080484a2100c50b980c810301c140c00060400e0304544400341e640031005021405a8800542404028070410805040354040c44041c016581003c010840c0360340340d00f95081c40700e505012240c0520f40a030104070042c0041500843d1111403143d001000d030106142030b9404078030804004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 933685593 1250 933684343 933684371
    0x40e0a1b08280c18020a0806090708010e0903071a010905090d14130b0a030c080114060f0304030e1e0108010f06020c011d19050405060603010312080408090a0602030706 74
    0x1507400b99000300045801c0c50100003114405001c4101154414101d4401007699800020241401d000d02840180c588403440006041c03200041d0085100355011001c111240768089459410766800c0f0f2909130481d15442c0c40e41e45036008003d001041031003400300001040009030402c0741240c51700b44040c0b006403205400242c6440fa420103003000503410196913002114200e0042c003000f040403030881314880e5500620f640036041000c0100010391100302540314070780d0103100c2e02c0c00f600e95400c0c100e1200c115040041c1d210302c54044d00d5900c62a000c40000c007418010140c6692450010b061f100d0442c80c050209052044010b000a0100703182c0d80000c00d4044035032492500f0398007a500180203184001c0700545900401d07040342070f001d0207010943d21040c1c5421030500300801f241e030441c400c030508010401080e10402040a80164010b00040002c2a8401846200d26840d820140381546481c1000fa0440c482c494a0b140c20500141000565550010040c40d61074020031081150541f20414 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 933686843 1250 933685593 933685603
    0x3050c0d080402031504050703141006080115050409062007120305071205180f0d092412020d1107110102011506050c03040305010e030703020d09150c02040e0a1b08 72
    0x10390580d00c15240d0034205c2074201d6017a5001070140c0c04130754080d40c0d25501d1400b004402568800310360030400700d8105084050081d003020f080d451000340030540c882e010a00c0d0821580c8103c81c411741c0c503000000c0500407e644406520850310961006865485e40051110740c880d0208070303410302d01c02048015091082c4102406074925554a0580060809080010b0100540042c0303a00060074914110210f00b0440e00103070520283c041c09692000395800b80058117181e200f10421000c41c0c2c0005450018010b81c1c60045440b030824044c040f00302c0004800a000703500e4800d05c0c0624111000743c0f028100c10103003d0503071081c0c056580c4040501c0049090700c654000803a04038000e03540c10302603a0300640261940c5070705d0308110f030308099480d12024207440241e8502130540e00001400014180c0c14018803036801040c3c201a00310f01d2500caa80c0c000c80355040c070351034200b02c0c8001d403840455480380c000400d440d11440032603808181034200b180c43e80ca112600c1400e0402c01000004507a000032603 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 933688093 1250 933686843 933686851
    0x303060825030204020304080921010b010212040b03070917072c010314011e0501082a01080601110303072001090b0a02070602211b0408100b190303050c0d08 69
    0x81d5403030007455903080c00003a410241044414040c28800e403150b5403540603041048203081400d126105503070b801c41b2400c54010000050440d0031003041000d400c000402190100c440004415940740d803203400448a41c2d103035800000c0345500c0140c404a2020000451109480001c402d0418031f0f44503014104020014050010314801d110004201041c4813822030391083c445140085000c4076080b01d8521212054400340800aa807030005021001c400c0050140860f00b115244140800e11280313500035204600c80d043c10032482d04002925030348120340c090101c03040b85040f25100e00741407102a0060441804100007011440c240070031001e814004c03008000d0304a103c090b1103440d2280f0b40340195005003030903a1070a8003000b41d114001c105449410110b040340005e64081d0500c21980c4589071511020f10354905001c0c00103001d04100070941100401c404800007805d9003400b000316200302058400e00c1c06141c15410000103050300070005210308459942076480f0903401041c15215481d00355 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 933689343 1250 933688093 933688153
    0x8031804020c0a0f0312020705031801022b020a0c03030e13060b04140f090910180b0c0a17010f03020406050604140607080903100921140a03020d060303030608 70
    0x3881408600008619000c01d170280c60108890306480a1580982c1e110400c1100d050b07000007134a1040c11101f600c0b0704160320091000c1c20312604c20b21070300b200140c2001021140325181941c0d4074802e9000300030300040d071a440b1032449460f5030f4030700700a0407814031f034144240608420328580b186103240f84203420940703485036806401d043c1486121070b810a148550290040e880c001d00e4603079559000344c036a20036460f039402030641d0305a83c0c1c4500107480ca0009902d084040150703200000400f03075009030398412000030300152640d03c039003c00c43e008803141e5010244004098004200300c00082c40c0e40c801e5a0095406103c81a521003d1080a11542c8503545500c2e414001002c0d80345800401417100078081e403061400c1c0140c03100041d041c02104411a810340d40e481c01036804002c000080325000000e840d83c0c0840010310401d000d010441140d0740060010b00004031907550b14026419900c00200d019010402a0745030315014000704094095402c0501c56000303410800c00500c044481c500681c6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 933690593 1250 933689343 933689353
    0xd03090b0a02010612110315041e061506020c210601150c060f0903111f051e01141504180207142505032a04060e0108031804020c 57
    0x6800d0005410141c11034003195212070b0001415001601c20340c2c046030081449594000e80e0b4420985020020301c0640354040c40f100070040441c0107007085c0151200140403411030f1803084e141150040100e40b0252040d00940c01c808034080303a0002345074010920649044491000307018820030389040c42c8030300340215403005005000d800c404607010540950700c0d081040d0696030950303a50301a60350480d0070000050755415034034281544404165201c0d404000078040d00c10000300400102401070a0207038a16032540c0c04100e165102c48034610424a050540700255611902001110510035603034502c40c249400c803401d0050405000c540446151403091403904550703070302500294005410650b603650740c0316201911424103000701d003460440443d41c2640c3d0340320080040d000011356000345005c1c0d8094610b5242100440c08c07942108094001d8241d5001e89100000300130340403d402c903612a141c10400000c1039080000070300380c000348e02c5103822502d19a0000340001c85c05805121041c035840 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 933691843 1250 933690593 933690599
    0xa06060b09090a1802030715030609060605070605100b0c0601180203010609031118010803190e0d1403040b120a0509010b010801050111010608010c050903071a03040b10081002090f0d0309 82
    0x3e107078044107141c02003089841c0e00c542c1c29000070742031070101c0c1d00c07002c4181c072840c01c50340d034841c0c1c548202c2e4090003907000d00b008482e080c0300d8020201d0184060003841d01350346c0e80c003166000c14103a1424000301444c02810b503682140302c9071107499807000e100b01c0e902002e100a0b51401504c0318020b41341aa800b03039440c02209851a01e0744a18800c00d4442c4540107030907642c114910f102c0034410340e406000042c1c002c40d0b58801d01010108450348031502102082550b481c060070580c0e0f0b00c10b17085a0150004900c401400c210805907086200701d0b401700403003010000384030b904900c103420b1003442141019420000e42e62509405402d0300c024400d0b441c005900000148000d600861125034540141400001c085e512488503500312481d030a004400700da408104803180e85001c02000b0003800310042840c5040081410015840c000680028903000b0f4400018141d0800c008140c4000c1c01c095084034000c01d1296042d900070340c800f80144e40101076a00c101c1440e0f0600c121015425030307041d031720310a049107 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 933693093 1250 933691843 933691861
    0x4080613081309050403020f07030803060d03030b0916081b07140c04052e0f1406071a04020907030c020a0201050a0c0206030406050108190f02150f0c0a06060b0909 72
    0x124080044401d6a010700841100e01c0b040d10880780070341080740001a40c0d00b800d0401901e440820580d101a90384000c8061000525440c19203400c08401d5a150454100701d180540c0940b03515200309410003402020840c40c201803611980d2181c2603a11a14526282c40c440c0f01c0ca12a034a18181404010410400000805408810f4440c02e12070080c0e600444a03600014146c8105a807000308005104003840c900c0c4480c000c403815140c104c1c44c180d114041c540204040200c0c0180b048804071402d100220300746840326012030b40c0312a4413110840056481c040088900001a5000c0e80200400310028410a0003881100071503402d540003010102039540c011030b0180d02116200d000c200f1070012490041e11010042c0d800386204a501080c00d60601620a03c0c2c4142c0111528000c00015000008946500c03407143d4055019038101075080c3d1107203840d048038855030034000589540051050710410300403400039580d9210350018801c0f503a443c0010180ca014121809601c04018404034100007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 933694343 1250 933693093 933693121
    0x7030c060914060a110c061305030c06010e07030c0c1a04021c0818040519020307090b0412030e06040f091515050d050f01060f080a0e1009030e06040806 67
    0x80d100d18004940501075030780d90403a540d81142106001e82c480300c203021051381ea60160b03030340171809500300b141044901e20781c444da580e5020701800c03882c0f202070015400707001c82071017203800c42c1008a040350503c1d60b58804403590080304031240745c0024500400944024402c81d91440101c1d0808209542c2e1008a00074015503003002c0c100f00d0780310700d40279101000718000703c0045200d14021481c044d20f5500103c01d0300d182282c40404a0b1150b0f1801040284840d001d81a00005c1c0d085050016100d558000d400e0302c0304051074103c03c03049007000c10002607900c0210702140105209030344540080300e0304014410a4000c90181e071840c1c4192100a1013200700306d6105807001c81511000c80c1c00690380d80b0342407c0d156040300101c00010000507154681c2603c030f02446801c4501c2010710315040d0f14003c0024000c4801201c0c007020800c81c907000c038038100c0c07103908489081c0c101c400a0b03444000da00821000145150841103000ca800211244072a181c107200f03a4007140c02c980003414a0340c2d240108020340c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 933695593 1250 933694343 933694367
    0x2040516090e0709140f121612020108195006100c020d0c0806010b0a021218100305090f01020c120c10051504110a0903060c051608090f0d03050703 65
    0x228000c42d0100c45503030381c7c1c0040c000c0c20310650040d1031b210303101420072610350342030782c100082c244450014080180d0344441d241d94403510b03898143d04402c0c2080f450401500303000210a00701c444c8068080074100799583d21030304c80c3c00c860404051443c003862414460303200c031044040d56088042d00007446130400400e010424011890000f051090650010304035000104094a07004003104d42401440403c02c00700b400340000c06d12244c103110207801c00070b581e222081c04100c0b24a00200d104820488403c00300c42c0e0b490b5000b401c00f0200140404010001d003022070f00c100e4680308003908807030b070a1010320890b001c42c0010805403c88101c00020041d10341c1c4650780640c054030460002c0d20156a203032003554005d90481141d1340705c003002c280400042d01e9580c44100d84d07185040141c1c3d46042d0308141c3e4441100d034401c1c8041914800d0f0b440030f0740c0c0340c0102c07160421003107404040c08007002401380040c5407080089803016900f400e0780040c407001e2101100010045981001f0941c0440c0c0506071070428 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 933696843 1250 933695593 933695599
    0x1909051c0201110c070609060804080306150702040c020a05060601090305030405091e0702011a1518010e06160204140c0732160b0c070608060d02040516090e070914 72
    0xd94120741440c0103159028010042d00c030740201d20141b00455200e000b80c0d00910381803802c030240341000d03220b80f0304034071024100520903400798440201c180200c1050b100d4040c0c004204128441b940701c03004c0c0d12030b040400201c0f054014000014450b40c001c3c0985d0058a8200008506103401c0a05010002030081c0890909480c183c1601000212140306280710b000c590740007242c0007001440c8024524105423115101c2c06511030810442c81e21041901d003034260100d201c9100010b905e006803440d64060a5040e00a40c1c009039204600700590a17142c90a4030942d0300b00f0016000101840d180c1c1019a400c4051282c20090080403c040740b0340281c0303008907001060030101d402c1d407054903501c0d1010008000c0307411403003024a401c00c60307442000003080c4422034145001b40c0c0100e25900c42c03c0b54015101030041a030041030700d9866039881c120000d540a003080049041602e045600c060819100b000001c181c05804503504407844100c0f80602c91503210100c07a5424103590414a030711203885c16030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 933698093 1250 933696843 933696851
    0x1f0c0f0210021e0115171908040e01150e010c06090b01090209090609040201050703120b3706090506070510020403050a05061f0e040206090405070302030709090204030506060114130803031909051c0201 88
    0x51f01c000d0500c03120544121540e55a880c9004040300086505a20000c4c40204400741079940c80d4100d4400e140750802444d0034041c502c001c0c0350040040c99400300203843c5a10b100300204007260242c0c0144612001220a407500313569030001c2200c0040c0490b0000c1c0052006d004d110006406075500d4620800c428402045052014010075020f00e82030000602184920b14880395060452044814103005070b180342142c0c2d828910090540c44c00c80c030407180035010003d40881401020300c90310440500d039070380640d80e491343c03030904035035840007054280c905010741004111010503c0c19078010350b440751010582c54074031304000340e254803100420903a04240100940c1015540b244140c5205511a4800584a00340b48000a1640103182c01c030030201d510402090021410000d80b0550004c02460700c40e007036420300b135200221070003108140c000303100c2e0600c0c020400b200044051807280701011100801d113001700c40c000c4280c400b60900506141c010400c13682c2d008030000b50107040400903000102e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 933699343 1250 933698093 933698113
    0xe0a0206030603150712050f06152a030a0201140114090726040c050d02010804060b01090b0c0708150112121b031d1f0c0f0210021e011517 61
    0x104d82c1d1004503080700014401442820b010340c118400c05410000340314940c500c528144003c203c42100498001400f00800b01d001031849070640307003085400c1e0303841c8030f6406907050002c9030654030340181d250038016509250120100d076041100d0b183c1203913000d00e546000060380034140060400c0150001d002c11400070302400c2c0307070318030100d00b00c0c14008082881c25141c5400d0514000400311a00b0651080512660b900050703a44500455003290300310200082c400c0c5103000503110001d4540c4042003004000c80c12500d0b6000100e810b00842c1da03441c055074050310101761009100c020900401581500d000041000704052003c0c01d070034028241001121384c0f01c000c0c400d941c5289294011800910500c02554010204140720000c1c20425030701c4c004882d541d5410107000b60302c0c800142c01000841e00c003e80503c4501d440d4060358a8010b00713030721002081e030349009455a00c5014420059207498840202800c0141b00b1545000c0d05456001141418640701c2c2098102d2000080441d100d103090075 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 933700593 1250 933699343 933699373
    0x1835010917031501090b0a1b02030a0b0f0105040b1018050a150212030c070209040c0b070818030c0f191503090510020307140c011d010c0e040e0a0206030603 69
    0x1074105801c00c001107840e40740500c8015242c4594100840c1005500039007007120004c6041030358085130a50402c0b01ea5039200c0c00b240001201b605101075858800c1d11404800d219821020f1401007407205001c1509a0700c890600041c4c85c00c13401039582200011f40e09400052040a0a004114403203c550040790369070f0700002c2c82850141c00c0741809031b00c0c1c4200b40f021103070108602070509142c103880354294640088051100c1c01031000c0a401000314000240800ca891415500540f06011074903441c6d070780fa81071001441d040608c0c4480031000101c1420111b1a002941040046000340710104503c1040c041c00084503910051600c042140384002c108001d01d60104240040c06540000e5400040c0c2041ea24000700c240c1b400e4495441082030082250380408051034140455003443e590b0071134400b10318010411100100c03410000e1a00d582c606040640202c2c1d40c03200ca5658064030140854104003c680d22076080d9002c643c0003040000050900c036010310340c4050300409981400c00841310b1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 933701843 1250 933700593 933700613
    0x311040b0304060f0e16050315010b16080316091e0303030e07030f0503071122050c220608100609051009050a09020901120209091308041518350109 65
    0x15110709a04600c00d0112500342601b465001440300314020a80d44020303444203144130f00113021300c02c1300074800184035451588070030300c503100c50303500c1b0380c46550760701d0b260640e0000080c000d80c4020000340c01200004018008424903010b4144001d522802c0e5407441d6801e400070300506600b03544ca801f84450000208204680125905005070040c41c1d5507105031808501403225034150502c1100e101700b0007814524800007008064416031400916030b11240000c6055024400356481d43e02c0740248854282da114240f83c000700c56040c0c1301d84095888200d03100341d032111a030041c0000507048020422062901e049501da403c1d2072130a2071148140c962000c01e070004210b8018440c84c07500080c1d41241540e2040306641180d049480031810001580c0004140c0303040607002c40b803105034006961017405110001ca4004040c100014400540308804c050602c015181d800819118042d01c001a611510341c61042000c9943c08c180a00242a800d541010410000201c2456680d024a00c0014182d120 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 933703093 1250 933701843 933701861
    0xd09020a080d02150105032a0a0f1701060e07051e0409050718050d0b01061d030607031a0402070309121b0b1c0c050a140715020306030d0311040b0304060f 68
    0x4040e002580702c4d440c42c0110010107a100b50b0190b84007880c2c0c801c48070103040b001461402c0440c03101c03000c0da00076000224484c07860b400c9581c0c80050700e00b001501d5103180c0c0141c6a42c1c1136000c001e01043c2c3d031b50300c4900c610000440700031010800410500e521000b410000d1a0260000c010a508058a440e81c540407a201142e40d03001103480b2070068000303082e82d41e0354140201000c42d0440d0307441116907212028000184038100600420711711101400886042d0b841064402508483c000d10b801342c001000b501e1070070651100c410303040e103510510341014021a85102d405882c1ca43c100c3e8034082210300d199400410175501c0010701d600881da4200c81070000402450590056030b21040d080000f06007149400c40c031400410318001c408110b49402400b5604509024207048080190405a403c05480f4003130004012a0107412940d00280c0e40c5d9001c0c5004180541c00c607220f03584080c805501700d0303042410048007608140820082c0e960b03075400a59102e8410040840c56584a010701016200b03951 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 933704343 1250 933703093 933703097
    0xd090803131406040203030d020d0f0c0e01140405030307080c030f0403210c12144b07110409061404200904110a0f17100b01050d09020a080d 62
    0x72640030300074040904891520a54040c19050902d580065660f10560f04c5201613940c0110344078011088940c40400c40c504200c00600c00086400740050120740703004889804203071000211010840c0c0c003420b50b0207841025000b1440e0008548500c2c1d6181c00c8030b0103407405440b0130421010b04421200240008500c01c2c0c149100200304000c0315503c0040300345014040056035441d0b10049035101050083e40001c41c20031508d40a54134000c2e1600c0d100b104010740d0014001c0205d00c18000b00d2400c030100c8456403500460402c000c0689025440300002c5c601d00f204102401050003051000d0010480010020000254407440c3c0e5294015550046901c0b04200c0c81c1c0c20401c03050100c0d0140130071030021140c0c0b05124640c52400012003a0070003410107001120701c1e2903110318a03143e4039080c0024003055542c4c100c1c055032303501c81007683c1c112001e010281401018000545201540156505280161a600d0403d41a44a510010b0480150a83e40100c050400003085c0780d00340149000d04040b5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 933705593 1250 933704343 933704371
    0x13091e080d0b061b15150915031c0e1f02060a05190504050c100e010f080a090803010803040f060305061c0c0312030e0717120d1b0e1003060e0c0d090803 67
    0x803124040046800916010003040b08251a40287e65041c03003241d4030188210204072040c440c83e0100e490044401c19100340c0d181040000e400301d940216081400180c11a00041031200a00914401c03903c40c10510380542d102c40b01161038544950032850740003400380c01c2d110900c0e40e610036010035600140e40a1301c84e5009034403940c08031708041c511445030181500381041c4200034000000d00404140001608218030800410355841d540e030401c0515a400100082d180c0d610741d1260381d1258890711601550b0250711b100025014024000c0c2841003400610b8003806d0318505c019440800200d80088460b50742030140030001900c00c1d1142c6840580c07690700000c400754200034003403606070150002848a000a40d48042a0300005880a00300c0c1c80200c8071621013100c14640c401421368000780c040b2070944542c18868a5906c16810003107890201c9075a04e0301041d81d40305404407001c0740102d44034523034040700041481c0301117001040d0171880584d000074100c10340d4440018a40003078031011214a90 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 933706843 1250 933705593 933705613
    0x10020415020610081027060c0801080a081605010e0105010320030f030904021b01180b18371a10140d0c0513091e080d0b061b 55
    0x10400c24560300001000314114140c0c10114010b40da851110f00c290034158039120880411219900d1264406d41d4004440d04100081c2c90580060011102d43d82c00040694000045076038002610844013500301c41407030701d407200b420b5039011840d07c80c12041d0303282d42d01c84511a80b030080910a5078001c602541e04d641c01d52010b03031808101c80748083c000030f100c0e911104d10302c6000003022017201c3c0c11071030450b80142e40ba4400d4622075030401c40280100c01551070031421860411111036400c00c07081c450561420a0b40e0740160210300b8440c0c41380c40d00e14540c4524462a0240011152400c445d0340034500150710451114001034078a01e03024040f54000b45800c203810203d1140001c181c1c00c01c0c8003110354042c003400c1011031412034105140c00c078802c0c02500c41c05003c3c055030300e0051028080c0504101c4001c20091b5a0030007030007001c40304941c4191100400641c14052a00c01074125034070005540c80c5c103055960b100080c7c101ca10169a00120400299a04070f49412001c1194264040a8102c48030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 933708093 1250 933706843 933706847
    0x1008070806010306081009110a081b0603090d120204080706020c0f03190615050d050d09061b030309060e1f0e0601140904170f090a0b0403020a150210020415 69
    0x1030103000d840c1071600341a800d0050f82c0000c03134100c900d940d4416001076803006a0601c107424801a80a56420541d550700110f6200c002041d019251140b80c1c8400785944460024000c00f448210f4031880942c12008040c16082e00c40c68800d01c1c0646428005820940c80e0701d4401c1c00c00c00e85030300c4400580d0152042d030000742001d4400c00081c2c603080f4050510214146035044130010b558000130241f80e5611044007070312803d007101d1009490054030100c960500d0b890026034801d60300740d0000108070071140000e04148200300010b40021002500290099503070b0b000d44c00340c00044811a4250340303c5042409103102005410ac4082078041d610000f03c0d40c06811204a609605000780d07260481c80041c400c00490004201410b041030318002c3c2d80e07942d02d05082446c1750360044aa8055900020390780394180e00c0d80050a05d41d4030468181c0421039403400314001620a0b0710000b50404070360001004814000b82c118004840540140e541c005405888170040f640aa081180c4e49260340905e018155 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 933709343 1250 933708093 933708107
    0xd05041407122625060908070b06030f030901030e1905060f07090b07080a05073026060a03080a03050f01170a1401020909191107030c031d100807 64
    0xc5440e10a00d00c0650b01d4542240c1e5201d8901500c0300410580c140003000300d1301400700e03443d003908640204024540761505c01c005a0083c0c20035545100302101249035440e0100d000001030014a0080d468810031000540181c641c400d00900903014154141080192840807400050706c6000580260301e04100c13030a09c5880c004d00850304000e240c410900120f00c684003200e036556080300c4002d4903108a500103c890744a6610000c148800315294240220788c1c00740c4d0b401000c2803083d030003561150301120841e800c0400c40d5681c481480c1008401c449030710300500c07054110002402401c0380c16200c0d141c8081e19800448280d0000b0354070030800c04080d60403030304503015241a2016500622401c034000c1d54481400302c0241130541305844400c040e10003541114510200035000c2521071510b040036500d8122814650103151741003100c0d040d0180010400c5410003681038a41415010407910120f488076110300d4400391040405c030409000e555910040b1400c1d070789035642d0380901e14050500030201 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 933710593 1250 933709343 933709373
    0x706090f031701030f020d06110a02100c0521130803011403010c030b0f010809100f02040504060801060f14010201021b0123131115070507060206010e0105060d0504140712 75
    0xa008082c00500000d60105051301c2c0c0c0380d80446c0d0340e201c18003080c20280010804000c10804603030000500002e00c42c1c0224010489883c0250b041003500202d00b4243d8582c860038604152122902c88600326030048580065001140c0400c0b05c0c0024215940b11174a6078001c2c5c100c103c042507031681c1881286024001c10721100c40e1407805003c032000c9100421030402c0d50b981d06c00d05011030140001e00c1600704005120f40041c5041040c444d02e01100c030207800a40c0140030702801035042090200740a5014095002160800004400c0b0f880c6804040201100800092030465408015050340e110b04000b2550001c000343c8000a2144c0009000400070002d0000c0d84403410007100400401c2d4180302103402e08281c011402d07440c1818210000740201084142c45003001001050389818030070300048900584125400310340146c1d880d1851601050b20901c901c55200c0420400700220b40b40c203800c0380790094490041c0c0d13001d4030310508175642040480d4102c4920760010b82d4061060110b83c40d03e183c89 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 933711843 1250 933710593 933710627
    0x301080325080711120601171b0105071e080a09050f09070e120f060424110f070510091b0b030405100e070801050f010f081c140706090f03 61
    0x288102a640d042e8180520600035140650b40101d1000729100e90300c0c0c004880b5015000d642d202d40c0c41d031211212484102a800990b84104a00c075141450000128140100140c4a0302d0605d0032942c0d070340294103500d92002d461044140395410001d4040c401074036459420303031104c20300c041c102402e0001c41350380200391714400e40c1d03203005004089422075020504c122003a02d02200200c2e400030000d03c1c000c0e10442e5410248501402c00050100750031400742c2d80b031030300d9081d081030300d0020341c910080e40c0e0800c000341ca20004c00c102d40603e64030044000c1101c0c178800c005958441c480f07020581c0440b81151010b5414250801440000020010030340e8041d14030000c5440c15420207417501aa120f48022104110a58481001e132141804010030402400c41600038801483d000441d00c82071102031003550403440d460903002c1011200880c89505401000c5c4100221003012202191102d001c4105001000401c01034800030441c18081c00034106e02a50a4920701e6038503140007000301c1303401442815 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 933713093 1250 933711843 933711907
    0x70311030610050309070305030d090501060609180515130c0806010c0305030a0b0402120403050903010b120307110a0b040b0405030615030307112b02031507050a050313060203010803 80
    0x1c95031441080162414149040d0b0386a54030500d81078603090b032681001d0007920000ca5180ba1504407504105041d512540c001d0180c2075507144146c9044685009100c6020304400c1c520010781c0c4642c2c4015070000804040c0082060b00303902050000011044025403251a462500c01064101e40c041350000d4081c41d01c151502c450340c60040c81404080d06401c0130603207902600301c0543d41c64041d42e18a400c80c844440f02802c00e40303806422070f07000e10baa490107942031142c4440c0f140b41a8880e24051240040a0f61401d104c941d11040701c0104050322580c010241400440c0d0081c0410180024003203e140191b9154108801c0601e031210043c00c072001084604036440c100d407800320665840c0b40e4012010130300d20450b00001031901c441090740040c4042c600010000c204113020b00000c4690081c0c0940e0b4400304800c3c0b52012481c004c40728200819010030201c2c1c1e1481c41440110352104400040c0100494079603184800d83c0e00130f0381f150015520200380505421030443e20810001a1098110 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 933714343 1250 933713093 933713101
    0xe01020a02010c0f0b0c130602060c0a030f1401230a0602120d09150c17040308011a0702040213231305061309060e12120f06060d06090507031103 64
    0xe548003104800203041141c0c409041040044880d904040f0551280c2c10f85500d00e0102015070b032a170000c41001c002e403401108005405800840e403140a10340300780355a840c04060354000d40140900e08200803403d907640100d41404807070348191601030034010801240495203035250000c0700c6d221002d00c610588500c90204800d0783c0001c0d00e4041020329a01064032003503a1580c0760010051100d000d842c03141406861012081158001d18000581c0c3d100c19006055400c880c1100040c01ca80040c0402c05140040c02001c1450307401c80c807004103880c04030f450170506601090a0740c21000010a40d0205407400b4414a80c0710804480c4611204440f00c80000003900040c0000c0d0516070030380c003203996410200d40e45440341180d411440304250001c0c031050201c2d00d0403400820b546140c0c91031a000b06420301d240e004858003101c41f0700c419210700d1301e1f040e00e0700d085030415400090319513688a035080100f61443c4005004100c0100082e450002e810b1a115102600b624041d41400350740305030810800c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 933715593 1250 933714343 933714347
    0x1150807060f020f0a081201090b0f060306271005030f0303011401030e0d080a0c050903070b0c010e1b0901090507021b0303091306170307050a0f060f061d070e01 71
    0x280040700e0091900e018540d02140090b03040c9968510b40300040c3c000c003070001c0144107407180108240e141d189540e8401744e9a9076100d8045503a110f60807503110410003114240752412801039034204030000e00d003221122440d550f0009102004001d401000b01034410012540320300080c1d00d00a003001d0300070701002000024050344a100c14001e09101d012500d0b08030111744d101f984290030310103241d0b00316103a40b0021130011f0001d400c22220560010f0400c012700b10759622440941f890086c0207002048414200407280003540c004440c00e8440d9942c1c0c03001000c8603241000884030550980b005032070841020400c2c49105034058200303008080c01c01007030110a03580040c15090804400c94500040740c11140003d055120b00c812440d070024401d07503440030070a91a88014116940700d003241c8086500120580e0301c0e0300a0b5080941250020100c0c0e0b00407540700d04424152500c60200025034880804d0420120795140d0010440f510361410091544a0b030300a40b1900400242003080380540d01d0000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 933716843 1250 933715593 933715603
    0x1903030b0a0617220803010815150d0b09010221071b201801060e040e0111070312090b01060c110a03020306160c0b0901090516120204091b080f011508 66
    0x20860450000c07040141383e40501c0305080c480142c4c460b4070700c2c0d907d5035200c1d81180c2d21104190508468400b00c0302180030040f40b60304690f16460091b00d00050f00c00b1326203c80100300402003070301c0e90954003000201d020044500c42d00001c01c5164a030b4010b41c0c00d001030002c05001d404580141a5014103c0d030b2008180155841d48882d021480e4410400b4040d0012411200c0044015600284000b00200b01c154001155005034041a2020402d840d4103465050980300d8401d000e03800500100070240c0460702c60501010b100c03901c400003040d8600142e450015480d400da000c440001d8030502074000b00300c0c00c506445149a01125121245400c40e000203440e0301c4064140070041090003844031440c0e0042620000c4160010f800407030138640008054013030000305904480300d01412110304842c100d080c10394001c0e50003611600303000400e00d9003444001c02294200399810303d14a805008002c91000c80b10000d412460301405c070a907450041d25094078003040010070200180f60303052000c20700c0098 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 933718093 1250 933716843 933716851
    0x1050106120b010201021c05090c0316090c1b05030d06050f09060f0d0c0305011b09060504060e04090f050709050606090102100b1c240c1e021903030b0a0617 69
    0x800201182d515005074024428a160900d009906d801c2c0e4501541c0d580c0d107c00e10411621007580e440b00280010036444100c05456140c458041400511441049a00c001a2415541440c00c8082c101e080e00d0750144d001070100715880c1d4000100307282851a18080d10001f404142c0e07800c2c20081075000012022403000340f455014050a1240405583d86c89050b070400139040708440324840d0300c03401d042c1d010742160707101da080c504050380701ca074841485046030382c049503c030340c1d110343c00d140c2490402c460400c0400000c03a030142d140c2c040100440c1260140071481e900c030360005d080062800b800c0c2019504024132161040a052002a10607600031030f85038210040003d00040d80e0303201c0e5000900398502c8142c0404180d4a241d40f110400c1170000242010145041e0707145581401c0048032000e44100c444001e00203100f1070000b000120102c0c003c4c0c502460140151803c2e076070f441c2078904042700400c5050707000a031100f5662480d0b084c05a4850f02601030382c90000d020b003000080e44256220060 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 933719343 1250 933718093 933718127
    0x90411010809010f060806060a120c0306240803090102010f0b1005130b1908090309012708120414040204050901050d08192109051f021b0d1101050106 66
    0x90008000180a42c4480b00c480c004d420100540381c1c42e41c1e06c0035030702d44084600d1800341c01825404034158903403901005060754071070907150806003580d8490000d40480900600c000e030891900c25240d600801521001e40910002181c0360403400d400242524210003010703810500c0d2003901e003859100c00100440c9140707541042d96640969800c0d03503e1f1804950b111071084200850041c1403d1083e203d4001501595a10429161a00310940d0b48030b104e26007035540030618800140f411440c43c66018440884589105c0c1c000079503403103c1c1ca0610030303403181e0b420056100103014050b510ad002e0142d440b10006450131400c0c01c0c1441d020440e02c1d0010700440740304201f285a142c08200b218022100c140b1b8448030f000a0511203d0409416522860391551100e420740d000c2044482035485007000c07003a0044024444200300c11810720940ca0b001849020740c81d020007548201041c0364440700c0107034036040e0003000c01d00c8413000010016a40c40a54000c2a41018010082c480c0d101d03c03510a280380302 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 933720593 1250 933719343 933719357
    0x19080a02070905331324090c09061115060303070b0901052e090b0a030c030b0109050901090f03030b01021905030d0c0908030901051c0f05100501111005090f10050103050c09041101 79
    0x10100311074241c440d41b50b40112080349800881c51803443d410017000c20095482e42595151a204107a88000f051411094a60b1160381100e0071840140f1040350810009070549242c00d003503884811340c1e0f0600303d4600216039103071028442445210b252403042c8488003610701d803003110001952140e101d50b03403190300c8070070352501c0045541d565010079035401180c2c80743c400715907581c0d01d25005041810034801d10303526900d8040040e103140c40600032a40c0c1c82d54448807200302c084840c0d0341078000780b250242050451240c1d40007882c900b540202c2030702c2070328011001140c45012012901e0256100e182c0c40d0010410740755000c020b21440001550540c1c80b090a03c551140f00b2050550098820201c444911504101220015400c95803110340540700341c0c60b02080c103e03181c40055800d43c2214258000c170303601801144442000503840641c200010200744c80c02080c0080d00a403406000c004400801c654507401001008820001c00030000ca06440e401c61350326007600d07a55004c0030502c0c2c0b518144094 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 933721843 1250 933720593 933720611
    0x9080a1a190912110102070816050f060411100302070209042411030919021e040912030234110f030102040305101407080708100b04061106060319080a020709053313 72
    0x1cbc021840d50b40807080480303200e4540307804c0c58018040c0b102c03021400303000480845a4514400c6c001c5075100c5030094914402c80d01e0341d4bd24000101c54081c82c00007041c0180411701c07810846405200002d0026050054031381c1828200c5604200b00640e81c5844030b000341d1142c800580785d4040641d02c1800b80390300d42c4c5042d0f400101043c090040800b0003400c2c01c1d00c1c07a000c0c0c0c003401c0d0140e02900e1040c1d1000f004a084503a5000b6090901c00912511054040500a0840000d900441c000016440540071440b2402030002003401c2e600a5041141d080c2c2224003004a403020520600088040e04200d400c1c407420640d1300a00510006403c070000c016a143c0018107600300780300f50340c008144424444e17550300e5039a00c0041c00c5107104510048540206400b040b181e140c0011601a03840d11000140d003003590960315140c0d50b9200d15040d0b41035001c0c01c140090000502e00c610f52007160b1518281d107140c004402c2030550036a106641d40f0103102503007200d54168541800880282d4a044400915605 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 933723093 1250 933721843 933721853
    0x51e0c0a052206020c0d0c12050f030a05071e0f0b06012f0f1b06130803070b04020901120302060c210c04030309080a1a190912110102070816 62
    0x403a1802d51048800900c82c03400c0407040c864400c6003281d00c01d609940d0840e0f245402c00210030802c031006822207801101c10b0241d19002442c06510030711810440b40d003208844141d5007180c001d8042c810201d00042110024082d401a020380305003140030050011142c540e58045400c0e01460018051008400c0084c080d070740105519100d0201081d0f11843c0d50340c14000d10205d003107003040300f0b10103402441400700e07103c0750028100101c0c0c10b8108040740454521014001e19810031940c0310140c08106030b001554110501c01021181c0c041d11824513140b9260044c0041168103900c09000e01d00100d10603c003196012458580000100c503c8a689040c4142c80e03010304d032030f419400c011901e1200103200d0000c1000008104a900c00c0c0c0ba000780d1260358559850325520750b090702401141003c034610305800a0841d030540d01070b80814448401c04c000d1032100301165014001150810001510403040c6071f0490900241041624000c0d40360220590b2241658040c0d680689001d0b0244400303c03040103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 933724343 1250 933723093 933723097
    0x614040e0601050c030d0506030f010b031b03150106090503120415230c0604060501050d0f1716061a041503020d020f03011b170103081219020406020c04051e0c0a05 72
    0x121310489464844082d4201c0080030117550301c6109100702c407070240115606001d1001d00200042c040d000d115541d0603003144100c5080480b540c1401103001c40d040c5020380b0214640078107415601c42550604103803d0504d8025080b25800d80c18106010800c9691030080c0b03180032207071032490000402c0c1c55480080446425280b4211121880440c03680300c2c8580000f90184114000c02003400306903a03c0080c0405c012039500c0c0130308800780700801440400c05400d44a443c08a0810300300d440c12040c0c04143e095000103c5044a041d03440d040350000000354000412201b171001c84040211898403081420300401903c0024040c078003081c604410340d6a0040319840941e0050028490343c480a401c0302c14940e81c0c070340340d003010545001b200d0200902e45141d29058940c8202c2030b03854030407a209151340303a01000f001030030f18030464035501c16510a5030025000a100640040500c24038010412054aa0040401e015114181402c0c2c05044400c1000c81d0031804115415980e600000782c00c071254 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 933725593 1250 933724343 933724357
    0x6030507060c031b030e0d330e01110313050312070305040c060c110d1412031501020a02060d0203060316080304060e0108093706150614040e060105 65
    0x203018804000814a0b0032500803400d0900c40d40d2803070303803040340c1101585100c0d04184003e400106c0c0c41c2c0380d0115505100c3d210030800d5004025500702c01c43d405402d00320707010a40482c05080c1c0190701009a039042c490040f074940c2c540c0300c0c00034400c9000d0056072042502006050200750840c0d400c40505000f01441150325001d82000110a1072074810b90207030140c0b5059404070b032111319142000585501c2480d5070340c05c0a5100c814800c800340700504000410401c0b107400d031b6038592501045091002d08100d0f802c4005050018203480c0d15000341c580420000b0307a50300b10b05541007100c075000180d850904460054440c25001030700c0e40c9603140840d00d05240f03401c100c55540090b41010a241c00004003800840e0280d642d031440c00c2500d10011a075078403094903400042d6200708048072495040d55265201c0e140c1d144900b2540f0f14582c0c00c84900209040d00603620300b55500c007090b41104145900b04080c00c1141000c00754804950487c0c0202d204900c154603042c1501d4001c90712a03032250040700e42d5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 933726843 1250 933725593 933725603
    0x5150c040b03130c0f060c24020318100c090915080d020a06050a02090f3312090613030503060d0c03111018091802040518071e060c060603 61
    0x503868445503407010600c0703e060640706113400200000318080038140590580720360741d840e0807070002c1950b070f441c600000f4070300c44100b5002d14403c0f05800c01d415101451107262810300d00b0140078890b581607070030100d01c4a0400341c11800c4c02c51109038190001c0c04a000c980c9410030001d640300d9140881980c8c414503030041e051a0040e4081a100c0c40d038006800d0100728000d42081009071101e402d0941284564bc2c241a041030544040300c00720718050840f0007070503140ba00f00700000c015a401211044e00e098101c0041613030049040d281c0358441c82e2415520030101da000f01100d0070b288000e5100582030070001020070200100040c0d081d1a00c15280301060350200220031043e44031301c2d02da021130100c1c0726414003907405c1c0c01110b1103061040302d0074030301d00f6003004401d070290741091111000f42981c00f100d01d07031200c8400d614900580741c5100741031040541c05a1040c010100464450412034030b54007040824181030a98085842c1d140ca95104a811a080c07d083c0394465180c200f0146c180e81e4400380c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 933728093 1250 933726843 933726847
    0x60306010c030e0f0d0b090d020c011413051512090304060c02280f03030e0118181d06040b0c07030e01030513060903050a0e0a030f0605041e0c090e01050405150c040b 73
    0x4000300c0300007440c082c0487c5030641d034000c80c0f00001240d9a1203010309660001e4500703245071000150f060020400c6201040c02e95503182d4480010500d01c071008200e00740b180000041140d07003c0325075100b550b08142c4510145103058070340100109104945e50000c6d100301541040c0300f030301c03099500c0c400311423000008408c1c10590b41c814400280710101e10007503010510252804049600c2034010361340b04050421080c580d14202400004150509650b00b4081550760072500c0340750800910701c1c1032045c00e020042400b840c0c90324240c60240400723032880e101500180140000250401100408150203203000902941d52a600d8040209003241c05808903141244081c2410792200080c2804c075400d844134880185c03031740280608404a0320021b0000425a40110300148458001a400500440d01c02c0c850000c0713980394100c0040d10890840306862002c20800c0084450300441d414052528001c10692415482c1c40ea1100b2141003000600051003001400340c0382c0c0d40c3d050320301400601400355 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 933729343 1250 933728093 933728119
    0x11190f06020a021e09161202040b0702040608150a020d112d0903030301140114120118050f0f0705210103020f030109120f05070b0903120105060306010c030e0f 70
    0x1944038031040c42c090340540c0b198106946031090220071002c090501a00480d5140d942c04400f00c00346002c102d001c0c0c1005104140603400300001e001070005410080307901a541d02641c8100400c8801c80d501095041d08170750301007000a49001c44540d400451540090781d01d403150755480b0024440300010101d40c04005c241c0a084d0784c070001010910401c0c004044c14032008908901d68079005418005a06a20820052103e40c0740c0402c1540030b9035060516140001d884c8502070100e0b0855a5583c0159001c240104841201e14211008100c40c60030100541e050124103810301c448014141c440146215020800c3c0c54401c070125801c2c00c001c0340c00048100ca0266400149140a21041e441240310000010281c074040c0301d0401030707a0f404080112440d096501c20b03103001c0c0c51501c822003440340901c80c0c030300852001c0d044ca6119400c00b50103903990340c20070700c000b24080d10181c0129025120601c20440c450742c04c04d0120b07103496014117001003034419510008440c000424203080e0070101c036042c54 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 933730593 1250 933729343 933729347
    0x6070b01030b0f3106140702060910020a0e01051c02030907182c03090310020c1009080430060203070807030212010b091807081905010311190f06 64
    0x10720b00035844002c0070300d03640d2100f807080c040545040315025072411101c0c50300c0c8142034403413240001107481800c02007840384019640c0c2c0c540202c210386010240e000362081080400051050b000844034090701181000e00a56004207070350040041c05050040000f03407005407160314855101e141c04000740546d80c92800e0b54003941c864446200c3c400700443c281800c1c0d46011082e01503500c001847e80d804481c102100103001c03021080c041c3d20010640800c00020b882520103100c503403250b020040002d81d0341d5406072180b03403401004017a4401a2481c06099100042e541c40407542115850070341c007400160310b28003444162104404100c081107080c141c1c3c4041010a0b00603510689258640100380d0340c803400c2c1602030703210f14044125951100c10043c091911070201034020f0900107810320200340c1c1c1d0500b180e2079403070b4140d8031540451076090800c0400c0b004084502c0d1038216031b000c248402e515650360030310038a09540019200e004408194591068000f0464005044d0782c03c4400c030885c3e0710000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 933731843 1250 933730593 933730613
    0x60103050d0c241d0c06070f0305120a150506190e030c130b090105150904050c0d0c0206090f0d02120c0102090604061805100c0b040602040906030308010915180b06070b0103 76
    0x1580062250b0100b0003a044c680110724030710418000f500561505070039a030340b00104408288110b003401400c2c40040140081501103501c504040e00f00002d0038191208400301c120031030380c00f0700e01c0b070401003202c004143d404500c00701d5900658208904140d131a0320002c2e003009141c40780140c10510400c80e80c424000c40f80c01c151002c140030b45005900c0c4c0d032a4024010034200c041c203c95000202001083c5560a06602043e8072410031464541401c00d864407000075039515010403001039110714103200d03104005204402032422039030000d151f90213144034040d4440303401c44ad08401c0c00401080c103200003d02034044858a030001810f60ba6500e4075140c028081442000e68039007400154030000c100d6060507043c20031520020380b14035004003502d9480ba941c15000802c1103c90075001e0100240c09401c40c012100610300ca511040110b6041c0701084003121780104038010100307104d007001c1180c1a442e1403054540d14648001003141c4400303102160031482200030040440580c040000300384074446003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 933733093 1250 933731843 933731861
    0x30503040605060409050a170f1215061305040509030702090c0a08150906271003061401030f121110052707090b0a030501050f0f0702060103050d0c24 66
    0x407042140e0f44680c0144411039040140082c40359102400010201d000450300307400b500d41c03d100e103518082c0c0503990048140c200b40c0f941d440e080000000c0c81802e54000320a200440e00c1a14260304090655440303001500031480740c0c81c0110354402c049001c484041c0121031a43d80c001e400070640741041c1003000a2036200d074024200041800012076003850800d11030f1856000014003809417a02e8600c2045240350201c0700b0300045040000c40c203440d5940985071a80f15000721000b03884510301e10b00b070a009840300c00155001039001c0000600c0000da521484c06582c0750003036038140d410708900c8400c0e964014450b4804500744242050518481d585030013051040051401007242d81246440640a60346500c540048580103000f05015001466015110b249001410320308030559903143d5a084403001e0790858461074400041000b01060401c0c1d1941000c8140300404441d031560302c0781307521012110505800c014800c0302d40424461607030450b0070b010404618141129141c402440001e0540d84 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 933734343 1250 933733093 933733103
    0x110a0804020114070b04120c050f0106081902060d09170c06071209050d050a2312100605070f0c261b031902030f030d06050a0b04050d0201080403031803050304 70
    0x10f07500240501d000d40381c031554000041500c81d19247e80301c03e0001079072a84030080180b254401008280c00300500000007144000000b401c03400c0c102502d0800c8004510304003000402101da00060311000122512403020346030002da44000c5150a40c0d2445d170780f16006203000c40110307049501120100780c59018400d640c48a4035069000114041034400000b0081c255030040c5a503144240c0c060802880344101074a4007203c400d14540003610450001d480080a0600c04034150a07118074050003160031041051000c8009490050b0040c2184034108004104402c0d900080c800c01a5014039840a040b00400e080c60608034039601680c07281001c3d80c8006544034484a5200d000031410030704a80d0703400500030b81040300c41d8103409c065110a6041c1242c052090240350341100b0410b1020b007002e88403d08001c0340c01407400e410030801c0074803074001542c4001c08000812072540c1f0015100c0740ca60342030924440c0f696850800b03600610304800203001120b0f10355801070400d40e05c03800031352090340b040c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 933735593 1250 933734343 933734357
    0x60a1d0105031509032a030a0201020c071703031b040e151003020a020c0d3909180b1503060106030207060e0705010903080f250201300f110a08040201 66
    0x31a640d04a0000c140c0c3c0f613500701e4004029014410b51440114007802100c2c00080c9540090080c8440c50350b07101c4900344006035400f140c03c0b40602c80a001d40c2008058400c0e40510b4485540072040c2c5a200c05400350f6a28011a83c10501d01000c4200b0b440c020701c03d40142046030b03e00101d5030301140309401406803150749100c1e010003a4034040c6c070036503c3d0354419500410702d0081303007800d01c400080061010380d181002d41480c14401c80070030041c3c00c00e1034980c0c208550303080c1107100442c1055650f50800c0c0100e81c10324881503003a1002821b4912080d400c04002c1040d03495031440c180800c230328000b4250f050300400001182d600d8040e0014aa2184601000c00c42104038080f01600e8072aa802041c0c001000e100042002c120844d000c0c24011074601101481c05c1110b840303212011800e10507124000f070754515010207640c2c0090589046d1010794602d05540e01c844690011100151182c1001c1a69510740c0d0107030003042c40d8030024591a82c045813640c0c3d0f003081d140c05810a0011902240080c0340c0c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 933736843 1250 933735593 933735613
    0x51b070515210f2a0a1106090a03120f0f06062303010b092e2303150105130b070b040210020703030c060c0c1e1205090f0405060a1d010503 61
    0x2485440720312034103190032200402d499080298400808101800320031400540b1340c020070078440401040c0d0420503450b02600e9a0615a8840c2062030041241009400044080c408650062070b024011070528000060700000e22881d84018449225900b406500d4110f0109020350407640c209416031701c041c283e5075038010054404200344000d0285030b40ca80801d2108041500f400e55442541198030480721200400c9114402c1d04003540c03415130000aa260200402c044101c408034501400304000c0c201d03c0c61400c0c84070001104245170003141000b5002507000309a0503800f040300041e02640d4035099440d00c50b4101000008002d0340c0aa100d0324502c0554510540005482800c0340e0780740d110140041c42d1a00d030319009040110700c4c1d01c14040c0c24414a40016070b0881d22914080048846ca0311f1100706003007400156800c65007050034802c042100041654541149074410707103013124007140994810000c145d040301c59030f1100305400152a01036020845814140781600c01c00e80455044500d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 933738093 1250 933736843 933736897
    0x41406090c060f07030504031e1e0b27011a03010e0703031b1704170f070b0f0c0304080304081b0a030804120201030b060d1a0f01051b070515 62
    0x101403000652150b8100081056803018502800c0c0250103800c01c9800e140c2e4a0702c40c00c6c0d40302e002c0c9080038102c4600d150300904212880655201c0c04011600d8811302035060b070740d00c4005040107041070002c8040d1815481c901071401640d114241130960090005001c9510210542c10f18643c40700d00c6942000c0340000d00940c0000c138101101d0301a039a4207500c00b01d020240703110701d59504041e01c0c546042e001d54158564070900400060402d0f0411010014010654034207006005501c110300f6001040100900481041a0348a8404002d0229a070300780b0790800c0b41c50351069130301180c181e01010800044080c004550038010716040a042d100404c0003000f08580021540001002d0800c14003040c0300300a40501c140941503c181000200008507c00281454211580b0b00000a1716032191846991290001c3c000a03403046d521400050002c07070001c1c0542c040d00440605170b6501512100c0c0796842005070740b000704005072000701060750844c0c041006900c200290107410000c681c0421b507074a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 933739343 1250 933738093 933738103
    0x912030c1412070804050a0602031003151109060906090a0b090109080712080705150103060b0f01050304120c1a1f15090315110c1006050306040b0106030b010507060504140609 77
    0x499241001180f0b540d122070a5420180283c03081d40c0d01d01c11381003828009855440214060b03c0302c0754050155601d5440c002d0401070a1540000300c0a041842c141480c0ca04203080c0c43c2200800c5840f2a140c0412802107141070040809180d0b103c101844000341c0c6002071001081d101c10283c1e181541d4a0725020720340d03901d040c90b21411901c2aa0404a100801e01001c05040c800e480b480c2a00c1d8034811110740e1800c0300e40d0a0300f0685141d66500740805a501c4e040854900c0c2080a00b0104d0662903d42c865100d04140b0100c40010710071200042010004e011041d0031000c08015011641c0f4100640c00020760350311a001c43e190f01030b2000f40421000c0c00e0f121902440e01f400d82c4c2c0c2180707490460b5514140344000c810740e200020380f01d070f02640f0030800d41c501034100c1c121008000d02c2d10490500901040c1c1c1e480d6403102e40a500300c481480042403039202110305459803070070041100381c00103004a801344943c5c030000d40f04501d8542407204000b08103203000c4d13000303991004441003134031180d0780c8540358 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 933740593 1250 933739343 933739357
    0xc081b0d1706091914090f0a0b15040603120315090b220b030106080a060f0c12020304030e1c050d1e030e0c03011407030f0209150903010912030c14 65
    0x140820380c00003209403505985813580000c0e00c502507080111440d4902d0160350113000d1245500e02d50f070042014160b001c002c0440300c0300480000741030044183d240c24955240203041040d40c20510040e0000790f88550304a9002964032280c00e840780e001c81039004000f480700811a11031029174200000f81103519004617459800018500500318281100703010f082441680006421616001030302180e56003071007030400a20500d800780007081210724288085443c1da04c80007526600c1e0485040d40300b64040c00c5030b40e04000d11400140e4039100c1c0c0c02d00b5583c201c80f080e07402d50f10804d1038081956860f0540400984503200307800f101d44030343c4c50f03a6003500d422016892a0003030005140c584000c01780f00c0e0308a207002d14503034429100e0f41e9003000086070966030440e603503103251411302080c0090f060785446001113030270940908500345226400000e4402140e00c80480f81d48501180108059400394402e003000340c0d000f00541109075440c4c101401601c810341d4020702045180b0250043d1401010841c0c5503 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 933741843 1250 933740593 933740627
    0x30c010801060e040f0c0f022a1509130b0906040917070218040503120a0b180a021b0c0109060e030304031b03151a04090f0201030c0c081b0d 62
    0x590707824034000311110311008040580c0107494031040144e100c10342c4180904490b15981d001c081c1c0ca611500645418400c0c40407100c13003142e201e014a803a102c0000446213141c4102d807154903c0d1054a5142400d00031825142e61101d00200c070b070080c0d1082030340100d038110003c1c0d0b11000e80d80c0c0d074002000111800880060a902c0000d00c9002c005a40000202019807008050110740000c20b001200c7c00311085401300c0b40c0d5071001541c101c40307030b05d6445511743c41021020103020040c80400441d8481c400c01c2d1503a02c0560301080410401d41c0c50360107a03080c200380f000782d85445654034440159903024881071540407905d03640000c52918820740100c1034201029005600d058a1941c1e043e503161112101440488601d800120014404100840340001e040f500410720960481c002110141022903143c4518502040000004c100e20b0800308400d40900300059000103901041d103158509441c024102c10000610450031080ca1001200c0c1340d031200112500007404074000c0d15003078a20b0f409000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 933743093 1250 933741843 933741857
    0xf09050a080d110d0212090a03270801051005040501060903080f0f0c030c01020a0825031a0a0f380d020f0703030e06250305040215040b0d050105030c01 67
    0x10100e080d0500078140c1030840500018142d840d2503e0000f10b402416100300301540004000004140458182e80c1207134600d0b019203018440e60f58050000f03d018075100304000044041c000018845050140c000c1400c0f4000344480c1c50480a4120785d9130182c02110b1245203404004199240318031122029282d12944403440c2000e142c0c0c6160305c9401c45440082d41c1142004002140391003480905003000c06100056214042e0400207003541c13030020300c10406087c01200414031800000030b0b8000d0f0382c0c070900b80040c03519a000e140011580c6415201038000d0fa42010000f1540f80408842003120400ca040024805468200790340d03014901e1040781119029840d003400348489a0001c201140c40020010301d030010407000480079400000003540480ea4440441d0308141050005030b40c07004a411400034800e0540c01903110820181c210700c03080550b030340006021902c601c0783c80e08070325907042c850355203c40e40c5e502d0751000c03540522000243c440c00c00c00002280e007000586140c002030141c41e006 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 933744343 1250 933743093 933743113
    0x5030a080a050127020408030a09180b06070b060d050607020d12020a051210030c09050711280c0306020304050c131a0d031707020601081b0d020d08040b0f070201030f0905 75
    0x102e41c0708003202c19410755406c102c00941c20030100000c043e1300300641c035281c102d113260200c0c2d143c01011941d20085c0080c00c00c2e0000640341d444104403081d055104052070095180c10000c43e902007000b2100400d28420f150901c6151a0002200181098503940c0c14a24118540c1884c00b40d010f0301c4025004141c082c40010304000c103241e1440e5010710303001d5800012540d261503625050380b00d9070216580603542d01c20303c07900c0c540c000c1c1401d03c8007a0710001802c4805002400a1210a90342c031080c142480001c2c6103810419141d8500008517007060041d5204e040c1030400c0f544400020a0507881074000810f0782903614218014034421182c0010035046101001040c84502c0d14482401c504100b04491190b100704200d04141e401070215034001d107440d6062258403490b00b5542404070b68040ca203030100416070303502c0d07201010480c0e905803840b104000c1e0f146400b440034040d6030000941c50b030b40840d4802000402c40c028101440c001d9805001402c01001c0c64411580400c401500344e81180c1103071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 933745593 1250 933744343 933744389
    0x50a0302010f1209060603030e0f1318050a0c0e06030703031d060c1014010f0e2202120d0e010809060a0e1c020105040b1006081f030b0405030a080a0501 67
    0x2034016015800c1c0301c03c00001110100d012604070b80401c032181980c60005005040e4000a1824507604c01d50383c07000a5041103001840820110243c0d01356240c030303042d010f90f4012605a4965415510408a8130b8150091400c0000009540030340960312401c0b00000d0f09500c0c7c00a0310700201c0c1c1d0140c4400f1040d402a4030000181d00e59012040d8201e8010040e8210403201006120101d0107103c600040340403260200500008041c0e00c04030100c0c03080d203004d01c904000321402d660441c0070034001d005055404007000180c1c249007040650b01c440e1800000c40c01450102d80b038005504690f6400000f00181001565000000e4402c500c081d48003070000750030883c46612500107c1d60350002c5800e88001804550020240701c2c4003000185d44440c00c0c0420230514510312900519460101204d950410500402480e03004104585035090a205034070003d107152012000742d90407100345a00780c03a00e410810799a43c014143c0c4000500c0c2030b000101080b040703109060603100441c0f441030b0140100262 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 933746843 1250 933745593 933745607
    0x4060504080f0a1a060a0f0306021308071535010303030e0102070b16020c03030a0905030601080a0f1b0503100605120c010f050702060408190c29160609140115050a030201 75
    0x1180d071304181c0d07503003001c51f80e0760300c03442d25000540c481c1c41c0c050385d2107c54007415a60808280e00002013a07016100c28084042c1a410107a441c1c10b8034503089510380c0740c2e48014540e1a090b22803200c8070514504245010351065003840341668020384040c070405280c400c01600300d100380607000d03210710a5000410704000c589041d8400340c2d006481200c1544080038002810b607400300c2d0100e40480c0c0c61100c10003d80c2000e002043c01481c0c8080905000306030703504d81145c2c000d400c0000030074080340104400c0b00344074001c101d4400340c1005821950a86042ca10103002000e29015840c801d121201da041c007080c0d40040e182c80c045406030740c0e645070f480c1224007d9480b5004584e00300e900200512002c41c2c55041000f8040440c0c01590382a82c465045082920a0410076084989030080403044000405c5050311054040d0b00034860803035031100e22a4103155001c1d01304000030080c0d03042003d02428001e410040005030141c01000300700d05884400c4024110800e446025007190f9080c00800143d030040310 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 933748093 1250 933746843 933746851
    0x1e19240c020913320a0203030a110a060c02060406050c070c0603050703020903010f1d060702031603170a050a0b06181003020c070608010317040b0d110c010204060504080f0a1a 77
    0xc0d0101001085980302c15428020000c900030708004541400100540c04e002e00c540348a1042c040c00d000240d0750003117901d911034101482d06014190107682c50b0141c08102340d07001c058015000b0041261820381c001d4a60342d040d241a1946814580412074446c26038003121149a4428560648a80341c0002507000c4c00004184000345a42030150100d991800e00031900f45c130011940000d904c0a0189286090343c1104203202c160b540318104200240350000100c40921404c040803225105040c0b808840c41c00c00c608800c80c260310050203100050116030017484c007032003800509103d6018068107222450003081c042001110004a01d01c085041400868684502070302d009031409803240c060501d444150b5004d9400a003140004009000c44c040a0311001644007484500c1e16141c050303c22a46d00503410005659503031154100415600c441c100e03080b000c0110000e549071550f0388805040e5410074403071801d5038045c000f4240140308000c94540f44841d13000e010414800e0058842c641c3e2520010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 933749343 1250 933748093 933748111
    0x1905040215040b07060c0c02010203040317130305010213050102030a020d230301170c030114060609030109230127030c050312010909020418111e19240c0209 69
    0x95040032840050741e004001502107420025522540380c6400011582088204002c211101502e42d0050f03034080100c4013100d400c150400310424034110008110300c12242200701c43c600c002800001c116064000d4030704104c40300030b8507042d0b030741d81c00c01645c0b60b00c0b580c0c902100503040300d03210a101c2c5000300c9a000114181400d0040c8905200c050350704139134402e030401c00d00341100140c4507540321402c1040b10f581c4842a0000d001c1198006080c504e146005000144901d5010490040949003540001c02d81500550707044c21500c65444000799003981081c0240c115420000e9980103216607001001200d01045c0d4070001c41c00164504485881c4000011111030104024a0032a0100141224044c02d040c2100150642141c810001140c20540795203112003280456000440c0c2e28001c1c0c15110340701504c048042544a40f0908081da1240110700d52000049441001a80d91030f50540203641c03101d00742d4044001d0783c031003000f615100715403c0303400140c1c040310480040c1081048503420014ac8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 933750593 1250 933749343 933749359
    0x7031502250c0e010902040e0c09010302120a0501050117040c0510091a130e0601020a0b09010609090b0a060b0c190602042303060a060b16140604050706090501050319050402 76
    0x1041820400410030201581d5902d41804140070802c00d03424440d00400480d5005c5142500e411200c5481000c010490300b00c400b004a016a1264081e030102c519a0740360715a13603007040c54942d40d4038000380401e000c3c440c001044140c030050030741001403941340142e410a10014215151004200d40c0c0c200c000c003ca820441c00d40400144140310b030015440d45000c64107840e845014200e032000c039890b00381e402004141d03807500500280da6000300c3d8480a05421038450311040e521902400c0c00351980354024240d0500d8103622109000e00308030054052030840c2d10600c0300c5a0344040c1c40c80c1034018104000030716004141c400e10525581d26802c03402920039400542041e82d100d002080201c1d6884180c9111056050703540282e03d01408074a030300039100c0008009141c1401e1041ca100e0042c004000c1c000920380d00c0070024086050f01181c401d8425208a0780300c1d01e800d01d0050780b40c0c0c08a00c503071f00c046100c0c4034010410f0b600840c15640700713600a20300e016030b1003507840c00e200c05404041d01c02c2ea001008 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 933751843 1250 933750593 933750637
    0x21501030b250201060602060c07030c030f09080a200f010f08090109080f0706111303080f0708031807080105060904020d110406090b011d150307030209090f0702010c0207031502 78
    0x10b01c1c094811410342c00001d0510b182a10180c28031100a0000c0d0b14101c4c100b00203030002e60001c4400d40d42171b800d49000b4114804005050352405460b41001100d4452072901c0c0e007c20412400c0802c0e542d00b0300c60070040b10000315041c00103009010403003a02280e51b90003c0d1103064483d00b40b05522040d06000811000f000340c0b9420311070b902c50304100050b0200001c2040c10301001d1701441c070446540704405850071200300da81024500c5580002410080f000404207212a468010340301025000301149030707281030045a8044502810038a034000313010b5140000340040040c0f04140c411040940707458025920340d0308100101d040c00724211a07208600400aa00d43c403244590740180007203100001e18015900009401c60502c0c03014588884052400122280c48110468404c103642580304c44e2a503c3c3c24203780c002e0302502407a16080110304081022040030000321750701444c0c164000304140203444104a88803200e50102509400c1e070318541c0e0b810300d40a640189008407001e04000b5a90074 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 933753093 1250 933751843 933751891
    0x21e150405120310291e04181e020309150403031409030a03270201110307060c1805042c0c03070b1b0a0f03050306011b06050412021501030b 62
    0x30b46032a5481559044280701c407220b0200c11210300c00703c540c045d05401001d410000418860304140e40f10840d103059513406070030248825034004d040c58456680c00112808031800c001c02d080001c540306032030700410319907040d600d6108a900820360400900f40360001540301b039041030006042101050fa68002c001e00305294845000d016882e103001855a81c2200480101a034410700c0800c505000e204601d0402c10011202540c079055082c242090342d560b4600c001410b5000d080e002510360b40c1020ac000064590100300030800048000032580c2c61038580c01413100700c52200d1900305181120341e050205184849081501003001c150440d90230402500c08079003400f0141d07100000d40440490303000f02813901d00d11050481100c039001402c01611030784500c505007010520250602c40000f02080050b48641c51038281600e520b100e40240100c02d240c9280145421281950034110290303060502510215081c000b02441d4074101c41d040e42103448403241c4800241181c2c4901c09a4054400840 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 933754343 1250 933753093 933753097
    0xf091603150c120c08040201020c03010c0806150c150402011209050303040b090c030703150b010e010203041208091012051f090f0603470c0c010b031b01021e15040512 73
    0x7005581c031800e19040c1b074800646403801e441a072600c030303034103007480c0c200d403541c1c0305107165400442164011400c1009d40707442c038040c2c440c40c6243c00041c0640900400380c0c03030301c60064a000700c0c400c1e039485544455685020b0102c03202464010495041000460042440d00c00440e030040d4a007001c2e00c680100a200091500e11940d0044601c041c0c000d05000442c0954410a10444800c1c20050450400c2c0d20000303490348100e003c0c02440e60040328090050064480959810107405000d04c01e03807401705900603040c41d8000c16560b0025007402d00050f000044015400c0c940301c1c140f150800d44504083d40c9601a19514480d03810640d583c0b070001000c0781620200b0702000003420000301c0c9818003d080000041220f07101840c5880d401030411003080354410382c003603212055240040c5c43e25070701900c05014180009400740c0c14822120825251200c0240410040809070210740360071025042100500040d0004090181c010f62051205152900038451b0301a20880c02d0b02d02c6040409141d0580b9 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 933755593 1250 933754343 933754361
    0xe0403090e240901080304050d060609050c090423060625030507050712051b0d050703031806081302040207030c20010f020c0d11030c06030f091603150c12 68
    0x581c05921120b00640c80c407442c0c0c00041d1210001507060000390740c0d4910540c41890f005003d00390790541403082540c00030740a40720424003405541070071a0700c0c042681201440714802d51400b20040e03082c842c403510902c50780641800342d80090340c500b001c1001e00d41000322200e00684034249038803a422020894490218481e4441541707070f100c1420b08914001a0f034005604100c002d0b901000410300004041300c80c00030706107101c140e80c00b0a03008601503403400440203013503125603c03000c010590400c55088458001d00352011500d80d41c0c1508544220056a101d10b800041240708409410310f41c006040c960300a04100a04403080e46d0340c4039074080d43c0c0303920041a07894588c65118641e0f0060124440440510040c142101c07014001002d200306c40800500004072014100803d440602000103c2170008284e2038580c0f81640b08a0403210044600380554080e510300c0d440004280450102540d800004041c601010f52448000501c40101c0040c1440071203846c1b0340d04004075014041c04 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 933756843 1250 933755593 933755611
    0x5040f0b041d010b0f0d1d010903020c0d020d0b040318030c050a120305090d02120102070c031b030f0b1f090c02060c03130206030c090415030b0c130e0403090e 70
    0x9601e2400c84061a0200c401580b400d4076103032180100100260582541c88103003241003442ea80743c4040c1a000000d014014045640c00c0b40c11000e0720b2029010b5021074030080c0240c099480c98000075080210242203984029448403450a2140108845d448065401b40c420305041e074034603103010003801c8084201e81c4101e507116884030043c8402d080a40c4032070020a8201c1204035050007694004e00306004020740f8078000c601c030001c3d400540d86d400e43c003d48800d0b05c8200031560342000e8200f80c1c4003031645020030343d100c5484499420324042c0c0030740f80318100c3e500050b0b41407040c0ad05940700e500c2010054880700700048440151048400400354a600400703405000003101001c903407000c3d003801002055041e00d207205000700020000704c405041d8003607604582c0d06076656200500d42890380039000c40c25400030710f410b00d40389440c0404800c0d1000d5074040c2d0104141940c07614401d0055100d11920503150140d401005c0101c0d800c0f07080200e40041c428149464100e4803500015403200c4100c9010724 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 933758093 1250 933756843 933756847
    0x1f060503041e0503130f0b0412060f11040812190f031407050307020d090501120b061b03030121030207170a022d01050c0318120d02010209041415090705040f0b 70
    0x20480d24401c01d8000284a41b985242c0340e03510b0000d04603e640950b128180d011601710040d5400c110071540061801d00101354200041d1000e0090384840790054060480d80303105a0005d00c0030700280c041640c04800d1004548030760b07407407101000c803031010030886404241512001c0c00003442c21110511407003280f05580d80e0740c5925104000914103042040c0341c2040c4440300070184100d99100c0300b41508100410000708440c203102020030b102c0d12070000400e0100d41104030f0801010701c040011350403035101e1505200d81240031b50040501031103007a00180560300000c000c2140c441c004e003108260109500a13a104001d0036000710b40b918440840405546101d00702410300c00d2200d92000c119503c083c603040f400e00c1903001826649200d1411000003d401ca25440d5441c0c0e0741e0b044a400740c000400084e540c00c0852100064080e410007004180b08505040703005540141c0e564441e8841d08a9045008464980780140708035094080c10850030000c00b00400b042ca0414080f03010010402084030075 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 933759343 1250 933758093 933758107
    0x9030f121201061d04150e090706112410090f060e09070501141315081905090307060e030f1303020a0e040c0902090a050a14091f060503041e0503 64
    0x80900d00c0581110f010301403403031180395961211080d0301e142c001c42640c1c001804000c03009404c0340108607a010a0f038220001c03040000c1c2d15804640c2d01d0031905980c98014924003000d0a0503103074451034400300e50041504a0000641840804042e0800110241d03801d250340c0780d6181c903041d00d12415040319540c0d102c2c0401c1010501c8990819840083c7c00c014000042c100000200010350340307451800c40700c0003c101c1303071b1800b003404031940010014991811041c4013400c201030316103002243c1c0f00c0042c00742407842c420f550503140211441002c0300741c05107241a0b038130f1b03035414010015201416a144402c0c081c4400513031100c8000c1400c1c3d10054510800d00e80303944100010308441d604495180214a030500c4001560301803040292802040050707101c42d26003000c41d584801c940d2203103030700595050780046c010044010ba40c05110080c5c5a0102e1962101c1210840b03030407034400d01c20b51811064081003928425006190000c0c030460380002ca0340c01495515040402405060340c1c2c503000010341d1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 933760593 1250 933759343 933759367
    0x60d1503062a02060606160c0510020703030e1c0b27011a040209010906140d021b010b010201060302010e1e03010203010306230906041203090516141c02010509030f12 73
    0x20003910707203944004c1c1a649403031000305042e0b0042c1c1140f005448210642c0c2e204000c5010620b201410001c1c01d505d01d40c1410003002950745600c2d100a801043d200b50f03041d8014202911561110365403800d030b42c19810115941c480c01d84100400002218036121201180c0c2012130106c02901d000010021504001c41c0240802501e5805282480365204000002c1c1d107907000440181250550308044c19100340c2e50702d0307140d06440b55420000c0c00c0303403000070b00c0c0542c018090303070040f50340c0e050030b00030401c2c025540f006908880c618000607001c0303007550100c0000e038a00406d000032000c044820402000340b210380480d0980c0c10a803c11164691160300b002c08160442031400644200e00c074111640f0304003400c05540f5a98040e1001d4250440031301c107500c40c3e0f40240c02c8101c86540c4003040314151030f1000d003c2c405540650168240c03200340c00381c941445150400c0a02080d80500b0728900b07d442d015070064800341d00c4850019014003c0011402540c4410f0000000c41c1d0b040d0020ac0303988004494071 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 933761843 1250 933760593 933760661
    0x2120405010e07081b10021c030903030e0a0f060b06040b0f0304120c0c051309050f0a030906090e0a180f1101180b09100225080d0e060d150306 63
    0x100c0310079940042180d03659807160700417044220300b0076100304101030348900c42203080010008078202030300000818000030070f50560205a10701d00907542045207800e203840e07040c3c503410f0141e80a401005d110742c0d5039020510320713402076800e0300c0020b0691b8a441c1c0e039141071042a400c12814541a44070100c10041071105040c83c4100c00103da180c9810f0800d41d9680c0c035100c1e07840600599006030882c011105800103e540941400f81d0408120b1b41100c04c917101a030b5981d8110b9600300d001400001c0c00240c0e00d030040c8030304e200b540d0005002e214256a6407180800070f14040c401e40310008007034080751002c14013074190041244d000781c2c00171b150350740c0110014000c0201100c440d11454984042081089107c41c180e13001000c007101d0305658003040d03400c00c80c13400039004848804800c07400f0510a0011030400640304580500e8152000903909810594801c6d18180e06503400c01c0c020400b0484030a0544d1140c2d80181c12204807000e070070f84a4444004841000c1c0b9111106505080444000240d900c1c07 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 933763093 1250 933761843 933761849
    0x6062b24050403090b0a020106090e030901020705011b1118070f0e0f010c0803060a090c020106050319050618070932071b0c050414040c12050c01050a0302120405010e07 74
    0x10341885141000da5000344245500c0c40f61034044d00010075250402c5100303411640051814030400d0128a00b001c1445440b9031003180b4071400762054a20000d042e50007851002c4105114550084c26041c1907241c2c0001502d4500040342d002504600d0715440c01c2d4006041030141d0030696643c4504540300310068118480c1c43c900900c5103c602802e4907081c3e83c0028004181d50f800000d9645a4030742101040d4400201c1d040008407034289201c03080f006078154008000c45008030200c0d000c01e2802800100c11284171640a08103400041c0020008902035880c0b43e00041c010044074512a6910054030417145101c48806180400c075060f1041c2c50041800d00300044444100400c080c20100d1000d8030303040489841c24290480c5030318040502900c3e40c101c4d001820040c0084c4040301d04400a5600344104070750442e061a414580400c5040a41c81001e129546c060000d058110200d00151270b15089a0b6003041016001c10506010910075010360740164410000800c8c07081c5901030325400c1850b550 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 933764343 1250 933763093 933763163
    0x20d02030c070612020d0c080604060b0301180c0c050118330b0117010e1b0a050304150b03011805010f021305041d1e0615010206062b 59
    0x4005012810400302e00700d400c64240d03040240d05154018040e10190213070544421109103460110b001281e008002548560300444080014075260520420300e40030a0041c4101c0b0500d03015a03c07140a480e81c040e0108034000d080012440e5400c1c3c4e81d171801d455a81050524120030072440c601001010800303950340d80c40f400c0c0e105a81c04030100d190500922901001c10700c035502c401c1c0b0808182d0042c5940031410815656840403580c5400850a402605070b851401152840c0e10b11101c462404007943d9000308c04c1d03520a4615101c0791508001b1018010105080d11b584034841266603409104208030300704c540403040000c02135414801d08481546040004807801040040000d41c01860031101f030751001c1381c0010704029100c42c04802500d00182d064030501c00c0d5406c006006070311800d04040080000b085134804d54800c882e285111280404c213030b0260307004401103152032800208410074101c0600504140501540c04451505000139095600000c182407001c1c540c400c080c1d01410401d040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 933765593 1250 933764343 933764347
    0x913120c0b04060c140403030e030d090608070e04110307120b01030204080721060204060801140303120a09060b0901060e030c2b050304050603010b1b010507120e03070b09010507020d0203 82
    0xd038031401966480240300500721139603135400c881044d0280d1464240c40e40381d8030b0f031240c42e00d499143c007601800300300d504580f1034440d4450f016000d40c4505002e0b8151400b0780d50380615a2030341001501e0400c41545020344c490b40350f196003182c075108840510301c0798070f0740d40d01c00031040302c40c1201204a40103592128105401000144110100000e0000c01c8640b0b030500c003c1294070903108201d04a003081e000402503800060009001c42c1c0c020003950599450182840040700c108040564070321a00c6280507000741e40400141300b402c495401804030500030a80411003c400200240042d00c09030040d4002c2480008940d0a47c201040b003a02050b00550760075030000e800a1858101102c8498000c5a032141800214100a82401500c004101c090041d41d105d50311090000d00d40d40180010741042c11100b0650024842d0500610303021b003400c0d44465441880803039900010b00225102c08040340710070400c0b07030000f03000344401301d110342e0138070000003002e0404d100000c3c00c2c041003408000440d401 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 933766843 1250 933765593 933765617
    0x120602220e01050d03110105040311100203100e04030c021906030b0301050f010312171510050a12110915040305061e0f070c0506090106030b130314070809091312 71
    0x300e48246030559408072a58842c064107840c3c12524900b03203146c981ca155080000740f108264200c25001c03946042c0390f040c1c0c0c0050610120000c03c03030104540804040c1100d55040100d2100c80d450903810078028502401c6602c019008100b244035032a8410110f01d04071403080004640c54408c1c07107017a201c05c03070003400181851070f12102d5640060101500003c0c02480316802203020340003801d045d0440003c9c252092503c01550100c03c5408902a03009003018008800103034410303400c980300e414483d183c2c0c00a04114400e45001406401d41003005044108500300496482e42c2d210900c800108415907512421450414100b65024120340f0180380c04840038404c40000d00e800541c490a07204003012265224841101c030150348080141150003a481800320380c01c4190030401c182c1340124115407241e2600705071055290745e407560103000944009500c201c4401b06400800116024100341c0e814480010001440190142c07518a5014160304581c020488130800e1440001070904008001d019 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 933768093 1250 933766843 933766859
    0xc03020714040204031208040512070f0b10081501090606020601080604031b0b15030724110f060915070516081e0a1710120b0a0612060222 61
    0x3031802140d41c4508101024441e60715aa8107071002160824815000303210901c1e405000650182c906603014001e441c00c044651035000700b190600c590100102000d0303a51504c4a0703820b044064000d8043e2442080d00040741d040400002614141c05064101c0c69450041c040c022101268095019500032030010040c8020214126500a4250409039240c400e5a46540c00b102a10b0720000c118038401410301c0891650080304001480c1c083e81250511902c552a00b203c1c0460780b80c0d2500c100503a00d0701d07040020710942c501039442481e0341c03c852044070303594055803c14800b2101d44009900c60aa90714a41c0000e4448a40101c2c4070f0514a107410149800c091825030800320180507681d001071201e1140790394040c200d0b4180d01c0719031030903102c44903020010107000d80c1c000f818802a0742000032031032140b5034240030811503105540c002d10032400c5540b11500440c00400e030b402c400703540b0000022050050458108280d01c1402c0c01030350b45c50440300341210a11030800070403500c1c5000c141409114 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 933769343 1250 933768093 933768103
    0xb181005190f06050c03090907031e050c0306010f030e15060a0b1303021c020a090b040f0b030a1e15050a0f0b010f050d020d02070533060f1c20010c0302 67
    0xf03030440c6800d0f50b6510a0061300c07461032103260041c0350000b45580400c01320b69819030100003060015a041030444102d140c40078203480341580e81904d41d00701040810780c0796003d100c0140f500d103564103005c21000d104604c2a0b00f42510054000c000d01600000c00c4180e14202010b4000b0706200c0e11018141400f07800399203541c61803800020300a1020900c0401948a0503496540c11a40103001464050329110b01ea17020704a00102540070314248802030000304038602502c17810300c03c00350040c50320420317a440c1d428811540c241c04400c40041c9001140101d900703c00c0c4040d5481e55002d000c18582001e911000450317803032002d09041986021b40351040b50384d201209040d035210b24508951030720840240c2c00002d205600c030820302c980c40010910200315000ca403544804c030310403003642c14944480c440170550181c004e0391580d0306000c800024840b80f41c030900c0c0400704d00003c0c1103540600c03506480f40800c501c4200d0269135180d00b034103000c0c0c04903001108d0421408002e2034902806450b50394007a40e50 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 933770593 1250 933769343 933769349
    0x20c0316030b0c0c030c16120209060409020f0303041202011e0f121107060e060901050705030a0515041e0506060408102403030519031e0b181005190f 66
    0x29442c502280c40420504151130320000300c8815255104a0300800c02d50302d0070100b02e540c841204809000800c00b00710017a985503542c003d490a400c0b0341c0c5500802c4010310030024102c0e4000b401c8510f001c901d840800250000d0214401d0b10101983c10f400054154011904070f07804a03040c0c0110010743c281d0002810b0414031450030301c40e800480b0880140050500d0302c80c3c410585401003108004c0c4021500039408849400b0b041c2d90b2076460700c039151400d8580c111680000b00d041040842c2c03200850341c1c08158031040765a1401c050103251000a02030700d80403000e4451911184c0e51044694400744640d90300001c049440c2ca280a28182125459680601c0015107403641c4420813030249810744011180506564540003c075900c0f4a009041900701c1c50000c1e03820007200c200c8c198001d000344105205d0000480700103d507204d6070326100707000d841744521003600400001c03055a505000d00b00318600488162102021007401c2c1020b019800551415200a00100860400864a80764000e40036 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 933771843 1250 933770593 933770603
    0x12020706080f160f020106030506090304060323012304020310082406041a1302040608010b0f070b0618040818060306130b0102030f0d06180213061b0b0109020406020c031603 76
    0x4a0001000301760f0042c4099400903082e4080c0d28204241341d0f80c08002402641c0250301c04200180c20b203445d42206184c01030140d605441154010f01c5161940700a001c1c40b401001c4801900c070304040b000c20140c0e0010340d02121500280d1006120801c818044001030600781c0d00121403c0010001e406010303c000703401c40c0d000e42e5484803400c400404e400c4080b070394683c000d4001c0800c807501001c107a0080d4030901c600303400524010000b05e10041c0000448a030700b84258040c60501c40541c803040043c10001d400241d000b0b031590404079400c02c05022032440f56000e10b5540761598281c200d60701c1422000c100d0320b4800c6e0340420411002d551503520724814148956070009030320940a005034030b035101d9441c28040342540820700c14070011107504004150350100181d180448015040341040e405034a03448101044008014011544140b801c4004c45100c041d038401c0900f034030b480380c3c05100c00c203800501d540382c0c00103001c4c051f5540400c141005000150010210b000800004c203c40b1708183c000241 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 933773093 1250 933771843 933771857
    0x80307200303070606081e060717070302091e03120403170a0302070203030f03071803050d08101a0d050f100e190e01150b0406140c01060312020706080f16 68
    0x30194408000b521412503200100300045600c94140940d160705604080452407140c0c0c1e0700051009001ca607060040001e902c490b02c02c00c1f542c01d403990070b95070000c00d030a08160303007840014901e5481400e0380741c04114280094207000d00c150306040c28084042e100080c0480104010000100c100304983d201c2c030507044559845420b410b000701c1c00b03481104006503040c8804502e00340e109014100450240d4071944401c2c01e083d1042004614810b5103104c007400642002a01e031480b68000d109503503001a00c29441b1882540700ca14a080c4100070414034050710750081486a00001284500741d0000c0a50300d480000e49014400f60752407080c2c60103003081c1c9034005c42c04940c1d8100381d885514030400a04105210341d1074540300d054000c01803885a9020200701c180000b980820160450f000d983d91562011345900010300d01c0c60b06a0f04c04403a01031150343c0c0391000000709842224041c0340101301e07400703490f00c43e10b4064000c0070450042c1814a04015101c14440424051107460b030199000d424400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 933774343 1250 933773093 933773153
    0x6060109050d0c080312090105060f0609092e0602010608030c070b0a020c0411030403020c1e011b02030706030b0a1517181501052b0b040807210306080307 68
    0x1040007183c0d5202015900c0b01161380e07500103560741605442842c0482c000c00282d0b880d40c04000c410600d0408254100804104514440c1851070800b03510469444120b88240741d050030070881e03022410707040c0c0c0c100102c030041444400d9081c00f6030401003089100540c101850030650b6500c50029204000310690001080c2485500a0000c01c0103058000c2c4204144a105c014013102c0707034012100bc500600885411700110710b4075101a01c0b60074885402c880070620120300644483c1c14007108802070001d140c1c00c6a0050382e0801411014004a50300807440c0d8800070144801001e0f103401c8000710100040381416800c0d8044884d40790195805c50446d040d4960003401c10010380901c2107088240644036001940100031075225040b00d205840340e030150540120008a801c22420409240420125071f020109142c1c100c2c01f0342141c011031425262520715a141051a08298400420210704810003541d054052080000409161000c1d40c0780540c0d50780d41410600002c0800d0200d02001700040d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 933775593 1250 933774343 933774353
    0x601050a091703070204060815190f020c010b040606050c06070e01050c1c02060601170604110f21010504090b0a110d02040b041403070b04120302032104021206060109050d 75
    0x400420214030b01c40b00422180c0300b1141c5943c420700090f40a107080440c0080c3d01000040c40791045160b280030984580c9400004180390350007401c42c14041600c5404c01440d41a01d44018031420044000000e0130180c44414170046d03d40c16841642400305c244014888100003258542c1d20250500d03008204c000d240c0c005030f400380035500d1f016006104110b1194201141c4040c503203005201ca4080303170803e41c0c0c0c08004580c04962504511a00c1c0d58000102e03a15040c2031304040c41b101800c3c500903090000b91081d140f01034000100d221aa0800071802807607000e03803041801e01610f41a0f81c01d100031070254485800032103000e03002c41c454aa880b6111444c94118500783c0d2010007110748195581d40e038801784558150024050000b200d0009603014242e403500081c946e044420508905082620f401ea000d842980340210580641c001004446d10342860500b15050401050340c049216041030f00521210544002100310103a02c40e074103025040c1c0c0c000711400d08a40c821107001b030300c02456182c1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 933776843 1250 933775593 933775607
    0x70903120c17070602070c0f050d081c1103040c06020c0d0b0402150f04050a090c021f110a0809100603031e03110a020f1c0c0f060b13022109060601050a 67
    0x1a100001d08003040300c0040003503d40003440300c42d0003042203000746a2541004254102e00d4401e0a901440d00405040080c02f0417000d00f140c0a507540e800301400181e24000340c19104003240034019002c0000400c000c000c10900c0304805031404d8402003110815100105095160151002c3c101c0599500000c0465a40102c01d91801c0040c483d41038892500c006820003a42103401807610271005007101184000291150403400ba500354001c00100e03e2003409000c0c000e00d92201004059182e828a4200085d0700b00104410203c903070360020a403401b159410b0506040ca00030b6602141060010008241c0c40400c1261030200c0110000001300603e20980041109102c000020680803c421107800d07000705903450151040015151014404640c180c1010259204040403800c6500804003252190b00710a01c01481b0b0300d80094000c803807a0005165203071350482002c5498000500320034048414a4a900244010000780341c0360074520000d5032241c100610050400c18049000c24000b4441e0b00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 933778093 1250 933776843 933776873
    0xb090c07082a0f031201090e0712240e070608090c040603050606010212130603020a140c01150b090d060b0a05100203090108010e071209260d05070903120c 68
    0x200d00d42c0022000c0d0300c2000c040092108a03105010b58881010706500110840e10380081c80601c2003800da0a00b401d02d40180f04100020550b442146004a00f901c84071000254650041e02940754070100c520441d00702c03140c0070758406502c60a0411030019600000b0f10311003a562241001c0c02d16945203154a4075041444041650050400c0000404d0000c04501c07a8000d280070f03400c0d00d01303040840500420034401c9194030854030314070000401203244664084e19a0340c400d860302d40d40100050107030014035008000c0e10700707143c2d6460780307500e001d800c0c21000a030041c864090a1820200804002217802d0349000f0080c040d03944400080645a440b252003801900008221800344003c03614000d64903001800c129000c80d074554000f0411400d8543c03c0c0d440398070369036102c0c040d0381c102105000c0a0181150110f4000c410200c3d418078503c1040b201880f1003071058140b80d10740790002000410358001401c0d090911102031418004a4044984c41d04208183d0800f050614124a40845842c110302 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 933779343 1250 933778093 933778117
    0x20904111306080c0103020a17040503070807050d0305090106050f0405100f0305060a050606030121050a0606180b04110a080408040308030a050a05180304060c06061203020f0d030b090c0708 83
    0x415a07480e2840e05034410341c15602a441110840030000d00150201e10a40b014040851003800c00c02c1980e102d1407061941c0305102d01c040d0ba05058141c1d48483c042d401c02c030350494054200c015030700d4240b0b602d4403134541c1c850240030080c080c5602e0600418003100c00410198051600c0704009084256800000c4000308000200031406950341d0a20940710941580c500200c00d0518010801518003181503030306036401d00001341d550720843c428104183c202110101e405014409c40040818401e1003024010844400d000314466029461481110034216115200320700c1c000000a4280740c3c6010382e0100c0d10a4286801661280d0801012074001c41c0e00003461100f0000030810140056000745014001d03910f402d0003551207405001013a190140c6c1c0d0300485078014401000100d204d00c040c142c044d03005680000d0b00580741c04e034004500210000c1500540d0215040700803800041148148202207441e0410035911002d001039800304014040900d141340214a01c82070020000803074078990703882 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 933780593 1250 933779343 933779359
    0xa1103071205030402011706031209041b0f0905190e09120406172404020a0c0501051e07080c030106031d010c18080703080f0c010b060406120b1c02090411 68
    0x91001040366108035400c90000d2100c8400308487c0103d00307401c2e801503200802a203020040b50400d083c01da00149080c95000b0307100c10b10900800c41d001d0b250f640056066407007450000500501424400865000b98081e1150f00300c03030008841c010340d1020945039000c01c1c15039903031502440d1501d4003c0000d030481c1c4201d0300280c0029184d400414904100c8405912288150307540441e21400440400e9030000b401701e000403000c03803450503900600741000a8148070100f01001d49070795013100c40480c1e050a2111340d00c10074190305071200c00d00740e80c44030b0070386021052880c0403040d200c0640010300c0b9060a15440703134804152440c090744290b50340c2020800800641d103a1403001000c1c6401c0100101203100280d0700444c7c40e081c08500401541c2d0030072105071500040d6205020135520a4035451400d560b1004030894654036140108001d04140d601c1c200303698040802c034400c03074111904048c411480c03421903000700d03c501000000440d0f0101e990040568860402d501802188541c1e980d1000740 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 933781843 1250 933780593 933780623
    0xb0c0c03180306010603060e0708070519031a0d121101090803070e011409030a03050d0e010e0d030b01020c091618080307060506040203010b031b0403050d170f0103080a110307 77
    0x403844481e0086001181243c031141d0340c030b2205400b12059400f41a104100b0180010007040c09980d00d5a0807841900c1c0c1580b801418640c0400120010036106001907254181035002d03828070101c1c0e42603e06c0485002040d0100c41e42c64100c002c88c94900c00c07082c07001040160080e000294404501d041c3c0010203643d4a29041c0320041c000d551100b4010b0108258030444902005100300765203030814003034010b0643c192070741c07010740c0c0541092508652807a251240182110428026108000030a000034500d0280d1650050260707001019468115805000903e800d070341c610445541010f100d02a07801c03d41c80d400b01c115072040c052042503140801c0100c2c001040100040140031886c01500100320b543c6580c0100026444203200300c9105903418004100600c803a124880462003104034005d01e8180e60342e03102c034108141039401002240c0d000c0d40340342101501d0400c1b50f6112040444c0030794258110703a07401c0c180f40140d138000c03802c01c4011a51101403090410450f850a6013003a101207404c08 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 933783093 1250 933781843 933781867
    0x14220501021810020d0e0f0d060905010605120c01170901020702092701050603330c04180212040615051804050111161101030609090606060306120f0b0c0c03 69
    0x40848240c50164482085540c0402c0c40419245c40381301165840c440c0c600305100801c001e05030140715460b40111050100b400081c00c0744203c09a0300c1c0b05200206e2000d00e00000c01045008a8801c0306013500024492500e03603a000d00e40c40044640365164007500e4451599041c020300403160000c0d00a407248080c89242d80c01800d01544900d40104060194a100803c0ca802d95405550761609503001141000440036801e150620103107036030540701864a050b44004200400a80da903c421140c0042c00b801001814208803040186180b401d61811101c401d403101580300043c805820f86030340f41011030075010f004003034038005c0c80e00a1001440500d0001100403c0c02c00380c1e4100d038150704e03050720340340d07080340b4101500d80300c220100d0160741c82c00301d41c0c40d0060141550705640e0704050351910086041c40c1c05100d65034540d17002e00c030001401400d0100140403200d4680002c1c0d00c17100003181d03660000e40b280790141050b9601400103240d6440d00607035201c1c2c500520004c0c284070700001c0340350304400c2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 933784343 1250 933783093 933783127
    0x30a020415020c040b030d140304050f120306041803020d0e03070b181905090412121118010e150c0307020d0b150f1e01140d0209131422050102 63
    0x200c81164104262170020003050785c0d03450500070a9010070031519841d881204c2000103140e11500a80a681d20342001d1800c036810b1019410450394142c2c03020091104609013881010082c840b0303254003003074094807520702035500d881c00280a4200f11110a4801e040e45041c401a002043c3c84402c45884080944101074003500782002d17140a2803420100c604e049825115003012141c0c0a480580c1603250394841070341608041140105005019010603241d40180c071608031141c0c22328004a46400c1d4030010810510301c1426298100302c070034125100396603075104040d04090400a046540e4280d088106800c50084200c042e40c400c14480c040001d21440125552045c003100500e8188103560904000001c2d0a80c2d00c0b058100c20040011846031030400101c0c18030107414140a41040181c0e000c503400b6a0190449011058000c44c0e0001113042c200d0188000316000c103c2840b000400d102c050009801c0140a0082152007a407500c600070b9210381c80a80b100c1d0400000d40da1208011104c01e040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 933785593 1250 933784343 933784363
    0x418050f030d0506030a08160305070209070c030206070906091811030a0e120a0807120b0d030302180303030c0a051e030a090b06011d013b0f0d080f030a02041502 71
    0x1c60700f8400040c1c131915020070324070b01c42a4848201410030340030000503d00c241591000301c0900204115002c0541c2e1025040c07480b408a903554030100c90580d107402410610044e000c0780c28840044400d1215640022001060790b40742c015444d035040c5000c40e0310019103000c00c514501001c002003808442012500b01c06034141080c011500018070514990803a8481c00c00d11200296070003010458951195040c501c0509001d0030205241c14179000003411000e90480440c0480d90000d041c1e4080d402c50305400c0c07070401c000c80256080d0725142107810076500c5804815002c100d000100c002c07400b900030b18822034000080d1800c544030b04d0903000181c002c00d0646425500d0242107000039215601c680c00c0030101c6003005001c0d00500009200660300300c00002040c540c94618600c2c841c0842c07105d003013421000b10703c1d0303c8203000c1c054845d03081c071011014030800903008100e00d00f800400b00300914101d4641223414030310a9680d03903032510003800a0141d900300c100004410400f407038103a58001565100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 933786843 1250 933785593 933785617
    0x1020f04080123010e0c030a0b090a1b0201110d020a1e0c0c0b0a051e0d1503060b0607050d080a060515033102010c0f023109110418050f03 61
    0x254040c0d1409052100f0800d200b18085011302038000303400f620445c00070303640042c078200000c103c0f02038440c009004010211410101180d0718010082181100c45001180441e28002007104072500c4548691512445800c00049900000e0200420b4811205c44103880961a4006507400c0221001018a10811000d44064001ca800450702522540441c1e5000b0382c2521100d25007800066071030080000000f010303081003400d102400e1803031001c0c09034410104003112110a1241503282c032604582c0562100d038014141031282d400059400a1520040d00142c00d00003410394501d4880e41c060000c5800550b0440005038034a070349140000c0c051800340c60000d03104190414a040701070b510b007006141c0764807d420720103c3c81015500500b2081d20542c011040b0712410040380d004540c185542040802001c0101d9065a00503242e00b646d440c2da4504144044c003520f1441d44400b00c15900440419200d2540c0b030710303441020b5030101141c2e04141d0f03020b0156945101c003c80065203a80218019004d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 933788093 1250 933786843 933786881
    0x70806060337091a01142116060905030f06040b0c0c2b031a0310090807230f1603032a0503180109050d0f031715040b0f010c0b070201020f040801 64
    0xe1540000c41c99012624000391600d0164050f11094050008825280300341d02c3c0238003000c82400401d540780c1103001e8421621843d110301c0c603001c145850400384010380015508000c0c14000055080d4000a8004041c5240692100d80c01c0e4000d40c201010b03242081895030712a099100c20b44541110410b0030789054070104002025081c80704c2c000c419140300301394181c00c242e0421a01002c16844a503104e8012445c0030700b88840f9968000c3e8009800701e00480781c14040010315205901042042c030b2004901c8082c0625440304203080304038403618000202845800d0920f41108050b4101c0605a03541040f0300c01102569410002d85076030210280e95100e601c0c00342540c1e1507502a01d580822101e0190445001908a031105e0108281c906401c908101e0001720f03030840800c01e0f020f214006e441d803402c04c01e450012031080000b1911400f00203801808071070b905c100280c0c0c01c08034041c2c106401c0310b500e05440c3e64426041340244505020001c0008011070041964101503000c04018681a180c0c54 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 933789343 1250 933788093 933788099
    0x5160e09040218151e030723091509070e0909150c0f0403050f0705130b1008041712090c041e0b0a05060a0503070806060337091a01 58
    0x503581a045070060b421484010715807030b030080507200290b8080446001c103509004082c2c0012060074030b02d24101c41200d4001c0d1012040c0c80c050100000906085c40d040003a4400c0000c0c08442c180c01034007180c81a9208400200c0500341448000088403005154018900e000a03002d02407020b01c0000d180200380c0c40c40080c08500b000200c040802800c4441024166541442081e4603400302007600350508050100100140040203a10701410114000d007414a00700740a10807898688682152581c1c10507881c5640360301c5012030a480405c4c2441e200406039540d003040b40c282c04064441505075400041c0300c0f0800f8512034190b030300400e130410580f4910701c1e181007008103803000c611505041c8205032203442c00034899540500540c100c05000030a600341d0301d2001600d44d4104803148000308a00208010140303a0146030958000c6040750f54900310f08040c05081001c10310703c10402e606030b59996101150706a00f01c4181032515455105210169081c6801d0380c032003070041107a0315989400c40001c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 933790593 1250 933789343 933789349
    0xc050411180a05030303010f061106040210050a090f08030a021b010816090803040b0d1503030207060309032706120c02063705100603020906180307080105160e 70
    0x10200c0c091580c08500e041003404411440c03001c241d010300030b6021902580000d8603441c2440514001c1c2100c0120b442094907019000c3e000340040c4a00c0c040d640c00c4070003008016610307000ea5590111513443d00c252500320040d01070342d240915401c034540c0c03200311410010344c003a070000040040e03640541c25603001900d01c50031800381e541200d028601081a4600007044146c3c0c0c826498021135a900d0030610050b500c4080905603030043d002100710000010b1240b04a034910b00400d4200160200d03240c10040c6540c42c0252245007501560382090b07181c1c2e0002e000c0c1841440c000080c06417042c03202615040c2e41c040c102c1144001d21412011400003510041409200d00c606400750203141c01920b0140d4581d0b1045002c2c0b8051182e42c1c2c03220758084038036030000340417a0304c903c0083c04c1090b00240908207142203481c1075500340d00039420980108090360440d2101c0090b1241003007607040c00300aa00800000074100312607a0850082d561915003000958000c1900b510803401c0540c4801000382c140d5018 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 933791843 1250 933790593 933790601
    0x30c05040509040f0f1e1e0c060f0c020402040e090d110c060a0c051006032307050f03011404030906230711060c070311030f06010509070c1a01060c0c0504 68
    0x700e5500c02c0b1940006004607800f90801c16030300d8810040f1031001c00300f41e555a1051184040384020f00b00701e076584c60781040440104180d5000242941350449841c940d0b8040000d81540111010011048021f011090041c0344050010368001c0c401d6407941c1d181c200f103000400046440d0021482806001d4600e28040ca142d0705020440201900d18034414400b4007610b540704a51300020031140308100c401042043c0180d1280c400b1000b408204940740d030078141981c0c0c030b210388078054010828595032154200005c1140468109a0351440e40040400000303005110000d542c035804540c00c82004105071b4402403100685d000758482a1140f0301042d00c2c41b403102c400415022007000108004c601180001040202110000341480d1801004503030321070408110340e0003154101c20310320140c0e0b114541032000320061407414008007019890140042c41c4900094240350500c000b2000a1051013198883e69503548440718074264207581d140c4004088403d4640c4c2a2500c0121a1001c80e4615080c01 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 933793093 1250 933791843 933791849
    0x5120114100305191115030709050306071b0809060a0908010e070b0406080a06030501020d090203010e011b0f03060b1b300f0d060b030f070801030203120a031416030c0504 75
    0x30042c49102020300c44c5100820391184191a141c0107040515610307038800040d544844070b41d81c0701c56100e003840da10180c1846110340003207101e07030442d10811001c03a03801084005c070441c6580009c20710038a06d08100c0740d14030440300c0c800d07004400010300028042c0c1001c208012107802038001c200c030f00e480e10349882d19030525008480b002002044100107461144440540102d42c200b00015903940d2540d80c00d00f20b07031000e035a10885540b114407410951400b80716806801c0a2400240010200e0100008988210345040c405210380d1307209000480d80700c1d03482034006d410300d940700d2581c3d80b111700242c2a072440d524598a4092150314090701e0144e0000f9040403d20001c0d0030002891079207000d81c03d8150b089081e04c10250081030024030b0000c4a00d008902c0200f5045514650340c3c20140c10384607003224000e2500c4140210b00004000507100060525070454112021580381d44071540f00f140580480d241102d1815100401e000f12002000440320414240b928208482040e162003500d06000b548 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 933794343 1250 933793093 933793103
    0x2070609080a020307170c030f0615010c050c06030714070c05091305060c090d06060e07080c0a0203031b0d0504241e09080c0a0f110a030b060f0a051201141003 70
    0x17400b009100c1c6801c510320090400c180564441c1c560742c401207071900b643e0b00300c140c1240d0300c10702c140100e212503000040803101080c0b030031003803080c12512182e40c2e070019905854010a00000002c081d18841c030510140c11a403100364942c0c401050900e1a0711421038081c6900c40d84001011031801861821112042903000002d000f82d680e8409552034280c00c8162281d801ca9040603103030b400140584561000740c20040510455400c05660042060320018902d1843c44000c210102c034240e000825030f030703022040740c44500f8841c000ca281404540a0400740707100d811b0030941403000300702d0f89140c200c1c03503000e4064406105044024190040d900c2d04140c100b00b40b1900c20401411030a646c100b40425030186010500d00880007564918029400070150b410300130070700680307003000342004110300311034402c0307458400180c11510344003104400030340f4070361181e40008000035403a20b480d0b5001004000040c03400a4200aa14459000c0c0420705a000300c19884d0758002558143c540c4030ba50252034200d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 933795593 1250 933794343 933794353
    0xe070f0c020f0102100c1107060509010c11010e04090803040302100203060a12020604080d050a18030b0a0915111c0507082a0403030e030c0d150b13090302070609080a0203 75
    0x5074007031040d4404440c031868114040e00c200304105078014000e2070090340c10341c1d0351424250342485200b81001c00b190081410400b0803c0b040c00d0326a80481e15210042d04041c0f0740109401c8580141c941c08843d01c01c0f15009800c2c628018140002c12028502c503c1c0070350260340004003100c03c004103d220440b80e8a601910000e800e002c0745440055030580c80d440130f0401840c0c076460746851482c0c40e081c4030184000901c0090544041070780030a04050416924000007540742c20f41e40c030b600f08000000c00041ca550340e5585100c0070703c200b41c4400c40302d19607072020802502100b110010455800803d0360364004c0b2442d012450080c00302e1003458801c4103107a6816105481b03203040b16188403441e40190b40382c10328010710100c41c915160b00400056100340c0794402c0c01a4104181410941150b101621070b81ca00104007022030711125440d5003a45800c1070010fa00d00d02840000c3d041010f940704411694034207100c1c5410940c000803404103880454540d407030880d03602d8500c1e582e55401ca5400941603000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 933796843 1250 933795593 933795617
    0x1802010314042607020604030605040c06050403080301120510050703150807030803060d08040317030105011202161e05011e0501050303041206020d0b2715030705090a021309060e070f 80
    0x640c1c60100343c4040e0004010315140017500000c0705500150001d40e141540d51041c0010407da811170312008005900300181043e1030b6407946260790105100d41c4900d00300c904054410400c040c05048281e03031f0031940400440c00c1907100100181040b940c0c220f5a01e0113644041780c40c0000050001c116507000161502d195940f000b03000325040c486008569a031003d0101000003401d0b040c1400d40d40200b01402c948a40c03506000500e03845541404000342c620400c0f0881100c0e944428141c95640c10071550107a5250303840a503211600c141002800300d503c0c018620441c1d41d05210380500300110790703c05200c141d8131101015181d100d81d00c14600019080c1c0f81c0900000e00315000b40041c0b2b00c0405000540302813240c0454400100000c100c0450a440c280502201c1c1d8200d51403030700003034429202240c0122042c04a07940c3c01042c040e40d44920007100c00600c0810450701201d03140c584d00100c5c80c41e400c2d5a000e0301c4026060318040c40b2011401117002651907840f40d058513036000002d41e600008140d0f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 933798093 1250 933796843 933796883
    0x6070f06020906070f0809210c2809020304051605061b0a0f03080a060e011d0916060f0806010203090117040c05040203090d0e06030c1903090501180201031404 70
    0x100c142c1030702d80c100e4002e201e003002141e0070981c011200e80c000d80240f940c4403100000c20015002c01e44082c40c4c502400c451024100c80c0000303144a42d84415107001d00c0c07007480314000701c16002684001550310301e80c05c00b012902d560141c01030f44c0580d100d141200c00000d59448050b00d0342055010300d13500201c05200c513259a50222148030284c1002c071055079941052905c070403480812501d405e0b00860000c030306002c1401910721689005210303105569100354101100c8000421840c60108607a076051004542c42c1a001d100c03513103000e03a1000100003803503550b26016214240701405440841c3c60a40060341c0c5500100450b0601070341651101c4500524081001c840c4a001c0c00070b8519426520007c101038070340703100460203940c11000501080c690010000c1c0700982c00480107000710401c1c000e0169a0f1a040c0517581d10503c1c0320341c3d441c0c43c0c0c1ca040c0c5049000b0200c2c1c00002e000c1d50300780130300e0392120f400e00c81d8140185030003079070282710404061501c22042c41c000d030f900600f0842d00c51001035a0203 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 933799343 1250 933798093 933798097
    0xe0703090209010f1d0714130b0a0c1a0606040603272a0501020a0807030c020310020405032e180804030f1101020102130b03130f050c040b18070c1109041208010506070f0602 76
    0x442224500020704d885010704151034201c0c3c400b000214101e44200002c3c0555607101c0ce0507800c60304624041843d014011541c0360041e0300c01d01d0107042e224424007a4050030000450030700c10b0000541584d103010b038144902005a030340600300e04003982c1420000b010b01c81e5613119090700c4040e0014090b144442e95003415a82c844201507040000702d080c010010f030760030b0003100c81c444400d030009a1954200002c15041a1219050a03005003021981c1407500e16031021030001c5050b10341001414140c46202404441007a82d00103081c0c05002602104019083c40c0e02404071f40a00030801c00c01306984016400c03441031020392202142c000e6420450001c03544015035015000b0103d003000f5900955655403450031002d021100c41d0007c6d000004681483c0c0301d0b072031381036008840d002420500c001e142041b560010701020308011900f0030107024030080c907201c408041e0010700300880d546070600f050604130303111170190f0002071b038140300010341c03031a1a40543c1c5d69250425142c0ea000034a5941d100025 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 933800593 1250 933799343 933799357
    0x311061021050f0601050f010c0f020405061c1a13030503240406091d060403090e13020603070e010e0f0a06030506030c150c12130e0703090209010f1d0714 68
    0x600302140301c20000400610410310600c51940040041e541820104600f0320884064075041080c0c1c070300070070089180526030403c40717038056400240548a00c1c000c920980b21211304500c110080000110070001c0d02c80040300d0350803038000241102d486281c07051403240e8040201130009002403001c1002d0002008240b10303540c603442000d00088040e100818280c41c880c2d8884540c3c2550f544002c0d4041d90000c40e030307120341c501c5100a0070180c41c2655014040f80c140d0700405076030312403040000c6d0010111012019040b03030000e15994803845c04040013081903001855442c001034060801d880e0f181400f41340700d030180e83c004040240c400e003441d004400401d0020402c50307051140081c0350200392240560100c507008034100180d038074402200366528103d40181940e81038241000059070104480d0003210a5882e201030000030b603140d1035030845c00717883d0503240a581300c0c07041400001e000d0000140c040c12100a4545083c0c11a2a48039003000c4400450307141002c61051718046d0038031403a20009203d2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 933801843 1250 933800593 933800639
    0xa03020c0709110a031d032a070b031509010b0a03020d2c120c0c0f13110408070602160323120a08150f04020307050f07080703110610 59
    0x2096640e0b05800054400402070344900100009403211004c0d454000c1c40384181034482e003020300d42d00030141199030744101d90b0448000c145140000b000e01124808952a013556003080301c180c076454030800c025951007074804119000255583d1070103400e04001035030403550305201d02402c00340000d0003603010703500c00c00900f080b060303440c0d850600c450b800c2c0042c07800714018010304201000354814401d1600b00c03d05010415903005000da0310f240701000540d4950b4590a4902d1042d0812800105003c1007241c01480340d401d05020401c20340c0300442001e401181c000004680510b0343c1c0368010b82c0c465025400340312140c1e2414030107101003036036403038101d041c00c041e8000141d038007250325045401d200903103402000300a0000741c00131100d81d0140060f0f4104200e1030122049080c00c2d40040d8000c001103100c0c60250741c0110001c0c0e083e5005a0555118030414040103958000c0e618003801039500040041b400305503064111408040c1c0022510b20a01c507001c13401d80711604101e03404000c0142c1e00c1907045 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 933803093 1250 933801843 933801853
    0x70c0306111c29061204110102010b01080903070f030e330702150705030f070f02090c0c061501050d020c0109060f0b0d060209191e051e0603100504051315110a03020c 73
    0x45c1c2c080340011403512407400303540c002083c40495400282582c20108513181000309520910585420100813508001d41c04bc0340e028803900c90340b4081c1c42001c3d500040e01e5002d900081c003a801840c4284511011011452440d0001d03040103006a41754090400c0282d080100020f00c82c061011840042540d0f82c09101220f0808010745c644e000c181d0301c980350840712104050103c1c3d0440c10708481d41c2e500030654848290130100c005020350364a0350b00404560b40d00e8400c20060030240d014030119001001c90b031f0003c3d5904d845510b401400390241d08001c070340d101d140079108140c40348148a22034084030002c0426035481100c0d03d40e4000389d040005089d5000c0701c1c1601000c529002e804107503006100000103020641440e80d1184d1f07035030300c1c1e42c0e121602801c10b091081a54103155000a28518821242203482e51901c0000f54500c10507900320342e400a10300010311020103110380104400500c0381c900c2007002000c2194000940720f10140070011004103000200c0e1a0b400381e0050144004000101c0d1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 933804343 1250 933803093 933803107
    0xf030d1509020307120c030501270b03030307050c0613020d02060d230109180b010623042405070305030118020705060705031501081b070c0306111c2906 67
    0x70100d0b40159010710200703000481081024125016180350034800c0d050401007985002485014044031181c0c07021102014100c45200042030791006c1000c4c8406000c80b80c9a10301814080c2c403da1003400400203070b1042c2e03000104008503003c50961415030140c511f83c1140000d900f40070207078206040c1e8903610760b02e52031229104101d01580e20072151303450072032001035450410b400e400c9036048003900044141404460740405c4001c5d41071790440c0c186140640940050a070252030700010800c80207424500041c00252902844040304100c00070f80a0005008251000036106442030740c0c0001c3c040b039070501c010030042417a21004651082c29850151134243e55640d1a8240340d01201c41e10b010501c0031007407190b245103040c0361640b44071082c2000803150405501c020000c0d41001c41412400380001011302c100304240860900465001805210000c41c40202000e103801c60034140314021140c0d5040d00d0940002c0c01020b00c4510154114160680a503a1040000204070212900320008000d82 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 933805593 1250 933804343 933804359
    0x20309100c030b011101141504020702120c030c0d2402040801090614060109051804030c080d321819030909060906051e042003180f030d15 61
    0x21007034a029900002c0b2508a000054904034418012956580c5003172a042c000500303440780f0381c0e00f0403142c0c179203240320180007000100a0b200d80080203400800c810740324264040d001804502440f012815109500b40f030000344141d40c0500c14002d0403000311044403801c09131000f02103c00c9413002c510007501e0f203a03c50b4091400c0d6940e03544112801031340d44003407245043c4840d04c100d404c00002d2030128809840c00b03001541404808001248441440001c14101400b0303e00400b005907006245a4503040d0745650b00b4000c2ca60b01464a4000300d81e030120800c860a03d024449032484d211030b010703c107511184c1400c0c120003c0d080d1116400c1c8a80f484505110500344090b000c6544a03030750b2000003034148860704040d01da40c2e0307011031001c3c0e060010902ca1030351012402e200221003228500c0c2a00304241c00100030b031031140c80392400c2d45079090002d418070b0081801144944103100c0204111700f00b40e81903583c1c8000c4001c3d51411904140000c64208078280c000307a10090f2000c00d003048058503034540d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 933806843 1250 933805593 933805601
    0x30d170a0f18050f07080c0d2a030f0501050106050304020607030f021510090605060412080d0f0911101106060f12010c0f0908030702010c0201030b042a09080111090402030910 77
    0x10960702d0b035216070048401e5080c104060001b83c104040138054036040100820402080d0941c002c26507000d00c4085c50000000142d004610b44249406444140d030340c1c1012880d80000443c281d410354288400800c46d14014000c4a01039580508500d1914806c0c0d00e080780c0b1265080600d034218050841403201c1c140400d000c0c80d008a00ca00041c440d204c0c0f0b0a00b21400301d40055002e1400f800051200300078910000b1810454070b504041540d0742e4801c0c104c4000024681c2c60300d0b109055250408807020b201d400314007540700701019686c203803884540a00c01d9030305641d0388503228200c0c0e02140c001801424810000c2003620b1026006c40e0504000c081800d02359107800060030f000820074000e49007802c2d0721185a0f80104071280140d4580031290300000d00340d100020700a41407540f515a00126611030342d100000800c0080403e4045026403030302745554001e8152203c001607201180410b007281d0610a440601426140341342c50142a0020700c0040d4000800301c0c44071740640041d5500103031361400707 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 933808093 1250 933806843 933806891
    0x170d0b0d051c0918021b0304091b03050609060616080c0a030e060a0e0103020313050a06060501090b0a08190902150307080106090b0307031e150302030d170a0f 70
    0xa0018580c284254100c41d141210b0340c00c04220f2601000c001d014035414110781c611030102005603841592484400d1080d600d06803039000d5200001e4000346506071544003940980703103040b0f25503031005003401c120255001901c00f01d84c0141302c100440c40a10f4600003c1400804400781400741c40d5164a074078000d900314101c3c1240395080000d06904045d4024040215004211000c5050000b00c4100500c1840c0b0a0945410b05500001091075280d420408098480d0b1220071185003106e42c0c940700014010b98413540d0b0108100e4040807513000415002d54490750001c0e521402955181108400b2640d254500d2200c2270795240305000141c0c440b5098081410365000400e030b564104544014500344c0c050b400b400070003051460900010702d200301200d8021800d813030080b500c1d44c05200c840100e0491540c40458080c60b20100c0020401c0140c41d071b0f400c5a000314140d03501c0881158060305c4101079416102c03a51030302000001c40201c8203900100300d8040881001171400452151001c01d604454 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 933809343 1250 933808093 933808103
    0x24100e030c0a12050d0c0312150e070509011805061e0708030408030f0c0403121101110d0e0f0606030d0c060f05130b07030b100c1a0a1b050304170d0b0d 67
    0x60b40d0401808020048502d609aa0b1b243c100301250a9450040c80c80c8400c000b1144410707108c02d10f6842c0b0340350b4080002c0241c110320000c04a10b041c215000b07021a40004200c0e0b001c5044011402ca40c042d03005801d404032000989040d10700b110310124140d1480d043c15288001c440b05100010200e0404400f8600ca40d1040181581d00d0602c44144040404010054070820400308014030008000100142c039800c205e040030404190050170443c09084843c1d1845051a0042030010000c502d42c0c11010f610340c100d500361044d14101c442009d032180d10803141181c01d0b5105600b00002180720f03030111070700c150007004d00264010184500c8030646005071549441010383c81403c1c42807201400b440c5402009a084c04c1200c80d4100c2c011640c2c50300741c242d00c40c00340a03400d010b88050007070b201d0301174000c10503841e44c0007402c1c1360003038045005100d030710417400d00c0c000d40002c4001c1d03060180c1c2c11640501d8024103c41450480f071881d00b1013640c0300d80c00f2512807e45611103480980c44188031000c445e1f11034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 933810593 1250 933809343 933809369
    0xc0501020712120311070203010c0f32090a0b0406021b0301090b0103030302031009110a170714090622080d05071707050f060a020324100e030c0a 64
    0x4000924100403600102e01103a5070241010001e007442605144100850034041a03400c80800320544902a0000280d015400d2025815034190700c1250040a0056500c1302030b1000b000014921032001303424030300d8105903415071002841081a2000d0714a5803401403001180c1d0781c403007038841c040c0c0c0c015521640240c0c3c0260700400328889910314100e940a400d800800900c191078581c0010b00d03006203c080c041c590300101182c0c811002c5031002c405440c07010420b01c0310000210f00c03405103600c007541c086d0002e8403251b8001d0f030050382c6036000c50141c00c2643d40e180800700100ca610090340d1040c02d000d548040200300c50703c8140940c01d90100a42800d8980d80302c4945040e070742a04242c1622101c1c82004010804407001a04071070b0805101034a0480141d02c2c0c0404d403a229203400f0028170409103520500b0104040b01040e80c00542c400c041c1000000708440c41240344c0c1044a8142d92801e9019424449a0001a100e005071290031074008003266240c400043c0411145161a0858640b800c02 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 933811843 1250 933810593 933810599
    0xd20072d30050c0606130f091a0603070317130e0106030203060102300c0a02040203091612020906060a2a0212030a140a030b03010c0801151e0f050f070c 67
    0x10685040c0ca019169042803883e0035418081d407900c61800410051003202c40500c0e1594141a651060103001210300080200581c1410708184404140203812076040e9014009181800d0209a1a0807641d01801000c0c1720940c0e814400207582001081c8034042d0442c0c4e600040b842007540c0400e008100f542c1740160b4905120000a00b400554441340410490b0b00e00c0d010015000d07044401c80300c0c02d02c2d205654403520004199420415001d4010b0742c4a8004002d1080201c000700c0d0300401d9a0482c0074110341e0a569203801c846407210340c00d0281d030040c68a40000c0e81070416000810000a00d490000b402c0c041101c1c1401000c58a07a10180300c070355110004408509040000c1d4000750701e0400150700b48999910004c0c040101d022a0745041c50011511021590190300801e0321128018000d00c06410071000c01040701400b44169911801c0100289030060b00503d03500c10004200c801280c400c40070401c043c0ca803401821400010000204106c0307a80700588030140131b00d18072500c220541135103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 933812949 1106 933811843 933811913
    0x703080405100513080601170d020a0201110307050f0715080c0301030f150218040c0f0c0b06011b0c080c03121206150d20072d 56
    0x411342d080810032504c0803a0840c181c1e088240c0100c0700c40d141603c11070307032640c483c50480c0158200b8072440300954400c1d0b152055944074441103910f40380550355150b20307120007004450700c0c5800507281070140040c50b4031030007040e808614110a4a00f01011f004405104c10b100080001e6494014030302040160f040040e19100c3c080c1007151100078030601c200e010790074107011601c1240341c41801650b407800307411040040440c95466010b040c5055941c0308020b41d028100d24144840080c1100f1016403000747ca5039000c0c0b0441e0032072451031400007420705e041d004015451103901304600011500e4030030000e881d01c0d0b1485550200d440c0d02d40c1d002044080b40c40c080c10314112240043c4c44014407082e90080090003005444034000c0c81c00c1c685030070449028160004242c8000b403180e504078290740a50009030103034207180b08645844141d036504076044024004e000c2841444040f0410381c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 933633093 933812949 := by
  have h0 := BRFrame.cov_init 933633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 933633093 ≤ n) (h2 : n < 933812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
