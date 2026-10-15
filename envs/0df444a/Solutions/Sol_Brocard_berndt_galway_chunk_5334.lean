-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5334
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:31:34.512989+00:00
-- url     : https://prove2.me/submissions/039c9c2a-6a52-429a-a871-3d081387b790

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 959172661 ≤ n < 959352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 959173911 1250 959172661 959172667
    0x9053c0105072307020d0c060806010c0f03030510032f01140d05060103020702100e0423071826010c03090b04080304061b0f02010f061d0406020409090f0c0902 70
    0x20300054940007041d100b0149503d80b0700c2070540101201d009440034241c0081c410b28409056042c011800001d5000e140e000804900000b0340550103901c9060845602141403001c610301130320110028000076280c8000402c1c0401c0000c0460380903030800c04500b421b481c00c5445081d0240c180701504001080c868107001c0c490700704240f42502030301901c0d0301c43d14014001c40d00741d8440700124000d11441da4020b503c40e401200c0c5485035988546117060012003a9020044880d5550092900100c1c00031103610940c00c0000044c00d0b00e108903000c20b170203140900640b00031500c44444144000200d054030092280802c41e00c0e00710b5409000d10f41165042d814200980e01140d2a014910080100090894a0000040703400c01c81c441d40032000c12030040b1a0001032407115100100203844901d9035500660903c2699030003000300707204040480307442d42111030400003c0c0c2007119200100800030340c0d002d43d003400009503280e01402120001e500c80c0713624031080030311454034811104943d0002540381c0d1042c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 959175161 1250 959173911 959173921
    0xc0c120c010f0e04020412150f090f08160b2e08030405060c031606051e22260702091005010e150705100605130e1009053c0105 56
    0x7803640b58404500c0c00300c0400e488480824007074861a4081d4443d0084408103c080c004060108400c0c2e40705c056052000d440c034400010b0a031801c00c0006440300000004540c00a03203680c0050541c281e420f114581e00300880c2e212598804801c480860a80c86003552503091100040f00e06600310b420b10070050034007800c0c0009581d590049005460003250009102040c51a081040d542c00860050495801406a2400704094007050303621a144e051408440038103030000c40340d020322134015282c154000d01421240404030b810400015240962151010000f80a0120520030400452032440c5e540d190607205102094000034903014a8070f045607828002c5d07a0b80400c03550b04005003140c81c0320148040404102c0c0610507550000c0075031040100081034242c144e082541180d208544a0300910100b0340514155481c03d0140d034885d40040b02d4030000d030561a803106080500600845080d90000d151103c0d02c5071542d064106282e0580c0d0800360412581c00f01c2541c010010700082c0801c0c200 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 959176411 1250 959175161 959175167
    0xc010b0306040f1e12090512030c0607122301080d0801032001030e030c010501060e03030405060405040e0c1008101d040b0406290f03060c040308070501060b0c0c120c01 74
    0x1840802002c2c9401582c01a804d501a005624501034111032a50100d4a00c0c17607014080c0f0005124040c01a01144100d458003140071040e20002c0014001400c0556604e440840e80c0c0340c40680c00a001664070325030047e42450114600d5000000c00007482e07481c1d410000035914141c411a23680040104500050001030f030402070343c9180941450306c0d050b4425040005901401000b030310004240300210b54071200c24815001300e4120341840d00c03565150741c00041890b8072441a070083d5500403130300300410002800d2550002c0a540401c0341071b5444241039800080c1e4140a103203c80c40007499103020320441c45032031030504000307090442406000140580c4100c0343c07404001e00240c1948603180000c0c042c002c15405c405100e02c0c0070781079400c01c81ca00204120162240d4000139024920111441e0544e00300084c20500400303084440d41c4c1081d02c0d5603a038081541c0030300d40032240c6540350340002030f82c1a048000f81455841d060082d1a00e00403040500642070840ea000e1300c890750240e0f14000303080c0d030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 959177661 1250 959176411 959176433
    0xe060d1a1504080a081c0e0d12060605040e250503220f12020a0b0903070515010f031e06020d09110f09060d030314040302010c172203020a06050405030c010b030604 72
    0x1178803107950b580710600500c0d0142c202c0581148846c8141c00e15100030304545000c81c070803841701e140d9120030541d154120340c1c00080b00c2950044801040040009100c2d00c000c0c0703a802c56001c0c0d140d0580600d03030b108404034680140071010703d04001c501c0200600100039046041d03451203d007004010f05050a044d15200080c0002000252020300c1e48056003100920901800046540002c454101828401c4515540e40d20a407800c0c2d542c0d004000e10300c4d02131059001d04c41d0407110a04c00f0802e0031411a200e07040050b001f04e000c29699401032034044002202030018040b11644840c000400400310f007401c600214480c00d445108991070310000c0380b10b0b03545210264020400390741c41c450b40061441e05400a1840c0c17000030391000d003140700b080b003015815002064400c0711644c80c1a481c07181c411801003405000d48075103c2c1081c01540d003c4400e00d80421410015000384100c41800c9200c0c6c0b508003c0395025203081d6540c0d000090300c0c0807200c400f4041c0010303900301600103005a103419155241448 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 959178911 1250 959177661 959177663
    0x61305060c071401050408041a0424050408070603050601030c1e0516020d1104151401080a020d02161101020d120504020f15032d070e060d1a1504080a 66
    0x4070001c00c0d0720041c8a00010007200d0a00c03038100801460034242071400c4950810b11821210183c0b1164036102100240c0c03d54048540010710080d800c554000d4103115002c48190110400c1400c0c23000190301a0204685801811a40c6000610782040b000060545da03a0b40f0400c0e007072160122801a406040b1203004c8120720407484c0c20760700c4400c4c8985a1a60310102d8030065405025076500b401800088100e1081c0201d04480801607140c51000f0803482c40302074410f100e0380030402e0300e02901c554059811941c1c0300316480c1d001890056400c08d40c0d41284c000d04082d2050800000317a00b8100300041007686c20f154001d00062210450380c0e0703001080310381c0346000c0b00c260300d485034041421074642040410f85c02c0303001403400c001c0076040781d8403540ea5042280c689844505940000c07140d804101c440d9810a0580c911016417596144000d0329220354600c0c80c1c0b900108204008001d400c403a2041c0b0021100310145852144400020030600711030015035040c000314200005c0084040004042c6081 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 959180161 1250 959178911 959178931
    0x80a0c0615030605150a0b0d02070201090f030506180f100e07090c17060a06080606070201020a05070b1c021318060b0d14070206190b0a05190806130506 67
    0x604103140920140c041c40c110240038009601022080005503003089200d0a205400300c0c0e0b8848104041144a20451191075402c1104000d203040e00c02031900244201801030401c80c0d00a40c1e2048218052502548142e403140c0009050084611060132030280c00d00d04100100f10b4203188000080c1c440290040c2d00390040c1e5070301d5540d2070000c0140440b0700100704003141008500040c3d100034000150380302c0681d0359104000c001500515020b1416070a03030b00c10795542d0306550303260340c00c1c004280c3c0300c1d20069040d4840d0040800000c4d41c02c000d010003400926013484e40303464a1082c0380e102a64000120014213005004103a1401d00301089003040310032440c0310f98a1103407074000170ba0041c8829002076070503150004140c4410f4045801c4102680030000074110284e441c800102c0c2c407100103030b4a04119a80a408030b011900c00d0fa0040c0d0086000100030b03102081d500e100003003801e445503803142180420705000b000400e2061002c43d0b44401c4140008002c10019941c558030307880020100c140c5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 959181411 1250 959180161 959180177
    0xa2628150b0316080106080a0e0c0306091b03070e040f241a03010911040b0621040203060601090e041e0f0b0405070603020c0c060f1303260403080a 65
    0x105854540080c4250a021400200031984815100034194411100206a0104600e0741c0c089140b24040c8503048030b0840c0d403480c000e0f0700d84080410242640c1140c8003014800c189038075a95580500c8020301400c0c44000504183c0c903601d1006911040d600080c46c420340004030100107407141c60140b80c3e4415400300d1104900b80d118a0803102c1c01d8010269049040d002241544400d1943e9000d0950260f100b9080042030600008050070703240a0503000b483c10309903900307501150410341c100c0381407204024440b60402200021000a200300742c102001500d03065804d00c000d5043c04c0c05401d030400b8003860070200c220b09050883c80b10703440213032000388518807255040c00210341064541c0c0469a100100c0207e680c05401c2950440400380d8003620180500c0384001001c600910883d201c0c00b04585c06081040f40080401c541d0343c101e00c00b6041b03001307000c200825a1082c030120380f00103188240a00c4007004030310501010601c03905000780f28050001c20052000c10000c80075582d1442c0303a440c140e00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 959182661 1250 959181411 959181481
    0x18091509011e0c09150504091d2a060d022113030503100308040e0a05070315232808030306180403020f030a030c020c0d02010f050711060a26 62
    0xd5842c0b00364080c1d56802c140c9250307421741c40e5000d0014411104a15828801c5000448011804004159042c0b8040d413111501c0c1c070f406c86020017580152081084240030300385030720020a2850b488042d105010950018004540d8540741c01c84103c066040c40c000d1000e490104490981210000000707404e00c00084000341d8100c42034422103001d55031028080740c40d50741d100303004000303200c0070754a0300704050602c00041e810a103c1d2041015032200500078200441c5404600518240141900e441d652000703988034500e51526a046911800e544200c41c42e03a0000408024551041da0003a241c250410410302000d17540b0700c142a0505428281401115103581c5420307807070f080c0848103440c039a0002048034170040e40c050340200c4040d00701c0e400307980f0140070070801c015681c40e91500c0280483c031282d140004980c85100a0003200e40322b01f904442040c08500000d0007908002c0501c00010b1042c103a0000a5401e01d0640342c0301c1403100c000b66898244802113a58240c03c04400704200348038900e0070300d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 959183911 1250 959182661 959182667
    0x108040c2d0e070903030c08090d030e012303060112110a050c060c1204060b13151a1201090e0a1b090c050c060c0306030102070b010e1602030f041418091509011e0c 72
    0x102045800ad103070301444110307440c4c0a00002d07400c010550111380c4030603140f0010040407090810b40061407414a2542e607400c00107440ca000340000c800005591003a400001e0200074000302030b4100c09440d0341d925007880c40e402c1b0b4074200b0018101d1988031010b024400721050582c450700d4000750312072000724100c4504000315032007a01c020380280f031a9042015405801044500581c00d440083e04205000d4016100844491054007000c0e1024801e4200400c400d0005911034042e0500b01810b488403594207031113084541c500c40a44a0121203101e10410400b085481040c0c10100e05091160909821042264071072340024102080740c035000001641c2c0780c1e4294103c5d0b041070383c00b80986000f0350f11910480401d1004a03403400450241100003da80341c000402c0d01c01040112034800d2130a07040015610f503010000c0e4081e900100700c0f0101c001c2494454052920030107451004192001c1d1001c103040100b40d000c1c2c20301c019645031070303402c014503042003022202d40c03401784c90045003900b0403510072 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 959185161 1250 959183911 959183917
    0xa0906020f03070e03011a06030f04140d05030a050109050106020a14101103041101050c03071e060603030201050a05100f03031b1b08060603011a0108040c2d0e070903030c08 76
    0x2007070480c04004104408181c0003602010b03d12000e80007040fa803050100542c1801440a0100754440320600014246170a819074165100e4405c0a000900310881c00c051440e1802104a14010450110070070084076103900c20035004040c002c2081c009949000b038041e488a000da04d010f0b202d40c0c0f95041e24800b03810100942402000809030400154581400da8048c03600180c6d800c6668010b0302010f030300035612800941c0c1c1e40300c00410103140740c41300755502e4101441c480b0b00c03004400c4518641c01e602180d03e51080600440c003d80002c14a4a4400aa042281c4009124000074001000c0501226049964050a890f41030414540481008080020380c884255000b402041c4854600d003490720105a200d04640c400780442e6810b44501c81050b0a8601c50725408000c0c1001146020a56214901d41500306014480041450703403144a010600c07041181c103079520b42e0f283d066080300b102400708440010601030401d441c45003800d103801016454a48806003c104024440d0b02c28484a2011 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 959186411 1250 959185161 959185177
    0x30b0a08010e01050f070509130603051014060d08030c0a02031c15090b061c0207120207060e090c0306010c1a07120501080a050715051e0304060e0d080a090602 70
    0x240041540d91041510701a01c080d02c007400495007002e001c00c582c0512032400c140a12459240c45d4100001c00c1d0500c41d10b181010981444a0340300c100010200700c050020414031003c0010110315200d01010020114a0203056070b0b02480c0c0c41d44010000c01c0c00e0105a07074020b2801040c5594a5010700000c0f8a1170041808a240c00d05491010359052821036101c0030000480d20000811660b4441c8440d080302c00e052160340c5c02107001c00017031200b030010079481c10f09610112001800c08149846051a84c0c042407410405a800454144611030308001f00e0703904481d0407940c041c11841c110a021180c0e00010b8500340c1031000000340c070400c00c00c10380510524200d000c40310f8032a40c07900190007400701144081c030441c0c161400c0000b04203000041070103001140c11030b00402c4546c0c0340444a1000034220044581040420301c02e0800035280e0450140e41d01a41c6540c2c640c40e403c2a0a0002c01c4031284600c00c04558003840e0704c4408980c022151640c040c1c480400090f40c201103041102c0a4070039011 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 959187661 1250 959186411 959186419
    0x6160e1302030108160b0403020103051b03090c01020106080a0f0b250503060a060302070b040b220303060306181205160605010b031906080a020d05010e0304030b0a050906100b0a030b 80
    0xd80020005a02560403501e01c1c2080304d01d40024100c0c03801e014595800382640d0700300f0802040c0b0243d40290000380d0458031604191000800b075410b4003040b904241c0341e4000035005014464240d69090180d28003601d0220090045218127540310074004513100b100130810004000000c00e00c0c0c6072205081c01010010348466518944008c00900307550045428500c12009450f000c1200d03031007403090300d0540f43d02c200f036655036880302e40b00c1c1c5071080c8000302100e281e540c003004200014805800d9018049101e520701003682c508502d051415280ca20464040e9500b24400c084040f8240500b40e012580c20781c01c03d41d9444400d80071403001540c040314003414082c2040d00004000744603200a6110741c18102c140d100c6810002d842070245c950034403401d1420380c404011040585016410031151500c107000000d10103141880301c0d41160070540c000d039a090042400c101c101100342c0282036202045030080e103140e251a01d600c030504007250142c01c554600c08034810540038080e0348800900c40c0d000b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 959188911 1250 959187661 959187679
    0xc070e01050a1428090e0a0b04030e0d061503020301141b031503191a09030406050f09130b011202130e061c0b01080f03090609040c090b032d0906160e 66
    0x18500c4d01d8291684500d65605281200d440c484103170215070040200d44c005c94545c050340302ca48046905204403c41c00744e00803160b01c03213480000c0c03c501c9102c41c01511251a041500e15600415003180c002e0b452045031000b0200404c004c5107081c10b056807000540700701c0262203446d4800d9541d401d2400c1c4081039014440c460b2101800f03140610f03040341640c07140003101c400c66854580c01c0c244110a5031011141c0d0310511042c81100d0003240981103c4021540107800e00c90203e00096203a121080700c4565299035264000c03c030751703002c00703000c0400c00d82942c15850605100c0007106030031100d1040221003080390700070488540c2c0d076400242c5403010a07030440410107481e060103840b1800c01c0c07042400901c03c10050041000c008016191220310013000641060111010b000181041e03400c0704d0704110312000046400f00406d00514002c801c1100788403402c489210020000070700444100c1481210101000050000003481a074010003080080c100c0d0140c10704240c1e83e40d2030384030070194084600 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 959190161 1250 959188911 959188969
    0x1a3c03040506061003020a091505120c0a02010608121207030605060a0206060f0a080a0803090a050303090c040b011b060906181109011203050d050405160b0c070e01050a14 75
    0x19114096070007100c1404400600c24420345c201c0c4610307046000031a9a08608004c4c1000801e0000d0020886050a9160840134844014001402c4900400e80d110204140741c80540c240b1521015080002c000d0002c100c10b02c59400e528042d90200040607040c00d80090391141c800c0e0011070013000007900c440d0316855042c2010f511002c0454541e03001e07a200707840c041c00c1e44c682460f6500468800e54041e01807640c0b0394035030184980c4000d0040fa0f6030700c10b1200300d000050040009501c100c0c030860107841c0424101040100341c0d00e400261504100310b807004801a402e541c41c0c00303080990301c0a80080c40640ca40b800001a01200f1003001030500f044940c9024448003140344c0c040c046086501d06026a00d90320f00c0150a40031420150014000f40f208141200e4641c0c4039642240c000c104586e4107840c01d905101c80602203412800320030501241d0044812410802900a810142c112041c95810070707000c00e40c10519445010815079952000e0b11141d281c400100f00300c00c441d10700c0c95680c1da0308 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 959191411 1250 959190161 959190163
    0x2042729180102130b09011206120f0611070302061603020703080601030902030f01050a0c11030a30051e0906091f0b060301030b1e04120305180601030506011a3c030405 74
    0x8078290b61f020483c0d596403419205420f11809080d9800d0840031150582540c0b2800414802c03007038200c8000c2d5540200c810503040c150050715849100781e0051610340740100818009174001e1009509150050106800080d08412041d41c8410286070014070118140006441c151406002c00c0d041d51030502889507014403034021400c6800942ca1380c00c90020304260b2140e4030311501c0400310004510a4106960400a01c0f00b48640c40c0184015007801621501590844d402a41c10b904503041c4084040e21601c41e14140683c8864584c4c00b402c03062422400003500e4102d101100e082c03110101d034001841260540c490541c1040140c802034030b035030312441c08414002042d600a800e018628020841c480c2210307a402d8419a070000d100382050040349000d4000d01800b406000c4058000f002121480404010040c02140150010550355140401c05040c0014803010300182d000104000101400740e10000d0120b030403465141c2d903c1040b00b10440c130a501309240c645040c1384c0000180414407034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 959192661 1250 959191411 959191417
    0x7051b1009260f040620010501090212090d090b1e0415110a0c030204020714030c1023130503040f030305070201021002042102042729180102130b 64
    0x101001d0b0208000c0000030000d6406081c1407580031150400040c031182d403054041140300505800c95668060070110141d003515070036007010002c20390100d24014032011040c00143c0240720000a00a80b901c5004001c0491003240250454440005850b000c40c030240d41841c422075024443c0340c6d48444d01c6040050240e244003140030009016800d508207441e20202e541c4008551184c0d44070695403035982408040e40011500355000300d04402d0040103e00709000412085520310301400280100c80c040074219004a04d54190300016a03a00d40e11030004c04c0c0c401900f00070b800300c07034070803440080c07038003900c0c5104941084041440c4280000109a0000042c0040a100b43c003650190508030706000b08178000c5200d10100e14020010071424200750100c40300c1820f0000e400844e00520740158507002d8151003181c4800082c00e00b051400380b10486c200300100e44141c100e507140d1100e80c01d040340981e50300505000011002800a00d075950401d40c1102c1d0044407500c02380060b20355902c50b03c241d0350 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 959193911 1250 959192661 959192693
    0x140601080903090d1a060103024b07150b060702010c050c0a06090608010905101415210c0909060909012a11120a0302071a0f01051807051b1009 63
    0x403900408034086d98080d0099070743c1c00440c030411031007100f5010004910400510790311041406003407c900803032091003644282161a0320005942e6011510300a01003000c0e210180d800185001d80c40380c81980da0004460800341c09203000f840254084c00d0a07400c241c510303071a0a034000390040300040e60a40099a00084171101e13240c1c100c890b80e0318105030044c0d800442d01d51a00c250001c0d02481180c44c803d00d46010205c0c0549400802c0f5111800c00003160b01c5080c162009074280c2055100590350345545a030300c03111083c1c46506190403000414100d0708058035161068940340c1c00201c02d80002d6024043c0d5510001540100707143d40400d2041494040954900242d24041007141c0e1f01400100c0f510400b4400c40352620b0a521907400728025000300c40201c400c464603003041040c000041461074003a1122030f50104242d4500020010003d0b000090780c0f11800c411010005c1251704082910400071441c1c9502070103000c241021070900c001c00f00007181c1c0c0c516040da407505105500030f1903100d170 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 959195161 1250 959193911 959193953
    0x30b0105300f0d0e0904170d0c1d120601031103030d0603030c0c0e040b0420040e030a17101202011b050d020610050916092402010609140601080903090d 67
    0xc0454036048880d000c1401813107400034690b50100d000589600c0541c080b003402e20b01c0346400d2110101215044c3c07203154403600001461019554607101c03c41001042540e022a40400500c8000354020748603001480040c1210b1502007081001c1c0c0c40c240111142c1c454580c100b04045900d07850050081e08040301e0580e103088401c50082280c1e2055000d0ba8051600070211441c2c40d03490341e48135003408e1004090715055151603081001c15880351302a000f2501c4e81131003d162140e02010006009050810240200c6c40140080c01000e6211080301d41c01da40645060080304001800180c0706040701240311011007270340130581c10600101040141280f5040d0b4251030042e2943d1000c0a40d0a000740601544100d00c0c030042a8040d6400c24075541d070f0b600d14145100402d58508030984c001d0100d4400c0c101c030030007000003880700c1942841070b04050040c14400300141003640b0325980c44804e0050906050110b074401240881070304105442c60300c000208000c20b17082e01c40c600a202e000c201c500b14540 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 959196411 1250 959195161 959195173
    0x60112110d0317070306050415030b0901050709030602070206210a11190e0f060f040f0b03130201080901110d0e07050d120807110106030818010207030b0105300f 71
    0x2440c030704904105425601aa5580c0421804020184680a0141034982450b5494100142941390380c0140406018400d070b0382040e50340355040022020a004210241c140d05d010200a42c40b5000007800054a07005100143c07280124408550385100b80054100c2c000b0b864030517620001c4c85405c021b80300f1040610300b4004403014804960660080e8042c1d2105c08103d09603082c0540c4c8208078060041d0b100070042e114158410010070707000c5d807286c00840c01c0c200e00098180842607039490180000c101c0004110f295150045211801c0b55628100030304101c9010040741c0c9100007500328020105400d04210341e41d2154450510042c0000380c0c0303a0800e40690700300040c00b4600341d046210f084e07810544000702c141100804407507072b190044c89001401607441102c1001c44c024450b6102451107440342d04d44d9640248000346007040340700c003a541154007440050000414100c1ba20381100d4095035070750000107200001d076140204520120182c0c41c103074079444480040002c1d0481c0c0d080c40e0b82058801c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 959197661 1250 959196411 959196443
    0x30c0306070504051c02060403051507020c01020a14030d052d0f04020409082808091603150608010f090614092e0f06030506070201021312020102070305060112 70
    0x103120082280ca810200b442480104218244101170781002600d16421601c4140b050b4000780c050f8006400c20f88a9a000c044040c15500c5e01c42110f58002940740001d1408802460000790b5400c880b800c01800d03000051507403440c1c45020003d44d40c883d4820901444a4a050f01005040300000c1c026000c00d1100e0803003106100c003148036802d00a0811041030411039449400b444007410f8101b80032218540c0421408560002129000310300e00040b00b0395002103680140000c1c20300c0006000389100303410400680021501c3c035003800088952025036440b09401c4038801f07100415050b801714403039500700304003040003041d580d01070807085209007800c00000e041d81c2c0000c0c1070900c0031100c080c6254414a1000d01545060b0b00070308484040c0c0c0a08a50304000c50341a00544404090700312100f45c0781d01c810300c20000706000380c07a80300340c59200071414015552032220700742c0040e1041c00240d0441c400c1e03810a591090080714051900030781114402d5a4030b58040340300c082e9001040e0341807405905442 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 959198911 1250 959197661 959197663
    0x61407140a080c0c03040b07060509070b43050109051c02120d090c030609200d030e19030c060f0f05030606160506090a0b1e0f042a05030c03 62
    0xd10401c1050341d0b241c0180d901e01c01d4240e407503402100303510401d1205000008107181c0580003010083d214200111381403d1482c02e5034540b90305030b04242510542070000140110a5085405030a584080b800f00b07034100a001201a92141994201125003400303542c3d801c3c4003054110445a900c43e4085540034507500c0b440360703c1d42900010403c01a04103a044501007020340c1d000d45041e907801c400008000d08585d4407504a140f403540111011501c80325800300780003650714031003280700103042100d202120f1a000a5a0500141401018400c00061011464070b88280401c2d4070318110174501032941c0c0702d0920a07620000d070722035080040c1c0300640303003070140d881001c01c050b2481d020303102d00c2e0079501c1c6c0d03000304080c540108c01c5240c104044003c001d008514204103040c001e42c00440036100250303c80c108104807400c000c1c02c0c034108038072aa10510316190882039850b4004100e1844030100c0c0c4a40c07412854a0500c2564680d00e00c2c003505d0450340c11550301000070b00b101e104030100c0d1507441da44000d00d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 959200161 1250 959198911 959198917
    0x203280b0303070f0501020408160303030c0c081909090504031e23032508060f010c0507030605090a060603031d1e04180204060b1b030c0a02040c090306140714 70
    0x1d805030802d104500c001155010301c000881e20030000541815243c000c510724080040502d03101c0c00101a40070401d141d01481030780040d211324500001c5140c0e42d0380300d03511644221400008940300c01d01480c20b00c00c2c40750710f441000d011f0210007803000342024200204481107035828403004610142070b11100501030843c1c80451007500500c2d0407050141d401040494000900c8621301c4009208400c102d1009c640e03220515040544450090742054070500107060ba0760742620303041c048500e4002c00840d40000e2824200c03a0300101c049200ea8901441c0c40c1800c0c030b140c100030100d500700140882056004190301290010010000000421020401200301b6401d2988c0c20502c050b1f11500d106401d164202c042440302072804403c42242580c0418115003050740310301901180458044054284140d40c000c105c5c3c4007500440c14012403005440c0c855441c030300000e2007981d43d82104c8070001d01803900d660085400030030401c41070102d800c0c103c0b003000c0111458070005d1900d64092091601003c25 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 959201411 1250 959200161 959200181
    0xb03100b12070e0f06120d1806020304030c0e130c0f0303080c07020f19170c130b091f0b03010b030403020f0607020706121b0504080706091401031e020328 68
    0x8800b603680714050710895a078805002a034200c04450b09200140c801005000034000483e9201406840b4601c200c901c3c1120b170389c20000031034200b0801080860411540c04c81500c6c0d40c4c4407400b405845d882c10b15082c01231000030040010844100004013114541520340440380240c0701c0303241c5940e880f410f000300380c0b080e03010095121070111842c08240c181400402c11406c80c0340c40c9602c5a68554100c8802d4881090103001c0d40c1e031040b11a000076003080c04680400b22907000c001d001c9140c609001400b4000d000746107102c032207420075800210209604100000307114250140d6601d5840f01c4e4651f0055008860540140c4192850780d0880400040c14a204082c543c1c05094510b0401c030085a03178054032145030444548444801c0c1c800c29050840c444030b078000d030302ea035a540d510700f450903418804070354441014004501010042e620120180c601c445d1000d20b00012918482c682c41090b4034504905505410700c00700030800400c4440e07005c0400c4480c00e045040c000c84025580b90305640340311139 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 959202661 1250 959201411 959201429
    0x60f0e041515090e0c09030c0306060603012d0e010806130506072304120308070207030c0b03041b1e05060301050604150c0f05031908060102120d0b03100b1207 70
    0x1c402c000741803502103400d2004000307103000281c4980d00c05140310410019204091025000a43c0d4070a41c50f0411140ca410103095000c1c08540c174080303000440d140014031440780d0a061290550102c5c80c0400c40c1c0080c812154101e40c3e41842d1110031400342c040c001d000300c5649102c1c034000304401400070071849200c0c0740d2040007460f1540d12070300129a120a0701300c403003032452007140c00c1d451920022401303000a04001c41c4450031701d809904005242a44c090003050964100c8032303050001c90103040b002c20903522a1600c40c0d5403612585000318483c40300020742080b46055810200710500d403501c1c1032668a694244101416444d102044510311081c4a1039a2002c0104002c01c000441603040d104011610309148100c0312054403001420340607844110740e6500001400381d01d2640c40c40000c8004002803800d42400e10708400040d594041e5011000b861940100d203003118220150003d20301000080d0a5401c000b800313100220103001d6006400c0e10030440d400f0b40040e80c00c00003074503400301c809000c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 959203911 1250 959202661 959202701
    0x1b080c06011a07020a05270c09040b0114070f020a120312061e09050606040b0415080a020c1504052d070501020a03021b040f020a050702010e0906062205030106060f0e04 74
    0x303042151041407200b07406c0c4503000302c81101207c2e203281c1300110300c01c901601400c0c1e42c5420301020041180d031031850403418400100d184d00507110101040d61143c5500c4244017030000000d00014800c0e809650002600446901d452000c0541c03006003141d0b100802c102c10301c00c0310748907610814000c03550010040c407130f010024108802601500025088000036182c180fa15440c0e0b02101c0d440d521640118031080040c007814140303e60f00c80220703644554440021800d100d804030640c0d484480b540c1001d0301600c90240401c0a01006000c000c41301c08001041c0c206054000702e003802e03031030001c5910b04040c0c0a504030008180d400070905000555140c2e000c1c0c4810480c1324151444001c00703e001c682c200c0d0ba5808100040a000d200400f94180107842c2d480d25000340e807000410716504482c0300360050350b075041845040d0b100e0708160703100100044400c180310004800107041304107140d07110795855824800c000039003a0300300410000c03420f0540d94191511810b601440b040e10f00320388401e000c0740f0a207 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 959205161 1250 959203911 959203919
    0x15170405031201150c03051e1b071202060409021b070602010603050708061b0f130e01090e010e031801030b031207020a08120405010f02010209181501020c09071b080c06011a07020a 79
    0x50001454080c0074013504a907076020003000c8c1c910982204548808080c2c0c0e504583c42140e80c100125070080280e00c105402140032680482d0b054003aa10032114916004a07091120a040002c504c4a006a185c12600070359501c0320300134081d0445200c280d4050160000c08113040002040480c0b2031581c01c00c0d000f00d8040d407803541c0700003a0300400551413100d5042c419811103403401d020040c01003070030f05000308103135040071408401c40d44030002c4001e49a140c184c104480d140044159414598840040c03006c4543c000010f0300500084400c3d10342c14024800d144120358101c102038420140262078a441c002e4441d803000d81e980110300168403540205200400083d803003400c02840c4403070030748005400c1c81e04800200d40314040301d030144900f1146031010005000d015010307041400000740b00030102c00c82610701007480c1c144054a003004104000809603424001c0d1005c10101036444140d0a236110b031050030039501c80e1000c1c0074807085551401035102c21030001509440030190018000c864040c54 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 959206411 1250 959205161 959205167
    0x518043215091305010f050a0c051204021009080601090c030510030b060910090507120e03130314010212010803071a070e010809011104080f0d140415170405031201150c03 75
    0x8100f881100c07412024103000400a00a40f8402454108049070a04141c0c01403425a040c0124070401c002c400d115805d01c0d041040c016540064065401c10002c00125a0403199800c07240c0200e20603100c2c02c130002130032a2140e8403c0c0100006a50108090340300c1300c080240c251607070300c4081e00c102040c001052652600d0071005801c0001c4405000c1c60f81e6036180d1000c25202c0890b0000f010445036140c0c0c41503010a40100c2c0d903101d910101542c6001c85084501c14203481900010348800504032510250701c200354103c411044000003240c2c510769403119800c1c2d903075002e4042240d0480044510625a402140e0080d0052441e500d400b120035005100440324518020200c1c01c0540d06d4550406044e041100180084c1803182c0141108144121b0704920b058050f540c2c44042194420800c0d0181d0341c40415601a101c8622100d1a00d00300707100b086811045001010071000f55050a20007040b5001009020841c8160341c6150a0f0b030707840310315000020f004203c040210360340140d00340c0060f02c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 959207661 1250 959206411 959206429
    0x250303110a120305091608030d0908040801060b13051507060207112718070510090305070905010311040c023a020601061407020d030518043215 63
    0x1a00080780d0711400316448107541c0582c600b0035540800d50b0340003406494003003842084d40604280d0103880056291088140d924400e607007400b04c0060b95039110307404004401c03040b43c00400b4007400034019241c0383c80c031500155220010004d9418140c0c000010a82400c0c00b6800442d002d2200c05801c05640391500ba010354130001e400c83c0d511602c44d82c100e0b01503844a00d0f281a8800c00680b041c0c500c421140e082000c0e140c09020200f0310304a070b00fa024000400020560165141a44c100c2d0841d0303540030040d980c507400f1340c100801e140603030300020a0461907640700700c0c103c901400b01c10030320189070310500040300c0c0c01d00d4041005810403403800210440c07540011345650301e852441d203403491000e4800c4802c2c00701c0100940c0160464001008480d40c41004000c0303c6400e420a0303443c18289900142c2e0703081c0b071018010240080801c0088010030b8a12400307110100240040c04a91f8840207101100b103203d0740c9550302c40c0c2000055942d00034201c1c090b10310607856080d1445940710042c0c00c000100c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 959208911 1250 959207661 959207687
    0x20405090a060b0702060f2a0d0e0306070e150301060c030f03020a0c0b06120f01020c0708070f050103111b1018022407051603030914100f02012408250303 68
    0xe00c0401c600f0310000c12080d0800c640e07403a807c3c0da0b00812311400c0c4840d0b0070301e43c1482c0703920200031042c1000300680d41d01161181d0850701e1801d24200c20344460f07012414004651440380320007000400005001da07001440c0c201c060f40310f40d0300c500c2851191a0182c04038000c0f031810744001500039400d6000a02c91171036035a013090000303045850324030f0000d0b485490004a9240c410039a5008190994500f608000c80720280c07201034003520340d42d410a1800d1215100c54800c0301c5c10951600241410340b02c1d04421201d010b01983d0741002643d88404265503500070f400859504a49401c60318181256904591440c1640c001c00c00c5118011441c44144141c040b5812510016004c01a40d400074508106d6901514801a44960301516500380600080d4041d40320700c545544106001d0110360300e4000c0445052083c1c01c02805078900d2a1040340103082514100d040315450b0081c44035541e030003517903440848032410102d80380c0c2c0175612004505410802c50000c0400d003d01000d100080c01080900c2c950 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 959210161 1250 959208911 959208937
    0x80f07110c031006030c090c051e0706140702060a02180f1903032006010302090415140106050403060516050702011b080f0301060f0f050d150b0d020405090a060b070206 74
    0x1660107400001d00f0a070006071418805991651308004202040e0840c00041c819517200300003ca0b1841009800e85c8140c1591407254000ca01c2040340c40001c4000fa2280700e41c001c1010417030520000307503882c18188107944581c09445441c1c0021691034a9000300c4010101506450301120000c0c41841a560b01c10f4034041c0c0c2c4102c0c10320b1301d48505c80c01852068011f600030b541e41e100d400c0c2c284154003840e6200325032030165a0081c030014805a1180742c1c0c2150480d91050590000441d164030b0040105220350381c540c20304248100000744117a0010292094074080c09082105480e034082c155410030800c0f03408404250709000400240d0300800c80c0420800c0100023400480600e0ba0b6880d900758040c083d9001d03115004001031044540c01190240c40400500306400d5200c000d43c1c000d42140181300c501110390b92540d1158886030038a2095200800f10000b0881d11180441c0084029401034003490303005019200014280442a010700c60449001105080c5000c01e5602400801c0c1c0c000c46144103c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 959211411 1250 959210161 959210173
    0x3140d0603120203030412030c021e1f020a031a03210c060408120604022d040512010b01141603120e100903080105010e130902150a020106030c06080f0711 68
    0x1c41c48250b10b40e507211440c0c0c0d0140d56240341c280740403c03050200f580b440c030416141c010301004464002230940300401d01c045400706500c040e500094904064031030703050341840d44014003410802403500500411758464405202d0034101809070103000106000c0b00c0c0c0d155004500400ca20700720308040e50003d0100001d1b80c0d1424a0048149152000175182160604000140d141040000702c000c2500b103d0b00321030a500d440301001c944881c1c0000d100600c06e510b01030090300f0710580200000c482c01080044d091030700c00445a41802d00a00300070000074042040c910988401c4400c0100301c4000c8500d0304404c29184440d5102220382e040401076500119a48448002042d0307070800400075002d40082000c25038920b9890002c1a910b41a40b240d0f050140d14401d80c409640c03076006403071002440d9100001d035031a10b0b0000a0044200c50303c01e04025100054000313413a5811740020301528040c00a4451044da100c0d03044071340c42d00c200c840c07809285d80742c40811481071164525444101204003100c0c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 959212661 1250 959211411 959211413
    0x1a0d0203060126061807021b0616030302190f1409030703150905010c02061311060d14011a0f0406080709030c230a150507030903080d0f0b0d03140d0603 67
    0x128a20791003075038103ca500d0030108500780c45e29000440c140041d1055142d01c5040c04c2102035602e4071901c0d00018680c0840344a40c0c103a07101c0209070344941088031035048460b9071a09025000798801c6081112910080c44c540031105d000b040800850105907840d6400c3d40b490300d85c42000c54000c003c4569150040c034400002050130b40120f000344036000540021081514600542101c0e0101440e8065400100030084c50214030842c42c13155035008442180b100e00e4a00c0040d0040c03103200c001c07003400c41c0b42c01d0001c62451031200710181659032000c0070420080c0300c0e14511100f070240c0114189025000c0005200151003580003942054070717400c000003410303143e036500c41c4412070a8000c42c1a090400000314410b9810109684142c10151801191241000c1804041880c050348180038040001561400c052040c4d182e0401990003590298847d185500c201000d00320050403103d015040103020455407518101500c211580344c0c07901451424040614200c6401600103d058156120340000c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 959213911 1250 959212661 959212697
    0x51005010e0604050f0609071d03030f04050a080313050f1f05090117040b042a0303021f0e150a15030c050909120d1e0c08101a0d02030601 61
    0x1806070040410892040c40d108062000300c07800240420711a604c00018050b0359212642104e0308040d152811005d50180e40a5031010340300041f1503c2c2c2c16110001d5055007600440b00a041542c0c412580c0d0444e0035907961400c0c1d030b42d004a01d000b040c0c07218001c804110629050120031988200901401103110402d55501c40c00c8940d0880c6601084001800301015a4400c4c003c0303071500c4400d103005c1d6440c2015110e008146a008200074140300340d049480e01e10400f28004007072648440d9012a00144d124a0029218180d000c07001c0002c901903207510303c10503514082c0340072402e4068014100441e100c0d2151900810260203020710383e41e282c02c58030f0209842c200c0e92002c1c601540c03032100c19900e41018454103103c02001030314150091315090f05c180d030141044410b810300c2000d0100b011210070440b2000410360503c1d2026031460a030a40021b640c0010f0410312540c16000440d0300c2950310448501e444100b12000c10380c0f000100802d608000c0160b0243d60415018074055610000c075120701 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 959215161 1250 959213911 959213921
    0x1c0c020d0b1801180602310303030c0c08121017030903071a070f0503090406031a1f0608181504050f031e09151b0c03030f0a0c0510 58
    0x1500c0c070006040030481d0b2907402c1c001c51450045103200821190607032044510030011a8000100840e400140104803011124403a22a070070b121407211482c403d00305649500c01c0b01c14442180482e05010503000c51900480c80c64407980c0e0814030b4685010700c15182280c6d1071200401c00d0b40074400541340131071036034100781c01d5402c44045400115992602041010f00d05200c96100b00d1504111592910745940c0040640300c070984e02541d008000c1c14140380081c2140911071569410610f40b210000912441004459a4043d83d8640004940b01c140c000c1300c01100030110301c000d8080101003003281c40d104805141e840707440101d40c029030600f0801d03c42c0c10000a22041110002c4141c180401d1040510a02c0652074494005500c0c165107000034910100351030403101780c04240402c039201c00c1e441e182c01d48070320740c5000d2514540e0b0307a600d00c2c1c3c3e1014509604400407018450446c50a002e410004201c80709000e854541504242400c0401c40d5406000d0001b00c2d1076004038814030100d10458024 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 959216411 1250 959215161 959215163
    0xb0408150702070f0501320702091303391a100312050901120905030c07060c0b04020d020102010b0a0314070501020105221401090507051302070b010b0d0612080a080f091c0c020d 78
    0x1d00c590b03408c2c00740104100410080d0106015581561482d80003c0e000210841a10012581160b4520700d070817031144104441d4201c0c8203040701208080d82040b69000803032000045850300c0009a80341c03c07082d96002d4000c2d000003001d02c54607030300d1404514024405010300140500d842440000d81c0407444081d1005550119500c3c1d0011510100f110301c00e0000402510441c9400319200c41c503610750500207080900040c2c0a003500c54003090541e4400e4125100c5260044d11941805680b40341000424860901890302c9000b404070101c1d0a42c410301445002e0010503000010b801d2001ca80000d103024660700c00c40300312421078500700320301c0004c0c0038110609000b6406044000d20309010b07c0241070680c42c880d52035900c10020303680050b54507404981500c404401d11912402e0303444050b802401c203074003c0c0700a0140c0800000070420715078020041840030341e0390608603888204802d41d0500d0243d40e004c0c5c25801007440000090b584001c0d44100c041070385442005401e458010603c01052410 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 959217661 1250 959216411 959216507
    0x607060507090b0a0f080a020f19030b0609010e15070b01091e09211404030503190306121424061207080c011101060b0408150702070f0501 61
    0x20070401c80c0e940000b0360b040185099a2a01d24201c25079400900c42d00c00807100c442071190394004035940a806a064900d240d40c01000b550b074504680310300c0c8000c41007110a00380024200b0700d0900c030604008064841c0c2103c1a1107401d0b00d581a10208010000010341d004c01c604c40502c03124005c29503005c0628000c0620280c00210b0030004024030404c0700117a1000f2660310701f0042c0c54000a0351a100383d05400e0748080105c012800c00b04001c84142c03001c901c25030961500450040300b0301c08044028020100710005400c90007580400036802d468240c40752801c100440310b800008980f6034640800146040300039070b0048500d1520014921030007a06507a08128880704009060030034040040d841a20703031000700880c0d0b103420b080315981c002800d00c0f9410485030010070b000b89a000d40101000d01408480380791903a8460360125a148401446500c10b10001e002099446001080ca0350680c0e1380c800980c2d807034a06200055505000f04103801130210743c90852034223800702c802c40382054803003000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 959218911 1250 959217661 959217671
    0x50408071205070303180305071407030537120c05010f020a030c2d0f09050301090b07090e0c0406080c07020d050d02012004120f0b280b0f060d0902060706 68
    0x104009007100c1a50b0440300fa1580002c21b9040800c1e00074040d030714240e0740003051141103200e0014881c00c10000742d00c0148140725800ae608020b1a604c4560303468820000b50700420a41042001f86a08940f03070310181c5001440030b8410801031045d44c4411400d8011000480c1000b54800c507141240d00160394100029030b642410114540d2003800104980b182c0701003801c0b020011000411011101c44070207051059040407039070040d00a5400c2d0000304001402080a00c0386820108149441100d00c2000110324000c00310b000b5002c00321650086841c03690701e40c109400d14500b40c0b0542006030910101a2007404030300012b94402d0b00f940500d0384a1406800092012040a0f080d24103007519076403040021803102c0162842e50045e50100c40d01c40c1c40301d42c0040c10b0380c14a1985096203010242131515103000b040150420038000030540004002e00b41c551000c007100340421501c020328072660041c030082c0c880381103151800242440350b41c10700001642945640c0001c4080d4070000d002c4071115226 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 959220161 1250 959218911 959218913
    0x313080d0b041d070e09150925030506071803060e0f010b060c122808060a1703031321021510030804030f032318060a09050405040807120507 62
    0x80e016101440388886543c2c0201c00c00c85005035100d40c100e01136003101c0c28403000060a03c003c10080c0c40749102e070340f80780300402d4105808250b44402c001c15070040c0c0c601c48400d402c06002e0300f050214044a8100d409000152a03814003240c1840e070040d10907210001004000c004544a841801c07c0c110080008105020038480c0060a64010700c0300c0500c0390809001814070980302003042c0e01001c04006940e550781189100010440b00c0031032032003103030b0b0010121510701180c005400278040d9400710385e43c3c070030309a803207401c180004859240d90b0220b070018000b003002d500442c1d0f1045c3c0b4982c400d00301c000d240c2e0149501d90046200b01018000181c0c08451401840582c450300030350443c4a0301000441e85055454000d4180318504c801407082000e41c0400044c03512600b803050f444410a41280c00061f1280704518045c3c001400f02829807210464150042c5040ca0443d80007140ca9180e91340010318040c2008000c0000030015507206608000010009645c40b139050749000c1c1689410341c8030f80403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 959221411 1250 959220161 959220169
    0x21c030905040b060d0e030706180b24130608030c0a0b09070e070f050c01140f0f25020c193f02010215010321020307170313080d0b 58
    0x2580c401d038007681c40e01003030580a4482c2001c86101032800304002c00d0b02c1c80d4081e06146184200840076002c54907140d044064946c18103482d03070f000c0d4003502c04040b45440b8140f40d40c40e001301102ca00000190380480c1b445060800d01e1400072002d01c10080019216a50050030781164001200034020b40c02055079001080780761003071a40c1100e80c21000b410346500304800d002c02c50402070004010f10010030100c0c80c280340301d0300c02c0b40c2c0c06010410080c0941011030302d550314140416181d50004d00c1502c000070b02c9407400805c240b880703288a01400001c4020031440c0b085a50075028480c002c5014902607650651940b14600300c0c0b04e800f450138580f6003840d051100e0141c076494111082040014021500b040741140c24003441017640705c0d44c141c02101c9510061b464640007a03072400d25407012a00000a2000b2104100d0849940045102d94021106822030300c0344100721000b0102c800300190740401c0e00d910740140d0350040041c04204402080b64075080a20b030011b03410b446245447e0021900c45040c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 959222661 1250 959221411 959221427
    0x20901060302040519140103091e1203381305090307031403010b030a02130306140a050a0c0206010909081e07021017060405040309170703120e01050a0516021c03 71
    0x1105c1d20042d10603505185129034135054050050741056220000c00c000c0c8031460300400d42506580f00c061111120b149442160f8060385c0f890080401c3c9050300c1e004040851000c3c00003001c015000c4c40703442956400e107646480080000c01c0d500600c0068002044803918480c080c0542c586400643d1110907602c2c00800ca00d591840104180200741300401240200340c0640b5008038003d0000350f01c0d9400b0031018a55031110381c1c40030300303464144042c5c40240703002c0c0d641c001d0094a0060052241d42d40d02101030055503608130300d100060f40100010040e140c8c1550014283c10f02c0703500120310b03240d44150b51a8040e42e0000c89560300c0403001900c0000c61a100c50031009816440c18840d4025840c44485003400b940207019901440c2c4030b0000408151150412102901d2520124035940c1c0689980990360031181c002160f445100ba5500f2503641e0103400b0707114036020305954241c40d0503030100c000c0b50660048807071058025030400d9518010383c0c8010340f041c5290441d0101c00e015032810701380148840 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 959223911 1250 959222661 959222689
    0x709050108122b0908030c070201120e1b24040e0f06060403120c080a0509030105060901030f230a060e0d030516180308030c070b07030c0215130209010603020405 71
    0x400308012030982c0038403040c1080914030212181e030f8912698040c002020348080d00c1c2c010700000c07001040106e200503000181543c203000380da903411481d04240c1084210742d50069940c0d0a68041c07007900e142000da0384609044c00d80c01421411181800e4441c441c03030346480318807480121002050601c800704c3c2544000360301007440700080200f418003101050441c8620f00018002482c100003186e14640240004900175074803a55140d0382d4802e2100040140d04020f881600c69401c0002043d030510b0000f138014141c3c0e07002120903101c1c0c4042d64504e0b01420220796148503000c0c0c00380c0c0f040c191403000d020640c1454080c80c0e004c60014840f541450826007804010340c18145071009100c10950b03c440703400510705441c00c2001054506082410414038603a1000740304440010410442c1401c403005400c166100309081079131074480b01801d50a07105d001e00440010780c4a0220b0498401131443d040d42c0141103082d43c3d01e10907410390003140c50b042d001d81081003ca40c00040c01c02c881d04003602c0c0c010f0310b0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 959225161 1250 959223911 959223943
    0x7170301051c0f0c06020c03010629130815060405010503010903170c1210050103060e010e040209040f0501050a0603140c1503060a1805190e030a1d030709050108 71
    0x103606250015420350b10289074852224004100ca00402402c200c4484010b03800048503294103a032454002d6070f03007203050b00c540d02a50070041e00141483e811221040d8554403402d8414061181d82191000f903000700f124010480b00c0041e000500d40000d1081c60601c0b682c2c0c80c07812030286040340a200035150181d00181c040d03031615000704d0101394001403041f42400c007034142c1d030825181e02001e80b00c01e003c0ca4610f041d41118240601c080d143c6141f40e40c1c0d0840350700b0f0300c090103801e55030032000c1f109402c02d10400711090108000500149850a5540c0d03000d407088014440d410003940702e40d82160000c0f22007190107503442c4018000d003c01a01c1100303541000d0001000c01c4100344020901d12504032590300ca010f0000700201d41555103850721140a841c48601c01a000406035405d20301509043c1e030801049609600340c0742c4495824001d00d141210184021443d100d00131004940340100302c408003150030106c000c040407664041c410386004001030034000c507095060913071079801c00c04005c0480f00e034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 959226411 1250 959225161 959225167
    0x605061503070e0f1207181d070b0705121206031b060a030b0409140a06061e12110604091d03070515040f12050c06060a0e01150e03060901020717 64
    0x2c49075004001e140c1c0d00c2000d036030301e080c02210305000c03400000541510205600509002045070740c4c4980504802c960041741c00d00c00300c0007103e21001d00581c6140d042c040c0b90040e00e014054990900010143c2c03034031401c1110042a20174500c06a5500546100c011041407401440300505d400c100d0140d031001d522034000c00545d06d0000103007851040460030014141c5820b9050051380e0340d58403011500342c0080002c200e00c0008100300d5103480b5151401c03203040f443e0200c003003034603881030b0085101c14a1000aa42e04941840c503a1204400480030071504d11880d0840b15809480307210180000b040c0201340410103025141c0c201c4901141e41300b41c058150700c280000000f01c3c7c0005503201c103401400302c82611540701c1c0d0500503c555002000906105240e081107803110750300074001c0c036900b004201900c089031904000c0242c07078046480794a05011403400140110f00300010015246409420319620030318125001c28101503049803803483d2a58045020800c0c030081e42c0d0381c00b50f880b41864100b0300d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 959227661 1250 959226411 959226421
    0x40c030c020304050d42140106030203330a270209121c0f0c15050603011e0608070b041520010e0d2007120203070f030605061503 57
    0x2640c0d01882c030480f80305007450f42d00d40040c01800702604001c250f10500130103e13403614001110180030000e881e48206e03c0c1e00e80b00c1c1220f1141c184581420100c4281e00e03e6030691030060218003a41016020000c17200b602005003803003003403003100c091a900c40040302c10311008448c4100705402110303074410181320854062003070342d042140204101d00d941840c0b0040e100d10115010030505540321a94043c00d1060300d541441c808020601902d0703c0307003035607a551404044150112801461204014141c1980d1018503500045030f822a40d4458400b0b0000241c8080c3c85100f444450307178071030800710740640d0b41c0001e121505090091030090205c050596242034604140d00140a281c4000d40081000e120a0092480d041d1240c02d40c058074180000e000c2c001a0f03c040d9038688a0b28030700d5002054030000480b216004010a00c0c101c06010005800064980b417507a920541520404a90500540b8404079840309800000c070055401032030000b0341480d12a060003858081103070054080541481005 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 959228911 1250 959227661 959227663
    0xd080a0b0f150405060409060e1005060304060b15160b060603040f08070f020a03110405060103110405150d0204031505070203070c05040f0b04020a0f021204060f0f09080714040c030c02 81
    0x1989208003030310070312070a0480e1110000b1a0280d40c01041d84000e000800251090007508000d060398100ca495268544401e0400840c0e04c00d80c1c4103c0d0382103581400058041142a0301800b403488026190381104c0c44d00441e10003131a8040d0b41100300741d00f80030001c0024030070f80030181a40100c0c00c2e124189981440d8441d520168000d60006241c10340000e918020406842a6600b0055000d0041d074940c548900c0c00091201404104c1f5020354035140000d60300350b00c80d000721002c0c0c00c1f0141c106480e00742400140492032030301e8052000c5040c1c0c1003043c1c0b0940b800380e200500003103014511201400584141e400142d80000c1d190001b1540140000b102103240d148108085600840340003031220004d00100780604100440190321a1000c900c000401e0b4105440b0540c0f20241e07402d849a8402c01031700850781e401203000d1800018004088010118084c0c00c1c0324802e00c454ac10310410042d075407580e03d49010202d070400807068842000f588440d0902d801020740c3d108442c1003d00258500240003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 959230161 1250 959228911 959228929
    0xb0a08150303190306090504120e0d0206040b0702011b0b0711030415030f0b0a03030807091a0a05031f09090b010509240607050709091119090c05040e090d080a0b 71
    0x1804080c0c00080740e950f00f0134040e41c040c80c020041070000f445645000e05180810121846504001c246000355180a6140c8030490785aa19030091010781001d0400c0003841c202e422100c0100d05100c82d4a41c8440300d540300c0d800100c2240e20441040282e86130900c802040c0b90111080c02c02c00e640180018000044404145131103c00c01e40303000a41c1940250078040a0103841c040107030413944455002c81419441102c080c42612103842c1e04c001d403540c0318520b008030301d91070f40110180348060228190f0136206900840d000142c044107429080c0c0c1d4404041d0000307895a2003c81c4c0e0755516848041004070a401c80ca004201c01c66044540385401c801050307400954414010b000766200181d8070082da510020340300d01c0740c2c11000f2a241e0035202d802c0a401010210030503a00580b241e1032244040c0307807420002201c0c0440101e02c2c2c8405140940c0400584a0b003d9143e0070700006100104075809a200c04030f101d0150134005003a90324900c000035020420203407800386414240060300a080c2c60704901 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 959231411 1250 959230161 959230177
    0x1b1908030c1614160515070b10051306090f091208190204030605010911040302060d05070507060207051f0e0d0e1302030106020f100b1c06090c0b0a08150303 69
    0x4456940c2d11842034070004941501801805950301c0360004196820028010b8480030515080072075a6446108110580c011441283c1c01c00c2002c012a02c0040c8012644030b0b0404908042c1c3e40f8015100c1c0c0000b0b0091003140041070754640d641c942000354007058000d02c40c1048805200f0003c40003240c49500748807011503001d2060003500804190444c1141905100c3c1d08600c2c0c800319215034981c9071003001f0740028400c51a45c2820a024040b056180d00203d030f08896008240d5031401c90030080e0a400341200801d05000c0c00400d04c4007402041c903500007070001e548600c015200c00c3d04040640a8026480051444010325016907001c103018000307102003144019007044143e8550b2480001d460040d8000d41c84001400440000344542e00007a20001c4844002c0681e015540e6284004080703510b5512060391000110403101494818011041034a40c021080400c429880e03459080620070b16070703c0986034100010341c60f603010b980b01455640000404003404840380c2c5140009550380110b0302 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 959232661 1250 959231411 959231431
    0x52709032212320d02010b181b0903010603061425030f0e10051b030403121a040c0521090a08030915010b030714120106030e121b190803 60
    0x2d101031083d01c014101c00c8a11008600205903620021100e60b22098a03010000c0550300303141c4001100e20b41505c080c04480011210b0b0038543e070703c07242c444000b8600603000ca04c0c01002080618400d8400b80070390700c040c5003c0c0e100401c0d075902c00c6004c01011203009100718149440061040010780315203100243c0009a440c000c542c8002d6044240000c14070b400e40f4004074444c1c0c11040e00401c0407504510720400c80614426641c44020042d171082c1c0c881140c0050000e1410075150b0815800782d88209405038100040051103541030b000325003203840055140b4040b44010039000000342002076400100c017640644034949061aa90340740c0e0340c50003d81c004000030804000a007001e102084000448110303001c1c0701e281c950b07603100500b07481d51007580d21100040d40d480420b0349081039081100c045140001c64203030580c0c038021084005000d40142003095005802034a41c001d045c2401038069002c031030b0240d12908000d1004d4a207010481c6920403130403203a86520001151841c030aa90b88005068 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 959233911 1250 959232661 959232683
    0xd0516051801030e101a010206010608370f0e0d050705030706020f0903160801150302010e240426060f0f09070302090108030a08090106050a052709032212 68
    0xc4807a41c1894028201c0c2e2014a1a0032545014450407001001d20010280c0279910720b03982b1070108454042c0d040740c13450420044010501c0180342068420800074150000a400c03a00b1040404c2c4156101043ca24a100f515102018100f50091266041c40041c13801c1817403415a5503900c8503124059444042c144c00e0b80814440c0300c84208004585500c500107068a4104141139108a10040c0f0350003004501d41c80c00c18898410040410710700240d0750161111941c44e550076082002c03543c1c44641d1380d0180b8070300880c0c4a0452034107a0192000d008a035510014900d040c228030080c222204e9442c00c031a074800e04c10300148010303950881c1e1300030045049044d5030781e498100361890b2200c15072000750004101000001c2c010070210141c1980712170ba13511440503456002c03030300b803d8413614000da5610941004003003180b80b5025024950f860050841c0070041620001d01c14041d80048582c420302c0c3d040040c2c0b1061004c1ca204500105402414440c1e03070603404d150048a014840f20780040c49c5910032 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 959235161 1250 959233911 959233931
    0x6070c140f01060e090c040603020d0609020d0503041508060301150e0c09031212090105060303040b07021807090e0718090f0f05040309170a110f0a08030d051605180103 74
    0xa102105007000d00900900c807070f641d90140c2c1d40424101301e030700c2c000c40d014540b406000da203010301840040341e400500070002481161500c00081101400880e800429222824001403081c27000d0030003421500036140300c040343c0e0280900703580b07001850203110303900d40125480d0401d9200d45200c1a241070f02c1040819999a8000100920901d140340380d01d44138080200b010040b0480040203110454251190607488084181d400e84005031a42d6a0607002031200344010981c08020300340040c0024000d400c01070007090703401c084d0312090b00d20a000440b25007080c49401c1c100c0c0d15184d04914a45881c019640c0686080003c0d0491030140c0082c1648903101e0040d140220b80100307018815801c4e08021034102441c010b80560210701c681c448490358541018408000412140240b5400c01c840c03040b402c0b007180802803206400e260050f1b0208030140049001d03c400c002511920768903d9000030242030822614040130300c500003035400c000c07040000341c440e08810700c908060160b00703081c04586c0400e4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 959236411 1250 959235161 959235163
    0x1050706050a020327070e191e05061e060904021c0c02010605100c0b0a11070506070207050907050d2703091404020a1e05040b03130c050306070c14 65
    0x2520601800d0141854184415062641d0046020700050745420802115280038403980c00034289001074035421000b020003410f100c06034503036031020000284130744144c00359070201c080310000301d109419103200703c19020018a091043c03540000b070440389400004105951f0f5440b003038543c1c0300319018103404240d0581940701c40d0107442600c1d8402d121019664000c091080c01000d0000c00200150300705100000e10317081c042d980312002d103899a40c0b0340c00e45500f92511204040d0181c00c2c2004150380d411700c0e0720b890041138040e01009110b44003401160a204400074a85016500951f00c41d02040023804080e5420404481900f0070074000420180741114076582d440000400780c114194505801c1420154054081801c4d103501951040c88000306805000480c0a85045040800d020403480200139040240003101d0409500e800342c513241e210021040c1c03c0d001514006107290101e6000c0c010003822400003005030005400030f2a19240a41d8000c00c03203c10000003401d0545502c04107103d00d80 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 959237661 1250 959236411 959236417
    0xf07030c080c0115150e0616020d03180e160e0117011202090a0b0d170705120301090b030609060c0a0201060b0a0c150605060703030e0c041a040b010215070e0105 71
    0x34200d4006a15030b008090301c2d40c080c0a083e1141c075004030b000d200100d0485041c481000082c0003694030071690412040500c00c86920560642001100c64102400140d46085070580d450b4829038030b64848160941440e06c2081c45a041004003001840800c00000d811200d2002401c03154948031307005050440040e035940c2100c02501d10907664010020500908500000c02d090b8401d4a00c000d20f95074940d064421a544a00111380c00020100c5450100b1040500701c01c51503c00203420789400d055940c0c8030b10302000c0c17001b0440074038008001044518100d102e001034041302507001d09000c0c40c100e5502c80d00c2c2c84000b4050841514045605204c1038801d6005901030070841d06040c1da00c3c20025409040c4442003441180c08050800c45084448010700802e800c480014114905000081e5801c1e00034005004042c07a1f18800d5014030001565280503410b810f40b860501d00640004e002c0c240030554102c0f042180c19503201e00c83e01200e00034117804095010305c051034440d0b03400c000003004841c244 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 959238911 1250 959237661 959237663
    0xa0609031a1f090203011502060f010311031015061d010801050402180406030b090c01020a050c01390201110c06030a0e010917090307120312110c0d051801140f07030c 73
    0x1880d401004201181070358005c41c1617034050000c22440d2025450126030741c4500b101e890017400c000340010000035602003c005074401d00141540c1d003200b5a400210100c038400e61441c40d801c00c0c0c0c0b5904015507900a024014041c3c14407546440a85445001034003283c1c040c03007040d012356400030705444911030718100541e80c11001882803160650304c1c104642210800c0e990700300d80d40107860000500358000103816580940c070101070300d9949400e00046d612a0560139604520320081008415604c030003081ca4144035411640f490318803015400018042c40c000550320700c072076100740820401c03a40e900301a264403081424000c6007418503282e0841c05004c3c0048010800d1110407259640501c0080c050040c401c0150304440034103a48082e4640f01100020016011403d981c0b1401418400381e000285107103c2c68116510f0012641481450021070b4495080080e80115810042504021242c240c5010900e04200840c10010b10a42a4480c102501641035000102d4404150241c14034000d49 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 959240161 1250 959238911 959238961
    0xe0a2004020a210b0d0c051503010312030b0301020d0e25050319080d02070f11040b0906041805100906050a020a0f051e1b06060d0816050c03070f050a0609031a 70
    0x1604052524106c961218002d9511403c0f0012814003004414030a03130307040302d801807e85405c50b028000185c004000f0000c000d03405540820100707580144074056070784116150001030103605243c60f60300d00300945681c640904440070712000c0107103075400a4012034108201405951503141d502d0403c945200d4150401c041324000310310b44080c0400e0841700715645004401c0103082c15041c4007000115002400950b90012090700817400d142001d0740841c480005211080d280c0d044c040c2c071402d03c3c251586411101c426140c0c0218010407066009058001610b0f0000354203044040b41e01504081e141c4032100b04000020480050350310501c4059410741207070f80c1c001a96001440c01c04c03100340c18010709507522441004003041080c207284a540c80c195030030060a604100e0f020301d486205100c0c0e01000d0b070780c5110f100056581958244000c134003c00100050101d0b4515000078013001600951004041c4000800e0030408640d00080f0070780b150100d152444415954a00302c04080c4082e80341c0b003081 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 959241411 1250 959240161 959240179
    0x60f040213170d03050903030a0f090f08180f0d0f1707030917060f150111061302041508120913090501060620190302010e0a2004020a210b 61
    0xc45010407590030102c03030107442521000799040e80150150307001036076200c0082c0d004000046244005601c03144800e41b5283c004221b0464603202c400400003d0981541c00e11400030f8104c1c01c2d14ac002c500315403900000d503051a80620600001090840c5403880503041c001c00d901d25004002d4041ba5100900d915803440310f844548a0a004000a42c01c1c05038440d08030310368280210980d0005192882549030300c500b00402d90310b56000d80500d04440e0708060500030b080010740380c598018047c1c0b40c0315a044008c0241140355500401c400e441541c08000c0c8540c106107001c2c401c024020426803899010340c80216510403003100800c905ca0005440f06044619240c8410200041074101c1d2046442540e100018903408101d40701c1c42012180c00311010b640315208645c241584070188010340f9001c0d000004900f6040e50b541c2c3c0c00c149944000b1a40786e4200c3c990341c07800b0240c0d040038050719001a5421130030314404490141c010200040362050b081140b0030490003d0308070760841d03402c904010b841090 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 959242661 1250 959241411 959241419
    0x31712011502060c0c191b0603050a0c080402090403080403210c081501170c0706090f0308010b2118011e0b15040e1e0c042606060f040213 61
    0x100c1d100c41da080030300040c0641c101059140d5821002e41d09004006006010031901c0ea00640070581c210800c1195100e841183ea081c42d4403101009800030039194401040c00e240224a41e821514808905024880c2140510015032214124182d00990600740b0b08030a8031641001e44005520042107801e4050480c0c0c01003050041e80c028014ac035070b181d1141c240d01e40300c0480710414510001e0398507001604041e0100320844810384843d80112400980030b2410b1030546403001a0381140005583d0409810905c20030545e010002c20b00500d00d034003c55041026004c0584c0b414210328402241c480642800721b9a01071071030100e01c0448544000030000c60200b403081c20344038042896013080061a00b0074500d20750401c00300e00c107075030b01c01c8200795403a0074241034109010a0b4090400a51020503418690100100243c903600828820051a84440c07901003106101965000c9034405c3c210341c11f221002901000403c181c102c40216410224440d90701b0100d00240190800319003c9411014009 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 959243911 1250 959242661 959242679
    0x9030409181a070e01031d01051501090e1005040b01121d011a0a03060519020c150c1c0506010e040204150e03071a07021503040b2a030103171201 64
    0x1c04080c070581041030481405110760300060421a03410000c03485800100800d90320950015100171321075071038080c5800450745401e003192011110349200b546603000d16109507030801040e0740188450390f00d0400da8030780042c813001903640d07510403a8050354440c0c50084040e0f0088880b4200210403a0042050b241d20400140500e0600d000c0318500f54a0440803900d8002503100380505108090944400c0340d00c0c640c3ea54004100007410480b0358040c41c6982d143e05042400100700740d42d80e000090608908001b001e88080c08040c00c102c008010411510320041600e036008031000d2182c06d0300203125a075000040c0c92449103a40d480d9401440040e0110300b40c10403000d042c0e0810010f65604420802c4901030558903040d42c000c03859032201400f070010300402040014078421303201504120b0014041000d0030302a810995044620102d61010880c1c100d0712100c403514100d0404c6a034058002f05058900100c0c881800040c0895031041d9132031941486480c216007008190480441c465a500c2100c2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 959245161 1250 959243911 959243951
    0x91a060906010504031a0a24031203050105030c0111070b0c1c0e03060412091710050a18031803020604240e0a0506090a03140703021903081209030409 66
    0x240d220306030100105105511480030366090302d51000c60007103580b50602141402c010010070310241c0e90340741c04056082d69900682015000582c603140401c0500350320b06040c5407001c81c0203090802d07260000410065400080310f8101c4a02800c081404c100c80114a9080c40d4003500000d0641704001854054044005004140404482418180c0c6004100100c5801c0940914160b1540c8808003050206044000c0001303908110305103d6009542c80c0b150202d504c0d1540f038100c590340c02403016280001c40c40d016295000e804500b00700b0110201540d80e100302e0700852405010003622950a407001d41804060038080c0d1740042c081525942d6a00000c180d140039022210031040315015a1200c803070040800c01d4074500000d2015007512b0810050021035000320806540c040c46480d000400706003114048000c0d00300b444013500700726084d4010302c5903021040002000c264008102080482d0410064626122040407900306030f4a4440301c2c107107180a039402c464441c9140020810b80f0342644020 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 959246411 1250 959245161 959245171
    0x20708060108030a090b0f07020310090b07080601390803010510050c0705060307121b141207050901121107030905030a2006040f03050f2104050103090204091a 70
    0x4458081ea2500d00d003a8490140d04848000f06840c11418400c540c1e105001d4a074510050441508200d0541c000918110a02c9804600d09036106842424031000d031130362641c002c000e42080d4000381010000242000c200c080460a07095420030103015038541804000301c00f202407400e00b41c1d03580da90b05020000c0d40c82841224401c40251761844a00c50150013502c0c648941c020180c10403030310f04802c0c0001e03540014040710801c222000c03070150003411407080e0058800b20100c00d2070b0040d0b4880c4080d14503040c03442c921364081c1d0140304031000c494101d98400e6001000f468025213460710040182c51850401402c080f590341424015404908102c001c0c01203075020350340d81c00c4440e03a03460605464000c00a0044c101145600a202c42080e0a248a0b09020360181c04a40f0b41a502c540e5146100601c0c0c01c102e850f60401302c000302041e0f604002004214011582801d242c6890302601d01a91041d4402c1a041c0745c4c89182505c29596141e000b9550140c02c0203503402a5035154490314004502204d03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 959247661 1250 959246411 959246413
    0x30f080c012f03072c0307060302340803091f09081e0405040c05270a03120c1a16030b0a0303110c040903050711090c0409021305030607020708 63
    0x28042c01c90b451142c421510000a603426030005981a20070700119440200300380c080c03080b4040190000ca0f51214074102c0100038212040b0001030080c1054245403656214004050051200180c0303070011030424804003810101c0d140400020b5040d48030041c15210020f00a0103020080050700c0002040080070090380003107003403103042d00503104811602d0004001c1e20740034017030100d043c02d600100900b0750058101086141043d070f56000090954805880c040c0025501056a220440900c00000002241c059080b0310840040010954541c4076100c00b414011700c10b03031580550742c02020b182c0280c64215050590f080020894080b00141c140c4071040000801407540b003000c0d01c0f91049000c1100c0091015002915503101145d8141c0e0880040d8820301030000710101d0741e603403840b50103d0320f07202e905d0381d942314819070911001c003041344a420380c041d6a18030b0404c02ca500c1030740704030380c1900c03911030005865504900103060503103425041141c140c49688140302544e90001042c0e000c0b544524 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 959248911 1250 959247661 959247671
    0x20312070302011808030718050406060c150e0c01360512010905071703040f0603050613020c0a03030e0f070e0a0f020c0c0f121212091f15030f080c01 66
    0x2031343d0039444003203560005d0072640e000e10106025a12440c0d41100d8183c4010441c0102030b1a18001401c450003a4008404950054601420800d100d01d214025080740c6404100b089034040102da00e60f01d00d5049141042070b103858001d4400c140c0004440702c15802c842c42c0b0005401d10107c1202107000f8014144980c01c07100c40c04101d07803014001c185c6420fa00202070f0005a203414107100500b14240240030403400103201c04100c407409800200b00411050342d003c51242000424414500001c01403600103d004101018003040005460440150f240c68001128040440c0c1c0908101040100303d09078040c9880019940d511445410300801c400082082100f84503040c2d603040340306072017030000d59411103404942107183c840300c03209030040060624440b081c080d510450414441c008103c0305404003040c542001c1070040c81596104501340001e044080a40c091000000703250280ca040c0180c4a181c0c0c24030b4540c00440301402950721420111340211340f85000e0306207400c0005c1c54103483d031902c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 959250161 1250 959248911 959248931
    0x2090901080f0a1101020a080c010c0905031515010314070c0b10210606080609010603120c030c020d240b1201050c030711032b05010902040f050409050a02031207030201 74
    0x310b050850300c1100c40080c0b4201c401d903620f250342c036030b12540c856055021b20790303450010968100c010804041c241c400068008103905c0094030400d41c036081540a5482041003ca1b1500c8081c000c1c2e8001c0d85420f0111414201100120b0181c100103c1c5040348032172010a00906070b400941103425a0b2085034135068903627070082d006040307003100d20070413494800d400c44881001c8503d6074401162801854040707040368480381c0e43c5141c0203003a00e101100f0f0390754107002c106000c403002c4103020302d10301d501c2c00710b200d0402601c004003000c0429401030310405980d10b001c0104010504000b0181d04000b066008000826031004d0080010f08004e5000d80300400000702d2000c0c040c0300c1c0902c42d103810815281144c5a0240c100c0e00206100300b00380091004002c51503000310b4100e0100c0c81c888000c1e90b401002a03500d0894010707500d060f0302c940a041c0c01032005205440380604024250b44040c3c4000400c20218200300313180c074084040281d0180642050071300560120380042040074003a400034401d013240 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 959251411 1250 959250161 959250163
    0x30509011413060518030403050f0705150d02160c0803130b070201021e030d1a1201050c04060c02030c0604060917062404330605090319020a030c090209090108 70
    0x41211422580c04104901e400040c05544c00305030000710101d203060341007051848041c03031039003c0c1d0401d5500d039101c400c4003882100100100809040140c5000340d140c000054404814024a1011500d994020680034035540444c01c1c0740344086d40100c00119811783c0c8000650b12580200000c03402c2c020540300c0801e56519890841e4101c55069005203d040100300c20501c01c1500a2200c0c0ca01d404104541824000300c0e0044030145480d0700404d4144115260401188407002d0f000c45001d1b90611041041c18441d8100390360031140607003040d5511005510003e0b050000380f4403182d034810030100c0c3c0465510b03880803014003070742c900650300c0414881180c0299a200c8080b580342c40c142e0380c68a00261981d80c80d1008c80da00f03140c00b40010403110b1000104401c00001041d881d801c200f0090b50460a1a4815040340b00809290409030315110320000420388550080d020031040c6220709a0110464803104504030040d50480000c00040c0c0e10342c5d4464020398040c034040e6124a10303403130010445640c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 959252661 1250 959251411 959251451
    0x90c0411030a0e1b010507021906050301093b0a060509010203010f0b040f090f060305030711090a09020a09020c15010609030c06050414040b0a1805160f05030c0c0c04090303050901 79
    0x89403031080001c01d404d140111500da204510480c3c005048490b5000b11b1a4050481000341c4001d4440540725810400700d402202c07986807010344609000d01a29240c18180306d030603010b152000d00014180c41c0064070380d034030b011035003440100218640700410442c0c0d441980514140c4204200e4480950f64135036001c1014003941c0102030a0761042c00c01000300c05410b078062004000006030216031031361f90391541829600070f4402078030a031087d9203000d1550328064030300c07a030301441c4001e08200302e5040c2d401281807681c0d140141596140e0024a154591000300b02a50105a40f41d0045101d5a101c41c1e000b45090b00b41e00c401c80307407a249103601040e40790040c0709440a44801403040c01c4000e07000810800500030746200136810150451000c9148012140e21403035100800e20041b44074202400002c9a61230f81c0b2180804102844c105040502c1d484821030380c0100b42c170100c258440c0b40e020440c07401c101d018010309a01c0341c43e09007a00200f58060700710511030481600208006401341c0c1140c03401d01 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 959253911 1250 959252661 959252683
    0x709030804091e0609090201140a05041a0c0a05150a3b0607030b0f0d08070b071407200a060e10051c05100801090c0608090c0411030a0e 60
    0x6005000c24080c0e00940c3e0b1001e006000c03450440fa107030070301c03d000c01e0088601d203411002c0100d45900d44c40d000c0d540c005a10035804190204050320b4540d0304440188640118003038000e03030030a0422800d65900c0c4480903209181640b01c2074408541e060720381280e030b030811480c2c03414404503080001800382580e44644071505c00d4001444a075070010780102801c10042c0070b0491041c403684100d080b440f283c04c000d102d01c242419280001d50032000010064044072844089119000182d0b40c06d00041e400c07001d607030a407076001240705510703212880c0980d49200000c4000301d003080d0101e004824000b0004542ca00c1411000d994601d0141c5d400c18481154075038010440490702041d440d051038240780d000c610b0300c041070b860181c0c00c00001805c0e070100d41180c407094902054a82048c401502e00c0310702100020003149008104404066403241d0000400384540b0301444403520000703110540c00c1c03003031034103002d0700800411a2100103000c4c0e0000d50001c0d0fa424011502c1e242e045006000d00080d80510702c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 959255161 1250 959253911 959253923
    0x215060306011401031d0d1b1a1902030a1505010c0c0b0c1203130506010b03010e270102030f070e060a0836010509160b090d02030c060706090b070903 66
    0xd43c1c00c102550a038000c41c0405141015070f43d0450355804106010948840c24110014102c0340c21440001003a1000205444111180101c2600000380c5560481c00c8450b1040140c248195100d002c0010701c40215079692481038000810009882c216501111b2009002c45a03068116241c000445224102d40c1004060003041c0800344155199407000d00803451990b0121281507800d138404582d99042581c09c5000c0c820300502201c208030003405500d000d40300801150b41158540382c03030030209a074041c01f6000c1c203608200059190100d200900c3c4080c094400003907680f420180c0350310064000c100c41845c00100d00d400034200a180540c111140010320365035580190304c07110702c111112498480040319400244003180c2c05032041c11581680059000000152460320000f106c1c1848019040551052201d100501411455400341d40c4040c0d019100803042d1142403000c00e01c2c10000f424400c4d40044045801c80800400790800304000d4401c00c840d01c11500e40c00d0007074035070440c580002000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 959256411 1250 959255161 959255173
    0x10f1103010621020915030906010b0307020a03051809010e0a1419020c0a1407030302010e1f05100e2403010513021c020607060524010f0c021f080702150603 69
    0x20450000000d00f000140100515000f0004001140100c1800c3c0b40340c1201008801c20006000a0050f6401015006c448900c0c2d841e024000075103581112500505100c03011401481e102505a8000c04000006e414403080313584541c0c4c0b43c3c1540740304498000c2030a0402c5280d01000840410b81c0f8011191905112104250701400002941000e8101c0c0200d1240000c020045041040c500d034824a6074400f03007201509500f002402d5522603010391055a102014cc0c00c1c07241c07144503247c10340d80d02c0008005020380784c02c42c51240301021580b1802201101005111074002a41c410884c40750112804060b1a0030a0080c10300360349084801000900640c150000507041c003585800d484240f21075189600242c6500048568004090540c0c2e616500e008000181c40c24000d02032100c042402800800c00b072240000301000010003000c0d0812502c010300b80115100c01484240b10701c52030b01558528556104010125141155107000510452a16100d211034400115008107400317000b40003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 959257661 1250 959256411 959256437
    0x60901110a0203060a020712030506030a030c141608211902030c0303040606030204050106020c130e030408030d0207020312160209060f0612070923040e0c0d05010f11030106 76
    0x80c1a4015800c44200ca018000c10040140d4080c01040d00c03401400200503250070f402d00301880e44001840e440020f061504e0140300e416900002d180d00d2030765161405996507201803034040750407000000d16482501c581184401075000064401d03060300d40e054200d413541191140100e9010010004000d050030003007103031030401c03180500782e01e003114030320700499203401071f0000c415203550300031941030307940d2940c4c0c4204f8011031910780103190041645200130648842c40600181c1c0303068109400325004c0da03458041c000e07100c6040c13040d80c001707103c6242540e490b2111740f944c103000b940c082d2800701d00c40c1c020808007858030315010301a1004c007c4580168841e420b220390903c110610064025503200c40e0503070b402600e503900d00e0000c1500d11210f001500560030525400f6040544a4000ca014080c9803888100400504549005010011600030892842800d041c60a20103060074954121103001500418007005410083c07000054010802241d0980d803814800c40c0000c2c010360b00040c1000e07803050 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 959258911 1250 959257661 959257667
    0xf1404080c0c090a0b03100903020312040507080f0a0b06060a300e03070303110319050c040504020403080c06150d020d020a0906080a14030403020907050a0c0c06030912030b060901 79
    0x40049900d190071103400003030b004001000c2d68802c946080496468500c034400c142010b0124020580103c18248000991558069224003d616403480d0019001e00000d050000c10001c04000300010303019150040d07081000b0584900b00c1e0503082c0c44001000780410b0b4241441c1c002c540407034256646070580142900845e070701c03000e03403a20250214007901c0517a000009882c4a8a00104200d00003181d5500040c80d0240965900d2040c10404020520800c207410000028009800607140740001d1a0740d82c00c0c07804551401590001034000344085008410004840000c7c0080101c40044441a945a541d50642050f850007416041701b504904640142010081040c010703200a1103085000e443c0c1d1118000c0358200e13801450291301407000d410611010031813903c803040240018600c0c4c43d0a5401144440f03602a2100c02008070002d280c4c03910351b10400c02c007400b40e03512000c50104c5270394a01000300035100301c0b90b060315030748401880803040707500a106032039800c9409880d09050050050041d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 959260161 1250 959258911 959258917
    0x1a03070f14091503031c0e0703080910121404051903050f0307020a140706030b01140322141b01050a210905010204031a010512070506030a180302100f140408 69
    0x24003802e0b0101c0003103008551302440508150680034415280d241d401c28080020b4460043c01d61016400c648400e2001c1460601192080d82c8103455480718480c0700d9074211036003881c03d000101501d00d028410301c501ca00c201c481e50b000c0c41c040d01c1150703c80902321b600c5210004d40c5406c001c003c28810070a820b000e2440d2409140d00040d0f60059840201d200c0c1c4616200d840103422903607880d041600c080c402250980702e540e400030740a28110000b1602c0b41160380c20751201503c40740d600c10141c90a00ca240607045041d405642d0302c1001564610a04000030741d82d405454681c3c07404216410310700c2040e520a07400e0b102c1c00750813a5961060b40c1d504003a150540792512868105140d02c035054800803070710900049c8000c43c070400680d46902100146800e0f20a410b801c4948aa0040700d200b401c0d00c0d100181d01030a441007120340c25565200c4240303a80040512103040030683e64001c0d04401495000300d004840049041c0c070501040e980f1805101c1190341d1510b901c0075041204001c500420b20350409 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 959261411 1250 959260161 959260171
    0x14090d0516020d1b060908010605010e0f0d0f0602030412030b0306060d03090f030c0906060e030303070e01031e140601020c030a0f05030f16031812020111101a03070f1409 75
    0x40a9400c0d00a46851000c01800c00d4134283d07030001c00c0700c1048642d0303014034203200804800000b088140c0c02d01c4002486804090390303040c880e1002002400307480e0340d28003004061550004d09581f10111a10301403029400c2120240c0e0005c0350800780804090090003a20102c4070000d001d0440d540e606410891500050740c02501000194400842c1c0360581007083d03000f4601907850380340b22a242c0103002e0290784640d0026010401646c07014a031680300081542d8201e90b150400004071070145004800800400101c0f60203607a01d45000c3c2880c550962201d080c2001001e0725401c180d560340d00691792600f84108090705640540d60700e00116403941d00c810f00d250310035400e0300c2c9019840d03000e041090300485521805000310382000c00815030840ca200c40c43c0001610301141c0b492030030008a84180c1c1002010f414031210041e000c4032000188803440710340c3c0e182001000031102990100100070b51845505011f44600d2401281a4092200c02d80c00c03542c000d41010030600080091103440301d40540 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 959262661 1250 959261411 959261419
    0x20c070503010e0307050123041202010b130204081009050606060711060408010c0f09060503010902070f050f1006120b01060c0302071a030f0f0f0a180f0614090d051602 74
    0x540810141c0d002e018411010760110011521500c09007072203400c5425608481c40034420307014042c0c1080b0303100b040965209402c00314144100595101c180e01500406403d00c3d48040246610036111140703030301a0040da5021001c07036400080e00f2071040103ca03903291002d0901d600040000303c00745089401080124031908d001c82d000003078240411456081074210002594482585600441d0b0080340582280f10b94505014407030314040c0081c0c1184010f000311018107400080751020702160103030401d59158042d0480d10503804041010340c581e003444041c204a01e0800340f00080800301c000600b8019504140d0440070780c0d20300003090b550850344c544d04070b00354010410002400502c0042403000301c80d520360841c0c0d6078580452000305c80b40c0000d021904107404d181c180501031040309201c0d64020b07800c99002071444152040100b041d09112001000c0c5100401407508201b400d41198440850f1f50b40e003c406502d801c6201a00c52003150b07185000103909102d002e620300d0140308070040150002d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 959263911 1250 959262661 959262673
    0x70c0809060409021303060b010507030c061802060d0e010f0c05091e1009031101091217130807050301150e041b05060d0b0108060a080a031836110d020c 67
    0x1210f5803c1e43c01a44c800d058140c21928100184091801520b5115200746000c5141c0015036401600202c140ca80151946581fa9180c0800824204100c88407980082c0940c0c0c944000c2c0080501518a0614080b070715403c005003d90440325038000c15401c003400c1e803604c60902164070240020f8101200c182c400d020300381d012941103600c86150341035407201940e8030340c4812411810201c100c80c0480d610141000f01091080050059686100c546140d010003200302d030031103c01100d070f194005c1b2848503807400d001042c0000c21100005460040b03850aa009001c59103000460301d110306d6881c0b05004900203003500041c00074110440051001d0b2048600c566150380b9000401c1160b08010803d9000e20742d6a00100801e60704202c0d942d1b071051084400500f41390421070b4044e02d854207114001c0a00c0900c1044290104000c861000617080c0307449903088004c04609400c61070740d40d510f140c0000302400c9030140c904240307a01448aa002811415a107440e43c01c00703420009510210310810035000390303 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 959265161 1250 959263911 959263919
    0xf030d2016030c2c0711012a112d0a0b07050703110a21020106120507030308090601150c050307021e030c090402030c040e07080d08040b07030203070c08090604 70
    0x1070030706480903500601900c1805030070094542e80e800b5200060300d184860b94400c91000e90451100558862100d1400004141c010071195002d0001c0d80d4900380c0c90f06801030207100d9080c3d14088940288010340c0d604040c1207070440c5890712021554548207503041c400c0d8140c030440940d0103010304181d4040c01181c408070000c2e00c60540915080c0c4074840040c0c00003070740200381a0310001e03043c2419514005002000250381d50802c2c418071082c02d00c0750082801e0b84a0500074002c4d40200300900c0481c101c462041d0081c40c0c141d0f298103560200306d010400c04408184446c500040e524140ca1f08052041c0e011903508400341c41d02d070041182183d951004000d41801070700d66900004003c010300d0884411405010f00701420620103019140c01800010104000341c3da00042030754a024058400280149a15110700c3c18150a9001903041d403248420000240d039010394200c0c41140a41028482030315205000c6042e80b100b59031a100003a100b01c000343c00315164200600d980e600090006d4501652 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 959266411 1250 959265161 959265193
    0xe01050c0303070e091e040b0c04030c080303010504181208042f121b060c01091e060c0e060904051f080304030510020a09171e0a020f030d20 62
    0x1003110407000040064130300850328140003c105070804c000c43c56520103200321001e080c00f0a02c0050000c0e001003581804200850391180c12580a0368220200c08103a584440120307549500a11405010354038007044481c08036003030104000c01d282c0c4a4110f10201e1100385084807600740c050415284100c160181c0301400540e40202c01d40c444201c3c041b2100d610115040103144d1244903041c0c18240c1010344440100550150304900598007150240c0d1150a45001d46004040d9080010206c4e100035040e02410030780ea000d85601207224042c01c0c00070240c0b84400311804120702c14141d4008406010901462600350007455006a40c900b050510107a07071641401542403a40c041c0e803507038100090a00500c1002d20219141e01130a2006518106604500502c0500b0034400d101e80c00015614213040000188503003840e9052509000c41c114034038160450f1035401001d8124451103000303008a62138100491034081c00581a202e01e1040144110803010801801c0903d4800740240c7d04004007080c2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 959267661 1250 959266411 959266417
    0x516030305190f1e0e031c0b0306091b1009050d15050709050310050705040b0c01020c0a0b0a0b0907020c0f0a050a090204081005091908090445030e01050c03 69
    0x3204900109400b4501880b180542107a01c0c0e2058009042249132400060000b04641f458011160b083d1102555402101c0042201d00704042e8175000f28000e0080042c0c0000e00b01c80100c2e21507084100300703107030306003000113049500356043c0c04142c010504002a10305011000e080300d009a06c02410082034125110485034110b81c4400450341c450414003c0741020821002403920800b4100014200200050014043c1d84280304082d107001800008140081d01940c45600c5a04222409001c2501c0c1201190004079041d00020b460b100f0501c500e8070340070814a0140080360040d0080344c9800c0e007480241919103184507000384003c074001405480740070715140103101440006843e85c0c1044403060400c8016000c0050b1241002e0510100003004030350780040000343e406900c9815100e24040403240a0369004030b43c0246042c0080c0082c20700742c42d03441c40b41049058290406003100c10461803030306e0b0405001b20341c17004000c001c10000b4011454040c209205040490603d1002ca140b0340c0740d54 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 959268911 1250 959267661 959267681
    0x8180109050706121b020304090f23040507080f0109060e150408090a0308040b07060b011403060108070e0603090703020901060521060411070c03051509060f07110706020609060106051603030519 85
    0x29100040410856030b4600c612010030f290320100340300041940b0744484000be0380b04500c00071301e17403442c01003410004200080c0c0001c00c841c00c199010031301c580440d6402004c00aa003a50164100220702a01c981d0110300c030419644545602e16494480d6120082242c02c0542e00caa0030110481c1c010001c0342884026200520580100f9070b50350f0258904942910300707030012181403041c0380402c4002807540700b0940f540f0560070318000c00d25507116002165030f01028a400d981007940001409031040d404281007013a40d00030b07200c284003a640c03010f04440902c554005e17540c00960601c0030070608817205912640000c00180081241c0c41c6d008500029a40106000c032121136884208000700721007400000502c002000c41500c02e49400130503251942402070080c1c0d0340e55064400241154042c41d601042201010212014a500c0d040e01940e205001d90b04003090744504000007848602c40d80c03c946440c100007403000c030844900c2d42c080e2701401003d40722416120590320920920800ca20800c0803213 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 959270161 1250 959268911 959268913
    0xb1b0f0403081c0e03070318120f031d1003090203070302031e0706030203060105180d170a021203040201052205040f0b0108090604030e101107030308180109050706121b02 75
    0x51040442d40b0180281c070f881c94100f005082501078101c03542c01105513100c0b90340500709440301043c40d41080000c00c42a4004560095444c0c5640060000c0c0d0980c40060601c280c6a41c0f070f81c6a01400c0c84e00300000340c1070744a40e002485500c0b40c10103503c280c004104080c03014084507101074036940040d042031400c0d031703460b44a40ea4205c034529030302c6000c001020003002075040446c514144000000c24902c2955a8000103c156625102e55070711503080320502650403418060700c82c8200c000f08000faa02801c010b80040c4178140e140d60159441d00121307401141e050b1a070b9032070b005031a5450030004c1a400222400c0705404000094161903a000d190034901d020480000c480011a00241401c0005400e400c11680400100300004e03412071034000086d44c04403001c41021076101012201c004005095568038040d0a078000708241d0000c0980e40180c001000752120075400810340e07030899951131320141003a03020b88400c0009901039240b03040b050600100103c0c420000c00000007440c2ca03114004401 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 959271411 1250 959270161 959270167
    0x41212570219021507050a05120d0b03060118090503040801090501020d0501060e0a1403010e100b090c0f0301090b010504080d080a060b070b1b1605060f070c0b1b0f040308 75
    0x80540c14003580c1e0a2034885003010420342c0082e00031460200459083c20549040000e41a06010b070400c0f441d1307086c59025003218441c02003004044429002569400d80c03542c180350a189051601040e001e0580b840c00000e9480303102c2068409000c2c20700c403581540c0c24001008081440c2000f0700400c12114000d40002d40c0d542c01c0c9140440c11180c05a0155082100c5108031001e107648200d041c070101ea07059984240e07815001400a801080c3c21090a0654481e0002d500c4600520750022400c6201c2101c002c0380540e030302003800e10300d41b0542d03a0442d401c82c0108014060170106520003250240180340032803c2c66101d1010038030342484010307520013050041c070030020144100d01902000e0700e403d00195080ca81680c1d00e00b000603c02405200c2c00a42c1703d0424a498032052040d2003e400c2441c038034943c00121800c00c0d0380c80304c105a9031710b4004c4d070201d000a0395040c012038030740c40c102c0e900051000c03203039a03540100000da521000c00283d8241f803c0001c5440c015030720004d00017540c080e1071011b507 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 959272661 1250 959271411 959271581
    0xf06080715020d08070203034507090e12030405120706050a0c050405060405061e0324010201140a0504050f10020a021b1807090e041212 60
    0x443c00c44010a0002001103000800104546c00320a03a908103d41c5014640107100c100e03001c81000c075007822605d021154854103d82c46000c040340f0040c205801ca02036402060b01c0c0c5003804166440c1c668203d01561141044480d03840c1c000f80150b41c09800b0368199081611450a00f00b01c2d9806002c00341c5100d91540c0500010050a11409061841a0030120700c1d01d442c02c00441c4040c091752044070320520001c1109141d44908906a482a0208080c03495484c58424004a40300c400d80350b403014a401070410b0310344654014400c0030101c0602c1e105072451075031442e0744071b40a4003005100f03e426000c0c400c3d00740c80380c160070882e18032402c100c801701588070400f0341d81c003c1c0307058580e0500c0040e001144030789501c244c459020841c0300e035040251001459845440945141089a100c9842c0000301d00411040c010300d02c002d110003580c55076410b1600c903400008202504e5008000c014803c554400040540086504000005851442400001080101502450310180c42641031804605940c103 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 959273911 1250 959272661 959272663
    0x6061403010b040c081b04050d030c0b010f060c061e090602220f1a190c17280210090b060a0b0406050301050118030807050c040b060403050c040f0608071502 69
    0xc0300c020070030f03542003000c15081c860003803050b40050940115010080d006a6900f0f80c0f800458000c0e03d405031545421008a180040c25010107131011b441206000001145007507003410b03400b00300d0b000c1d80d94000c00c05000742c031240003c05041c05104900c0800922401c10b4080f107000d201c1c406801382d10010b0302c40d10103220100850100c14645010300c580590140820740c80728105409503102001032102c00f00110314283e05a1248221003c45603044110206401c0d5105611480741441b03030040d803040c0d9082c441200d085024290200c280d122041c603202a01400c1450300c0021014103104a4120215019011003110030015064451742c10782c004022160030440340b02c0c4000c0c070a0070307900380c1b4140c5405c000030003d0006011b00c5040101e11420504210903009041001d03540110007141e41703071007511f4081d6460b000302c2143d43c050760501010412a161031800d8600b12501b010140c0b46c00e5084000300300040400e10725450180d03a5600740030400138000c001280141a0701102840c440b20600006 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 959275161 1250 959273911 959273921
    0x14041e080706050a0c200303070c060212160212010b0d0807020918030d05061f021005090d02120d020c0607020d0201180f020904060e01020d02040504062306160606140301 75
    0x354080c81400c001e84d8291035805400d03e0919034010301c91005004103260203208000d441c00d00d503a810b1001240d0f000a011420f40d21008a5495030215001c43c400c4040c000c00c680140c0160b1401c0105007103c420250818076040028080510000183c5096500010341ca10b50b09420580300c08801041d100300b1410001c0713001e6000b00c840b1058240103000705543d141c0d64441c0c4402d41c0802902e9034003040e500d449803801d40d8002010781d40b004140c2c07071603060001c0d520800880b4420301d29041c00e01065400e640850402c41010f401d6000d4070b1301c0d1400c500c284455510011207400a039508000d00ba1030000103009690203042d290307020b080d0308c04c00038030300900313445c08000c4c510045043c0e60400c0380021087e040c0c038044103505403005942a961414540300806c80c4d5070601c0215400001c040c0441540d0f0ba00030001d1794801c03981000403540310701c1901e0b0010326945006160000c1441036111514180010b84480c0500c00740f5009090203560381c110684410340d0145c0c00b200140c01441d0305a190038024 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 959276411 1250 959275161 959275169
    0xf06081609050402190e1c080d021218010b12030a14040302040e07031a0108030702091f030c0f06090b030a09050f01020a020d111603060c03090203010e0705011701080a0314041e0807 80
    0x1041c47d00303100034103001c0c0318030000100244207030400500301c2410b4580c0d0b0107588049805003513154007490540781c40080d00c0c0141803032a189505e88084c080d07861504201e100040f000b000b00660034000b854800b0f950b40c405514014000c180c007030100100598490060340502413044020700941407542c9003255400b1030300f040514448031950018844900000709540949070115240d0171140c40c1c8005041d000003403240c0c0121440306458005c41400103d800e44802c4501c2600202c1086a84100442d460005030040c84e18101c001c00101d0040f480c2d940111001354081c6080d10540810000081c3c22a44030006180c056045210100c001c260409071407644040f506000d843c1100c000c528121f00e901c40c038000240400d64401c1004020340c401d03031081400036809002000b1b20160031404d10f955004034459140020401001c0100134030031116244d04035200e05000380b19141c1265420780b803070903a00b038204140784818030000410b440302074040d692040800001c0c8411724109000541841800e0b04 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 959277661 1250 959276411 959276419
    0x142103130c15020105091902010804020117240102010903020c0d05070510021501050402070b0403350f3121050c01060e0c07030c02030705100f090f06081609050402190e 74
    0x106106c1d40c0d0030303001c101d1f2269091810b003081c1d5a4906c0103990908003400c49140c92200c450801204030201c03c022469246200c0080503030703200503001282a18480c103c000c0c01038109001c0070200341002c1c2c205046140c0300e101514503142d1180045000c0d0b2120104107070042e030000b8002d925884000300520701600054030150701d44141e42d01c80c0c203e51600a0310040400080711030008a01000c149071003400805104603500c2403559041800c030f207030720558001c03154036000d1011a00c1c08031050340f00c4240c1200031082100d255003c40b9801001b00c0102e0007690751a0719500f150780c0c02c01d44004064003061045d101c0b1616003203010a07982c00c5800c1600881800c4007103909002101c0480004c0d90748203541480c0c041401507041c03011905002107a48001d070003518240e0b00580c026044044000c00c2c040c141d80711100c06070b44401039081045030b441083c01145c0b1142c0401c0256044200001051070b9a041c08141aa80d50b00460100c3e884000002c400810121f90380c1110307030b4011450400143c00311 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 959278911 1250 959277661 959277673
    0x2060f070206010f0b0a09091d07050603090703030807020309031914010c0905060a050405100305061507081e1e0301060f020f0727090b0103142103130c1502010509 72
    0x140c03014008003402000c0c3c0c0c5c00070106140c80140c1c41500c4800140117060710030300000105a042c041c508140e1803145207203000340900030410b4180038041c1e0307104800820041903807900c1d6803010f403000f4030083d0082c02103000c208202c0c82251020040481d030221000b0300100c04901604003040801d02503036803070680d079041c5000324032150341c40f03d465402e459044480035a80c100446007910984281e5200c103802201e0541f0f00b00b1281c1d0141c0c03000384548000d1707520128807070f10015100c1091003501001060150180a5920098109604030f0b00b990858101d247c640340c0f001d010664600e2041500203104200000140100e55000d40840e403200180e000a0040c641d0403901103850303c8980c095050340303110903000310b11944802c100d102054055564200b00f031034003a00f400c06e80ea00c824002074460748081050000c84000004051420040e403001c244402015403084c20115030001e0400340030342e40c0d507806041c081030480c080000100071802e01c119080d081e01c0400b0b800c1d950000c0c040c6090f50082 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 959280161 1250 959278911 959278919
    0x5090102090d0b07200f0606010c050624040e0604140703051906020712020601090b060301120b0a06180f0b092e0f1214010605010c170d090302060f07020601 69
    0x30340c10408a5400f102c2164207075108141160390f2040c00c04030002d00101c00600700070752440480c503805120304c05c030203803400c42e901c03840159802120194010040c0d4801c50000300c1c58000000c06004002c40d0110440408410300300140589182072001d1203150406420b100402c030b941e00b01003500d00881805040c2c910324645035640c65607461440c0390064101041d040c01004104d45c1118030b9140e206a5144038442c1041000750349010034000d542d00b007841c2058002c524a80030050364100c0b4010910104604001c0c0d0304c8204c0100c2c040c0c84060920f40390203002c01c600f4000c6550841c8040200d00010f120011621990140d0f00000310380327405000e9600501c204510340a0b040e900c3c0b001248001b040e014a4030002c00c07031003a4598032a114002c480080450b10344041c000d409010ba014900c4410303800c201c0c10b102400c0f50b40c0c52049a011484003a1004002280400c90507a04500768002a050900324160743c0d040d5140d00c1c00440040c0c00542c00c1102460b00c4041e01034110405200400c86503040c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 959281411 1250 959280161 959280169
    0x603060a060f1202030c040603030c0512182e0c030e040e0304030b091c080402031b031c050c0102030a06031a090d2706080a06060302070f02010e060f0403050309040509010209 77
    0xb8010000303030f015000f82080564030104601d10010801400400c409270352814010b11503c00210101d815001d00f414200361201500c0948142c20071031100c1d1252400000b04000b100c640c1c2482905000000c551102e08100140075251000c11007925803413007100071880c0041500e000000b20034415490615900080030000050354103407640070801007215200d140c1d07054603111642222070b4052a44600101c2d4041c1d1140031180200c0c0300381c04403802d801038051210b170f40c1c4d40604186905540301000d4141040f6281140300003e04a50922a20389040c02c0c3c400307803ea0380101c1d00e5180d001d440e54010010020865178440e0f14104201410005050407080d841c0c0b610b0403100340c1e80030048081c5c4e510b909107400146107140e44105080a4407101e94030a0054183d0341c046840d10b1403280382480000b0345070f02a00880c0d126a500071104504500c05a00540c1c411840ba14515000130301488602c104c800b01600070009503015200030340c0c443c420030040000b528002072802c080c90b401031060301c0581d15 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 959282661 1250 959281411 959281439
    0xf03061d0f0712020f090f1f050f1b070326181c030f0813030203031812220603020f0d050601050d0903110f03130303030515120102030603060a06 64
    0xd01503590703288545480e07004892105001414403a9503200142106a5200c4c4e10300825030710b0429102c06000103908001c00c4400400e12038078015003400340c039902810b5442540106980d0f0710000c00541008003001104200c000c24042d604032503441460140148101d200a0b058998031120540070400c4c0117020324035441c01001e0034054403e04000070100d4a54031130a400c0c0c100c0c4820194650500c0540c240285070103910300074240410500c10126039403240340c0b4100403405406400451a603241c01501c1c0c64840c1d002c07104030000780581980c0c400900e1024009281004d602c2038441035482014070340701d0544501c4e0340010285413040124246040c0103505559032140c101c0c0c00040c807540c4260042c0c0b5030380305154081c0c08151600ea000b400701a084000c0144c04028141200e440c400d080304d40c540da9100e0803900c0d911040303884004000080c4a6000140d115140d00e44070306100c0c084501280c035041c03503c0c91000701ca940100802213039003030400c0040e0b441040302400303012241c80e201040601036 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 959283911 1250 959282661 959282671
    0x2d060311061e0a0201090b040b0711030405010c0201080a0f06060c03030e160b090109050303160614040215031008060f0901050f07120b0105070f0803061f1b050a0203010501060f03061d 81
    0x40b00201e60090528000e60100160f2a0040c140f0303030403445c0c01c0c50440c0700741c5004c440f40c80c0400c0c1d01103c40520001c001058400341d9106856090804a00350015561070400800103001103481d00001401c41c03445003c0c902c0188030b55102c00d02c1134069484e000e02541c481c0304049240c0d40c0a0001540d08104c658101310841d1441034855544441c1c401c01210383e131441b03412150b00b6100003c1c0781101c0c541003041d0b1400840c0a0174080140c901d104031190300078141620f002c0d41c400e8080081011544c0c0081c000c2d900700000e007151400480c0d50319051400c3ca0000c50791708048803000c500b006500c107c01c5c01080c0d070089002c41441482c0c90094009028005000c900e20740b40b0b9519041d10046901480c2101c50040d04244a003c3c40019468030740182c1e0700480301c4e1400b54000c50b0340b5040c130f60480c0107102c03a400d6103929003004e004541d101788403000041c004161128442c1e5020040035803003c2c45298044c01284d915510440404200541a01c44550085141054003245d400c0060308901c1c1c46a000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 959285161 1250 959283911 959283967
    0x170f0403080402030a0c08160902030f0c030919030f0e0d1a100f230307030b0c0d0b1008040b0105030304030803010b130803180f0901182d06031106 65
    0x2d44071800442d182885120004000b650300380c03000f081000c00024061021459038000550580d284c54005091b400140c40e5003030080440c4000c914614080c00166600c000bc040403120201c4500d1811744e850130030080700b64080384440c2200e00a640d03206403c4141d84109885a44243d06981c0d16280d0b0700c44002c42e907104644c1d0810100f620b6407130710700c4110b0040140b64184065161200c43c0d00c50140c604158075038203404401d021701068180071030078600b00c2c0e400c010081c0c610303a15014400b24035406402c0c620f101503540d07c20440c0da503988550107100500165610b8440c0c0c0340519000c0124841070700f105209a00c03e120400001b003900040f00e06452040c0352a40c0c81c2e401040709101e01501581003030845000108022800710b0f1003008031004130000b19080000c102c0040f0500820440a010324840340c178000e4031010000905801030b98400e2840b030306001968002c0701c15112182c42003c100412103844800410610000300c6452440c01001c03110a4a042800c0c1d0800c114400042d01c0d141e20 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 959286411 1250 959285161 959285177
    0xa0f08100f0f0c02100e0d050d0c03090b0a092010051602061605010b1009090213050a080d0201110306090105012a03050415020109080d021c060305010606170f0403 72
    0x707145040d4100301880181c10909001d4140090b0300652140303820769144840525040070381140034400500515041c80700c0d1103c52910f1110100e41c1c0207444410f080b6070500d81c0b07640d86139002a403016206c03845080e44070b03400560003c992800009140300320742d40fa1214080c040110341142d842944491240b6014100316940c0d52030480501001480440d01941c01100450004840c3d040d11469186443c0306400800a06100c2010000d0095403910664001070300700c0c0d42400f4054080c1c2c0100040d6039100e091600482d61140041c42d880c8240d04060299004030805503034442c0c090240c8a40d51940f104502e00718681000818141001441401d04012444120f805600010f51711a194000310740000d4200302c1050401030701a51045c403400340c0d481d45140c42c04d840248107204041c0003d60001540e880d10702803400301d00294000c0c103003a84401070a85035200d60f106da50b200c2e46004500c140004606245003c101030329042007d2920403040065108111901d00511003003984151f15062583e8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 959287661 1250 959286411 959286431
    0x203010605041d0d03140a02030a1415010f082509090c0c0c140102120310090204170d05041503111215090601030908120601180909020a0f0810 63
    0x10240c50a584025007092501c050300c0c450462070301e03802d650800c0c0c6408075002400200800c804035550b005c000c1e4001010640031680802041d0001c1da004066501c0115103001127040b22190f84100380d900640103030040c0180d00440d40c2096240d96140860304003103505142c59034010000341403175620303060f41c800200c1d402107042c0e0140d540074016103004541046424211400503040d40003006090302c440c1d504842c00039225807803404e10b060740d62045e4060902d0f01d0381c04c9170411080d04058080c20707007968540e002252482c0d151001e07100a04c502d5903d14160f80708e8102050810120140020400c08100310a1110303e100042c0460303080c4041c50001040080b80900c01c00ca8007403c900d01c00240800d105100c80c20408500020040c2c000b20744c141c006444481c01902203a0280000030202d102c1400040c04500700130f528190700c01300c1810100c0e1442c01301d140c4041e005041750842801255654500401d42c180034030208080c000c80810b9510707260030040060b5880300c00a4500441e42c1c0c485014070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 959288911 1250 959287661 959287663
    0xc0a050706020a090b070602070b011205150601021c02070f0f03021e0f0d12112a0a0e010e0a0c23030a0b061603120b0a1e030c0b030718031e0203 64
    0x200142041c0041d031b80c65a100c0c1c40d00c0c0780070390b220010070350b61403608400100700014201c05801100754044010001c1c4480415254001e02c1d00138041410341c001c840040030354600180301040a0841640549002d5003041000051000241c004100a001542083c00144c4600092800d45c04004601c18440c019a1001450710704842c03601d290040a80400c040030000d065201240e582031a403a80c02c29004047d00c41a903400010404017540440103903900c0740d0880c40c103000d141c01c010182c25032115a460b510b07680030050080c7e000000a440343c41c1040420640c43c40b52a10f04d140307501d801e41661b0416060b148043d41ea613204203654080002c08100c428000d40d02040310018040c210359101c180f01030821000214419047c0d0104040c0c3c42c40d004030300585e104404003030000420644371981409400c020031b96500c19a62020380c0f018030040082000300840b24028240d60030b0316507886c40c0040000741400098030310380d00841c0f2290028000244404003508541400d8104101107402a000103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 959290161 1250 959288911 959288927
    0xe2b0908010b0105090603370c021f0c02070801020c0303010e1b04060e0607060e0105070f170f180f0c0111030307081f0f121a07080f0403050d051009050c0a050706020a 74
    0x10310003060401c0e20852000e000b03002c0092508901d41c0410118000a2092f40c60f084c03440c40b2415001006c1c88100445043c66000602079210745c8101e580303803911341050500f241d0000854070070b564008401088001e0480000640c8000b9000159104240e00c041481d0240a103000d8403003407016035540c01e41c0644900058134038480e003000f81402030b1421420140c1c028041900e140000501840c40c508406018040d40d61200c03014010318801a07aa4a240b03480102c030140110a46100842c00032118601c10088200c0d500d900e4805045416801c0c00050590f03480d0a40059030785d0428002c000f03080e5040001729034080c2d404c41c44440550308a114510004010b60805510310344450804a00030070b481c454884a5403168010006440070101c203041c5c0c0703400072146100020a4480082c2c0107450300c44049802603ca07080144c10182461008815a40d04440051410f40301103020040c4171002e0040541006035013085520704030b42c00c0401802c500c40c40e8009005143c002900300c040d07600c07071b142d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 959291411 1250 959290161 959290201
    0x81c030e03070605010320030304150306030f080d0606030915110c01020a0201020d0e010e071e05090c07110f01170c07122d0807030e2b0908010b0105090603 69
    0x80e2030360ba502034a003003c020002030000f690303100b40d4001030117101c840e4402c1009000c003001b00254213281c030f8224040002c203140b0240c44105500e61034000000f60703c0070542c01a082c490300c01542c81d030300d081c8410300480d40d456201e9010503040012510100e85820100810b282c03030240b001c60564108441540248100d011a1516620015080154035410740c007034084c20b54400340074003001d41044411801c0e41c1125000c45410340024404101121024000d04800100e040300008456070714000a18001d0044542c07070340702c0740b0000308601000060b00c0c159100c0c000844600003010307404000240b41050710706802c403030550480042007108942800380c40c2c40c2d030f51090000a44040400c1c00500d03a0040c04c001c0e40107115500400c2c0c10910601032803013085061070380d6500079079843c56011405000d514082401601900d0303803030f40c06071718507482840464407202c0402580e804c6281000f0309a1340590301c031076526450701480c80d850340e9102c422111000e82c201d6000b42c4a494120f40305050301d22441c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 959292661 1250 959291411 959291413
    0x30103080a091e0611071a030a0b0d290f010501050a0e0d050c030f0714060a0509100201063b0403050d090c06270302060c12070605150604081c030e 65
    0x144880d26a551141150140c0c0c80999940d17039000c1c001d16403560303208800c0c01544040307001e00f5a007840031a00b1034061035005040d55070110782440302001144c0c2411400a05a0f910204000682e0f010040440130100e180b000e210580154030b00a01c071004651018007520b4100400045d02c012000d10682c40d140030700c2802040070818581d02c1c903266580b01d51380750070035009000f1074840d40207808011031040c0481d800c802032a800c55a070301d0100440303030b0f02480000b418000240070f0100540c0310720982150081d82c507000000c035903081a0040c006035a1b10031808040303003030400c0d40e0304010007d0354419842002c1c11003103840c16199480d0a840754094800b000742c00c00d150078000018809880c59807800c86420b5141c0079071503041d840040e9500302a1450396105074581050400050a100d070060601400002c2610f0b1100048424640b195004c5681921003507280c80c14410851145080c00040c0c41d81143c03a00e1600340b03000300d041c0d01c542c00d072441c3e0a542203a2000b00c1007914003030741080d044015141c0c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 959293911 1250 959292661 959292689
    0x2030c130908120f071e03050402130906050604060f030f060f0209030f0a1505070c03230d0b03070b13090e010b10180812040e0a1103040c1811030103080a09 69
    0x94400c80301c0e0881100c0c1c2c4e2491341410350108290b103001d58a1600d155400d02608413200c44a00030a80c0600400780c01242c0024003900d070640f09110038032414007840d10075240400d0600b020410401612a2070300100b6280010740c4080001916080001002590004001c51101802c0074500c001340522050180c05009014806400182c0400e1001020b4418001c85003034030342c108610340899404840e00c2010901c401d00b5000800c3c000c021740f003024100c4a040c600d01c1610031050030210b030865030380c101ca02030310380c8002c1c49180f90600c5440090402c80351250309000f1100d948041f0700d5018401ca918055640287c0b018407542074005101002015021304038030396000800516040c4000c000380d144904401c404200520f010505440340f080800865042600b00f40702c540510707001604007540b407a43d03012000b1b44c40500700c0c0503601c12400b807814a103005107003000144609483c521240941e07483d1040c404e210f00e40d06402e4905480e000b0350110744071040300714155024a03d41d01f1180c60070501c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 959295161 1250 959293911 959293927
    0x6030b220804140301110c010e10140601080702010b0303120105040506040e070915030203070b03010e0a020c030f0c010b041e060b0306030c190e040804060906050702030c130908 78
    0x640006805890020040c0309400c4450240400340250140010301c21a8104020012841c10700c0c02400544001000003910800320b083c0104154010240b03030780340b6511800030404c00081481a410700003000001400b00c106048180a0070b000c0c0100400e05000d200d0003c144241d200354000f24507100080c0c12a690b07160401e03404880c52409104852046040c000056100d0070030380a4640e010400400501c0311504002084000e4400c114081c4460208041c0000140ea0304001000060400a240541c1d039410044e46046200700101032081483c01001108246a4000102c41c0000c4081c14125164451521100d0141010340241d507405410720103480341340000e11900d403000c50080c42003005141c0d680c2100011700d0208803a0980e0642007044020f060381050144c24461b038511020040d60030351181c1c81c0064081c4165415a0400301c0420184059500a100c01e0050601420843c0c01d100407a400039a480c100c0715141c03402460840c18201e642e440f680c00c5225119807140c4003503211a04 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 959296411 1250 959295161 959295173
    0x2007090f140a27150f180809060c01051302040509060709030206091206070f2a0212120f0705010522060c030e030412060615141c05070c020306150109060806030a060603 74
    0x144d0810f40c13000d18605040300c81c8400113445124041841d102080601d0402038891409a070000c07203c264011400300258000d81e00203100312480382a00101201250f01c15006200403103c0040c00504540d00c01400d00800340d8004046800300c13a0704440843d940c04110011800c950011031409082d8811041400b4410303401c81807010030f0120a96031070507208829421280c0c182561021912507180c601d5030207000d810907681442c0032400b84011507841c07081818852007664071007020091004400b069007020450f081c0569500f0007651070724440404403d988113080c0c0d110703002c40108401d42e9a491004c40038002e1300400c220460b85019251101d6681440041460401c2800c403481c1d840e000d4045802d03800c000c1c0391102070901342d840c19030b84407480394041d215a0000d244e905c2d10010f00140306006003d01c0c0100e074400d5500c3d65a02103800160b1043c1440c02d00050600c00306140d425200d100c45913440410745040b2209071a020b441a114200030901746026050003500150602ea800310503c90 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 959297661 1250 959296411 959296433
    0x240a05060f130c140f120901020c3403111c0b010b0912162601050712050a09112704050610060509061206012007090f140a27 55
    0x107040d26110740c4e110380c0400200542c13040103201124110f0034080e40107154000402c0031f034000807200005242010058500380b410415580c1420240481e91140041303552001c6070094200d10003c4c622074036810342c0c0c0c8004052800803002030140340d41c20708010040400940c020340040d00001070520301e5845a0301415154810407825009110f0300c0700a407618040003c0c0c8070400722079060140714050820140b6510fa8892404604080040d00e4420b202c0e000c00388507050059016496002a0101200340324081d0703007000304048101440c02c22400f000c02d42071000c04000f03035000c4901d078900c07015031307003911100b05021001c5160040903030342088100302c00014007a004440220701c4080d50366a50038103c81901c1180d2407150000e00c2400400001c10170903050941080b01418509092000da100501403030f40710001e010401e0b030052604001e60402c52058808050b2200b90501030142c0780c69011410180141207001d489585202128052400c095044400c03101d0406145a4001a017040c1c89000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 959298911 1250 959297661 959297681
    0x204020a18030c0512070f0311060d0c050910030c0f030e031608091801120813050d0c14010c02010c0206030c070f03090518090a03111914240a05060f13 67
    0x505d01c54070030300010000b41910803030301c5551060015078115500d1011170145245001d0300701d00e0500800400d000c1c03c1c09244008059903849c035807240504e504101c101d01740420081c05040c900380d8007030b041030307170004181c01410703028100420601d9020300d03017529501c1601d44100c0f1503400100ca8404001c034500c000c1c0049030b01250348119a4150b498042c1c1050028855403c00010211812001501c20307405480390340b0703800007001000380e5110086910714006d407900312021091840103010045040e01c8a141e200390078a04240401d09590000e48010814507019108407400300001c0c01031186401100c2000ba480003400d031a8051515014001c0d1381180115482881000108180c11a40040036445150311b68002d141d41c80c483c0e00d054030449040c1500e20220b0040651032910f5a100010607411184100c481003501c0030303140003080c1041420070a4420488480e241000c08199160b1590b8220501e60030000322916010000b8488601e5408c40a0b00641e46400f04054440c082c0e000030007030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 959300161 1250 959298911 959298919
    0x302090603010b03151012140f0303070c0609021c0f0515060f1201150b070309051c241802041802060d0c02190506010f0b07050a0204020a18030c05 65
    0x303403603010425007a1040c0000e0b144d016403081440480c1e04960f1034055400c4204c1e0044c1344041e50b16000c081078980442102541c0e800149805058080400c0000d0184401044065400e5040204000701000946040070700000e407100d420f28190f6a541000c009140d00c0e8202e00104c20409140001d540780a00e07405407240c4c06044c0c00351807500c007130001c024850b000c014984c0c11141021403c201602c5020b0300c55020035075031a014075080c40d0071891850090820035003080e85400300c40c90003d00c240000c4e00320500a003207180760704080700010b800e0307009445d902110040001011171102c058401004114a00003400c2901204009000007100040b81740252414852402c018030000e000b01036848000b50403820810400142d40701907070002101010603c10794259806880100341170715106031060350142c002800400c4640c4001120100501e403d4845600304003403926801d4440c00030600103400b803500010392101d0680700f206260305080c140c5841410a548a0030a4840808140a0303a401 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 959301411 1250 959300161 959300179
    0x17030f18011103010b1b010509010b0a05010c3f0f170f160309080309030d05060108250507151b0e0306060423090a030e012d02070f06090302 62
    0x480e00040c002e01d00307001020404540355910344801c0c1c0381c060f844040401041c105c42c401c00f016015080c0070b003c5c01249030800100383c0300001801c0201500c8103030304c221706100403442c484000900c0d8031403240c0502408041070700fa0b0f0074070b0b0800203008440101c88170508600050700300429a000306000c01142c00a603100f40300300d646006404401c81043d03600382d400c00304410004094003031031040c030f80b05140e1518002ca040e035850b0b501c0c504160825a6884c2c03003500007182c51907800b1014890154041002d282000707003410070086411004100c00c0c4035540c815403000b1800c042d58016406c44e500340354801c0803a5038048446035940001e00d41c090b08003000c5450762070b60b5064588140c014451015000300640b2194850b0020400104900e0144812030702040a640c079484807210360480c401c00369040038286c0381d030440c40d005140348020740e400d5043c001c0b40e00140240180d410700c101040715801001460700012500160316010855000c003000644110001c07600c0b560201d01081160700c260b9030181 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 959302661 1250 959301411 959301451
    0x804030c181b0507110102030415050705010b030c090406090215030106020d0206010503033f2d10091e150513060b1c29010f08012117030f 61
    0x1103804480b010400550148400f1010444205622600c190140100c1e4901580c0d42d600360041a000300d02c031004600d0200c2d101041c030000703008000540300c00f1400b52181d0203054001955100001d807014146275684d400030742c1152180445112030726401e100c456101d680d03e0740025942d40f8900955001801900c0000459082c000151031800042d2a4842e00c0300a001e41c07560749446491480e195490407000c8a0000e218464551501035440000841c88110402035841d928988100e5468483c03c04202000300300e40c0300c10000790950302072640220f1305840b0442e200040b10341d01d03800f24030601c3c03038140382101e0030001044200840d1800e0710035040291859541c10100d481e82e00c00c0341c4a001c02000460790305081c0c0c002581e2281c6c3c118200040050082410304083d0491039511400580b840030141800d40e0446045061002070707290450361766040080071a0f0200780603003c94400300c00301025004104c2420500040c82c401e11003600e899161548085160356800d4444507a854445061a5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 959303911 1250 959302661 959302691
    0x1f020f12161707140f070c0303021203061f020a050d09170303091e1216030801091517010f05250809150408091e190608130804030c18 59
    0x1030344458800b4680380e50390300b030240d03610a15140b02184280041005c07180c03d01d404006066510300a000d0f00e24031604500d070191400700c401203038900400c0c042c010488265205164980440207a401046840c110303000c1c260315010741020b00410a000e00000c804125a000091404840e0030541c000c0c1c002110917001c0d5140e1000b524003000700d401000d13512070410300582005980c1c2c0e041ca8119076004010045400454214070824407030303a24042c0300c24051551224215003d0702406000300041c601c20803607440110034511400a014417412402c4c101e0383c600798007040408005500a06c02c82c900510000201c10812156820f00501c1040e11010144140e0900e41310301c9000c801040708542404c0c20400211006108548854007040001c415031580b00c0c400314601030105078129940600030803c14405d42d070705802808a224031000300901a40300a1264110141c1444d010b0080f509040c24a00d503c00ca410144c10000c01000003d080c9010080c40c00c0b820f009007004020607441400f01c9 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 959305161 1250 959303911 959303927
    0x180907050403051c170408030f011a0d0510051c0507090b0a1a09100e0a0501110a06020f160818030102121603090c080a140d021f020f1216 61
    0x3c1c207180e108581224900316518103032071484a03c1e0601c03072018030b8030521440082804980840d10f510000c4240f25030424445078943c09804100412041d400c01c249991519011b45030f101c03000c035a00ca038040340c00103401450104c00b030807000d41040040401c0740764292003164800b8007110700b071003100b03800a211905c07445041811a0024510898503183c1000c00c182c49072400c43e51022140304000000255441403001001c02c18a621800c2480c00c0003820011400101c2d48202c1c1400401c1207100c2c818040845c10002e10341e48030100507201c00507008608554010fa5116031060500f003060704092244900c05003811000d81b8041c41d47d9682910189400c0c0d000d403070a8680190031000224242e010402e05d41290614945030010309083c550700ea805010072590311140319034000100748400e00c01240001501c500402000301012000032100a60354400c65034001001c1520308120b1a4034241601200c985181814100e6250004280941d2440d4816580b42c07038201008003040c0c0816000b2864 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 959306411 1250 959305161 959305163
    0xa0c05030a030e100207050409060906050610050415120f0b1903020915040b0901170d0507170901090e010801051e100b0c01060306060e0105030601170601140a0308180907050403 78
    0x3100b100f90105030500c220058070400b94025401001c0740420320b82c407240304066215001d808081200d41441c1401c2085a0000d09000e014002040041d0000d540010894003101c6c0c0340a4403a1050180c04800c59000c000c03c01c1e0865002d05040260700c90f100799401034000742400f1201c14001d01298000b444881a807884001d411902c4c05c4000345c81001165440c80008a014202140214010b0300069151500342c001e4503084842c0d043c040c1c100d800810142e2114a5141030003483c7c80542c2c2c84401d070065401030800f0025a00040034200f44c3d00c1090290014000301060381c4ca1561281c950394081c100440d1a201da00c1a4414801c840c2d0b8070144040e07000d012005241b01d429424031564041c0796100d401c608103150340352000000040d6561040c1c40003040d03602114125035040200701400c001d8103900441142c4621002540c0e00d00c2c1c0445c815045441d25507051101d550603101017905031000b40c0c8040c1c030004020400280105495403e4004817000711100a10b541e58481e06030303168091804 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 959307661 1250 959306411 959306417
    0xe07020d09030605100e040615061d0d260903011a24130315050a140f13080406050a020c0105210a0f06170f0601030210051b01020307020a0c05030a03 66
    0x703010404a000c680c4941d0f003000c4602d40c1102d1064880c0d0341c540098109840444c2c2043e42e031440c4e0600b8a05035034844000c1d05140c03403c0c100c00d0815584500300030060140c03440c881c4d1034401e200c60030450400143c4d44880030250364084d10b0002c040300c1050703070f03004651018002d5003441c0c40041040310405040841903001042d907210351894a2070071542668030030581c2c400003000c0004040700d22840c04a1002984a00b1a081c15910280c00c0d5005981e4050904583d140c1000e92040c1c0d130910024090f07610a000171514115540e45285441e207040b1550406044150000750115180e503210000b0a0480d007213800700d416544040d80111454414013000b1020594200d80c1014034041c901d1480d0b4000d146e822000c16039001d2812100b007121702a52015004034402004812440005d0007078000d04802980681074543c519004100108200c01c042410001d0000e22842c1c4440e661400b180300e514141e000319100c1c0381051001e5035070703c850a01a03d01d50303091342d40020103141c0018010702e40b5505603 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 959308911 1250 959307661 959307677
    0x1a030a020a030e0708100f0b030c06161a0702060f04050606130908030106030903091502060c03070c12020601260a031b0602131409040f03050901030b0a0f0e07020d 72
    0x5109000035000400540200b41e2100f0407010090303000c0100c0d2003e00140409801025140022041200c5a0408941109023040c0d03007405d00356008203401260070400e5852035500e121004007e0394020394824000e040a500110700703040b40782c2140c0800d1103a003030744e0216000c0380c4a640e03100801c140111070051095100400140c61410420300c00340ba0500c0248000c126491075039a141c00300d80098105100003a80e8008141c240365104040c0c0c0010507071440152098203d03a03400035100c040040c508026400000040790140c4e01c590f000c411115084181ea44803182c0168000791111402c2c8181c03540000c004120420a01e9400010301c5049104c1000b440c2410003a0740546880c00704801c802c0f079003440d40380940003180c40d0f80010502c04201c154405540c80c1810300f50082e00125080e80c500507100d500420000916201c1e072050500e03014103203c0e0310381442e00b004134003400b554652550081c40b020400280d1003000901a4107481044541007003079078039403000720307602d440d050134482c0055018 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 959310161 1250 959308911 959308921
    0x13f15090605371e0f0203070212070b04121b060902010f020106210515090a020112020403020607031101110408300d050c0f07080a020d020d050403060e0f01050f101a03 74
    0xa84c0001101000950b010000c40e402400c0300080362104c20003000b1280c0c00204014040303506110460441c00d12185c4103062466548070a40f406000800041c0303c6510703074400020a5009040764005560010004282c1c4050f6241c908003601c690002280030401c02040f6980f00384c0103010b9001070b9414200201c0502c0e013610b03620b032411083d40e08151030f24000d401703042a00c000d40e44e000d94455440a4024000000584001000000001403298449105100070300050347ca00c1708540d02c00d40c042c82c1480c043c55440c40b2680c014403c0428800c40750000040004d0304101c00306000c2058071042d900c40150070f10703103032a24140201d0b644003035290900400056013a8075182d8465500081d0003851207080c40003401c402400c2e5484054140d44920000c40c4010038154100200c43d401d008a2002c4e210040c00d0b440d0191050099000041803070b500c0700780c031683c00391040204c0681c81d0004002031209051526480821401c1a100340402c203101080206e00141c0380600201c6620030700320500d02d90303907403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 959311411 1250 959310161 959310271
    0x60501083105030c0f160b0a231606050f01030c050909031909050405150a0b09010314010303090807080102030f0708070e031005013f15090605 63
    0x81505050941c1181108400400d10400150994901040041c05000d22000906280c020840044040114040801d10121118900303481d01c00b5600e04046003815070891071140301442604003c5041000807400710000343c10070745c000c1503480c080c490800c280d403122082c40c0352100090002500c403024441c0c04202a080411840303a01c030345500241d0f0f0403c04031010060420703100c40f495000281c010007040c0414038003441141d400c3b2804000c1c08404051010101760600100c1c82410b01c2075002050000b0f499019402610000030710700c46c59113081d0b840c0d280240c1000c0c214003c1c181207114180000c103040005100702e074007900e10311116042e00d907103008040302c6200c0024803200400011520003100758404014000320a01002c5011481d5810901e0741801c08500810040042e01c0c021101c103408010060040026011107541492800441c2401c610560341c50841803850703440c109200083c0080c40d03000038000e00702401c8810040460240011441c225000f080d081d08182e601c48207002c0d50 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 959312661 1250 959311411 959311471
    0x50102010605061e0c01060801091208150105031e0c0c010e030f0301030b2203030b090702071202090a02040f141309020f09100504090302030d0e15150607080d02090406050108 77
    0x607642c4d0f002854034103807811090944100c2e600c8008140e443e00304410030011520b5200c0040482440c00003103600c0c2c4422421100c94810001a051110020100d00030555048090880e02814a480c4071342d4241512890519400448140c805d5480d001200078130f420040300b1074910915203d4010f0441e42503803580c1c1c1c85c884003c0c0503141e421744540c0380361800030302d455800e468150007510b0007d0100c204000384620305c040100088115000454140621614212100e18490701543d0601c00c2e40d450200e1000207100c1da400441411890250008004a08049800060301d05030346942c0c4100c00305c65000e042c1c2c0c0c01c40e030340254440d0a160006180e400c0a4102c1c0e580240d4410001d460340b40d50320701080490b5546681500185c10003d4410a07580103030152500d03444420000706a91182d000410600303c030301030084c001c210746c880700003804e0740d0320070040d20b01094012084c02d40c0c844040300c28500950010600760700850900c04000b070300d503003c1d0584501c0f84041d20340d51466001c14104594a2003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 959313911 1250 959312661 959312707
    0x30b100e0103031d2d150405010914040e0105130c080d1d0102070b0d0e0c030607051b150c2101051c020402070611030103020a090c020a02090705121f05010201060506 73
    0x440700e64004c001c1d8880210406040ea0100d6050164001500042c860691140350010301d51b00420842006143d80c800b088400329103101e1403825281c401000080c3c0a403290720410107240d0f00b05003c0c0000c204050303100780e92051203840000304c240d42e20000c807510f440d203010079107001c00e02008250040402c110851900c4047c148180c85813507031030300310060090700320503c0c034200e240e6600d005071074820040040c0500004210700800c4070f4900701d803000300907106803c0b6500110300100c425003280c9400300441d861407030100c981c0180d10b250502741d80c4040d42119a00c9651210b0a0250720b0901c082c085201e0305072000a0010810300200e42c1e03d2060314207074410104d801c60350811214002c201d0b14401c00012150a02c136055484d451070041201c410103d401191a061a041d212200250001814002254107456900690351000b07429035550059820300400b082c02101007003108000e20403811540541030b840803000316280e10049080398860b001d117a801600400c031149410503420708821501c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 959315161 1250 959313911 959313919
    0xe100e03060c03041401050108100e010b091b040902040801020a0906031406121203160f080f1303050d0207060c110304050a090f0e030403030f0813081819030b100e0103031d 76
    0x11048420b45c103084480c03d900503003140d00260408508042d1b00d021300c4082c10b01c85002803241c10030070b0002603010400944aa00403540c0751314840140010081a90000c04080c1d40031500d50740d480420074041d5024140da02c000400310342c8081000c50080c8108000002c030146001c070f050795950103201e0403a4081490602d40e100315900c000c0044140802540b0950040c4400004ca0002e2100501006038208101050029035130410070444040350f6241e030300c524290000a8007180c1424252803621032004100007042c0006440e405204054011000103840e5a4808400b031104030300d00f03a2a03021f0390180b80c1d403160780d80d04208000303101900030000d074a60060002900c1480c04426502e1544158002c070b0100341c5e0902d6a8591300d42041032658820360740a500c840b900e09503500d5607000c0c4180d150340c0320100800340c201d0410303448601d0f8001002500140041c3c40c103403079040401c2c080400702c0c3d100b0340941003a000894003840c1d011045040325419102c41d4048081c43c4a0f9a0600c8600c101c40b40d00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 959316411 1250 959315161 959315183
    0x60112061a12010f150507020a03060203010b1201091803030510050916020d090b07241d01060510020606100509040507050a030b0406080c1009030609030e100e03060c0304 75
    0x14041c0300000408441d803001c01420390701c1030740d05a0312440d00d00507800420b81e494468002c00c2180700c85c0012412003209031415030380e20003440c40000e0075041103400c05058144080004582442454020807203605030640018490703a845e8404d0050721031710740344003c00881e42032401300080c0c00781d000950450401b8ac0308080b096101d01c08a006d101c411506075a0385a00140d035000c0c61074050140448465207813500d800d1040c1080e0840c42c481c840d01100810115261200124103940d80c20740705006201c0341000d01407502d84020701000f0717a11440100c0d105511300400000e81d0315041c492400010920340251001b55500070401ca004ca029000400074414100b040312110fa031345118061094045850b1170b910303950b020700001c044038400c1040714002c92802c502845a0440000c1c0c10555182c01c46034015950700c1d42600320380514550303000410313190500001d482007541198410301c80c2d010507125003243c0a04400d040360510826040c0540641005000c9219a82440000c640c003034018911514 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 959317661 1250 959316411 959316419
    0x40207020d0803061c0f150b1504050a05010203040509010b070807050d020304030618151a040f060e0601050403170a2a0201021204080303010e0915161b03050306011206 74
    0x442080d224504036002c01000042100c0351805903034800841d0843c81103e50301010569074040f400380310107005820a00c4106400d80e04440c69004000c40300c10150039440041000014200c0c1c9402a0050714410004d507440428154400030590301298bc00030401d889076464a01d10501b90b600075102a1602d000c100300b10004030320204118070440070960b0003160307201c0c41d41c1030880c2240d0024018454914501882d2008a64441941301c0030709000c0b440054840c0c0124045e04090700c060300610f8129081c000002811146035000c9803c03078030720404600d0103941d0351703004440501c0349010050241c03800f030118011840281006e03000b1042e41e400c000b05a500440480c0041c21120952844424202103002085507814454551400d00000344181494207101c402600d034001401183c0001e0002d80c0010140e20003084001800d1340b40c1000c640d074904005a141e2408020103101c2400710b01e040420038400c0c002c000503a0b01c41505603a940d41962511401140c50354900003401c4442611150081 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 959318911 1250 959317661 959317669
    0x30702030a081201120b0a0510080a061b0305010602030f0913050f040c051516020307380708030f06151c1d060c1b0318040b031f020904020702 63
    0x540c01405001203680b180e5500010021083c4140c215000701903800801600096071000041d811034080036000c02c069446e10b81200103c0d0240d0b1200ca203602c0341c440d10348244245984500e50418003060701042c610f030889415000e41d8420702c60580142d10411107500d551042d0740192410540003400d5030f00179040700341040d003915001d4582c1d00c8006040000e03c42044820721550000380420345052583c441007100c2c0c00c5c640e0141c0c11408603801080c3d82c0010071903500b403011304058903403810503181c030001030103004ac1c101d001303520000c000709909203100f15030000c290140d80410b0790000c007070361a65a4040043c01015000781146400c4407800341c034403200d5041c810103004803408080746140003003a0420b0507030950350f00540c00a45440442d0320f0312101d501c0407410661100c002c0c200700c1d54542e21030380700c0691401a11141e0002c0c2c0004540c015082070710300041090b0f1041101d0a00c46d01418404058031005040001006402d00d54011b0515400340d0700940000c0e107000708010b040c905260045 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 959320161 1250 959318911 959318923
    0x171305060307170714042108070309030b07020a0203070317130905090d0503040b0c070f3f081602070b03151503091203060409060e0c01031a0a09020a0203070203 71
    0x14000700e00d450303400400c110f940940c80c0d60b01826919007115250801c080c903240910175402404860025444201d590000321000d1014040e80504517075a02c00745030078024003103800c501040b10f48640c02ca000c5a0894400503403d2407042d00200a80382c228615524010741d8992585082004107060055207130481c0c038042907400420781440003081618003101020304250001c240042840300c01e00038800401c0d004e0605a03403040d9103a61482d621542c1e400e10880c3d1056080700205011160302045404202c3c5421202402240d918180a6013040c01c485000703020400c481440081c00200c00141000c005400d51402c00e15a8015900e065403202507104c44c1d940104c034140c4111100f900a08030606118464040d16036640d000a03046080c0030011644900800c1480b8000000200c08100d56640c1c0390b0064030502d40c800b00410082a840d40d1b22910b480c1610b501902007403500c64080d01841c111541603141035070084c60407040c01d090100c84802508110414005c5120034040724005031010419 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 959321411 1250 959320161 959320171
    0x60b0603040b100801150e0a09240501090903050a0e01050c010c05270108040b250305040302062a0309100c08010f050a0b0a0e1f110c0307031713050603 67
    0x460000f440c2141d041c04003100d80750f10800003a8905040110a00b000300102810350300b80d120080500e44803110000050014140d000c1d2481e8241510f265003208030f104039a0f100710090f1400e018903aa80c842d0305080f02c0c150b00026000c103400f0481600c0042c031a0386010344c0302105042c0b441c10980d076401982c0c01c44134022840c10108400107200382240345150f01e00d100882000d010507000c0081000000c04c54040078000611184800c4003107600390544030001d18041900c119000c18202c85000001e02038003058505401500525012a00c1c3c01005c1170419207408101d0500d0b000581ca1180d250f105070b10040081d204d5015191040100394214010b600d0003144556961000354100501c42501e010560721491048103264001c0000c010f12406550704c3d40900c0c1480d060305600385010801d0f010320011252801010184210745140c1c00840520700c00341e400c03040b50022008001407503580c018600010b000040c40442c03203500c100c402c138000d04070022641d1546034170310742e40c4021420340d420a941e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 959322661 1250 959321411 959321423
    0x80111040f0b0901050a0513080307080702010e0405061c030e03160f0905070f0c08090310020a180e0412022406040f1b0f0e0a1e0f1503020304060b060304 68
    0x501000510804035040010301a411245450b1001c3d040000e841ca00c2003844580901c030001c5102e0140182d4804503c0082c412003050705d542e180b05150030b0040741d0089508a02242070050418181d02b00b6100b941c3c8100c01c0a0841400b21074000e079900c03c1a18640b1007142000300081181070a510144201544110503084808846041000030803402840b42c10241c03040e071806081164542d1705c00c506000e025010b082c042d01c0c001d618203140e00c4034464442a070b60148110b054001850006500905407561301c2c2da24808500c0c0104203081c03a0741c1c83e600c11303400300d0701072000800e01250718614804c29000050044400c1c40c03c0104503500c0c00907582018a40020b10700040019505050003140038400c82d9103030401c41151100f1300c4001c80041e100000c410088002d00302124280220070b0740ca070b00040180889902942c0758060300d50321110605040d1214890640054803a08010200082d90b007000300c2e100c01d07444644c070110020740000303000f610b915403100e220b500c0c183c0b80c0e50300450149008032 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 959323911 1250 959322661 959322667
    0xb09130f0501031707050607030b0d080a090608060d0203070504050a1b111b0306070e0102121b070605120f192301080d140c100608030c01150f0302040510080111 71
    0x10400e0504000401e0030784d411582c042141030002200403074820f920180c6c0e400c00103459807500c8040b51412010710340c001c1000e140000c1c40c0c000c2980190681d0110f90b065034071150369a4500c07050014100d040b45c0020b4155000510902081c0350681026031702c580c80034030004400400c2c41a081c48050700c01024404140030496100364080140300011200380100e51240c07250000501103603035290001c0c81d002c00c1015008046c11660f1091045e85040d03105241c50310740b6030020360359041c42070070b690303020040900c0b85d02030003e1900e000d40240c0f1400d5040a42d08441591540410015403500a1244d9042101d240c10705e001d000785441451102081c030690200c0301c030801090b409502c0b0040e044400c4582c0702d00300c21091640d0040001901c080c18104041c0c80d5002072111a1070200300044c1c000b050b07801c0043c0030582084c0003018024252049000b8081c0010035200c40f816086503008404c50b84080c4802400542019004a41c0005010b8225803401c0c1e540d1440c2407c56031100c201c628644400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 959325161 1250 959323911 959323913
    0x70803580501061407140c03060a0c0816081906150e040e0705060d020a02010f050115021615030c0507021503010f0506160320150a0c030e070b09130f050103 69
    0x28460180540383c2d50034096a42c00080706814060301841e107000303200785210400608030f94400d00c040800001c004c0c3c2143e2083c00c061401c02d003d0001e80034400300165401c4001002c240307140c500d00d00140565103c03045142c440042407030783c06598107107020009482d104002800c2442810030303254001c00e03a4903039200e14100c0d030410064500c2560700e94440e60014500b0701c429680c0004591510a0b61140140e071000c548500380e0262040d80500c400e00c510b000c00000d02048000400085070007aa800d603000416841c04500c0040d0950141e08641c40045404003182e9019901003070030100c141c20140c1c00c100c400d60000305080030340071260b410110080700402500a8075241003002e0901262528100362001e0351000308000342500240c104200d4000018048081504110040755680d00f40c507407180484180c5402c0000594150035005e28150705003040b41c0c401e1140c85c0403001c4c0b0f903002d450306525084080f01a50420f20025a015407420410396400072244140f0340d07841a0704101044640c51 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 959326411 1250 959325161 959325337
    0xa060506040b04021305060a271d0f010b130e10032009060d06090b160e0f0f040e0f010606020109050c04020a0801090e0304051809070803 61
    0x102c0301150340a540103110078420944240103500503248255121a03d595078034204482801c40d42c0129004c0c9042c1c02007108180d1001c90000f0251000240e00901c00c0c1c488030101c00c44844100e0b02c1c1599885134500600240e220080106103400701c843c180046e00d0303180c06a004041000340d0742d20030914002081041000b481035080c011300111200040d1070b200c21140400c440c0c240040425206207002803e00041004aa01040849401c0200e013111441d20145010721a42020109000720b01e09c20764260491401006040030301c8000f400303650154001c00c051001804051204480034010420b243e11162024450003008060590000c20809098201700d410103601c5107005001d0b5004021056a4035049011281100c80c9803e0020343e03c000e12060380e0942c0a641c00c1158406400c0084242800380c0888040c003c2044400360349901e40d9a80c40c00c0e550f44038020b080300d250403403406010010103811068850309c034025803215440ca40c0e0b00d600041c08072506134000f5040440350840c2e41d05028 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 959327661 1250 959326411 959326421
    0x9080c150711030d1d010e0a110405012303101a04060f0e0402060d0603080310030210030b01081305070510170c07020f060307170a0e12030f010e06030f0a06050604 72
    0x4450034412898071101e001a5244d124081c103032400f05884030396221410a0a4503440d000b03400c01c10003004400b070840c0d01b05407a40f1821000f13980440610203280e0180c076080c4692030403a40074240340304021500b003151201041d06a9000c0e07900d40901035611901460701e0060703104c140d950201c6860380b801620b00704070440b000b0f80c11032060356800e10400e0102d0302c00880038a400540440e9040c0e101c0f40385400d402c0260200c2e030002044080040203000070005030954060569200311030940b003040c407001c001c45c101c8180c017040354000349645002c030f1940703041c2482c004c01c1c140c0100280c541c1c2e01c4d21000400d00c4118103403031800c000b03400605081e540f01c0c5100042c0382c028032111079507481c1c40410b80019544034040d040c4a8422140000400c550b27030700407000c0138a05590a1040341c4180b4020b04482c00501a2801541c1107005c0c0030f1444260340307103c00880b40700341408050300348940d00300b00c104090b00310002c0805406116080d01445204010801d12510b144250004501442c00600b8081614 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 959328911 1250 959327661 959327671
    0x1605010f11040e040f0c080f0703030e011818020403080412031b050a030f05121501090501030228030e0f01050604060b0306100f02031908310f030309080c15 69
    0x441c180300501100d25405442900a030b0000d560100352200c03070511502002c1140e12071800d91040c0303015001003400201c0c5100480340a42c4910500411000c011358001c6004c200c00046000414400c0c0303c0124070a241883c0c500d400c0500600303084e00e0356106084c5600c90382180aa82c1c62400141081583c84070800d581035000e0180080d0410456407080e944108560004040c0301074003500030b100320321031415240c1c90040e80022504909102c841508240c0008900074000744507280041481d500900032101c941e2101e5104036001501074130b05d04401d03d00c4500d014101a141e0310007000c800e80400c8414030010102000045a040c0a0100030071104154416143d13441c0c1841000340558401514100351801403d0a400990382c54070300302e08502c101007407118070a0300002081801a8800c00b0f091069007c1681c0c100b02c00e052007a40d1004804080001d80d09000e0f0119200c00208450310501d4098824140410b520700190b8822606400122401c4c195900202d542c0002040003035100f0b400c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 959330161 1250 959328911 959328941
    0x90e01241d0d1113200d0b100c0c080105060f0d02060f04030b0108210307081509072a02150a050d060308090f010f0503071409090a0213090605030a06111605010f 71
    0x203900360b24410005003061084900031170030701054603158101d464000f29403042c002440230340780d11940c803000340070a01244001e4841c80c540180c0803e480b581481414040c61001740301c0c1d0f400405407800c00100800008040760031030020721101c2d1000d445000540040e600c1a5608880c543c1040a42c5280501d54001c0241c10b054032156a4940302d000c4048076000081ca11f40740101c2c0d55800311640c04414a4001541c002c498138080080707060740848410362048189803251006801e0800c541c50142209801035401081c540c51540440c10a50050007056014200700c3d0420340b8107040301003115410791085d0f5006200190801e09880d10303607040c041423002403d00400710105100b00a1181c04002d0900c070501103115a0008101c00300410307030b002d10302c000f40348210f186000c02d140c1010390031030300800b814a00610030220710150350340112820388002030010b00310300820341c40300f602608401c10030b042c2c2700200b0859100b241441e0005a00381038010b40003c030b2070207280e03c400c100f1070b6500d030040b141d4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 959331411 1250 959330161 959330171
    0x201090b13141c030504020321030702010f110a0c152a0203030f04330c08160804030e040204320d150504020114030106090e01241d0d1113 61
    0x1000c220f00c590910111268540004d00c1d941c0ea01c0440e00c1d092103003901031624419060300d04262502032000f580309502940c0280403095070140b0b03039001d07100d51405070112602c2c00d008200d0140d11038030126040c2409000c0d072a0844d035003040c0c07020445001300d1003400050b20700e03e10301d000f006103100c0d288a401d101d0f200951540c40c040603510024038001e44014040c0030303040b00d42020350101c0e45100da20703080110381d00c0c10040c2c203044400e4003d010084070100810007400008404400120f0008912215600e40300100d507580e036030848442d07001d0007003d03030712690a10011518454081000c00140316420210045405104103a0500a50346824078800c9010b00581d90015a0342d075411040c03c400c034480407401c0d440e0740c8016a10040110710710780340d4540220001800c81c2d408003904c004c0701c21154a000150741c0740d8800e000f60300e10b02d10043c540c40011311603110208d440741c0c40c017060302d6400c240c4804034005070800051103030101c5c04007030f200f407007415000c1d0740240f61000103680a00481c0100f001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 959332661 1250 959331411 959331433
    0x80c062101061e092103030b0301021c0f06050d0f05070308030115020115081e0c12070e01050603040c03032003030a0c1d0a0b0a170c031e09120a0201090b1314 70
    0x81351170000c65a9105010a00c0d490404040c0260008440c01600500030754407040c59011211426000700c01000072641010103240d41d61110340724a03802c0d40d4010b484150400000e807640f280311142200304a80c0c2c4d2160040003c00b01c0c0c06078001e9806401c00c04d07444800004004402425642c10750318842c0481a264410400c0010005100c3d5103030100300380f590070210921389094240176502d220190070581c0e007041300c10311a401003214002d484914011003800c0c4d88a00900c1340390b00084800a2007003514220500100c0e006014400d42c8101b80c0541a502d00142107003907056400643e0116101520340e25a0822140c0040102032504110201d032074030b8000000c0000c4103030070184200c104040740000c0d07441d0228419a401d8480c01103030117043c3e000d400c200b82800e205c1d6000300c403811028880352580c044000c4014070024090100300f0000c0203944c0703404900d54101e9000c2c52920f0190341d03890050700e00013101024024800d41e8251102c10f030303c5045041c03142503010820500398254001c458081c03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 959333911 1250 959332661 959332679
    0x120809060f073006080f0d050708030105060d0e0a03121a1e12030703020c0114130e130f0c150203070b0f0c0f070f020a0b04080c062101061e09 63
    0xc0405800c02c00d108503d110001501c0ca100c0700c00d40d60120100d030905401040d10b10b40050071414403048401154450445403804072418022180b00a020207001c100400a030716103d8041c103921016600700283c00191038440500d0848169000c8021400017440c07508050341c00c0c802c0d03000c02c5003441444020320300034200050000002500a1810840011142e0b02c551140806002607100000c103c0355100381038200a0756030840b4000c024001355540c0d1248a2144455040e1510740740c1c0e00b810491074908010003220300381001045841810340c48007046010401e4090581c00d074502548072000014140b0600e2512000300c403a850003951320411081c400502610b118952201401004012a4468560403540c52141c1d07200003541100100b0325509101c0c2c0f540210290500c00ca696511655980081c5030340c43c000c17445855150340000000024608041d0018606101a003803141c40001d107400300d51030b01510a0700f140c40059010603030b4415084036814803041c410980c1c01d100965916100c004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 959335161 1250 959333911 959333927
    0x501050a031509050f0303132001050d0902010201150f0807050102010e1009020f0a06030e0c030f070306050c04030b04080c101427060703020702130507020601060c0807120809060f07 80
    0x164125651403d10506005013840035482e4490389405a07a0f890800742d1041e080c600e08400140c80300022010134080348040c1c01c4640d040d024060b140c440c204502d0f0b040d05001000240b0007a4150754981e00810710304500840c0003401fa0140c02041c0400720300700108145001d4541e00180e040da0b1400b0000c400200f00012000d0001e40895004a1a10114030221351806001d03001c6a0b0031000a10002c20b101e81c05030828428004003808035604401050105561568044120a02600500020701c04104150000c80e80310914000081c0b81036580d40d82c000460004a5056501180224004120070800d101d02c02c0000c3c6000018403400d61340340d2180c1c0c02031801405a0350341260707105004108101d00000141700858440a964052416820140280d1300280d4124420200d50594041c03410b5144103c07800791150340d00a24460b070922070280d0b01041e0400007a20301d044280180000541000c4547c5031080075696104d100b8200000319a140c00000b800540c03007441102c00b0003629650120603 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 959336411 1250 959335161 959335193
    0x901030b04021203040308030f04030201050709150e041803090510030e030d0b04150303020c270a0207020a0f06031406060702030a03052101030807020307060203130312090e0a0b040501050a03 84
    0x43c291403d4007509028550300c280d80c0014800302c07011041016040011811070f04c0749009400030310459581c49822984076103135000d1800d401054005a0507114440c014201840c9000b030800600c83c01d001c141d20f401e00c0052441200060201d0105011905144500d605006c0e100c0c01c052044289200034151207015920013900d1071a43c42810346020364803a0030910104420b01c1074100c84640300e0030b00039150ba0000302d0450003000a015940e64001402250480d201a0301190540c1500c400d2030841c0658800c0006030f0317000c4000200800c14007000c9810800400b40741c0c8002030341507580828500d0030a402081144516014060940913031404650284c0d41d41e89490216610118600000c440303819a80c05080800680c000110400c050751000740fa4990084040380e018030380d950f6040340da0348101481d04040707078401074007040007500341d00560520200030b0030401111512030f110f41501c01c9080350100314003900c5003404000d44c10948500c50240205880c6090403900790340b28880e200d541020 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 959337661 1250 959336411 959336419
    0x1170d09060f090329060d0c151103130609060c030c0f0c120320030403020109210b0a0c030e1b06030903040803041d010501031b0819020f07110901030b0402 69
    0x71400311003600c00c80d03e8002941e40028019080345402d51100740c1803945601800840380340901007102440c000ea850650540e1011480000c60b080504902d8403d04581e40b1400740030034240c481500100910140c0012108604d0f1318459a02c1c00300014000d00e0541e10990a00400107244000300340d00010103800c098101d13201c08140d82591034280003002c1903902803400c982c018481041051350041049224982c0048004c0d100c00c003040346d20345c40788203a1200070302184264600b0481064051950415510480745802808003540c684112602e41183d001e02a00d50711075406150903050320544d00300c4610b82005100984500c86c3e1051000c4429078500e11070400400020400c5404000325405000c031007050b66252541c0300e2510010100e80c050780808860302d2000850254428826640300d0041b01044003000000c441054400c8040039000c60400340203240200362150b594001031112103c40740703100755181040c1c01c20500c03441030909070a100e0180b8200400200b00d81298598105030119 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 959338911 1250 959337661 959337677
    0x60f0402010c1101090b0c01020d06050a0f030b0a11121e010b0a0e060c01020c010212091209040e03090306010e0a0f02030c090f0d1b15050703080c1605120301170d0906 74
    0x80c01030305c05110b9540042030640002969181040b03040d0041c00300c080034018248103035504c4001b00003940b283c1d4000c0b038441e20503002c0c0810101d00d45405070754100618800c00030300d84800c10124030079540f015044103000c2d610b88041c8012103010b0404000b20041700c44840c1140c0d4100385220140b440354200010821107102c80842560781c414080301e41c040c4152000319038404034900d005020307400803103c2e000c4c06061000011520301c00440c040404e040303044000e9250503240802c00c07000306000706c240c591030710091050038007a032003c10406003c1e1a11100c4003920380741072903c81c2d0942c0c17080a0303071060050061040c071103405d09030000d80380c51040448580525260301270101e464200d00c1c80c00039218a00a156015060301c02c4001c9200b84d40c46485c2038641100b0000b0203032901c1c45090b0004002945040004810003005006440c2808a00d40310800d181030340e8582d185040c01c6032069110688000004006000120712004061034002000c0d0540810083d405031081225115041c00c0c85285 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 959340161 1250 959338911 959338943
    0x50a0602010e0d0e06040b12010504180f082a0601031407050f100c15020406030c0e0d1704051002011d0d090b071a090a021305061c0212120c060f0402010c 68
    0x1000c162006000c940f01f0103900c54070398060302c4d4a20700e401e00c43c03280224940142902000b403881582200301d90002500c20041e10541d98006c107070b5001600d130100012070340880080320328064480c01920501000101150b504505040d6110784180000c03840c1a400840e01b00720580702c8408034a202e4500b01da01d070a10713600369074056450000c104001030001003140e80403002008140d0207802038812944d0704001107540300e03e050b90300e4003c84440e40d40c44810003c3c030200090142071402132038036100c803041d810b1541c0c80c030106d405081030350502c00241c0d4480b08483c800e0006031504c0201140c41e45c001701600d821000000c0c10b800900e000704e000c2c80d42c00040040910172009442d2a10f08040f8540c0c609610301003084e40c0d122030500ca07080f40700310042c02218141301c0c21801160300640c0002d1695200c40f02c81929501c0301c0d500c840d012600504584100c2e000c0100910040c4e12181c1c001d10720700c4d51890084c40b02418403800034000c103400481c080c00d200150342c1c040c481c943c4255000f1094a45040f41c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 959341411 1250 959340161 959340169
    0x60324021903020915030f07120c0801090b030a080409060302130c0c02010f0c0f0c1806052206080601060302070b0a02120a0b0409020916030f050405151b1201050a0602010e0d0e 78
    0x1c200701c000178035600000340284d03504440090f80c80703484143d840c03c03106540b915808050790b44900c01403000600e410b006200c001043e600c031024102c0010103c03642d00402d40e030784881c29003056101c10708151391948100150b06100c0c080c403041c411494000c002c0c84005802c00303044800000310103410401e200341000001d900400136948856000961210030310441d18103034222402602070020050614017103141a04007074007402d070903580010600b400126034014142040c61b004808200c8540d10381c0e00019070480144007181c084c244640d400342c0c1d1130410742012a8810f001400045045104029145c6031148040c2e085400001541c00070440201603400140503014029010f90701c40a048184a1020b0328041984c8140c2076030344083c0032a581110141c01150822200600180c220b0030411385e4071805035000640c040c480401d0783c8408004088600304070782044581c201c0482080005000ca85044103110b8000c00e02840280100b404c442d024a46418400c41c21030b0601c1204001c10090350742d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 959342661 1250 959341411 959341429
    0x1a0408070c090203041a060a0e0603070918020a084209060703050109090f0602031b0c03090103110403031b02030f24090a030f120207060603240219030209 68
    0x1e002018186110703150420700c0000c0d40f058504448aa40c1c5008980801510500407403103030700000c1050070706500e001c0e20100b1021001340180d1b814000d6240116180c0820b20420360351040a0030414983e002c90310600940c0c111540001c500c03070303219121144a00d0340c200c44045a28200f00704a4103460115499406540f041d031107900043c0b151072007081a012000101c55100d10041e41d0280b241d0799030303030403c3c10455111803409400040030001c071001068207a0003d50304141800c0e04003640749901c00c6c03c031800b60030040d00c81c6001e4100041503001982e040c0201c0d5081149404172518051450743d005d0304a00c0600c4940071241000c0e40c0031070941d90305014103511904410140c0f411043d58403001d0000718000301050118926142c04101551000540001e8065150f15580040c0000000c181c64441101c50115200b9408100b6600003c20038011080194803400c0301110201001c0c687e020000d801b410b01000c040d1046c0000903e00002e03a00f070700910300c5035050042e62401a00040344450b1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 959343911 1250 959342661 959342663
    0x51e070e04050c090a020306030a060b0d020d0b04060c080f01060c110604060504080721030c050a05120703020606010309050c01030c02030d0905030a08150306041e0507030b070e0d1a040807 83
    0x340400401003801004240b00c90300580c01c0303510303c0f07031699002106001c1b800b0954400b80c060f807000c6103800000f0303080e038840700100000400805074036805a0000740b4003503032184211503240c08803040c0410440c3c107004400404203d4140b00005140240e1110382100e0144221030401c80905000d0061200690000d21560005407000c0e0703035241c860300045d00316801445821814418030b00c000a5810043d8100703445002d41d410321044211203030300e04440000078101c050750305025180d00400050300410201442c540c84c01d882039168081410041d080c103400911880c1070508144950000501c003051050031230100342400140c840400104900d18002d0814019002c2d2400c4040750601c180003020309030400044e90f4140301640ca49100ea00303040000103081e0340550021000c20001060040c0402030341c48079203c01450003034640c03141803130b1103144d92040c2c0340074101d0f4060145481d40708030600c82500059a19102c003045540d50302c1c4406103d43d00400c202518500810300700417206003110074031 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 959345161 1250 959343911 959343929
    0x82202012105010902130504021204020f120109063204140c0312090f06040f03060b060904020a0e04051605122a030a0f050f04111909050612060103051e07 68
    0x10360310340312010001c6d44440044804000444000038081c03401e4000c8031000c0d0301440c002c040707030380310f56003481440d500e038006040e0f00000c07071501c0c0124800c0911803262428041d0001182e0107040300492003c881107001e1905110701d000760301d460310786400100c29420075403005150300d600f08125005418007554001495050084603c1c0c6030303101c0400c01c0501a2000101e80e4440d4007141c1ca4100b1030f46115510a074a00b8100e10341d01000820303a2036021828181c0045c00040c604154180090102d0380541a0440407665107100403020342070603c602c541c022903400d5000501e80b070101001e40140541002504144a6117000804d0104c240d50540354500c0c00d4031407100c00030122800c0c580704c0d0304200c0f100c0c850940382080c09400700585004a80c0249040005150681c4403501c03009200481e06132919000481001204c8802c43c0c00035211009000300c1c200018130341000010002142e0880c41c0204081d0700c80350041c0082000800c030742c07622504841c00c01001c440340140c1141041a107902540385 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 959346411 1250 959345161 959345171
    0x405130203070c20030d210c14070203160306090606050402090f0d1109040302060f07020601121e080d0605130b09012106090b07032003011505070b160822020121 71
    0x1c00d608440280c10089007c20505000c0c0b88200005040320b880b55038580009401044003139000e8410703002458024005011b5070040c0449501420008040da40115100c9584240003020f05c900d5119000203048102c40a5251002c958000f07110715001e40102d9129070004844036041003003c004030102c018002d000b8880628040c20044c1d100d000440d1524100350050001806a51000c103102381607423210500c10140b80056295041046145412264885605126040403e84040140000074054040860201c1c1043d0a01c05d4080c03000c5111040e4608101c0004d88640d50584810f041d9042e4404403082c810001403d4501c01c054084080c04052404501c0d40600c5100d001365440340e14940c400313120300502c2030915655072008810039865501c00780018002040c10744101c0a00200d2468410705146040d02d0f50301c803041d01515205c2420300b4110b40c1d68510742d00070583d19400f600010b03803010382d551014041040000840c000a040055850004080d0301452003c0542c041d107101c41004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 959347661 1250 959346411 959346433
    0x7060203250302030a0c061514030c0303030105150a0212030c0a08010e0f0412230d0b060c0a02090402011b0303050711030426190303020405130203070c2003 69
    0x5165403000001c210040c6401015068009100d0781d0000c0307542c2e2560085142019001c3c04540341d4091450032903505c0e4490b02d05001c0759200e082c003c000341c054000482c1c02c2e0052942014940703035511031201c0c007941080c001004180d1f50000b245500d6030881c1c0300300303540e8241024207d0919100301b442c010481c030084140141d078601c1c1d80141c1080842520703000e07542d07606e582000d0400e5404544824004041400140000d2261000070100151318201240e01402840d5250418440801e100c2007104000c02c0c401d8046c016400b4501c0607240030f4031418035100400341c103541c4411290b0000307400b400b850000700e82103902c10f21346620411840915514403401620300140501300030f850100c0020b543c00c120b809030b008040304031800c50b2150382044d40c02ea20b40a078a06200240d5400020182c020034a11002c407006d03040305000e07010720964005035600c2c180410042e00c1c011426006160714418002c02507208c0e0001da20414464012071001c03410f5601076039800716042c0c0036130324a0700741c0070359000c40c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 959348911 1250 959347661 959347663
    0x6040908090310022505060601030f1b0c050c04061203031524080a2705070b030c130f062a080a09090e010507140a11010212060f030d02061b0705070602 67
    0x10031404c40020414008050009090444061202018000d0340109011500c40c0d0f000e45e00a04c43d0bc64103400c0800c4038020040002241201e48080307901080c10118007404200d41404500e9060404072010030040e410441c20081d180d11301d5100805040e56512800f850400c003120070401020280d191407041c0403181007000400244480c600c0100d501c10b40844c3c01458940103e0520a422926429126091105100d100311890740140d80a020307440010442d002e006009602c40c1c070341da0706066540c4145510150b614500c6511540e1906c0c03c18409000c000d0f40315805181c032285100129010b03a189040303404854007540c43c018100000020b0785d03003145410020410031644c24400070000b1a404a02980c00d849003181d4580001e011001113251001c0b100014003004501c1d80b8101030300c0495078103a1400c80e400080c1030091001017808100040c1780c01d038058150584160003a1910380141c0794041d5440c5000303002041600d0031810110a94918001910f500f1a000130480f00001d50350100030b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 959350161 1250 959348911 959348917
    0xc090a0903030b010e330a0908190c0311062703010605040e0c091801060608040b011d070809030d02030412080c030f040206030a0b0d24060602060604090809031002 72
    0x200d0100e81411903000c0f044d80070f00084440c0101c00741410010b0031b102c0b940d048803c0146c0c007060b0940010748a00485070300054014003440300d002d445039500d0342e00b007200c41d9140a04524000240401c40041180004c811510708000c03643e00007006560f124030800004c049000e014403100c039207807401c90711642c402c9204440c20040758040e8020880c0320740b18021320050342c8850f2002941c60340038240c0c60f8180d04000c080030342d01c85418154070655402c01c0484038259440e50380a180000d141100307101c1400818030840d130040c02e414040c008420f41d0000c00c07800001d4014041410300c0251400144952018000c54240440d03d18045540c0c0c034103843c0c00e00d104802c2c0c0c2d9151002907030180018200c0c4000d1800c50b03015032501207400f42999210350070040580c0c4001c214000c180c2c0c860010498a40b50040311f9282584200e40701c003100349c0c800840c0c1c400301e0440d50b90f00c1c0816041c000c04100660b000700f65150000b0b0140c4001c24081c0389800d00310030612070181e040e03815106048480264418603405 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 959351411 1250 959350161 959350163
    0x170312060406050603090a1b0803123d050d1121010e0601080c010207061205040201180801051608060a030807050319080915061003090c05090a0914010e060601110c090a09 75
    0x1700c14030a0141565508e5049090140d0ba00c294801c2095000140e81851015440350307250301068200b1920542d40c038810b0201441101481182d08045200104250452400362105640740c3c901d004d519258682e00f124113821072030160044501c8a00c0c3d04d242c0c0009a02011140741c003e1280c034848140c880da0340c0c8024425541540150840c40e1060742c070101d50310040302c16a50352020910700d0840c09400400c005802241802482c00003400290f130004500c500074a4140000980742ca88607407904100e065035400c40080100c05010000e80d0f9807411104402c0d00d41010b1030030313180e510300d10741503285104202c2020080480d800c0241c54050744014100d22900f000025208140e041c4402c084c00b103d8244d9180303500010014000f03050b6031090340a0380e0f0f0303d0300549a08031040e03500c2c004115034200c02d590000c40151102c00d240c050120030040102840032640c001c000408181401d07075194200680001d040010f0303400d0010b5580000c021285c040c0700c0091001025050011544008012447c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 959352517 1106 959351411 959351423
    0x40f03050a02032208010c08010302061c02120a2408060c09040f0501030b181c140408010c0903062426030301030b10170312060406050603090a 63
    0x20302001030000138044401054100039156003552010407000c428007007203c00410050316203100300d800c480802c24210044a03110702e2030501034440d20702d4130700c400524001406000e00c070355405601d620319030552402c40c5588450503c40924542d00c142e00242e04250300244440e540d420082c100c040000f40005039141c4a40c1c0b002c41110400e800c1525821442400c00c03184030324500b8001104c907040e5000700151200080000c800c9010740c401c1100300003050b0003e40802d60b5200030f45014110000090142203038003040200070030300d41c2c8015603560303060501c07980011402400765075024166102c1c0c20030346800c03d000003098200c4220000b40143e411001030440740c2e01403001d03601940c46824030075201e091026034080070000320b800165002220402190300108000308480d4154071300c1c08200d20a6031604001402854180d0105030420b0000017085035540c408110035082d640300320 = true := by decide +kernel

theorem cover : BRFrame.Cov 959172661 959352517 := by
  have h0 := BRFrame.cov_init 959172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 959172661 ≤ n) (h2 : n < 959352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
