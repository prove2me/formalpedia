-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4160
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:44:48.042032+00:00
-- url     : https://prove2.me/submissions/949adbc6-1ed0-446e-9cfe-0e44093bfb36

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 748021582 ≤ n < 748201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 748022832 1250 748021582 748021613
    0x3010b0309191a090c06041a19080f0c19110a050706030204140307080a08130e0703020c06070c05120a02030f0304060c1403090a030c030c020a03030302180d020607 72
    0xe020b401601400e401010040c5090a806104041e0010000c02e8420f54241c030050501c01c1c076508a28145155602c0740ca04440894441d041c0b8288841d44542600055006032089040300c0014881f00c14210341d808082540110544912410661104000324145108880148048409030700c100403145014168619190f010302040d1881d000182c3e950b14108095034100740b01290740460700f4444105108003a0740070010940007000ca103403d05602d01d9641e080510000c041200005440b0172072501c001007580140000452400d603400c104402801035040b544100c19144184c40008140d14800c4122002c07251300000941842030342e14a0a4446d603201c9500d544c00d5200400038800e8103080c450085110701d0207400000b0f03040d00100001400f10800d001041940d1070300f8414030841003408106040000d6260a103560010050b107811f44540c50380c4240654856000342d4000305140e010740041240c034140343e4441092020b64010842c0a00030058040e40100051040c08006154082c848450 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 748024082 1250 748022832 748022851
    0x309100e0d050607050c150c2212050c120613060c1107031119061e030f020c01090611040303140d0213080d030b04050c032a07060e07050307030803010b03 68
    0xc080c0151291071400b00284d07000e5001900c002105c484100c028802042008183e0400d22128109440c1201a500038040c8a08024580000140b070742c01c41092524020024402c40441c40501400d007142c480c2d01074051280540c0d00c161680f0760726035001c5211446a174400040003540a95a242e000052003844545400d1001405007484061000c10552004620031280107403140c0c8140207210b1080313164071075025810000001403064a400c0307007403030110f90a80d09040061a90786030703084010b0544528202911480099103542580041d0000300d45640240c909000c01c40b01d00070364040314402c074071020780010090b00754100200c403810700600c2000070f07070300026088c020080240104040c02d580400483ea0040825640240c3c02d8007030610740000440d010010717403a080d101c01000f80b00040c09130009410071001d0020f500d031040c0b200c01c003055034803e41e0764072000c003803410314014a88c1030890b004900c184c036400203d51800245489c140c0307074401e911500b56460041d10661a0b000900041d1a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 748025332 1250 748024082 748024099
    0x30c020102070512030324130b04020d021602030d02370b07050717090f0f01120612111009031709060f0d0c02010b0f0d020121020a08090309100e 64
    0x2000e6584004c42108014031201940d501e080135038a502e01c1c807420400390208269010000c9055a940c006180510143c5210200d0000704040005000b0721442c25590020342c0b0116211031600700000102800c3c030f00c2642210500c48000c141030f86c0d01c0d080300303000b03104190003c04600031000304180955060480000c00005002595481c0900311000300d440100141000c2100742c28000c0a00c1c0f03462940f4100b14201e0310301b500000104808440f09045207000b8001001801c0311a40f1810740c0000c0500d0119041022a03120780a41c0d01d464030120046d02c0c103a80c0c103440c840040c6042c44484a82c00e00da40c039040c1d0050324507503600030f11400071a411416403000b480050b4443e2102c0c00200380b51803003030500d281d4402d180c80e0034a0803a40c0e4254010110b81c50100e0190007516421802c40705030038116584403031030000c0c1c070040ba100449865264210b103541009030300c01c040c85401402119010380c550b03403103507610700c141709690b4041c07070195541c404d0740902d01d43c414070300442101040c010050590300 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 748026582 1250 748025332 748025339
    0xc220905030c0a030e011e0203070b04050c09180c0402040e01140a17030a091202090a0e030f0c03070b130816021807020a121d040b06070506010f05130204080a030c02010207 76
    0x2410204400710980216a0041c18040650b0780075855144a15000315813540700460580009e5076401100703001402102c2c443c000c0380501c4000c22200c94045402402101c503454226209200030010640401c0e16104250510500740f0303007170096a00703481d48020f0810712030780303000d90341c5611300e070f02c1589683c000c41ca0080100306c0d44c01000b540c000c884101401103940b04800c02000b0508181a445603100000c80c105480060307452000403a0024010200421075004440030b490a510030f2050320407270100001201c40c80c0c07090200244c000c379409861311000503510a03200b00c0907001d903410300805a003c1000210142e80050741c00a20741c81c000f400b5640c400810241101c0d51001c04c0e10302e400940c4c8110b846004000b10490004804040743c507000182c00740203030500c07001c1d05000c02e10620441e11030b1201c50700c584503182960381c0560800308031070155a498426546c900c01c0c5006190040d240494420003010060088900300d88580c001802114260f80341110300d500d032000120b0440c012141c000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 748027832 1250 748026582 748026607
    0x62d08060708041104050402030a0b0402040605030f070305011a0112050a180501050a0516360b03070306140f010f09050a170f0c010f05070515070509030c22090503 72
    0x51003040552039205543c2803a00701010600a00099144521b00b00820800181c5000c2000096a85d001c070344500e054880d03100013400f415054102c0d64143c482d113043d0644a510000d019800c5a0044008011b0b070214102041345007840450400d003c180c0d100c0c8403c0c8420351580c071803076002c03510480c0000c2400c114500540d01054802007518180e44840901007511134500c00c0981119200c40014104078905001500c244440f1b02c086a619061464110a6030003981940c212006d015014000c55511080c60301000c0d002510040300103840d004d000b003204640c00c045ca42c0000c200800b8201d1410f805070044450f2003400701d20101b00251284002410380396101c200c0054440c0d403c0081c8410300030314040f85001c48012842d85507510042c64001c5598005061082000080c500540d0746d050600b0068941000f00c40085000660001044145a4400c01401c406001241560304074490030301004805103418040240011080d21070401c0720102d80d0003519001e105806403820b100c0b4175101e1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 748029082 1250 748027832 748027843
    0x708040f030e060f093307110904030f1e05040323010911040c210207080712090611031224190e0f01122405090703030909062d08 57
    0x1244d4200c8020551820500d095540000c1020350b04070450280750500d18800d1100d5005a151100030303000068000a011201c5a20510070718080c0c101c01003400c0514000300a4101d04903402c0004840d00c50590b44030a42c2d030856540c400c90307982c9150a0600356218140c0d000780c85980e40d0700300e0b4242d007000c0580942c02c0c011312a01500548440007940c102a00f0700007560249907400041241c10105035154840c40c422002c0c29051b034007001030b2107400e2071802607902d105108000c2d004205504041104d1a4844100020f50b58255600703820f002c0c0c25800d06035603024954600000d080035030002030b2407004c0c0400301d050003000c1600904040402ca008110840d14503110489100e500e074505000c483c0342074820b241c028840e10501e01a81d854498811414155440020120b1010840310700000a03a48075106441c202060100501d091550115556000c903110480c0410641d000015008145200b0030007107070001c814890350074464034404003002c001c89440c18029500c000c0042100d640c02c121 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 748030332 1250 748029082 748029097
    0x1509060c022707090e0a1509020f041e060e040c0203192705041b0203040308160606090b12160b03060a080105070908330405010e0303190b090708040f030e06 69
    0x213035110307201c2c1410055429610001c03d9403042c641026074803a0060f03040324016049507080000142c880c142e110010041e44926401841d03a020006082e04203402034603107641c120356243d1206da1100d049802880300f84c030314246800780942c200b80603400180d040e42c04000c03030366441e525140c041c0d0804101e0540b07102c041501c1c0044104600b90303040c00642020311400b813040130001910000204081c000960328421800001c107041c0004c03a0200c5512035896140d21480e51001e41445000e460380281c1000704011201c4034402d0f11518458001c1c1900841c03149180e46003404014441410b00503402d402e688094440ca400501000c80011110000c1c030400f80200c404d40d0b599200f1614101c0c20a141444c140c00c0c2e00d500080e01c00441e521080c0076050b0740d80c0c002c1c6207003e9154665490070000e005000000344040940800420018506503030b040014500700c03110010801005881c0a1048428044a68802144142c0c1c0424045010070768800c030098800e290100d4084040030214030309070008203 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 748031582 1250 748030332 748030337
    0xd0f02180a020a0908122d0706020913060302030714130e0a0c08070b12130203070806010f0806060a06030b060408070303052a0d270f1509060c022707 66
    0x7103400c40d41d0313889130700c02005203046001403d072001240400300c120301c24000c51001d103002c00c40d601d14a92000103002070024011050094480c0c3c998180803000c0d5204003074552040030302c2090350812020503c00d8006480c0c01030018480d4904184144480140311494103034400c0b400c51042e6109050360003084840317400140588400f0350f451130403aa0300d18481d00652440d40241e9024007400d101c0c101034039120700100c0d040c1c491b1500e40c140c0c201e109580001e0301075094007506034049200c40e80014002d0407520901e40c0d140310950358245594403550b05803446580041d4222080082510a400486d209000103080c58030309503482d401d0a1420006500440104101244044030404441505d0201c00000341d01002d582c49005483c031b84603554040e180d000e00003030740305210000c2030580044407903038060721451b103985840e221401c03030b8007485125200001c0117401c54616042d00c00c0014a049070b000c1c2d21850780303250155003004044085500c24443c1080c501105a0403490081a4580290b580740c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 748032832 1250 748031582 748031587
    0x31e0e0a170c1005180f06190b010203091e030f0114070306030f2a0e060a0b0703021005040f0c03030c021806010c020d080c0106031a060d020d0f02180a02 68
    0x140303040c0d100515401440407081c40d003809504145200402c160a1040c0b03100e0300054581d84032411a41c1000201403d540c041c03107690384100c4400c1000440070f00600c000200c008040300420100d9003940d05100c91075005070018041c804107070500030649600c43c2c543c001502204c41441c4007081c540440310381d0381030035603458010700c0103019003142e1015001051441d00344000b60858035152240c01106400912141d94807619101e6960b08000806c00f01d4440030403071340a669107184910324003205a8520b480b6220680300000c00101c6001101d02d840d5150f00500441400b5030140070081170700400544051f070141e040307403001448004080703000c0c611940b03816002d0405401401207041b0780032000c203d410704410034020181e07040983c14280940c1110900e4285480c3e02d0600658010703240c41e248290700b041404010000c0a25444110f034074010b103400490758070304003082400c2c24030240c00794100041500071030104a00b004800000da0001c1c00c1c01c0407038100c10100449685040314140c080c140c0c003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 748034082 1250 748032832 748032853
    0x1e0a080d02040b0f12100e1602011b0c03080603060103031e050d230a05010602100b0d05060115230a0509030114040c1502070803090105030702070e01030506070e0405070c03031e0e 79
    0xc0480d5406c0301d080c581140500d42041c2d0448030b1140f024100c840503140d00e030424481540300350003003402c1c0700796030883e08150340d0030010103080c2d410104c070110040784004000440500300010302d5030407a41c040d43d41d040c01e40c0e00c031103640d0400f131059a829000c201c400c0040d0601000703640075100160b454059103440b4092643c448007014500588080c0000342048010820240d000843c509545e546040000b182103170301d400100f801c0c400c083c00406038025030740001a0f074600c1581c0d01081c00314a0b258100c0d140720071a4084d10b400c55141c141c4403190742c1032240a441c0c5125002404121030041c0c00011188101ca22426030743c0e008540443d6041040b2409021110305203c07440c111070002d00040c5602c03070619103510340701c0c02100f0060b41007007408800039110b1b9200b08140c1c801080c1e03002d5500f11030350f100c1c241035840c0c0724215060004540c0002c038889281c201885000d2060743c0b0b503a5001d840011580e0102c020302046d4010300c225503c100c201404c82030701d61058804a4070868024131200307070b0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 748035332 1250 748034082 748034107
    0x8030c070e06010c02011e09031a07020c01020303010e0106180308032715130807080a030c081e0a090501320603120d0e070308030708091e0a080d02040b0f 68
    0xc1c010040c50400c6490a21000180d80202c5101d07501480705090354807081000c103044034402410341c00500b103000008070402081303480040c0c4601800f810350070fa502850316040107981d24442841144034410010340100042446400031a45043d840e00007807001959030b85402510740c206640410030050491180701013101c940044441c07000d040800340c103681c0c8840c01801403406c0c00134124010380c010501300904000042003103a03c3c036984a007030f494440007801c80c002c000b032038074a41c044e010540c01d10205101040c902c162028103581c580a040300b41d0350b070340a69000b41014500c100e80782e6484080c51307481c4a25290f103441d0810740740c0b89929000d244a076011488414003500040c002c0d08a18143c0c40c54004620071101403201440c2c5c0030403034064100381d1915120283e40050401400401400031141d408091180103240420403100d14409a2901e840007920480740304502e640449036240004900301d01501031440070000c014100f0f69a001c1c0300c40380380e1081407810032184002449800842 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 748036582 1250 748035332 748035359
    0xa0506010512280606090e040203120a17010506070b13060605030d121d0d200304032012061f0e0c040611030304030e01122d0c0201020313030c050708030c07 69
    0x7043ea03c00d1000515250010340114114003820403401402d40001d001c0d510200210104a0303540a00180e07030740881800140040c499021415216180c040001000d140c8a801d450220b41c0014445250340c030355140c401903e070307120b01e01259500e4407038a0000f25507406100d2030040f14026212044607883d421084411100b481c07160401720849a40da4101807031001442e000502224101921100c40003002a103c0c41c0341c456080c60725102c0080c0c0402084410784072000500c0808220307142210004080041072400c0020500407948a0381c001800b4103481c00c1800d005201c00360703a51156a4580a60340d1103604203c4480d40180c1c0e000504110392682b00c9071080d081107444c4099030a50406940003081c000e6081c0d501c43c1000700004140c1c03a0581e5a5000c404241400f01e00004c001d00703842c0d17546e052844090f0b49210402c0c500703150300350750740d0040c022203101e45400816414038141036501035810881030001a00c192084281c0419459000c2004000e82810700009090381ea25103515540940e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 748037832 1250 748036582 748036651
    0xa150e061005183309040606020f0a060f021312031b030804170903010914120717160f06050a0c0e090a1a0d0f0605130b0a0506010512 59
    0x1102c00c100d00c0e1407801c41000707003d0440b03c0c2203c0382008007aa15810026255859100500c04400a0f600440c0d00c550790009018030042501c081c00303e0359841e04180c4c0c840c0344d2100d182c0c5180d0015080f5500041040d4440d0400d0142c4220060401c0030600d400c0340151000e400003102c840d040c003d40300a261300000560240950007262807051650796030000c08000d0054802444040c90802e281041d800002c184e0300e552001070000c1052304298144049113861401442c4058001c0a00000f40103a020044504280e005807441000c4000300c5c030441410751000402b5520000108400d07400a64130480c40424a40a401e01040500380046c0c0e410442e00c8014540c010f00180c00f1000c1126203c02c000c0b294850000580000c07069484140c08500000e00303050760303502003600c40d00031701007018141e6468110390180108100303607a11b0302c10041d0101c4140101070020341e001800200100e40d40d41105074071031018075000b03080040080d117805130440b041d00c041111440f00c1124480c60740400070058200b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 748039082 1250 748037832 748037837
    0x31c182303091f030204090e030304021305130807080d05071223060d1406070203130902070c05240f04031a0f07110312100806131a0a150e0610 63
    0x2000d1110380028400e5001c0f4000441082c0c68070302485038103010350b041c2c82c000c05c5510300c144103c0e60132a0050b6225417084804920070156180c080c0c4141d0814801d082c81146194413600b641c0b2496201d820041c0c00c100022100800300b000f00300002c007014012540120303400d807100c121103c20f9407003d1065845051000e1480d0400c01c6106185001d0f40c0441078001d5019200304040a01d00c0c14070030300921124007058614403d08040c0301c03800c0d03400802420b2904241c110701400036101c0b51101c042c0e1292100240030305c0b080800078002440c0c01411800c01c1000c038170081c43c00740404801c50119801002120700c44540118007082404000c0208800130090000101038601c3c0841048814600151114041000c01c2e90310302800311040003190342070314401110f5411403610005400c1002c1c4c3d14060b4a0a13400f902c0007003039050072040d1018080640c404410f0b084005048a4048141c00040148441c1d0f03440c3c05448004000300c4007070700041d1980c0300000d510b5282880c00d01001e4400d21103803004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 748040332 1250 748039082 748039087
    0x6050a12110f0d0b01032009060307090507020f0106090f2f1b031b010c1722080c060619050303040b03040602090a0909030f11031c182303 61
    0x5403041507200000004a07007894079845a1070210349524072000c0010078a6100000110902050380030508010600c0d00003407002540510600003080d50039a00d0f03940541c0000414800340c001ca812142e4402598812100528803200340b6500b900d01707581c01885c11550700e5034108044c1209019100c240c141c003d0100c0c060107103c902060308050b83c140c00d1003a9260109052070100062100301c6480d0711a0340440382c43e208a010900245200781c1c8018810b0740c45c103400c100b03e06015400030780c8400019a020b20180d0344840e442c040e101149084050541c07a03801c45a400a00c407080601000008600180700c5883c00342c080c0b21030303003041c0c83c5900c9050100440c1003240d50340c0001264161500e4541d081e4880d00c403850410041d016030030b03486500064626000c071ba02c54441e448580c41e14002c1d80e8200c00c056051070140c42c01038603a02092150f41041001d103006102154041c84610b6a4036000a9502424600350310054046c1c03000310745c0110340005503c10000c41100d40400440351901843c03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 748041582 1250 748040332 748040369
    0x20f030a030908100e030d0c030f020d06090506030606150a02070b0a0c0303050906090d0c0809090108030315040c0f08070207030212010c0810120209100806070504060f090303091208071506050a 85
    0x240c0d03038010301480d87c400c2911591a1030700544203410418045200d8081075440b03145580c007070000386c0007501a5114062030034000030514540041c03030711702991028005643c003510240d95050a94001c0b0300202c15885920300000d59041f52100801d40b0140740d40c1c400124003020300d0000d00383c40000d4103490b07041e4040000e2002c4c005001c1590207803a10b00c0d08107510400001e140c130342030700d018000c040c651024013a800082d40c1400480118803484003040c142c4030009540c410001121a00d0103a42c00083c40059140be4090140a00303e03005043c5004580c0348a80d0307a070008450f216104001c4400340d4581046140007900301c0303259508001c454400d490340a051a2840540c005042d0019104004038400b050600901c00d00600150111005841d4a46001f14010f4001ea10a10502000820b9140000310382e80c820160502501c2c5e040e599905160300c2d00030301d0506500c5010040d1614482000f103440080c43c4640c04485041c081140402c00074a01000c000410b68107921507481031300c2000d05034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 748042832 1250 748041582 748041611
    0x90305040504020c010f180213060b0904050a0e100209010314040203121b1501140607050601090c030b12070e0f010812030a0902060d06090b0315010e04020f030a03090810 75
    0x3202920340580b40162980c182080340b90251208540d000d00c090b291481034690f40d2410000500098000d81e8807505000102007800c08842e041d20501d00200c0062000803011b03d802d4001c55004000200702084511104080c582008900c4184801e201d600050342e228035601400341c0d0b044105101e0501c0100e20701500886d4846000c2805441c5030400000c2511a40240c08400040da0404004541541c0764020070801070303030000e02900e02c01d40041a1b280d555494030a007122592544040a400c0a03460922100054100300c1446401d06031551201d00b0740b5161602c00019001d092030040040900d030042c15080440090103803d8624072400052015000000d002c0507001c0c01e40811554035913919800d04000e10061900079484000080d054034014050340029059400592003000200302d00c208150b40c40da10f022008015680c05001001000034460540740e001d4000b42103280c0e0440c030316002904090300c80a049000c20b1424009200e1200104640d900c0d1150b480c004002210511820 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 748044082 1250 748042832 748042837
    0xc0c020306130c030c030302030a08010b040506070611041701051909050d080c16030206160e0f0f040f0204180e160e07180b0d0b060304030503010e0c0705190510090305 74
    0x11007602d85945500c0410040e81c4608a0010b50b08242ca0305c2025403a03290007502c0c0e621007050003002030a6000041500e515a0080714100c942c02007070710b03180610340d0342c6074000f0304201340781044600c0007444000344003009034001c02d51001d07482d400040c841c900384030017500790b05142c0c60201c002c0f4644811080050f000160381782c2030841505000c0d41c0b96803800101c80e41c83c410b0320f801c00d420090340021401099000591503020b0b801d4542e030803104101c0150704407120300c005e2000320f5118072020700468a0742840d40726508140006030020481d032103036107521410f9a00079488282a21208441d107034403880c16200c0c040300f403808200a0098680070352065550301104e4000c1f4803d07408640081400217002d200e060340b02c8200c02071601c81007503403409448902d81104031002c0c451820304c840307003c103486e005040743c0c400c540c0341d00c869096908110b11800e03003860007014120a908208104404140100554116a40c2d00081d04401c49502c2c039026042c0304d620f2002062041c00c1c0500350b070010b41c11009 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 748045332 1250 748044082 748044091
    0x519030314120c030a0225050c0d0b0114030703060c180b090d0b251e05070c0e06060f1306110105040b1803040911030a05090601080c19031a0a0c0c020306 68
    0xe8152245c4494813444028804e1505404440a0b030500e82040810208603654000e4051010b450500c8107120502c00c483c00340308002040d01140800500040e49411458442c20f000502150345503510707035a0300400c8500284480f80840c1340c603104003120f500f0341d59070b035005048100002414400a1b40200d24407220322480100803502800001d1820320405041031540024492101021400d0701c0c0090318442d280c0c1e0b0440c0514650701051087c00d80140116440c8690000d40704100030f16104145241080107007920341d1190b0104050044590004040e1540c02d403641c04040603a4a40300d0040c02c3c8590011520f141ca90402c0c00300400700e00854041d0768001c142d600f03042041c1081400840c114800d40c1c204009803454840403c901d072190401444c0b184403c100d0030001e41d1204180c007907990509101d231603415803020042641c01d0400c441e00810903000113044003140c80d22643d664240c90021030602c0000480241000000c071802e01031100480c8490611501400c403139008607031610030050 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 748046582 1250 748045332 748045351
    0x1170706093002040510050406120308131a040b0603010f0b030309040b060915030a05060901080d11030d0c020a0c0611070608040203150f160206010f1707051903031412 74
    0x380c1d48030440020318040b02c58568001c00400c0180380040c0c0256007520a802114011490071801260100304c3d034540350031080d0540c80d9007416546415401026000080040326000300c40d00054032400c018294481c01144109601c0e0654a001003d150031101050700b106105400d003034150700300e43c03004012203008280c29076010a400c0d0703640300812000c0c0b1a076040140c000c4070009070408004103c1020f107014030700c1440288415100c0c84204102500e00b070241d016285c20044903809258010505501010481c005482c246114008880d040300c94409090015030400010f50f42040080c1490f2000f400b035504050001003151800c41e03a0712040703805020107101c4110f0100d81556020810512800070042900e40c0d585003041c0650f005646c20348030449181168825102024004a40c0c5416107088401d0001002d10b00484220040c0240705008414000c809020840d0344420410a0f480d4085140e080b28143c95880e00130845a00320381200d50402d42804489054901014600c2d000600d21 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 748047832 1250 748046582 748046639
    0x30406080f1603020a1e09030221031215100806010219030e01052214091510050a180b03090d090b0301030602070804080a0b1801020a0824090117070609 67
    0x6a040c0d42e07105403000b520700b1510440500404251f0f10004e1762059910995541e00c5040f02d02440342c2ea02e11168030300d80e90360381045c0188908840b8035001c0e15809045641500c01410781c074404071b044c0d105004105d800080d245030401549580412a5149201c0080210741e0b0716038040d00c0003840a60b074030b940b4604220002444440300c0f1026480440d00149078010224400d559841075440b0b650229045805034a0580c0003580c4020040d048901099002c4c184945802102c4d6003114158050f108a2080c46115175a05101d26111500440070300620198260b4038245401441c0c039040c8844500c504016101c0d1061145079025002d49045950003100075898600501e084021801140c001c0c21161081e0324580b02804040607c080c000c3c0820840003809200200c221401d1f481b901f419000401c00703000104401c4068111251074500780e8036039400f41c0000390400600441c4080c0c0c44540140004200200a05414030069006061501744004814580788808150524004d0114808640c5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 748049082 1250 748047832 748047847
    0xd02030d030c111b030c0102031c02131d010305010b040221130b10030c050108090c12100606051321060c120c030906051b0d020304050a060e030406080f160302 70
    0x1400d110f40314407512000340c9400e41c6003003ca404000001210580c46840303440d00d41d031802d50020080b62251114484500302c5062400e410b030000e50b011100000e61454410300c00111001c000c1582d039140c6012042d204102e50ad107060180c00c0d1102e02c0602c500c07461041114484110303950302c4c004215130356543c03042c80c01c8c2c0d03035200440c1d064281030001074085d403c00000c1200d250300b4014281c003540e20070f0b802030785519201c1004460315041150490500d42c40010032001500e0000404c01c88520b9000172642d0480106c1200020786060b60b105401003200030610229103920304000001501c44402503c0308980340341f4014032803802108018041e81d0b550b95805c01000c1c41007101602004044000344441c2c0b032000c00050051031101e000703440091510f00440d442054640312550f0441c86811284c0c204104c43e00340c54001e50010300119260b1080f1542200000e00d140a141500c4007500003441d2918540040909098001040c00c1540c0140d001000749100d508840008450028600180c40741d01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 748050332 1250 748049082 748049087
    0xa2718021e060406081806010b120612010c052104030806090a090204090b0403020d09060e19050d1a07030b100f020a0c180b030109020d0308090a15050a0b0d02030d030c 74
    0x188074419000800002c002c0b46031500144458003c0b12840780b00c010300c0803820b11807900c841c000e0156000c0c2001c02c0010b082c000140401160704480c00402000b9202000c1c0c83c0d40e402c4641403280540411004655080d800740411201d0440041c40d107003820091610f40d4004000c0400108014840c0086201081012034107501610700716902a10400c0352035000d0030420380141089074102c00500c50041c415162600c41c0c0b60007411a482a1161008101e00300708001d0905d00c0c10142031170380c90880308006410350f5039504800400c0d003c3c41e249152a0290010b0b102d41000003007040040c9401e0403d45500c603151002d03000c40016251401c4c0300c03407000e42c06049003405400c090242a081c251a40491242c4a241c18001003054103c2c00f004409034642c20702d42640c149240203035006c2111005c5402003405441d40b10380c0403400c4d0059480081d0740d90394110034561900c0900068540d03503010420010304501c03500c040324100b01e8160340b0003e01c60340082e91350180c4001181c1096166000c0c0c5491a0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 748051582 1250 748050332 748050379
    0x17030414010608071a0a0801060f11060f040302010c18051e040905011b031401090e1516020c011706040b060c0f0f070509061e06090a271802 62
    0x104150000d10141d552a1240d035550355050240c400311003070b500c500051120f00c800498040c585a0b45a0301f460380c0c40c1041c16a05504e030751004034240b11250b030350368400031002c0c402c0b24400d0080b072a200310941461f0400a01b11488c020004d1300744601c110540031410360303001450044560403240104880d10301507050412302da400103269007060400640508214040d0001600c1014424115103254080c000072001c1d90b205440500c01c40d554840140074049103a04100d1009040d07804a4010040f011800d4070722000880700000080e4900c6595a07880780d050003021310702c400c2481d10300081842442e03429140d10001c0e000702d200b10780d21112030b44251a0601500c406040343d02c15120001a40008551039480781082c80119000d914408260313480c000075200d00910f80903000d0104074803080c0c1100e034043ca003815201d0b8000428000d01e5181c1d918850749202411325944159560101c41c0c1c2404031103464016018641c500307040b01045107500405041038660340445540b0080c2c00b69284004051 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 748052832 1250 748051582 748051613
    0x50103140a0c0c0f06140f0c0703051b16030b0c0a08011514040f08060c0307021e01060f0603090b0a1116021513030317040201080a0b1206040b071b170304 68
    0x1003003584120340c140a91540f106c107400d45c514003024041c1c0d50319110101c0d0303c801224003048042052009601081c0302d8000b0380186c40344244480a42a07010f9a96440c00c070449408020403410700740b0034810410728500854000d400003580300e0601903040805004004140150400d02d81c2c20700555413118030900354295911502e4000f15911a2900018681036403103001d04205845082d001c5001c201035002100d1060b181030380905054081041003000d50364504090110079901c41001040d00c20b611380c1c800c2d0040442e0f480000f001d440c146801c0640c400000c0108200c5854a801061080d000004480c0f1101c40704040070881006440000d800c0b001661980722403d00109290202d00c950003400800d41e07010351a14010000d1050042c04101e804440007400980320a001c915041d207290401c0341c41c1c40004020008039403041d6521868540111001c0c7c40034059041440a2980c020f580b00c0420350001943c0c1e0146010b9442e0a0700c00801002030301c3c0c8803080040024180004190f0b9280b05 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 748054082 1250 748052832 748052843
    0x73012020d060b130608090d08090703060c022b021c051b010b040e03130b030a0902090403080a0b0a0b03180f12130e0114040902030111040915050103140a0c0c 70
    0xc10b40700c110301501a0400307004c41c0a6024030510118025005034035a901c514289001403110340700c103d004807030361200541100054401c807000400011103902038601c09a1702a8010015000403980811420341c01e10710031200716440341c45500c04a540803075112220000c035841a203602555180880721840358412009a0000d80c1a200001d410190460902c03004100d905000021402c07200c56228800d592201c1c44584007158100034200d02c24001c4d41d0301c01d140040000d41c51186401243c01514116011030001c0d40b000200240e0804034131404141c280c0039240ca45000341058615803541c07101a00d006c440c1040086921002101007001022041418058943c403035030803007000c1d05a401c1850918401401820041641020f000200741202e42c0041c2205c45260301000307000c0240645d450a0703802d552541058490325800700d0052000701614000001d030600e801742d041c1990076a9130442410181840810350302c850305c005070f05800c540b0f41080040c016290500540d0306a0184c50700911 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 748055332 1250 748054082 748054091
    0x3011508041407080c090c040b031303051c14160c030309020f1203030405060a0902060d090f0209090c130b06041715070915030b1c030e15073012020d 66
    0xc4e00071010078801002913081e504801c0c41e1316140c9500b241805a402221401c1c0014800111040e01c605040d500303030785c000e06100c0d00e0710071600181e00c0c003181c3c0001a04881c0b030321102080302d840301500c40c40d0350051241c0800f17820420040030080044a202c08040c0804d0b403642034030025540c91403810301e0741800013004021081140e0007a0703a1030781c00464090f0380500a0000041e4184210b00915407901c1c0d0040a0a1800c0304d9440800003c001503075080c1ca00a10380583c03000141c071411328050044028400070210f25407001c003008150034a0b001d248101e5400c00c07106050903100c880c1610309560b6000601400b081c1110031640c40c2c8001100c581d101c61140d402030080194103d840141510380341c54a00140004c008805c2d019a40c908240c29003040311030f548c101564840c02034028100380b003803624540f49e110710b0340000e40240011021085141002031301e401000350200d807400c0c14007405c6130558030f4a40d4006200c000382003550716410500c441802c240f1348094030766046070b4030340501480800 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 748056582 1250 748055332 748055339
    0x10207060e061b0610170a061a0d0525140d051002030c04060f0807091e05030715020601120c090902040b04020d060303120e07050613050a0e0f0c03011508041407 71
    0x913501c03038040d10819a20440103c000c00e88188461709003030400080801800c0c2d07c038659495070001c00c141561082c00d00781c000b48402c01c681d51250320000045c080c0c5c008260b40303180200b2800c43c000e441c6100ba104080c0c80354041024402c020102605954111402c1180e580319041a40c10a03145a101040301c0c1e10010400c500303117240c03401410558180d0717903032002041c0703068200b42c840a5080c0c1d40c1c2030100d00007080811020001580181c5211506c00802c070520b43d803100403900e001e803507070010010003000d000009207140e410080c5900500d00031004441001064443d00c02448190092480480e103401e100020764540303400503013003000c014004641d107058004a90005000500040b800120310b0b10307070010144528014198250b81020140040d035140104100360b0394040e021001a000207548001060342d40c00b42d010009101c1c1c00c01240345850702c0c58000050704401441204038800500052002c01c54004030140c2002083c10101c070580c0f00c2d401e043c1c40030500340112031228072684a020 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 748057832 1250 748056582 748056637
    0xf0608130317240607050a0b06040e030d060806070305071e03090c0e07080a0b0609040b1917010e0304032d120e010224062202131401030b010207060e06 67
    0x4940030343c03002c222460f80340345040140070b1059030805020340d4003411380c1d0b10201d4550301c0225004a8028000200c1424406109085821006c41e08803400d503900c00c10003240b90240132095200c0c80f640b404000502d058400548460400944101c0002111340307006c109034041c3d4048240281c004010885555548507100c1c22104100c440d900010881300100d8a1500d07603000300c50315450300400c6542022600800d2100a101032034810b907015614205002e41c0c14001211540500705c1ea9041c8021051028405800e40c0c0e861603500760b07150700402c820008100d0000d07842030175440e031301e030b03440207120401c000344400000c00321001d820b10880705d031301d810071301e400c01c0e420304880c0800e80079265100a00341c1d8216140f07a100e6a04a40b404030640050344a117046511070aa8a0360280760314060300d4101c030160126081043c2c41004464401c500748890115900092050703582481c0c24032045506800007505c44229201d100184940c0c500302c54000d40e00c01003a41c90b244204602c030700d075400940856 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 748059082 1250 748057832 748057861
    0x4081204120e0a03020934080103031103090612060d02100f090f141011010507020717010c091e051203090906060c0a0b0a06031e020108010f0608130317 67
    0x8a030040782200c4400206414250f0540013100d4004000b04101e030748041d40c00035a04140c9518059505000c0110500110141d0b1801c001c09040e64868070305606601c3c01500702c1e10b94803c405041d500500070218160b1301d0000312140c00c100116840c10a40300d110114515103030840c3c00a50003150900121031150f4841990042240c070350b0341e6000703000d99440c031181241d40301d406207819180d1034a40142c01410000382c1400c240c00c00b403074000c100d81101d000050846e1001c0d40c4c07040068220540c1006018400485010208490b10003002502c00580c0007500050152081005602e02000a0004100b40005050045c8001380038010a13403050142c054881d403210040038400c0a50304040b417018207190081d24204003c07500105008034843d00d0f4800e00b07031401011965110303168907000c00001d0456070240d42441803c00446000d0a5910025241081c140c10103012000d55280c10803920b82c0c00100c0a420412049440c04481203c0c103045443d1032000c10701d60441c01d8020103109112599828 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 748060332 1250 748059082 748059113
    0xe061e1f0e0a03030c0f050a080409060e010608190b030c03010908130902040e0c22090b0132030604090b011205010e12071b05040f02070b060a08030a0804081204 71
    0x840901412480302041820900b50001030001101c81c82c1400000c2c000301c24160f242d5002c0c80c100c44001c0d00325524110a6409a000800b2240e19800100f20018030303906201d01400690030050f00500e0240c0d105499610030300562180140c84482103115a01d091100f890f4002c4050003d00903481c1c6420171001a6100d11107658800340100800a042d000034030980b4280c480140141555072521020172071503070403000c440c00d404202c0f0250301d4034080008100d080100850000403d04403104e00000d01210f07000745010045080950351154076401c4c608400d411901715084a54407901c030703000814000c20b000e030b01c01008580a5030000c00d29410045129419510800091010707000900b05a5103c42c89206000c1c0110300512401000840801c4110115101c0310055a841707a503400000e01500c90400c402c01e1403942c005940030502244501d0903500407015183c1055031850080f08654070310411500d07100b0000f8141c082001c21600c4822595020005c4034426103038105410555501c801144 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 748061582 1250 748060332 748060337
    0xf1f0c05070e1003260703110d0903050705010f0216032307030b0c0703020c03060703020a0e060c0712020111060c190e0f120a0c030f0c0f0e061e1f 65
    0x40c0005410301c0b651125602c188a00400326142d9450b5948142142000c04100c4194180c8a100040c3e00c2d5982c030094030459000e0341d107000140044031022414014986805801c00500d402c1c2800810070008c0c0b01c20890300c0a2070806415068054100e0a25841352042000360000361000410301c4820001e01940c0040740d0850110001d50103030310b40e611806448018800c4902100050366050000003800c0b540c0c1c0680107a882402180c40000e06001040740d100b00030035804100d091340e00d54050700388000024240c8130f05180000f0911078581d030762421710501e0009091247c80b42e0459101d0000d810380c82082d82c08941ca5410b14040d115215081050030400d00a055108680007521030780315400413031406418140c00d804400c0a0141c0324034440117141c030902c00e020076040095000b2004078011401502d8064a8020510780300b030b10540a5800080c00b8032a019050024180c0d0b000d843c0d070001e0045810100c00001c1881103030f081d03e01081070b0365005c101191070408581400c0f00c040320041096 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 748062832 1250 748061582 748061593
    0x4020a0324110309060c0304030903063c0605100c1205070206040609051306050907080a02250203100203161b02150306091006051611060c03070c0501090303050304020f1f0c05 77
    0x210f40d941c8450004423005070009454500c20008101a54403030f0b6424280c20b04444a81886000401807a0300b04101441c07016240c0b40c4141402c109030300c180c5000d0002103400c1d405100c0c00040040030a19080806405c0c072800b4a40e00c034a0034007400440e0452940a4815030702c1e140d448901400d000d9240c81030902031068024281c0801203984210f006803080249641c110ba1101c0303000300c2d01540004c0040d01090341c02c0005c42c0c0c0f540c80207004402c4a04030507101940181007403042c581400c400c0a10498803d0050080c00441c4d000d84c040340100e84c1e641d00c0d000019501103469aa80c1215281c00a0341203900301c040807001034102d2000f1340c0b2848082e00c54440b1919545004140341200784681e4000482c10700c1480301420702100f5210806015030a00782141040900042c0c0a6008018030320032039100140d0441041558800070f401007409007860f11072a49151800360091100030710091240c01c20720004c00c10355070740c0d0f00804400300c4140d8044401c0612084d0217814180d800200707484038401c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 748064082 1250 748062832 748062841
    0x3070609150f0b090c0304020f0a090603030e09010602030301290d020d05090c010203041505070209070905101e030b0409050115090b060405030d0e01110d02100605060304020a032411030906 83
    0x2c0c1c0200c0c650003401030b105407071a80d1130040780300640d04044d000301e81c0005601401d800c50303034409130745102a0400a00024007103103140350180c684001120541e00514140f0700400102c0d4010040d0390460702a51204204c92440315610011fa400150004440440c0407d0080d103120055000c1d004039130042000b00000d440d02034210303030b03543c100c2400c0d18010f92007084244020385c4203140c41f00d800c42b107a05105081c1041c0341d0008558840484007640042c0c0502d108001d9071815071245100001c99017003411039888580c0141103403039a08515402403540750354401d400d5407100d521040700c058004000300712206012500a140c00040c0c80740e204140d00748460700400345005070031501110301c0100100300c0120304400035505d0f88500c60b00113041c03050310020000110302c1404008001c80381c1e507000c2e04220440b080d11500301e41990304194040c1409004010040c1c99800c081c0c01940e4001c142c14001d502e441c400c6140111a81080d00c0205062844882490701c61401170350203001964160368103680c5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 748065332 1250 748064082 748064111
    0x709020a02060105131a060a0c060608030a0f1b030c2904020a0f08060a0e150c0a18030f0212070f060c06061a030c1c020f0a1403010510050c0307060915 67
    0x10112048140b0b0b41503200c4451b15180c0040141540344a40c02c010110181c140c0710503044507003d03809455180c20025940d00d503264401c400b020310454504105030580b110100084401000060041c14805c0c008120707814800c03c966040c08005120b030b00c040300002464400c0201c004295800c80c0103078459940820040d201019a200781c40d4803100030030380c4d59603080d6110040c0c40c4c0030039455401c2c000e9070307003107405526281d2005115000f070060007596000c011000604248646091440110b400c3c0003c0c0000f9200142c106150317a0111000030305004090015828552146d10000b004420417a0000d0110780005a00300003074052007003048940c1c0e86107502c20003a00e26800d000c00030001000054114a09400a0400031205103840034042d909101c0c1c002c102e80c040c0b07002200c000b2000c80e2042c0465070102c1440c6003940c41640003400d6501d40404111650444c508100074082d0124100200384800c0040d10038254001c482445080034904001407003900140da4640000e060180481c040341 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 748066582 1250 748065332 748065341
    0x151f08090f030a080604020c06041b08010203010b0409050717100806090c0a050d1403030f09010f0c0e04320115051806070203100f02041823090709020a0206010513 72
    0x50745540518030340610100704035031070003005082d1540a0b03400d004134040d640081240f17500c01c03407180c400c22025000c10006035081c41c02642c0000314a80c0108018410406901d05490449a4070407000c112616404001e1b86c0441450103210300ca002020704204000e0384048500088400003015a58580c4650f00c4442c0c4504e90101c0d202c1d0031543c1d800041059007806103142000c140208035004008070301070f844509540c01a40c50418884203502800080f0700280300313000c0c0e039902c4c1810411040552110261440380c0755080280b00c0d942d14090010003410345013110094862070300d800001c0000825080000300720030b01680c584521401d80f021006800f07030f000c0310301c90078041c04601031101c40340c4100800b69010407412a01070041c44256001d0075081d00030107080d640b031008056250b170300705901600d20b47c0488080303c01260038046a48081d4180064445c0c40c11500021b80300c855564442c0035203010304a50140304014400151118031035408540389058940032074078014001500e022000584 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 748067832 1250 748066582 748066603
    0x222050105040e0a0c15090f0803030117060702062802030103060906150e010317120a061406070809040b0d050f010b010215010b0d0c0201150303021b01030e070b03151f0809 76
    0x150035480b06004c00581c41072007a42c0c80555181014509232140c80c4a1001c3c107980c1d0000e041a40003000501214203035460000300440750600400c034601e0a0038000f5550000903219081c2c0c3c40490003104c89100ea900581d441c0d60b40380c500c0c00d540c0e07940d40b40782102c0286a520001d8035001d180c0b981c282c1d50744c03038200074a10481d890316054540507420750715400c00d104448401d8820300d2000308030140910307020018091003111241d4002032410300d4001041d59202186100c144101030400c25500000c0149090b030b10007400075107001032040d03910400f00b0044041580046c140b40304040a2000481054001c589030030700070380c25246401c01c01c00308141c5080082c01034141010040c0208002c3c3ca60700e90082c429291a0320000c200030507800c0303490460006a070010b400503044240d10f41c9030b0007425410640b42c80006e1900300051000550015190708181c011500341c2c000001c01318208840c81c030064400300701c004054603d00e4661420b142c0e529240240140007003001c60000803e280008640240070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 748069082 1250 748067832 748067843
    0x2a07110609030a08090a0e0906090f0f0307030e030708031303120905060706090c0308040f08070b070206070b04060b0a171506090121151d03070215070222050105040e0a 74
    0x540c00e080d034940e81e11707803c00c545a540024909000280d00c1c902070084a0081c0d440c0c0d0060803540c20100410350400c1007002080e91507501c81380718441400320001c11940f806803d0314002e0f400610201c0040e0030b29103d0b03804000507100c08600480c2e040d240b81c2101046a20400b2580d056100305802991f480c02d140c400c05a20440a111b09000720304260003001040b40b00f02c3c0880780d510344a6981984c682c001d03800c1021034240441d41403110001c104110f00181c61880d00d2a0309281c410303400502244280c1c88010003424042000c1410091039800a42d00e902c001801103080544501c0c2c07524440c1010203c41c0070398428100e894007012541c4000f9409000d0251103044560300b014504c82e140101040e20901c402d043d48100e2010810303051420040d04502d80b008030700341e185102e484c01241402450396000380c10400480005a40c0d2810000f9462110101c03241c44900350300024075200f095007030044100081c01c2581d1808a029840641039401c2214104844c2c1c03180810141c0d12030300a00000c0c01c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 748070332 1250 748069082 748069093
    0xa0e10110a1502070f03081503010b280806130201031a0d24090f02102c0409080d0b041a1e030f0d21232a0711060903 52
    0x410b5402c9519440c0b2400544090b1400041da03440c0b01c07808403500000c0d800200e000c418800312441014030311039003d00840003807000c00240760010b101041c40c80d60306184045c1300d03100c4d0b48140504509080c0182407103415500c0904e080103403000100c070700d1042240028544040c000e0015040c07401400b44810181003206180e1aa544040891004a40340025860507030440c00b5420f007640200c0d11400d101d05100207440c01548140544004003a60802c00c2c0541003000e514410036240c10ba10b07a45070404200404410001c001c9401030038800c2001d8064440060484880d101603005607180c0c3c041036030100480050002925071003d0800b0455610142848418500c0b80c801000c0140101000301a20201c3c00d048240a103400c2113114050041103104031000d58000802030307020222484000280b00824000381302c00c7c00021441000810302d906040440c042c61a2072185100c0d400034444c030f4190718089070480041c0d64014a03021103201c4000c403056065410700340142c0b4081000a0010032 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 748071582 1250 748070332 748070353
    0xa050d03021c080c031f120c1d06150d1104030503030403090501030e3304050a060501050603040c051c1209080705060a212a11011b110a080a0e1011 65
    0x440a03040706c0400a444014210100e01e0681881c0d140605510038001041107520346110719240d0030322252514044070110080042e16215480302d52454a4400c940b240d50b441e070307651743c03400074041032110850030800030501104020001000b54069070003500c0e0356964680d244011019a16011814803030b60300110600c605074000485404400400340c41d9440c0111024004200d158a04a5054a055022030b01c11010b1181511170b40340900800c0e11010300d149000d07113800d80301e94014855a801541403a000c407102c82092000012140c1d88828020340200051100500320001c5014a2800d0f004540c80002d284ca0040212041100305486414144416560304882d81d000d1407021040c040c1c071400856200403540080b0b030302c1e5059040c2d00d425200d041d540300400b100039241e80c49095030701d0058480d0b400c81850311900c105c24007501c3c1650301c03001c002d8605410510350308401013440c1e1012a48100b9540c102c0d2510020740d109513840c210f02424241c3c00c6840c20710812024403150046400c64 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 748072832 1250 748071582 748071601
    0x2040e0607050a051b010e01022104020108060d0602070b070e01090807051819060303030c1d0d0809040212101e0e0c0a090e0901050708150108150a050d03021c080c03 73
    0x1010301c051705916500492949591150a56030000204000d40e5800201034880c26048a0410749008a03251107018528156001070048800509540d1142d12000380301c4040100540450f92419405102c804603824010005420800031441c03060100c1c007103503c0410713940c400194840480380001c03d1201d000800000070403102c500580b00490318401c0da03010b00d00c90440d038080d0070003c51096030b0010701c04082d40c1c402030460000811000d1040317400f00c0c180005a549074003d010303503908107075415520082040020028403034800030401168140701001130307510903620000d04070b640c052110704040c0605c0d1140719070201503019040501c19064081181e070074030000640311201d9582090b446040d1030ba00241d01c076030022141d1810b03513134552080110340c0d64400072840c0c201d90350040b60014401c102d030019103a4200108031004c42e60b045001e6120550300c07135400c400240400b4114584080d211f007402500c641d042c9403d1500a010b501c071500030301d071244000340e101d01418070385141035441d484c0c2d0a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 748074082 1250 748072832 748072837
    0x11502010e06061002120309030d060603052406130e0405070e04080a08040309090f0203150303090303040e0a0f0207052401061d18010f03030215010501050f0f0d020f0702040e0607050a05 82
    0x104d030840c03140c0315422a180901c20001d5009026400086444107803081014054071030300d8010000b0103082c8001e111260400452542e28450030354011000a001c1c84c000c106540212501c091005c0c1c1420000a00d1055512000d4003540c0154262411252600041049400140d40042150f9420040d881a15202d101480e030002c0c400e01c2e000c1c40440d500c04603202940d004030281407550741d00106000084031000550803000b58254041c508100324040040e440f80158072031040b28181240001d101caa07016881440b4800c4803ca045441e202a0705140d5a40d504c08104003c1164210000d640a18100024241210a0b82c1e56141c002d2311180c42c030041d40702c0ea0f841004d0308040703c204c490311241065068a400f80210851103c001443e42c107000385842d02c3c0340c0c0300c082e21000d500c0045c086641e01800711040312403a40c549642d10406408030a10394130074140070407422440882d100c060420100000c0104034000c89090228100c40e0080c0b607201e482c103880030004104100140d00da02e9008101 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 748075332 1250 748074082 748074109
    0xe040e010204032a030215030601021c02031c0e0109060227131805062404090503030f0405070e04120e09100324060806041407060503221505011502010e0606 69
    0x120713041e50baa600c1d4007046007040440382410020902000304421564100300e0100000007076a0000c1303103540c80510107502c0e4481c1000715030070389052422440315801c858000340c800c0000c0c2d00080000199504021000350010031550840505141d40000d49032009000d42d848488002d1418102e8040d000e6800001c01c2d603980e0074010500d00403030420214006004851042c00c1141c2c03400840c1002d0000001c441d150040824070070f5241a14100211b00b0010075207602140903050385440f0703141c03418014940710482d4808410b008810003004200440c1c00654880b90b038880d191042c9010a440402000b65011a00034203550340c104c1080000c41d030391044d54602d883c41c01c15451072548100c0d100c3d2080c0c0340150020000c40d403080c0c050004010100202c2641a6104d2026200450400100508600c0b024120007070f450758680c554072410320311484c0010345a030301c202e00e4101d501c922461003026000074443e500060300607210100ba5140103008006200e51103801a1010380d5a00d403c104c5400c48010703 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 748076582 1250 748075332 748075403
    0x5010507031209050c040c050f071b08070f210f0b0a0b060f04050f010e0901060503060303190305180636010507080f0112240f0c0e040e01020403 64
    0x342c428514146510070506441e01440c058139421075080103200980b8420322070302c0f04000c1b04100c3c4000741b461040c15500099071044c1210340e1600c5614094424200310b8103c44540e01849400181540860014404540d1030554025500e01503490700b010485102402401c00c0100303114000c00034201c582c00079441101080e0000e060b005410100740c1580141c0741140d041080020148510b00d403050000100340000d18000c0b15411882d80820003840041c4240f80511801001048082c3d806006a071825040750301c4942e01d203552103500401070b00341620031503038045c40c0912203440d4000108169101c0d0149074202440005100d4a0400508165400a0300d5000b840c1e07104401c2c100c00e02400d03006841c5543c4132982814681e14009118070103034070900005030b4600d0f0b00c0002403840c65a01c03003450805440d409500f8503007034450001d05564042507085620346201500c6880e08000312101c80c1c2c1c400c3d6010010a807048449500301c0c440c500019054140c0b000c1081809000700114600030840707030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 748077832 1250 748076582 748076597
    0x203070f020f152829120a14010b030102070c0e060a0609140a21290105040c053c0c0a0204020a02030c071202040b0f010804110d1b08070506030c040501050703 70
    0x103084c1d004850540207441c1c468081a0000c00c50001e0000d40344070350403800c42c0c80d04078020303d020b49155070780101100140601d13900458040c6510080d4070a080601018000703654400c80707803801c1e00340c1e41c0c050701581d030702128080007054180c1400c5e02a48c054070f0142d1200310303070141010b0f1142c01d505070001c607e550009111030049200340717003403103203114640032501c2902000f0801d1400700d03a020940c880030a440c05900d0b0030fa10400c50b500e98520b0441b04107840c00590045446130450344d5115403100f1003210074801408260501d40d03241c2d524070024910140c0144070085c2e004d400e64030301c20045210034035440110150b001d8070b002e900a240f803040b41d0040705c2c41c1001c002c03034960420603580d110340650303000e1280410075403c1502426408480498050f42c07190034800010b81140f0024202400621182c10618226200c5150200700160000100c0e0320325958188010107440702401541e20901406034002040d041100c1503d0049810010a81c1060308043c011102900220707000e42c1041642d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 748079082 1250 748077832 748077901
    0x9180c031110020d0c151b080f0c0a08011a1905090312040506161e050c0a0801050105060733240b0417010b040203070f020f15 56
    0x140021440110311422842110362140400c21000302c0481c40124155040000001055944500e02407442c0382e0000450700c03003c03500c1400d00c0007840500e401820403500f1310840c0c481190042102d601c40c03a8103070000c00195460302c050111900031200d4000c003043c1e800c00113002c017090020040040248515030242003030380703021414900070f8a003045000420702c001441072180c20280071081c0038502c800304207850700e031170600450401c0c400c02c0d001c040032141d160365000400c0707079441a03030034401003d2141d034501500d2410b2a50b02d0344460b40e0b8081c4900e50458000034100018001c15040302c400070132580c1032080a440380006006009043d4a40d040700c0301001070440d01403042c0080c8219150030006400d20450007050030044085601c1080c503103d40000c21a200b400c104035800d944400059045107200310b0003242c0540300305941d0545c024000300400200c9030b48010342e00044105907084600300002c003200d20341c581ca68001c080718040310000c0050154012940f858600407440103110104410303 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 748080332 1250 748079082 748079093
    0xc161406090f030a0c06020f0723040b03012903070602071208070204060605030f28020c1203011409011403031222051f15030605040309090f052401090918 68
    0xf182d9208485c1001c1600e0305220440d070400000984ea480c0b000201441418110340d0303030b0702001c15600402409691501c80f002c0c0d85468104000c0c45001a00038400d50b0040401910020100402c410082040420b000010f2400050450855500d07801411160307007130005802204601d00026601103000300070240058445125030703402441c0e55642d035526400c1840480c3c01a103400b50200c3e16541d9941041c0c00d822504030040c94100c90b0603200141e40e0b000ca9010345080c607080c0c0c0280c441140300800005122045900b04000300f400850b00320260340c1e01c82105400a40c01c8003151a0194400e00c001d021080c4202e40694004100c400c0211100c0c103840018400040440022101a0441c0c035440442c16401e540441031046400400d0165420440707194040c440e180c030014250070b4680002c41c09160288060324013814a4a00c144100b082112541002c4d00341a140245000201480365440d041c01024100041605940e100d00342860840300c880a810324403031080c006401002d40100044 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 748081582 1250 748080332 748080343
    0x203180f06210a0b010c1a072d020c01090308030f06041812090f06080a022107020f07051c06090303110a030b031603050d030f1503080c161406090f03 66
    0x2000903520180a290a4243d4004c0d0b50501440f94140075030f0843d4040010340d02890f0f022144103030340d024489580e5000c42215060140407232485040442010401c41d400c100c1d085120809154080b6440e034141000110ba0040e200d20000d46110420b00101d021108070044c0305800c0000140045a0a01c0d904021010420354540842d1a1269880c64101c401c0d00310310040d0043c00042000c589181c81c00401404160004110b4514190300042c4272140b64108010596260340d0041f103081c0c3d518200c10042e6403009041203007170712846800340c0000c0740d01c3c00c0d60940c5840001d25550010662803590b9000203480741940440526413145180c60040c00a50085c01c01e00301595004602c4a020b4020700d414850300030080c041c04a1035850510102e04001441c151054051800180040e900d60380d0390010088005104074117110b5441c004240500d01014050101445003580c4000c0381101c40d807030b03402c0d415106500d20030503004c80081c1940313400c01c0940220034016107140c44000c407000c0000d0800 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 748082832 1250 748081582 748081627
    0xc05120c120115051b0a0c0602032115010e0102010b041109040e0c09040803100f03060f0c0305061302130b0c0d020607030c0203030f0721050105100203180f06 70
    0x14040401c09292007020721a09600401182e0041c4034403066a1900805070304c1081e0304100140020300302c6015080003001859030491700910704490701910340e00c00a441740d10880e241ca0080001c1e680d6042004400c5410720b0107911001d580000b109042e40040d192210b204196030305655070364154215644440c004e6450300c41c09c07122210b83d6981c19a0420048641d0b1041380d0405500410300d500e601e0300d98408068219400c6502c0c2c545966542c4d03200a400c001541002081c03505a00000041000302c0d0086600d0022240060000d10002c08089007268000c9030b81e03130b900500050107841130402550040c0720030b49401600d00f0900e5122400080203500101e406a49c50380200703200e10401e81c1c1070080580100840c80c0c20304c003070b1009507002962030001805181403d200712004c503d05c00e014034207507080d00100030304540000c1141d0310b03440d008003424410140110010616007840a1010007103c1e4070380302000e602c088000302e000500980308203802985400c81d1007003142d004007082c3c400c540243d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 748084082 1250 748082832 748082851
    0x18160810052205073606052206030b040e0c150a020708011107060e030703050304110604030b04050607020d0207030203030f0f0403081b01060b040e3c1e0403050d0c0512 74
    0x41844540c038105140b00b0f500c0181d5080f07010044640840e07660750846101b22610307403800d0ba48565600111161149000901039001120340d0302c0040d4854068201c2e002111007220100300785c0181d03401ca40d855030b0902d0692580000403050b40e5038040c0005000d4181c403a89441200d072000d480b40e00240c03c43d911038141d80107145000c5000810003e840c007030800240000c6e0040c60400c0b10941e070142c25800081c000912802c140610303039501d622248140c800940d0400700c08011400c0c1401c01603100d01c2c00f0b4501c0ca0060140c00e9000c6280d50000401000300e80e40500190300e068040c0f1704010498020009031200e10804010000100c0c08440c064641c40c02d03150380094055501c402001d003143c1e92031384080c4840c6c1c42030000300515041e0080c0c5035800426050030607143da4806825141b00710100e0388002d002211400010f2080d0022580e1500c21500700d2008149180000000c81590008480c0100014810800e440040303c0301d4114107500f030b04609050741404828019540a00380c1100c10024 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 748085332 1250 748084082 748084097
    0x207030c061d150a0c020706080c0904110d020706050f160309050c0907020601140307050d03121409010e011a060301061103071a0601032f090f1816081005220507 71
    0x3450503c80c07103981703160142c5000810030701c5e01d4208050303e10140200011010701c00402d41c0007850301c1b250018541c900310ba000240c0d8500c4076990b404000d402588040d60003e10f410005039502a1036100a0b00800640459281080c401f0608501130400d0039001c81c1d070b5001741840801c40d62504000180603141e1038010308603a604201c42242004484200c044c801d0340519420011a280c0031001c00031260545004201203200e01180d501900e1501c02e2003003c1541e110401c054613106610040300e0640550080c007104803000300054100360300e80081076000c0420001005141c0c01f501c50740840d10514001c0d80e0030320620b40c40c3c0c240c0700c0302c1e0042045c1200c11040c00f00300a542e4103109044c4c4030058102114030000b5081c5040c030150030305a000364820040051000c846695003c1e1015010310001c28803100100c41101d00086260299040280010708a10584459001d030050761b204062034501c42c03a01a00d400200030180c0b040da01a900410405a400c1d90108014010359209031180c1d110102d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 748086582 1250 748085332 748085341
    0xa030201091b0b070b0c13090b10030908040b0a02120d02030703052a09010c300801032d020603162c130b030706080402130207030c061d15 61
    0x40d5021010742c084550006221018080d0403c01400d451500b500044420701c01d9481090303150300ca1080c034248481011036200c00254885998011052562045c0ca01c1014048000c00c25805d6541c0c03040700400e460400c0c030040c01015002405809250401c1c8100c03800010001000c0b80e04c0d5100c00011a4402e400208012056405025407138000502e4454071840a00071018078040078652016034000100014221a807030303100340f09440c4802d40004400b070040d50b14100c0c1c0c00440900c0c500c06e00c2a103202130201720300039000350303942030480f81c2000d105021184401c4007100d58031059001c00c0140740b44044580090380322800030718400c48442c050201c40c48400007010380107540305034071400c6540e41c03000e2646000c040310500c1001d484007550351403007028101c03600001a09880e41a281c240c4110074002456650090050740907034026510f501d010018220801c00380d00c03440c000600800c038094520b400017051507100c11484220000c14010705201030b410f9030f0811100c4007000303030801003d40901 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 748087832 1250 748086582 748086593
    0x1090b09010e090309010c050f030a020312070c120e0414040b07090b0f07110f12061603140f10030c060c17090d0312090c1203020f300403050a03020109 67
    0x2601402c00032542a500e890042d844594034450202100c1c10480500082420008104058590b0244c248262034481c0070840d8020740e0707a0040102c0c00c0d071200b0680d02042c40c1c54003ca07a061b0f076041d00241d010307400303d9110394107031100700401c0d1078983c02903a1143c9410b4603e1a404850713008910130034200f40a4145500002c203007001d140c004a41c0a002045503040030400803040740d8010758007000c05581a0100303800100102c050080c1103801c101c0010342c5d441d801d000480c3c1d0301c1c45000103409901400e01d15100031070495840340d0140000c01410008120303012031461155a0003000c220b484501c1c2a1265a0010007e1850b40090b0100d038501c0f086000b002600003203001c1ca101210380325410b141c0d48d2400103856094601024090040d029078112100c01715401c40c88203a030708040709440c901d60700c220401d40c4440c864420f600600a042002c05001d1020424110031a844040c2c00790344010034401d200c1c01c981c0381c041440b00b513104200020004034248800b0b501c5500980000500341ca036800c00c0e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 748089082 1250 748087832 748087849
    0x106060f030c0801060e130e12090a08030309030304110d02040c021b01081905061507030801030b090a0c09020c01090f0602120f010806070315030f0c051005090a170a0b01090b 77
    0x20b40184100c4200500c00c03a9885134a0343c0c03074448201e5440440000d1746208100030402d010341c1d42c03e1401030000008500020000800c0e698405980701e0342141d98450790a91640000e966055040e001080400c4c0851160745000c0700d000c00040866206060301c0c1d0015048a05021480000d81c006001c60245400c81c14030081c8014003c0c20001c1d03c1d4648520307084100e51400380002400d81d500e601040351512207101d560010615480800c2c0e40300c09505002d40b880b1401d1108450840070100002c92031200402d40c40031850780410300071116800c04103040c01079045a85c0c440d0866580d803042c6c1c0e000c0754210442c0c0066070700980300165104910049111041c80c024421203141c002c1800401c0b205000280359544104a850f001a02c80e00c95180f158130704080340e00142c40c1840b00c045010511003a101214101c9400311440440402d20340d00030360301809900007880d0f000300407600030440b5107441002c8181049074541543c03a00c00c0e1568415204030020b03040000900d07502c00e0f0068031410514607 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 748090332 1250 748089082 748089101
    0x12020a080f0307021603060603020f0d020907080403021002130503190506041221021b0f071809080307051c02090a090b0a080327040e03090904050f0106060f03 70
    0x601080012a254109944034544058003070000c00000544401e2091010140314000305ca00608040da0364249000507210310301041c0d11500d03525a0700d5105240c10002100e060354050000321182e6600141a1030740f0500410035000d500901ca0034000840651006040300b030800284102c803035051005040c038000340f802a00340d1802c0704c5264035000c5032001600c5541b29070302c4407a8000c40f601048085404c2186030210b00f041015070030f00c41d041029990042c04114103c007141201d145222103649a98225918408145030404441840300070503088516504e10140340003c100710707442e9507a80170254400c9038080000386011440701040e814140710040c0e09040da400c1035040c1580d900018402030340501ca9000d4641c2c5d41d01c0c022089480d03150341c2c2c5c8000c3c400c850940e6290780c90303d26106418448150181c0d940342088502c10385a1410303200f5030012162040096060034010300912003007400c0988243d601d1700c03d5004100070408240540e10107800d860f80c4501c80c4c5400c4d2100034003680e5083c003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 748091582 1250 748090332 748090337
    0x90303040503030f0a0902150304050d0e10110c030a0c052d06180405040b0a142e08010c0924020d0e0a0302090c0c0c1e0d0614040b010312 61
    0x4103100100d14000b054a4208015031541003164654041000041c924a0300080d0041e4072107280310000c28904008d10300c030310300800540b00000700c0c42004841400c00f82c500c0c1640705a144600038205803145481004a001c21011681402a840d00207460007208003000c403111400c55005110f1400c00c0c00c0d503414600b8038007401d041040c41c14000340e6803441422881c1401980045849020344102401c40c503011305e8040d00401060803d0f0402680b110422901020464288510000b100075510010761040d81c0c3d90020302800b080325aa000c0701c10010b00180d1212a842e0030000c50100028824840000c0c10b40d16242d800c68a025500204108078160b0300880d0710030060320314441c94011401c00704890487c5003032403006c040c180000d01a2042600040e4000444900b04a102b50300350000b04028919401241c078610b5840c01000082c02c0491001203c08000d00ba10710703464142403181e520200e20400f000300e84440080100c030410001210180d50441c0070178010030a2007008a500131907401c451 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 748092832 1250 748091582 748091587
    0x90c0406080f0d1b14070807060509061c020f18041104140d05030d0c1107051c0312110a03020702010906021c05130b0307170c0a0909090204141008060903 68
    0x1007000c2512600668024418450030643c1c2c00307400c0400d041180c0c401544429052100c4c1790310a200303a550009801410724074461440e001c24128010000d981003a200205110320301044040c000d02250601e040c40009107809000070035010440d0350107040040c1907280644454100b0074100000c0d51515031000c015000c042005001c504040f10300c0b0007440d0000da5624114104500d0118034512540225090092078001d01c80700c0e00d60b006181d05415a226001c803801281c072403040007104131294006c00d032103007064203110002078051040a00c80648801d0001a603c0f041141c841540e480003100d100001d500040b05011036800c00020b00240065200406280d0100195040c070b40c070407021240b0500a021802740e00c0d9045a121030400b0b0b21003090b803035490303003412400a0401c91940040001440c55030002480310302100054524401e110341d0b80030f031203d00d08440c036801003855040998000340c0300c2c2d00c009149000203115034082c00c08902007010030b5280141080c10a10003038046c09868104 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 748094082 1250 748092832 748092853
    0x30a0b07141c0504020d08040602010605030606030f1f1107030c02011701080d0c0c03060c08041505160e010210060e09120316050901110d08072a08090d0b090c040608 73
    0x69894070072402100d99000140c6481350300015a80902600c4002c00607080010042000c1e80d041d005030045990540441750319440d400105a11903681040300c0e1980d41c0015041c41d02c0d124000101ca4004000e040002003000844501800300c0e48122070580c08a119005440d045580c46401c1c011a40201c0070006415410030500760b40b11b250f0455600100031445da0010240b00c602d401c5c200007158412010070208009120190a80004490a440050200000c1007241c0014001c252180c94050441006a0165030702a1100c0c4d1042504d24114424500480c00c0b201040c443e101c0075121441505110749040c0000360316100700000c10502c4134106106100c0080d40050b810261004142015a02d0344040c000403903460106483c060064425450101c000ba90015003150055800e980c0f400030490b207510071a11001461580450620501080a808140410040c108240006142c058001c8180d2102e41c0381c448155580341d00d9070001d10900941d0b142510500e00105600030240604900 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 748095332 1250 748094082 748094107
    0x60e070203162006030406050402040506032103040804091404020f030d0c02040509010b0d06020a0f0e1809030c1204080106140607060c0e1c03030518070306110405030a0b0714 77
    0x1c0b03040010200641d036800240e4001c00c603515010500302c00f03070004d500c925003824424068071080c0e506a0040d0720308001b0400500300030030324800030402c541c40c8442d805003520f106d88155100070025038480348148404109111640201d1400c80004845000300f4180381c010040f0380100c0d844294400d40c015900c0c5603035550803003402140c02d0340480d070001ea5580c0d01c0c9580c034050303c06001419800510680c0d0b8204100203039000c0d0100c00040e80c0e85801c8407c900750150359041d0300047c41a07011064803500009032812240035540107002c07409583c02e025840104070f241c020365602401c0c404801142c140060f00d424403450000344100c2c049c808228a08101150300d51058040242c1703480d0f241c100c4496690b0284c03e90744841c032809000170030310745070020344014440c020b42802c0340082e04110104c0e9141060360302e03d02c402d80800f005414000d1566a455004080908401c019180103000000e1241c5d0113122425107a400740d2600e644a1400003130040c02805105107103010712005100c88010040d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 748096582 1250 748095332 748095367
    0x10f02071a07180b1c0e03040609050a0608011203181403060a020313020105180607081c0621031707051e030702071202010e04051504111204030f090b070501060e070203 74
    0x11208100c480c1d9502c690001894502d403003804c11170304c80f41810390181294900000034021035000e6a582d111160312082005110000341c0300300341c0018041d600510000e0307100ea411812062003824041c201d002d8050301e4201c0b8800303e0340648081041e011850100b81014000d003503204e40700800840c50b41c40c1c420300d07400c038034060450302a0400101103001044020070000a82c0401002040181c49884d40d1800d44001d40c410940d90b0980040320141c00c10449241c0100700030b82e64240740b841300883d00148600a4100350001c26820003140411300011044040c1c552030040c80560f4925544d501c885806800042c0030319062a1041e40401c00c11502d90313808204482520000c00c43d0383e004000741e000403900d40100f1840c0f40c0d0f010345000d0500580407065044800d031a41d040d1820f00c0054040b24042c00700340600000c030400c515440d00000c001074894400f1003203401060810f0000551610401111a008010110f510340c0d501e0f5018031a03584440030341648100316100551810348486403810281 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 748097832 1250 748096582 748096589
    0xb0f0102070e042406090204090c02010c0206040311030f0c0a0c170c01050a030e030a0201090201182d170a0c0b0c0a0314090612011e1a0705010f02071a0718 69
    0x9040240e044005586168144c8284003020388240649611407014200960046c0b207118911841c01172100b662038018000d0515000054000d80b03a10b0b47c498406940c441c2d203002d8902030a00003000400490700f4200050718078108a000181019115440c05007819185900001c01030307005801040584140040c00c07080741c1c0400e10b0002d45900043c80181c010b01040c21007c038140c080400d801070f00759415800000428001d83c0d902c440724001c401c0c0603005030124000c14501d01d40700c00140142030824520401c00146001120026030356501051040c404640091105900702406030400d1000c0721640002905a02216916185071111495a46c40010700020288003500105180c90755021080d1040140f000e000155070704070385490031580c24000d02604003983c0091040384029012a104102603c60100088019540142169200e500308000440300f40d901c0741d2300062803000034000740880740d21030342701401c0c48150a055031a05001c000d00b40810080c41400094403100780c040b085084 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 748099082 1250 748097832 748097843
    0x1021b03070b0a0204052b0609030c0201090608010f090e1507210506060306090405010b0a090e070b0406021509010b060f0301150e01080a0e0a0524011a03010e06011806030b0f0102070e04 82
    0x610030420101447c00c040148003400311480c101d0050700b415004191402e42c113100340c1c0c0e0030807255104c0009550451003070195a80d036a807030f500c0600030b1546a5110203071340c9407088120f8044482038107207076400d0002118461300003081d001e40300e00c0c041d1121100e0b00c09003104150a1000e80f03403100c0450414000108802e10030103940c0b01107000c0c0503080d4006000010054084a0f4068030345a0b103001a04560003d04407511903007900081d801c032508184c405031a0280d0141c02402070403010901480c1e0041c02000c9075542c8c6560880e03c03030340c82c84014000342d29144401910b80d0315110403020701400307140d00b000030300c11088602003c50b0f901140301035105020714000201d150650174940c0ca0300c0990f14005000e841000c01007c00301e80003005844040840301008921a030302ca140c02103c0b2100410485142c0009200510620203030102c2c0641c480c0062410183c40c8036a00791802a00d03540c1d500c0100401c0da00d404490150130184c0000084c0340b400e00051491a213001d00c8450441c0c00100f01400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 748100332 1250 748099082 748099129
    0xa08010e060c0d18110f01031a061b0607090314210a0e031e06060319110402211605070b0a09080c0724030905030315010201021b03070b0a020405 64
    0x30b0902c0d03135110000c3d01100100e11303e2513110500d00050384104031140548a2440b81081c1d82c0198841c3c01542c00f5642c4426903030005c800341c00c0511542d80c001310fa51103120101808195103004040004902c030f084255034014a1500e541480032407101c03800821007040d0000e0800f031165107010300200240c082094012075481c1125001120317200b810035641a0700d4090b01c0b40c50006112001c1c03100492444440580d41203890380d40406640d81e507242e1496000340c0301d40180c0c20118458983c1c0c40802c3c01c001e0005480c102c0704852000d40909500501c2800e46540801d2004688151200004441c06030401514290098031401340148004241c1e5080da5103514410b020080400190340300c050400c8203e44425441d00420401101d94070030345064103200b000c09450b464820300a450700d0a4000000e503103551504080d590b84920700100b0b076415903400704600070091515500152040d000c0c0700255455420a01e40180c0503013000d011210700600500c0207004503659011203042440b880b841c00360 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 748101582 1250 748100332 748100347
    0x90216020d050c1009030c05010c030f0809070f150806031b150409020f030106140a320315031605010e0d06060e0c0c0114041e030302070b010b090a08010e060c 70
    0x103161103030792440380b031304068626100c81040750440d0814081e02d01c9581c03105036990b110001121000ea8890703002d40010070500181150070700170140ca94004d41800240c50903903441d454104c0494125900000403800080c404820032544109216000030088024165000b46003000d041c2c080f030281855807180c444400c054030b00703840820031100140505401551074000d15220324003590424880c02005c509010100703d0319003000c0c000c41c0c4200d0321036100d82e0441c10b400384a41d0844001e41c0c0784029050014100198050000340145206110034009060419520410303d41094a03000482c0030184107003005001683e04040800401102568013004080c0d290070030070003408055100900b02c0c1e089600b4049800078220080205140380b1000344040400c3c0c40201c4d001c2c100841d000780091001a500c54030803081c80e403600c90491b00910300541080080e80b60800c00381001c0c1e015040140380001c05072980e080c0202444000c03c40000200061650f0304000c2e5140c000003450201c010800162a0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 748102832 1250 748101582 748101593
    0x703050f010303120e0304090f1b02011811040e0f030904060b03090703030f05070804030605160e0307060f0e19030209073f0c0909150501120236010801090216020d 72
    0x358000c1c04c0c014009c3c001c500d01303000d0b0000100286141c101c807038900312904095550050085120607401c0e8284d103124103005841d80c0406a24942d451341d441500d6165110b00b001080010609055000e00955564229030f010441214200d50119958850078810880304030f80100301c20003141c3e01403d168450141c016011502d611941c0350080000e1000708002c0103108080e480342d0710880c64500d240c50344d18040401550340344a22002d00707030b0640c00f618007030104a11a2075200c026040500b0324084605190001640b8024641e0303200c420351000d43c07410401d40c907100065940000b4182441641d02c1c4001184902150450441002d000e10750b025819010440411180d0380b81540b413406c2100c1030103002c006103540d80f9842401c2446003440c1c3c42c1328440750036650740030444005840b900d86034243c0004650180d0800000c026424441285243e85120720306520084100c5c07241b0052a1030823064005426018181c00007503065106015480c02c1141c01c418400f0410340468403044c24410300c0c80d01 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 748104082 1250 748102832 748102837
    0xc110d03020c0d140d08090318150d050a060b0f0d0b06040b0d020901030c050a051e070206030103030252090e0d1b120528080703050f010303120e03 65
    0x2c0b240c0103201c180d601418840310515507040403140c0419200324480416049030001d02c01d0301d070703621590810014210380203621071000b4407554018140d51400e0600c01e01c4800242c000240724554107403210200403840b845072080d140980000402941009210340d2b04503924007481c14803200b804e0342c680300d001e401e80ea000c0c1036070010081070040d81c1c0d45010040d00c0c5006508092000f6001c2801d1070343d0100c0c62809182540c0c07a4a8456580d9410160001d090041100f4184515100038408101203805625407900940c0610b00075001018130390310680541645000100c45049444801c8000804009843c81c5014006130842c40c020040e81112288000b1a285075003c00d2209141ca00303030900c1c040e000714044440d4002521602000f286404129001d08085c003070040c080440e0300518aa102d0141e00540400000780c41e04141c6058910704220205140800321004941841e003081041a0325004265100c1d4030f0f10001136095146603030140101c0500300054100b0f94031030130710480600c000c005 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 748105332 1250 748104082 748104103
    0x7060e0a230a0b070e1c080a120609020c2508030a141c0e0d0302040f061110020309031201090b09061002012009030f0d0c02060a12090308090c010c110d0302 69
    0x403c1500b0464000781c400001094194060043d085508601c0160b00b089221a16040b0440d140350100c404d004440f0711b600d030070543e550369586034404a06a00203101030300311035400500900d070207140d01c584c181061002034100c0340703034845025081c0242c51000c020303207500c80c0740ca0401210294040b05021044e02a803e09440d4001101c00c815101c0d4070b89800c1001c810808409480129881e5002201a071082d4000e5026800300224100469440f8080d811b00c078001000545041044004460042e81c0c001e072404c0403a90300c081404401d40b036469609900400300740c3c0040010940707810205444d5080240600d12513a003204000c01c00c14000c1d088032104140241940e010305129400035902900a2045907020f4802d139800d4410358140043e19001c08a81600d5100d40a105a0f0030001d082d403000c000c10301040111aa501c14480450041c2030704070f8442d8940c01c1c0700d45001c400041c58000d117009194100104010301402081800d080c0710080403082c0c440081208960905924103d401007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 748106582 1250 748105332 748105343
    0x12190c05120703060605010512040f021c111512070f0e150d0507030e0604140a0b010602010c020d08270a0b0c0a080a050106140a03060503060a0207060e0a230a 70
    0x28180c4488021402e0300589200702030411666855900460f41c50249140018800c03510b41c001c80c021840a006c0f541b241d5100410b545440b43d270030154212004801c01e402c40b004254190000106d240c0081d41c00c10028402036070742c0c00e00109031000701c40d1950140140c428032074031054000c2c1492046000c00c1602c400686150a062240480348800384d0284224507003540ca4640801c403054443d010b02c05040e1050b100030001034461f80c030f840ca0310311048044100c00d40320340c6610703c1c006110303108154000c001a8000103446800810041d0600303000003054410401c603841005500b0111080e51641e550883d108007040c2d11f1000308aa1402058200140c403c3c0072100400800d00f030a0401803110450340c0c0e07120407860301d03581d0b2000c080c0c0c2d10a01864001c00d16405124403041c10343d40c064100040140340200743c659680000c01e0130200f068500700d8a01d5000280c203014000c00d4054900303410000c2008144180080c0ca50b84040615141c658008003200340c40e01050110420112804507000b0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 748107832 1250 748106582 748106599
    0x1140118060c060b0604030c031202010b090411010215070801060f140409020304031b080702040902042a030608030903060c070c0f06170601020109030c080d1503060203010303080612190c05 83
    0x181000b41084009400840d0310381d08041310044075040171002d0b14200e0f41d0002152501a0a40d41d9018002c109000f00d5002c5669030341e040b0946a43d9040e200b40114010b16003128602114000281050b1541721020030343d400050130300842562180d40c10b41150501c0c580981741850700801224044000049810b4110000c500031070713185c810741c0c0210b003e43d1090b221266003009a04540502005a0b08081c010b00c40520600025017420f030420784601d4070040c000031300b44502d00f44d160a130000007400c0c161044440541c0300807060300b51050780c014090107001582088140381c0000da464030018051450000d01050384020448500701c05406014a600c11907401912044010428804c04040841600240c00400ca6550061145009240e0155100511180036032140b6070954030004e10b4041c2e0561b03d00e82c208421010010001c0514031501d00907030b0340e525600300140b03081c2000c1c0c160344c464100c1915000003a0400645101e0420303426041c1103586002c0d0800450900b120380c01940c201c0e450 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 748109082 1250 748107832 748107839
    0x101d190c121b02060612071203050910030c14040522110c0f071a0304170d090b090f01180b0a1b0210060b041404150915060905030c0901140118 63
    0x2000b410300c40c030070b0440d0300700c5007290303684810004920900e00c10010260400c00c0c05224001315110700d070012034002c0c10810b142000c464042900c54000f041c148000994405001041a5000c2444420403a00300100e6080a0420002503901508590702c0c2c860b5010032100b1199401c00380e0868282400c0340100f40d6121a507095001c1d8840c02903140c02d000c40c2c01000400314031902d92901521224211228181c11a959559402c2c0a035030680d00b800d000100a0081c2e288851a42c020100c020748144490440342c00c001c805107182c100c5044c01d48905905224900c1007040030700d01c1100707209800090261491729100c040704c0007803102074156a000560141ca15203010340000b400726809040c00030801c01c69945a000c9180341c000d5005030754804e0303a11011210740e8601504036150034001c10481d0316140b5620100760313003140c00c08103060030f102c00d001b0000c2001540204070340008200c280c010301240060140060030f580c2c03050195510415005200343d0032079114520003814280b030394002c0c201d03440e00c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 748110332 1250 748109082 748109111
    0xc090121390b0703050301060c05010b03061e0105150a18360501180c020705040204060309052808030901150603060f060507050a0227101d190c12 64
    0x800c1040c1c42001c0e80e11400050002c400038112102180c06030707145400c50342852070850300312109aa003580c030396403986508005030794148001c0d80600d15105007000c4e10b01c04010407084124050b80a24443d00511044048001c80102150921442840c010b080c1d07441d0010500c0300099030390440b411804444000107480700c6907402601e9000184100416800184540721050740c4c024054800c070441265000541e107800c1e41c115540000860050301d00e5942c450000c41c0032608107a101d000020344076054001804003e12040d200749031024818404083e00c0c0d5019001c0d86441b036401404001c00000240c071310002075026511007120700c8005c842441c3d070340300010040c142d680140c2d0f0f501e0a446000050080c05002100d0380254480041c2c0018069602004804100c0b0f0f036800e0f02c1d8080c20344140a1a020b0320201c14802c080d02c020b600d201030b0514400e030381d40407044507c04a41d1490302083c0310902d000d44125407410598842c2c045514084000d0403074840780011903118105041c94032440740e10f203 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 748111582 1250 748110332 748110413
    0xc0d050c10110109030525050a1101050d020f0918012102040f09111e1c030e0d08130504110304150f09050715171b0f0c0a050c090121 59
    0x146005040d44210f040c7c4401c892a0b0030200300240940d1080a080002400702015401203d4050400354200700340d00b00507400340e91211418a0314220005030b141c055117018140d00c83c08000d46060480b0130743c1001100788503030003126995042c1036501440310301195070390b4000360005500001c050041034000d141194589002039401407107443c5160b0844103008018801030511440201600c9004441040015110130040320640410000b07901c0382c000c1d5140c402e060014188500016035440c00c082401101c0018560040d0b48034508105540d54110000340540b27800c9500614026004403082400d07000a050070700303014140701d06010380c15090241c0407031800100d50903407014820740840c504040786d2103075003411030314850341c000404101031810080c282d820198031244010315120540304410466044800002207075800110f51804100e010301ca009550081603418041f554104402440c600c0b0114800300c0780d8911132100c440c24004225450040320751070781009d034001c0000b001301080c600d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 748112832 1250 748111582 748111597
    0xd09020402040302060a0804260a05180d0f0b2412100c12060e06061b1f0e1c02100b010509090a0501030203061509040605091c020f0c0d050c101101090305 68
    0x5002c1c1a000c800400c1c02c0e00d02102e00c1c0003110540912b40040e240c8159041c2d0007003506018481160601d42c0710680740c644c2006001c0c2c2c010420402c040b1440c0c5082c51507183c0042c0008039010707007009403054000c0041401c020013a021900880e40355440b8100c686001003209017140341c64184505803810a410081d0140c0c01c40142c07800744a6162500f038498002e07041510800c1d000f1604110000303030b40d10500349201740d4000e200c058900c0244034808c030030703a50044640c101215680d00c1c0ca285220f88002c01440c0c08960462400038010386131840c010b5120969a41c10000454803903090322426803150040700c0854900812406150911040c400020082400704030b005e880345001284403c0c440074119034049038001c042000954481e41d41c01c000c0d2502406d01e03081c2d0300c60410307034aa80444194810828030030390303401010404843d1005a15056290319118005d820102440000c61008224201ca000e025141329009054122084031031003905000081c140d46060030483c10561300c007000709000c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 748114082 1250 748112832 748112843
    0x30717090307060504141512011e1223070509090106030b0105030303010e060f010509041a0415120809060f0a02100b0a15120209030a060e0d11030d09020402040302060a0804 76
    0x10300751152001e80300c1c0d05c1140105045003100c41000c103290701d88441003080c204000c5103914100b001d800e90305c1c0d011550a07080ba44031300c0c00f208980242c6030301c844000002401044044901101c0c20b45568036594150f00c0031038104c003c040040c840703540701048000000d02c00540742135071901d00841e2072030007850140000c03102c19112200005043c9400000d581c103039914407800700e16548400082007444440400001d042c1304080c480540140d81d940b0541b10040d2034100b080302d207049598100812503d8100110103849444041800b89003400450741a035141d10060302660360002d20006a00303400352124043c642280020618200d5074041002011200428414040303040003c042102d4110507000d4581c09480301446000382a104941105c10031000e100010710b4000510040f03400d20341e920f00299009070f2220b55174845902e082180610780241c4e850324806920400c0011501da1181a1442185980390032440b4299038486d81150b0045034018402955640a600e02410941084405403003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 748115332 1250 748114082 748114093
    0x302040516020d030c030f0203010b09090108011e0b0a050d03051c09171606110a1b081204050f010519050601020106241e0203031909050c01050c0307170903 69
    0xa10244041105404103607802805600c034007143c00310b0080c8194005403041688505001c0400c004520046d0301070309906540c00d60303504c0c200c81070005019060b48001074980c5400c1c0440c0300c0301c40841c840441d00c00000c0d00866804001c50020354041c1c02c50300510391088200e10881c08068208004001c6a890141c0c641ea03030403158030040e011940515400380c28860603007502150350004100400400103d454000c1011101d9111754040311202703103000c0e6240000203521200140c1001322000954090100b9007040f00c4c940d52500514050181001007024018020a00300b050a00204850300b440f40000c002e41c0c90800048003071064910801d003029440d0002007401035106019203c03d541c074500200c44050700207084803451400c000c0c4220204416500715101c02130746184142e0540a0a0340215100e0a0102461107205912620340d00c03540c2c03501480c0c20010707001040701c4010500c01d003406070f210107885410500f0762244600c0140013101d42001002c080540c40c02030b218000c000c1e01183d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 748116582 1250 748115332 748115341
    0x306070e011d0d0b07180f0609090b0d0b270c0108010b1303080f0c12040801060506130e06060706020d060e0a060b0d0c17070f14030412181203050403020405 69
    0x440ca1020b1102e50b411119510881021502c0307250341e60b801c01110301d002c445002c90740b0b4100350510100e8000c0240c100003114100120380d80044c4240c05880c4220041000b03483c8400050b00240007980000d1115000f0800145e030f1142c02e02401d130540c200c1105e1808100444a0780c44d8031a00e0b1880b0590100c2d01450010481903100c80c103864441121030707080b0101e2800c540710a40c3d01d07001082c203412540c0041000b8400310501b80101428000ca6641480c2c4881c02d20111600b034034000d1704018003d140c1031103001038005801c41042e040758216008009503840303c60208099120740f090180082d800010b00074101051030340041e0488004040030441912680f01c100c0654226100e40500e041c418400c1ea034050025502460581c0414184101405203000004090200855460f03010404c01d0824108643c4c0001306000c445866401c01c2d8238601c2c081d603a0405e90800800741e4001c2214a00694140c458208465006401e008101181000892600410507402400304070b000d14103100119 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 748117832 1250 748116582 748116617
    0x190614070c020406140906130b0a0b1b06070f110a080f091002030f07060b0f031f050a1803030b0409050f013905130b160320060a090c050306070e01 65
    0x4a0b000000240b59101e16100e1104000341d01230580466195107640da10b103c41e1b503903101d50f419001403004408658440d5410407d15410031403180c91103585d600005c0400032082d0b030001101f00303009698200360215000c2054841d290001e039820090410030002640701c000e15807500540141d47c012200b2242401500700d0032a240d0060701a1000703110014000c5500040c0c0d982c1151441e14400f9100c80400c0c40f841d00040d10b040440c40d0307221401d000900ca10030541d0254041e40e5445407035a9414000c00345800c40540305841900300c00b0702090b0f544d0803544616a11a00000041d41c3c00000700e413044111154114002d15001c100e800a01c01054000d43e04c40904240e18044500112007020341d100704450140da01c1c0d0f102c400f1120010210800214851402101401d0480c59180003400701c0c140b11304d0068040740e402f03400030010125468064961400000744654883c803a410007003840703103144c0381c40314003205203412141d4540241e10402c54602d50006020240340c00907a514600c0e01c1040b200e8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 748119082 1250 748117832 748117859
    0x909100e091609020d23040309080c0a0603020a031b030203100509040c03031119030e0a09050411150702031507090e0906010b0a170f0a0c030e190614070c020406 71
    0x1185002e140d020000c104095a81e07000d01141550a17501103403021000c2c44007442c5810b0401c100000362411014881071503408050f82d40585030703040c000c1448541d10000106202070510450f01010f0b000180c400b01c0f684642c10901103c80700315034941d01c00c585818054040d400490f2083c40701c1000410004851074940d02a5005a4004e424480c005045860458060b030326030040501c030380308040c0603600c80c1e501400400e01d010302a0303554a080620042c10810904c02a80c030500869060400f0f000100390350552444001004540140440c4402d02d852140c5009902d4040d43c94007494452001c407007281901d8910600782595129062600c6203404802c807030041d1030030580381d8480c500510010000d54000c1072035084d603090480c5030070705039640307000022000c59100345d030342130320400703100c900c0440d40100018444c035814140412240d0900040e82c41c7c605081c242084410f84400405004440c4d02c044a500b0b14072441c2411468500c001800c0100c503120101c2c00782e40343c0a00040c1c500310741c492 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 748120332 1250 748119082 748119103
    0x6060c210917100c0e06221701050106020d030b0112050711070608060306060328080f030a020c1c020c0f060d1422020901142b060e121207050909100e09 67
    0xc0c07c4c50304e0320240c01c00000c001003400e0003101c465240401d01b60f000c2c40c43d107520159041c0c00803134607605101c8004d0801d04804440018941091b80304150340c0e0b049210100c44140c0584006420703075074010203d540200841100299004d52080071a04030b52051410344262020350884031192036140c00d06595180c24280d4400b018040a00f0a05000488500751340560141c076105040059484014010364000c0d28104483c540c00201e51090b40018407030007201e42e02990f102e0b450b14828203406515100c1031340c40d06101c1c90181d0104441680c0d00c01c2602c900e9030090b0010000514000182d0301913140c01c2d54000c021030014109580d6444070440201607065000d40000c0140e41390000e03080d015013182105035841034903051403c0e5100001e4004840300c0c3d4169240c149607100c103052290840e1190a000407403508002c140c45c6400143d0300480b1001441c17a02141070075034a032003003200c031806401c01c410341c001100000c0c030802e40220380c0450107480c6004d010302e55548808210550311402601c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 748121582 1250 748120332 748120339
    0x80c0109050609210f090415031e0804180207062c061e0a1d060a0b09090a230d0206010611061312090302190906060c210917100c0e 58
    0x4e0700700030140300c00005450341050104201d800c0100880c00103041e280030810003090700101d103c2c200140030081e43c0ba0398400084000305032421055403155949445603000300c251800c054902c540c0c0001150713044400b000c0d0014070030896241d980750850322000c070103940c41d24121143c84981040d0701010904a004609244410802141c100d44024080500034903155a1a96403019030218840280c070f400340d00b03c0f40c1e04c00f91031030b40341c2044410304a41002c00040d0040200301b0401a6100001032000103030358104154204400c6070603071024954900d2240104c89014200006041d40d4002071558180e03070080d103035900011140c0700c0c626034070300c0216420a00003604806450104200c502c7e440000c608501d464544142c90303070040b440d4603001c1b0040801c80050b41a0401819104d4881d800180c42140350400c184603c41d02c446003020a48480d00c041903000c41c10744403600c1e00030340b02d620082c42000001341c0050707c480c400d207444061003c40501c502d1306046070f116030759226103450340d0a000000c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 748122832 1250 748121582 748121623
    0x3130303031a030609011b030216060b0402041206060626150102010e0f2a0306010614070c06050c011508071205010605030f0d030606030603170304020409080c0109050609 75
    0x5032021405010003190300d414450080c859120716803024041503108520284c008030701150017404508002d1200c0101e2820580b041c00303102464803510003007090140d0090004600c0d85040700c00100240f00d19030140d0039010b8848a0f200030804070b908607404803041d40c1c45a10013040380c00d07044403120314041c0c1007401140070f0f0390014180f4072600d4140c0c82c02d242c061000283c8071005460503071501b40704035032501c070710781c0304e5a05500c401407441c100401c00740e6940c0340c060960182401083c0e41c1c0406000398010b0000b2150f035000b081050fa002c1e101e56a41208000380e0003a03070350101074496444100b95840550900b08070451040700d045040c41158100c100905120b8130745500e2110310881544111000d54231148005116a0200406141c42c2e110350081c2200b902071180240c11180a03510050505007018000c0001c00c403440c880044410f038948440d035032540d42d480000c00518000000808112000c134085a650405600c10100c10307200d00c1c12603031191150710031240c3e5044450100702114204 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 748124082 1250 748122832 748122839
    0x41b230310120f0b1e010504020435031204140d02030f0d020c06040b07020d02010e030d0218150c0706080103390803130b180603090a020a0b0d0e0313 66
    0x50a0902010ba0702508014110b14100c0c1da54568195040e82c3e40a5000304c1041402142d140c1600702030300611084408500d070500c0c04986a03680341c8588440d103802503100040d2929030130280170000c0d40c0c0d4030300300c141c3e1742d14010803500c1314200d002510305a51030a02e0fa8202886182e000030079120130406074000b5401d01030712092300d480c2c96000384407440940d0b80a0000c03500030351040103101e0084e44030325000c0e03282d450641c3c00280307802031075074030034045a0401494480320705010044070141e560341070700580e886d00c45540303100004403000405030704051480c400c0d00d05603400c0030150960081c0601a6000159103041c00c0305e903c0c3c82800080c0a0403c08100407103d0b00c0103240c01004035044804205641c9040e0601382a8a4919407298015400015401800080350041c0d180580000040541040324070503600c44d08681c03215001c1c0c0640d20010200321740e401c041200c11039144d0300501191b03c0644440c3c0b044043d4010041400c1000d00701521101d901c00d0110548110108140c00182420315 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 748125332 1250 748124082 748124099
    0x31a01080f0c06130b12040209061c0f0303110a0305150f01120203180312071709030703080907090e070302040b0907121e0e0a0c06020303090307060b041b230310 71
    0x403882d40c44003840c8000da800640c1c85c111401030002d00d015403c0c1c1d88114941401444030010008068920520780304101c401c0c0003407030030011505583c1107401d0a6103081646000e40040480d401c810030358150109210b40c01580c581c014910880300d070902e04203001c0301e18041c04500d408030086d46000c910b00d2a4034000121035680a190302040c081d02d000d0800384440e000134115800210800b6024440350208426250884014107000070356603c00200c40c500141210345a0295141c010204180c0c040032030841d000800c50345010700003121040080d8100d140a083ea6042503100480c042da00702480000d0a03d03208804500c140c0842e202c010902d1144103500c070082032509002c0c1049110084c5005025080b4450400c0c8200620024905a009030031300c012916155849102154820020020140004000d40d001035520210124880c46100c0018010381041d49042c01003a200840e40b20038030743d011800e40c2060b00e8110711100b60503211080810f4a100446100c500340c100c0000402c00041c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 748126582 1250 748125332 748125337
    0x501060f080903070f080d05011a040302102706030509060c1e070c030b040516081b012d1b030e2b0c1503050f06120313031a01080f0c06 60
    0x1000b060580e468010030356981c880e41010100e05031014800400c520320714100d1032080385d0162903130f0115590300c40c5220f600c0b003640e88601c2c0002801948a04841c8005a004040b0300c0383c503068507121310010716040d28a00216000d2032040360000303401c14011902a22000c19180d000f03071156202c4d10b2615204004c00310300503480c80040841d511301008440301003040d041c00b200c080c500c220000300c0302c7c0c10942800ca02d04a00308001104080428004000c0c3c840c00103444500013080902c00100001d0503401038444484c07506203040ba032112041f100c0c80c5030050601303c810861843d01c034400c0c0940c4a68501d040e051828074010080746241501c3e03017642c503040b41d18084840310182800c5044800344030340d41c0c590a203070303104440b5284031880900c150318150f565407582504500d82080a407800309030b54280100041d11050262840707200403001c0072003c0c021540301745503040300e0048050703880c940b000d000e5140c800f520032102c3c030000020508820110721840301817007080081050100b45000c000207035 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 748127832 1250 748126582 748126591
    0xc03050105210a12051c0b030718020c0f0a0209010e07020a03080406110c07030501051315020310031b0602010b0a1d090f01110711090f011404090c03120e040501060f08 74
    0x10321440061200159840b0a5440c03120b0740c0390750b100e4440f142c003909044502c1131601c6c14a517460801d003a0481540380083c40008903880903268038503000700c1e00d200c80700034800d1001502035400744084003446500e00040344150944261690a000e80c2e0390240220561019038105c00180c000010032008a8070540c0e800c2d400c40d0254400040d120159501008070b80d22445030402560440601041805400c1c0f01d0f59502c0704008820b6501b1640300c2e5200d0080c5030b4040c0c00210a5a80800440c0014000c0110f80000d95070009806a80c080400903840f205000c910600300158281501e0b44400d04000d80288101c0d001d0140812941c580881c0304942c045004042c0461840340711a00c420301c041c2401000c030195080038100b9614556410300400010054002e1402590300d502409400c5044c8a030f03590445400000014041d80e812000801078109440050501290484040148030542181e405401c140d82c44040c040c1900001340001e0b01c0c1c0903c03611000c249082007481543d8020000250f00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 748129082 1250 748127832 748127899
    0x402160c2c0c090f0918150106140d0608070e2d0406020304030c020303160303060e0106020d2102030c090102010e06090c0f060c0109060b09070203040f151e030e010c03050105 77
    0x54103000002c40c10305c200071a60054030004014011481c55000c1c880160190981d641060896040010162404010414908007002c0015a00903802c04640c009809020b8a00584103242e40c1d8121101220305e051341c003101c0b00c1203103041580400081146403c400c802c40e40700354181b51384a1701c80c24000e420090080c0d013070110007109000140d90520081c40e003102d1001e00b441d032046444c00c00030100e60298120410403140d841c018014150001900741001255182c00c1e00125812250200710039000c4080303041c200c1c004014132041441c0c000c05410b44110a80c001c0141c9074201000b660703142400e40341c03514640c001c0240e02e449801c0500647c2000840075001c1031400b0b12000009086a282c09001e0f40c1080e510001007800c2e140064449030852000d01c011801c0600344204070010042620581e40981503060b125012240280c00844000d10096580e0802030203801c0c000e409040d2410959140b540380c01c01c8840310034040c1c403076107040ea2800380411100000c010002048205c100d10318404 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 748130332 1250 748129082 748129099
    0x120a09140601080d030e070f030602070819020309090a140a0e0c031501080c0307060522050d03030f0c09080c0f010203070507080a050c04060308180402160c2c0c09 72
    0x924403040100318002e00070742008040e110102d11004048401e0001401d090360840340003004070200c85030f280c1c401c3d03e82190b40140d4540940c5042441e511408039080c00c90b10744864010806038012003d42041d00e0190394804050352501389101c11925a41c04070749403002008045451a180750b07018124007214030084420345c1d40c4840000c0d107008040e25400100300034000042c041c40c1c0003441754064440b0150000d041903428014090920f0045103403074802600300895941000c4081440c8000030203001c0d189a010381085c3c10001c0142400086070071002d07081281c0c542c0302a109802031b04c111001f04000d04080c0c492402007008650400440754111302c0140103000c0070030400d0003000c0040c00034000a00504801e03142440c1418206040a84a00d1070300e90108042622101207800760010501b48050310283c8a000500070300901e400d5842c0349001503d18003c000502d0010401d03507a4082d1041c941d000420070780340788280c0450810000d115003801140c1c48800110241000110007003c00b0b0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 748131582 1250 748130332 748130363
    0x127060b040b0309070b0a080a0b151903050f090d0804050102070c0f231c1a070f09150e010c0602040803070b0402010e030a17070213020301090606020d05120a09 71
    0x9074000ea00314039a03000b40041030040c40b2000300aa480200040072005080070a82800074140320002081210440c0d200c104d605419907402c40307a845900c1a030344a90740c0343d0340120000b4554003803441c850b0340441d2030300c030100b15124520682d851240c84250010000c1c60041072081325504400780c81102d40313640038804540020400312101c006400c08260381d0300b0480c03a00d8209100a00c1c001242d4030400304008404402e91941143c036841600f0002c09000c000200380341480000780d205000740c544400d04810b0108240d48402c4000c079400003940c1c1d080c0b0480c0ca43c1c08070040b1003900b04202d0301240c48151401019400b034040c3c0d003089400344c880141419035540d9101d0031580007400485000070550104011980c00001e00098000f041e0000c0c2003ea03583d54a440c0310400c4203e4081c216040841c488045603148142c2d412920410b0f8010f40d02c2e540c1d159401e0010b44074900620015025240014420350312440a9440c0c000101c1d07582d05840d10356800100052140728001e07070380710b0318509800303 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 748132832 1250 748131582 748131599
    0x5060d0207050c0a0305011506080c040b0306030a0204140108120f0301150908011103040c0b0313060f0f060e060a060f080f0a020702041a0f0303070317060a0e16090b03012706 77
    0x20b000440c010000851140c03003600d807003003800c80c20341c0001d818000640c1c180040c1c00254070607633003915030305190103a41e40c03241c800203480c04940b100c0007503115007017010a1020390440390959040703070008402c070764004001d4042c280c3c40f409944641950b0031400d20041004003030701030b01074007144c042d41000c1420369291604c150a44502c0780e210803140f10004140402c0099a001e9580200754440c8100d0641c204a61a90302030a81c0f803c000c2d112035200c1d15013070305c0c1051552000118070010301c02000465950517020842140c2100c009100d580d11082c0000c03503a0080c0300f0b0418002950380c40390101e50301c200446e020480c0150050600741d50a00403400161241d01c00d894024111004115500203040104903413080c178010a20f000350401d002850002e80c00087c000c0f141c68076464035010542c0d400000c198400d06c194068000341003e030051003d0100c2c2c1c240c040c0a0007000780e40381140243c54030240c19051102788038000704250060781101003103003100c41401c1c3c4082c82540110303030555501440e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 748134082 1250 748132832 748132849
    0xb18061003030e01091202100e1e030f060601052203020d03020303090708030406170415090c0801050f010f0b0309070b0406021b040e06010501080903070501141f05060d0207050c 78
    0x6680d00c0022140144145074200503204900c2909280044403d410314044810445000b04000e0240c8011901118414019403881c0410480541800c2007004003440781d16610460020860080c01140385508500074049400c0344108010b0b1520f42c50102071684005800110714400e484410240d407000c4012394a040c1980e003454000d600945d2681801c00d030290800390245c2c811203042c1d008000400180350807614078441d02480000495aa5a40b424408022494a0012652240b81030381480800c10308101c04025180303a074008000c0b07039954200d03080c9542020b02a8600055204c03800b04000c2003000d00455004d0100019902610782c0c92440c00e001e90060f4020302c000d03801502c001d2201a540c010602c1c41c0d0981110103000000304503410503210034042c020941000110700004221010400840d00d10380c0c2c0c000d0080200074030807280720b42540780c142e80401c0f081d2440301c000c0c91502891035224060380c0c4024006071802c0c3d003029488000750702100003241e96014404007190195210040b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 748135332 1250 748134082 748134091
    0x92003160504031e1e1502090103020409022b0b090f040519060b011101020301031a1312030c110102032701090c080c0306070f021902010c1b0f05010f0c0b1806 70
    0x10041e13001c1c0558640f070b45901d014010481803000d091000f54011440140b00505621010100180e44166500041f40640b0480c0c0120307000c00d000140f04009038035031465100305a50741300c00d800e0310b0000e00d0310b1403400c0d120907038942c0d50b01c03138401c20120380d910303071100e444c0307074005103d9411148040d03c040c00c4050b240144001c10396003a0741c2c48491861558102d4002c1d5817101102000314950b40c1180e4803044d80c110781c04110008045403070300280002a14450611900e6041002956401c80809006028140e540300084c00105150f11b96000080c0500903603000307004a00300d0310400152042c00099050894100c500590349584142d000300f00c0507072054000d00408000741400d1246401410701d450b4000c0d010000f00304413600703048011940030034003511034100740000040510325400100c844042c9924082e001003502410000001003109041c02155648282d080790030b956031005450b00c1c00b11065501c08118454040000201007170314250b4448014141200c10f1034000b200c09141500444 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 748136582 1250 748135332 748135373
    0xe04060b01091508160908060f01140109030f2402070506061e01091502101107030e011107030602031e0c0c0106050d0305090103020c070801021309200316050403 71
    0x104991503564001c0614000d80900240303196500d43d0b1401c01040c94100800e05030700d005030414070400c520702c2640c0305030060800e9421a10b213414411454400820203114003401180007000003800c65025103d0392080700d802044400c0441074684811040e4070000002480100514030f01040d02c4013144060407549000700000d04180c94880c061001d40741450240d8020300d00c4642030f00311241e0b0b03c1402c2009075500d54070221a07249500340140d28060b02003100b501074508125103240c070107039070030003a040183c080c5d952070542c81042c800541300c01e510034002c0005034005082c2400400c02e00e070025038102c1070880c81c0c5c510003503036048403128400081d10703039000050f400210004001030074041c80000d81000c952140c1100e8159501800e00c1c42800c1c0e10314145034000c03a441c0040319050181c0030040003800001c0d51355680c44ea907203044007900b9028a801c0c480c60302c4040c1c0c01d080b00703503a4036000312030f4510384440ca10742310b4007095448071240c1e01c403e400b0440200000b00000c2d090003102140c201944 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 748137832 1250 748136582 748136591
    0x207080f060f0c1b101401140303090d03140301170c2e050d0204030c0e0a150501030f02130312021608070501050702030a17070b160c080c07030f050304090b031c0f090e0406 76
    0x1b0340100c1000d401a40701c4045402c024520100355036000c4210790107440c041343c450000d07104901c0c0c19501010b407124181da20001c04800060b00c41c1580340e424000d00b203448160b07404130240e0010094110508058800c06402e20400020342c519010034611821129040c002c0c24041400004016640300703030000c07200020f0b8030200f04901010313004c032603820007100e81c2c041c030140908005090342c600740e5226960406480b90100c404181c0180e04881c0900a01e500c100034040c1c507407d159414218698000380144191205000000b4101c61741005481c0c0c5c15000d094068901070045605170452102641d0500440b0505000a41110401c00e902c01c0000e007000e88940850138003c50992006014016110791180e8208000c6da00900c01241c00740c0c403c501725110182100101d142c811315410040c0409c5050750900300f44140000a8400c45481040174000f14642a0078151101044508450020340c4a140314a102c0e01601c2c0701c810b000101d00e0900c03105580c0c0c2c0302e4203041020a0350203640041e901d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 748139082 1250 748137832 748137851
    0x503030a0f0e061b04080a0c090b060c10151d06010f0912020f0301061e060f051606050c0f0703030b100c0c06081b0307030c030b03010204051c0804030f030207080f060f0c1b10 77
    0x2270340a11150700c80c0c11034030f0a08002c40c11694584a5854038480e0302f4151380c0b0112080355a904011860150103101c0226101c1c00002401e04030950042c6c03050740c0441c454000c0046140e2151020400b034070300149882981c14078682c2400594550914415419501d4000126120350030440800010480303400041916107132900203880c0810071901c08040080410510024000311204a101e01d0303403100f00001c017655154440c045c1030007016004000c071200024030100745503258002880750041241c03600c4050324070901c291a80b04408200510001c100310080100a00500c1c1036584140f03111031443c02c0b580c5150310400c2590040b40c030b40c004240e0b903100d1070080c00d50501c2002d0b402902600210311b4a0304003400240b11998421b5100a000d162005c510108040841618002c0d41c0c00950100325041d1032501039150515402000f2032803040c01040750040c90001147d40c052401c182c81c0581a0301d03070315003c49050744403000764200c2d241a403110440314801000800d01405c0300300c90003e0041d84 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 748140332 1250 748139082 748139099
    0x60a051c150e0a0b1006081602160602240708180f1e060f060112090212120306090901021611040b0d050303090717030f0a18030503030a0f0e061b04080a0c 68
    0x8080d0111729040b04c000000e01c000c030f4010010b5500310308051401402000c41c10303412450803030b003400142c0b040c10031140c000401a80000c4e5250303400d0f031303005c444c6445a094a10490b0704241c0c201d0b184000640c000d0007081400c0803496841c483c0c01822019a80c1d28503803403044e1031034038843c05020902c0070f4040f40b4200d03004100b07000701500909000e44c0c0f242036041ca040000c00c24020f550000201c269500c004404541d507481111100c00d15280a80c2c200320b02c0c00305680600e4008070307080b600440360302000a903100018422212902c04000d04070002c0c40203070312100041d500e0b4405054010344c0e100d04225035681ca9002e890304c61f5101e040110354918000490909002042e407041d0300e25201041802200b40010042d607030181c1246512544841071044101c6501d0a04505081000309010000c81400b4001c00258840ca11a40f000c0c000e0040c00642d03d000c43d02c402c40002d100303801140105507145c1221141400808082d55046e0806494458990404501140032990300801c59401c029204 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 748141582 1250 748140332 748140353
    0x1b0b0f0712020703020604110a080709091b0308040303080612060a0504023303070e21070b0301030206030402040c210902100824030a0609060e0105060a051c150e0a 72
    0x1048141d05508126642d03a001c2d6650a01410050150b00014869103003901c0b1a4030090082800c50200c4e03040790780d42d1024000504003800145ea900c58070400c01358618481c69415021a07502c00525450f261442d01c044901c041d02a0055501503542d0b00412504a41005418090141c09000248504162040100c40e000e01c1b0a901404110039122051a0300990b0341020184007404000d50789548098080311002031902403180e01c201200a51200c54801134150002d0b90b03054011260501c2d152603404180d07000074407000754401d404000090041c105a000484003900a0801d0f40c444060914000d0000c0c43c0c0d0407501606683d40ca101400b07501c1d100c150510145050f0a0034402400c0c1001000602c127460740d042d042d40d05011008000035142008411440303500140d08000107903040c40c10781c0c040c08041d85103217819820200401c5e01da2415400c12012103800400032221b04419101d608051703217031898161100c051551b101510101035004c0c0b40400d41030000507002c2c2c072840d860500c2048 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 748142832 1250 748141582 748141607
    0x203150405010b0a11030c010912170606031f0305011a0901090501122907211506110a02060d0c021902091503030d0c05040513110a1b0b0f07 62
    0x1182004010042400c3c0780044481022803032600746101e6241c1c40d00c452440c031504022250643c81c081c00b42c010302100c01401c803080b80d0103a4880604010454007001ca0400607100d60b41d005204002059251922944400503030030100c480c40d556965036100e00742100c08603a141c5400d0341c03944901120f1803421011450161440c00780402895041818058040810340ca000b007058001403402c0e1541404c070088030508060f0341c1c42c4d11001e031400020007001032566240080d110200c1001807184405540500f250b410007c9100c40078051401e10100ca04410380b000f0302c1c407180203540e406009a140e00c2c1c02084070581d015000310b03018110b590b0017482c0c0605e0803600d02035080044004001a41d44540003500584c80440031a1805070f18000a402c601c00c40911003d40c5107480112000c054101024000301d40048400c00c20400d2a42804801d032128610166a20031040008215403801040300705105045062451030f540f42a03541c42040e02e0042d10510004081c00080150b22907020710709800c1e5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 748144082 1250 748142832 748142839
    0x10b0402030114151c020a030c0e090a0c051e04050a231e0d0308040b0606090307032604060201020301290304020d021527040c050301090b130f020315 66
    0x31580360000ca40011500e460f080740c8207440c0403000340c841c14400e03c25a168100d45405040c410301c48007038040c00946c480401720b0003180c140711007030100d05d0040300e400c00b420030054400303000c4d981c402c0b440d13000401c40000b01809100c014407425000082c65001007048140030805c0710741d0349041c80304120b8284815808441c116040e0022841d540b0304e84840f10a22000588214940e03600d45900500716081d6207104a8011200c1c4141c642859880b0503818055402a0021686a2209010700c13000d4031036200d030540c240e800f207402000018080f6456482c0c40c1c1c5034203410b1001d28142c0080903000e9100d64005030050390007100600420710b03002100c120f006840b003010400104001c55000b0b0361701005002911075048d07041070070300b992101146e2140060100d11241c0e61201103000a151881513003801000c06c1824035196605402e0a208005038007003203480c0c050960307180140c1d0344080c1c40b4030150240c02168001507403440042d02d0140044120100c2c3c805070710791501da0344410502c00c03042c080300d10 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 748145332 1250 748144082 748144087
    0x30103120e010909111b070515090105160f02040b04051e0a0603290106020313030201050702041d0102070c05090915040f02060a0923130207080c071511010606171f09060503010b0402 80
    0x8607035035240d8100382c0204070b81d03009c0c1d4941c0409001a2458001c21000400d8500480d02181c20007140282e0240ca192003101c2c00c0109400310301c14070040328803c42c4c0d0f242c0b0742c3d01466803400c4a402c0a1640a40c0000144008030b0b03065125554080d107000c0040030700d43c426554120058955444042c2c0c07234090221071000754100129540340b910b8041c00340c81301174148400001c843c001d41d01c480d00182000d14011510780c81c1c0c01d8681018034001e50058005507071a00480c074000c10b040c64520300721030244044a00401d6100182a8600e0100c00007030700494240400ca45944010384a00c80509503100d050780710490043e1030240d00d02911880b2244405100c000908000059654420002e200c20480000180c541c0103903d0301c440d05110708080298030b40709039074000403030702c0c0f504404004007549540c6010a0305031036140603003602e40501032440030840740c0c04061341d4002a0404a6444a250070846988043d001c001074a008815004945029107800b0140301c181802d001d1040e94840c150340451 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 748146582 1250 748145332 748145339
    0x706080702060f0a240f0506040b030604054201110a061107080c0115050114090f04020d05090105040506180c0d03090b03090604030e06030103120e010909111b07 71
    0x1c1d2a02e0004010002c05046080802c9428105920001030300701e880da107100035000c00e00c507480c0c1141e206204249140140150204d20380c01c00d0303c01c0d14100c95158590313a045840f240100009050001d101003130410301442101e1081e8652411502000020340b0178010030072000e80602461049034048030f0500c08010180312000d2000644c000c0c041d80c200c900001c461032030340901c464600c6940c801420b00400821442c0b00c0c004194001990700911411070701d15583c0e92401034900c5612041804d224402c18042a119420140e044225880008000514041650302031000301c49003035584442a0790b40780104030400c03078200043c1e034100031001140340114540640d490380e220446421030340a2110300941c40c04048c014081d41c005010341c03450864030303441d007500540e589860888090700041e010119462450a00004590589400200148204400c070b48251003294043c2181170400600450000b0307040001e10804900f1525801e2903a514a070f41120080c0992000c46110034070741020000f003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 748147832 1250 748146582 748146587
    0xe040c060311161112030c0f0601050307091104050a080c01111603020f1305010b03160903030c02010302031902040909050c0406050f090702010f0609020306030f0111090105091309030206060307060807 88
    0x48669032203c00c0d151456001500d00071020962081c809074200c982210307080808030300840584a0030381220201d4014a503582c1c80c451740e0380001c3c8035843d015040440140036543c40e83c1c210401603082d12041d149415030b1040407540710031165011140a42121071102c403550307405038650021003020002005150b62102c025000c2d1103252100a00c110800c0c48107007211380b6030480c4a1032079085090108001c0d80e5883e6003030030b294821540f020200c0700c21381c103210a1034000c0e440542500d400d981d95407001d00c002c0d8019002544080d0040b049410810300704144981e441c0001c1018200401d40440e1100052a082e0f181c1441010380920403400c040c01803285465011514081c040116403d01c40317900c0314070b13040e03004000e900300720480e242c181314000c0b81101c46030700158001c0300d042d0100c542024582c84402e00700c0b03210303001003401c1580400816207650300c514040d22442500911178207907140c00c120f0120031151030200072805a080f0504200e102d00c2e00b844030301300508107407c01c407585107406c0a00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 748149082 1250 748147832 748147837
    0x507090f17100e030c061006020717011515120e0d0323040606181b05090102010f090524250309320c090114040b03070e040c060311 58
    0xa121504250800000c603281e020860151942c6030207504001040400d032035152a944481d09141d554466800452060f00c108152482121080e81c041c003803070307400e24020721003615011018107550f40d240d45a4a18842428403214010b0507290030751505100d04e58009020000250380c100400341c6041e003200a10711001c00c1c00400314809140000f029101e00d000428010f00c50490b10041038500020030081044980c001c0003a6204100c401c80316626203445002a40c503a2034514483e078808402100e0701d1805440500300c20a81400003080f101c1c04210460101d6034070b00400d5035503500158050110362901402603d0300c0c8855140b1f2280ba00c0d0142c0c00c50700c0c1c404484003007014107100804280c0c0b041d00ca039001d0201594840324041c0c502204416038243e032092000880001c1c1820000000035140000303c6c01041d503005042440d81ea0f2821984682044c4e41c00e003260f1b08070380c4038120000d056600b40704401c081c00c0d1081010459040508240b80142260b420200a062030f1030300c0203010030410300a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 748150332 1250 748149082 748149089
    0x302090618090102030a0609050603520b0c0304121506080a1101020d0e010c020a1d040611030c07080c0705030d11150114130b1c060507090f 62
    0x45041a035110354010031420070401000002240c940414000b1440064000794080c11351100706200c015100c111810032241c1c16204641e055012040c4d001d4500301c4202d0110081003411401d250710030280704851400d440c14040c200400c03004a40480d00000e0941d1004d0203024000d00701802c14081540088c1c2e6440b4a00039440140d00300420a002c0240080e8a40b402464201c82440400e59848100b070703a5110000c030442d1240c1485500c817015510015a145521502e90b40300c202103801900155082003609200741d800142c0e0f0180452048480c45d2001001aa8602d018144d0300e400d0606008445003c0c060b034030124020028400c140d8902d00503641c080383c001d07028941c1c5030201c4002c50b15184090340110f030503004868075000656049a400e00b0301000d288281d40b000c400010504002c42824082e10400051034840c038402c81c10710050a8041d05101c8500260321400d44001641d00c041100110a52400b8400201e0400c00d2501030b550304480d49041c540f03031243c00c109400c0110b041c10300 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 748151582 1250 748150332 748150339
    0x2070e1006050717040909110f04090b340c021804150203090c1201050601140f0307050c150f04030f02060f0105011202090d140d08040f020103150b0a110f0706090302 73
    0x25150b00610056130880d402400256410802003401c1c1c50a0031090004400e1544140f00c1c05480405a0815001d0904402d5004100581668039491440d40c140582e805056820742180c881d0032180076045403481d104075450703c0c1c2010380c40c40c43c0704011198011414846900618400b4080050112025054541401c5030b015032a0355460060720300d0701e5019215190b01664405100d801004198410f5024450a0361405807040586c0c40f0083ca03403080c6880c43d4084103040000809051042003c1c0100c0c0340350f034080d03449030303442e40107d03030302500c0180c0d000b601038601a4103100c200364000302c50300c1e10500035001a01a52500404901c01c10f081442980e043c404d4440b080c0c2207000329035044901c10031000341004a1000da07420940110304550f82c02d00c40620500a0815000d40111050742c4111f0703100010b60441d4010ba03004501070701c60079070b514404c000c80c08401b1500ca800000070b0200010750783d44640503044117500f0315140c40c2400d54071100c80d030840c000c00c0c04601e41c000200e60a907031b0182e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 748152832 1250 748151582 748151603
    0x5090c01050c1018150606030b06040e0408070c0b07110907030c170403180806040c0b030402130e10090303150e010807050904050f120403030207140d120e040c02070e10060507 77
    0x250b240c1c10984c000403001048000741409511748800242e01c12401c0d5503240e9010401c03026002c0c140b200d9449a8001c503105007202c00000f0f0005406a0300400407603118039a02080241d840100368103540101c402241c8078800364107100b44a04000f800c1c9a17202c0e0b141e103014403000b82d40300e1000e0200b0001ca82e000340b2501e13400d00003900381801803c0b02a1003000040d40c0b800c00b01d50300c2540b261949401e503401c64008007103600000f094501942a00e006580086c4841c4415820488800061140030300401081c0102d03600509449440e1040890041c042d443c00b1030005034044104c00c102915070841250108040c0040c07102c4c103400241c21090362421769006c40c0e9a110750500f2454402080c4032035440d4410541c08070340081e10a0080c20450780300e42c00f26250036480f0b020300180f9140d5407400301c0d0414105091040891087c2d941c0346108020390620713645880041c1c0224080c0c4c3c0c9068627400251340229410454040400441d645c00401d82400b0340005041c40001485031045100107083d4881c0f8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 748154082 1250 748152832 748152851
    0xe060a050a0c050601060f090801020c15070314130b06030105090c100507021917070b030c0a180308030612011b0513082b080907170109080d05090c01050c10 69
    0x14449440ca003d0b0000708941e61380d81c0d2610014042038812100d8400540e150000040d405014000c5c0c45124140902801d12051043e1240d41400401400b0b5001c1580710311802808001ea1000f1078007a42a6240c18140c040d641d0070460148003019003443d02a030700d40b4081207655040804c2420040710308488081c0e25075440b4104a4076401580c034069841584501c0c810111241d0022907412038031010f10764501c004030340e0704a545400300e40c031400d02201c104200140c2d407102e0010060010b090b15040c2010000160b4002d1039041c1166082100c2c090000024054186088a000c0103c3e0720f00d80300900c030412110114450080e003480d60601807010106004280012098442010b085180308070340e14100c1c024010744902a0251050029038100c1c450441d21510805010344030303008840090109620303042191140c04640c02c00d42045540c0c940c5048006403d0400520f000c1d1104030004c1080d040000344541041150b0700c02c181806810814100301740c0011641000481d071191000815022 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 748155332 1250 748154082 748154087
    0x409050c09102d270303030513030e21150a1d0c041517011a0411161502070c0f0501030606120506030a0f0f0309051207090509250311010e060a050a 65
    0x420b06401840ca002a9401d07038841c10f0031001360741124000d603024001c64807000c00340c0012810a0030301500282c1017903503880807810207040e400c108040f805c4103401c000c01c1260f103950a050701c0f41c0411400910041c02d00903525000d018402c1410480341441001c00410324105990300c010240050180713498004c02a00640b102d40b001c03004101001d00e000b003903040901410f00902c00f04200809400e828014002c050903d407140080d81d02e001d007000c030710303061403045040200200010100c07140c0a0f00a890120080300c1d0001c0d200303c0e0322803102002a68200540820060681d40100d03040501e0704100700196944401940c521544d20b03500050a502c560380402e0a01540b072902802d45080800944100000d558180140a0107545c65107a00d035290000c1240d00280d800c3d58460581c0300c048113101d58201c40d031159401c014008205c07040e000c580c442035440d85882046034490b208090400f0810f1105030710001882b81c1c0f003440d105144040c1000042c0b0b050085100740d000b0000d020070075020050 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 748156582 1250 748155332 748155347
    0x5190b040b120312010f03030e09090a12181e121e030509030607031e0b04061d010810050705040b03190501030b01080c06090a05010c080409050c09102d 67
    0x1e8048404082c20502050303903079104003801c5107205440342c000507400c040403e8240c2035a07499030321129131129150800c000080090528955402840355010020301c007210041c500040310f0312005070700902002c0c0440d410000c0c0d844030700c4660ba4240100c404c441d0350002d12055641000040e9200c41d10340c00c09241d02c448184000b106400c411f40d04505140d00000507058200782203084030381c292b5070091308a09441c450b0f4600c01051204074492080d000749500810b03c0300b01d0107007000551613540c0c981d440c401408464074000704800c0e00010b20100006110349030109026905c00d0180382443c10006049106a00c10805e000c8008000328040000048681b84c80c080104400d0200356103a0404c1040c0b9030b0300b071086007641e11506603030300314a0030804191200d0000040101101034a018015074000c40039a00031612000c0402001c43d03803800700e01c180c0d4000c1244509107501c1e202c407141404105010311801c0000e01c02142542072005030702c1100394805074600240c000c10348149940640b0440c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 748157832 1250 748156582 748156601
    0x21e0d0f11031303061a010c03050306030c04090b06041407080c070c0e0405100612030507080306040209090403020d031103250311160605010b09100c11120c01110105190b04 76
    0x40c000001c2c0701c1801003c244014081d68001d050800c03c138100c22508080401c0b0f8803e0b040d0114024011102c08a40500c001c2c550041001d02540c13400e40f1074100040454424030004c84200b2459018050759060038440c070402c00c02030310300440d5241419180504001d10061000c0d004540c00140311003004003200d902030090501082801803030400d8984180c0324074401056022052500100044078018001e00d06079554150301d071145044159180d41040350f10082400350060303020415188252a8038054904c91400703640541401c03d40c2010042c29991130950745c504a090900501418240c2108040041610300e075289886a906c03590940241041c54048641141d02084da80720711340e4a41e41c0310380064400c0b4000c00c183d80e00c0700d0070800c0c68015108030f030307401c029100f0080e201c0f5800740300c5c00365003039009201070b0304c01c1080580091280103d0345e400503070b103800c252400826941c03c00680c030702140050000303006502c3d0000400034031442c51072603010840d8940c1e15852168440e0351005818 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 748159082 1250 748157832 748157867
    0x60f0e04030207051f110706091202030115030b0f0112030e060307030e030f1201080105041a040804050a170606010e01050a1b02100302040509010b0901170c12010312021e0d0f 77
    0x104d1381d41604c003010f22070905c05c5800314a0080c011046c10348007086407000e8681c42e484613800b59080a540c6110b800543c101260550b503202c1c86001204054a0700400542c411003002d9540c1c54441500040c5010617805654681640e61b600800250840f40b05c80d0494019200301d9280d82e18107104802a042241c17a06c4c14501000070381450b01c4255600030403200d4000e50241041b41d0345c030221380d401c0b1072044030040c00e05403928540f02041c1409031443e0350010b000e804414101034985000603001165030307005041c2c480c007074455444403e03000e005c0107601a600b400c1c41300000005100180c840d11030b0241050401c5400070b1036082c08941e88242805403a0060982150100d4075078000d03000350b0060041c01d00c1185148000031b107504203001145c101d01f1041e981d11101140b080307c459a4148060140240d8820901580700140420003c030f60095004d1846c6280e81c3ca01440042d04150004100e0b1002651844c0141400d140004042d044540c5034074010070700c0031030810115020314a07180f1142a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 748160332 1250 748159082 748159099
    0x60c09061201082d0c28080114010b03060108060906150708030105090c0408030a200d0e09011d2a0d06030c240c023f01060f0e0403020705 61
    0x1282140001c0b959561104440e036082807a40800404e190a00b844440e48801d07484083c0164150400b03e05502e00180c0c507030070401920707030301c201c80211045c2c85070042c44042c2e41d035074000942c042c500080c6c0d81c01803001a1200c0d00d035003030550000703020303400043c1103502684403000480c1c41501ca8802c009a204501100c545c1c6581e0b40345042c1c0d01c10b9100f07204d034511a0301c003000802c031f90380c124404036801c6501c1031004518200700b602c400e482c6894046415040024058140001440705103c2e806080080d692649076403002c410401c0001881a044140803c1107006000007814846600c0ca03006510082e00340c1d169100b00c404480c0c0750354406003210403001c02052041031044280c000e001501d101c1d00c00039078004d8a03145a00700601c5a20100f0303060070b104ca404441e4890040074541e00007030000c0c00d88401198040181e000c626030a0250b84d11b01d001060450307501c050b100520f00c2407030031118004d0005038688100311417458268054180410606004901058000c11052005120203000080d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 748161582 1250 748160332 748160339
    0x110105040b0d06050918031b011b050d050a05060303090f0609060712020d030c1d0112060611190807021507020915100827210702010207060c05060c09061201 69
    0xb0007034903152180d02e018151600100e604603601c4492100d150b941c41000350f040950f21062115014801e141002c81c41d5a0b4800000c1200707039032039594502000d1a01c60070b03504e0b2607a005000440f10014041d44107140b5210a001c11640e021044503aa20300c00c84c0e0f4688140c6032400040d4080c8207901d505035202c1e0b000103900c01088410742905504100715000d46040c402c0308002a0b00f56200c00307084400245040c1c0c1d1031100da03010710158038201c84040c98880081511481007201729030854120f5000f00d580310b1501c0b01154810095031590079080ea11002031110950344043c054010040028031a4000c2d400c003948201d5603000750386100303800030000c0d2400d00b000c2480504070b1400440150080c0414106818030354020100b59014580d40030030120100f907050840040000082d0405c481030140c00b00603178480c5000c26a00241682403403009940704003520002e0f02c0e060701603100000340b00440e95240e000c0382010a0003036100701c1107a401c940d907451510014659105a00344080454050070022 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 748162832 1250 748161582 748161607
    0x9020a0e21070f060c12020316030e030f0703020d0305091201020a050918130b130f06060f05100206011a0c060a0b120c0d060207051c05092b110105040b 67
    0x80160300c01c000940d81081c0e16020324014820140c0180e0002c281c01000c0400000e29a440f021840507883c81aa4200840e0424402c1c0c80c00c40ca00055001410300d1510002c0c52400740000300002c035508008100c150301c0c2da80425131160340d100001d024000003103162201600c5100034a8100c41c1050300865030b8044080c4040c0c116001880000c0c050107210b40411851140109141d0140c0500d400360b291461070341d522007091000c002c0800c20380710340e07641c80ba1000900b049131500d50503100e608041105810b00d5010b40144100fa48050321a030081c28009070541c1e00402c01506458807402d41010200d00d4228020345840303007461030102442100f042015101c0d03941d1003550002001c8541c8814451f40301032580d510000e02400692103120100001c0010b0ac0c16401000680d1091040c1c0b1461400c0e4042da0f0030030f0002e01c4446001c0303900065182120f182c500c0307244030314009800d000442000e10301498511142c00007001820644d41c810100803d03030041c0b0070b460050003210b80745550b600c00c140c0c04 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 748164082 1250 748162832 748162879
    0x91203080712020307171b130905160909090206040312110f0708191403031303020f150106080402010c060204060320040e07180b1b190b0109020a0e 65
    0xd00001d800542d142080309268001c03280210144da035181402c6214100c0f06241260140c2041c1c1c9002c003d80406004010385805092220114002510107038138124001042d1407009041100f103144076101c0ba000940c101c0b021406403582c84200040004081c0b0114a4510950304040d000d50304542c10f80103295070190755190b0303041c03140c02610302c0741c0c445a003919516016409803400c150000c4989180305201d159994091900a0750701501002c0f40c02429420750f842070358041640c890904060b0309240d0104241c1d8101900800201020300030321034100f000300340601580d000c100b5810042019a031050b2810400c40c0e400440455880d581d0300009801041442520000c0d01f00c44040480c0038411a420b550860303400d58400d141c2130740d880804648550490103448400071241130040b0304003483c6400b03007110300e50406a0807542c0050300600c1d8034100324401100d4000d0800104600020300300d0b0034043c1160030f20070000d0f03100d40241800741c4800824502458106280194040800355030030301 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 748165332 1250 748164082 748164091
    0x711030c030c0a090b0109030606060801030b13020d060506180f1501050304050c040b030327120d09050613030b1905011d04020f060c011a040f09021f09120308 70
    0x11a8640c04548080c5900c2c0c01c048078001d40d02800c142c0c002c220380801500f0000603520145041440305031640d41d03035012a10320303410030400221110300520401408480c1035400c000740748030f0f032100d02c00141d00080e00c40300c8901e80204a15120008954941c88240141d00091141810384106140860000d0b424070012900500c00c020900381c50015035010700d0407203000b10340010140101100c40c10500c000761400a0300f840d014441000484070117144174911000c00702101d40703440e00340d01d0000104040b11072000070451194100c0100a07030466000301503a811150f0648086e03840d81000c1c150340c1e803030000c1039201402c9009402c0070013000e20403100351900c001800407030401259803201c41c07050700c0b0f03112425004400c11001003ca03001d864090f02c0c06180c40e00090695140c0711446814a0035520040304440800c109145903d174a071038980075031130204008010410481c4034940002c0c1c81d40702c0310905c04c21680001020b20f10118401e020501c050007020348000e20511040c0340003400c000c0200c8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 748166582 1250 748165332 748165339
    0x3140f07020715020601050415050307230a05010f1d0a030303050f1501140705030732030f04090b040b031203070f0801060f050307092705090d0504180b060711 70
    0x244040340b2080143d416071030019643c0d008001984c02d01040c80f0007040120044a000b146038000010540d500b00b114202400d50596562a219010001ca0002c0c0e01c1c030500751441100b00c020280440c0c1d90002000c1415555850120070b425410400002302d14101c444035038004403120b00110905406030451401450b40603030043c0a0768610302501040000700c0b003541e0000d80300c0110399102710110301c003800103e4060790a50303143c00200c0c3d4500c0c5202484240544904100c1c80c5210004940c0a0104050004401c06945410701100f607045007032249003d1f245d8143d030b54208589254640e94815005404050b04540b00e4041c0b0006581d000e400860711100000c02e124031507902cac1840340601604803101500c0303409404041440959943c3c1000300400100011110002044c05443c1e082031102c400d140c02e444a50004903c81c5420b68030010807401340c1d41d10071001a00f0300c03540203003140d04030b603040342c407003501c0b05107a48042c0080d004c0007601583c4040e0200d080c0003800100c0403813a1038480c1c201d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 748167832 1250 748166582 748166593
    0x51608100b0a0b1806030f01030213060b0d0e0102040b03040609141c030b040f050f07020f07051f090e04060501150309020f1903020306040503071205250303140f0702 73
    0x42540005035403196a085402448080042000c402000301410510151034000700300c13800305501281c4070b074000711802e40344907171f0740b500400c250304004450814040139080d05102450900450407a41c1c442c10350603150542d070307984d0700142d601c80c20350695001c5d01d200b004080c0e490030a41070042c0a0f06580310140d442c50110020325180201c0018010182401c8003021411103107400c1c401d4008100d081100d83c0c1260326880311507500085841001e1052501001c078045600b01080c0081c9000407042c40800d141c0c2c0300d103400b80000c0da02c8840c156140325030000000f04800e44000300f100d1288003944480106901c080c144070402c40d1070782041d810394100c401d403000c41300c059800440a0364418607001c1c0d00001113500d024a942003070a003906008a081082045161b03580d40031a01d00740c1d00f00d03402e442d607410103d1014200400d98000402c2009545489801c00c042c005200300085891084042005034080d00e250425020790003412810079808002d0000c5d2900c021001311140d021500d500050186 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 748169082 1250 748167832 748167853
    0x316150219050d020c0a0807031b050916030b0d0b0c031308031312030605010c1103010e0a080903060708040c060809100614010207080d0e090901090f050f010e030a1e0903051608 78
    0x8442c200c101c0701d07500010302303803d0301d0f6490702e8000c103001c40c201781207145044c0404107154503102000c42c094507000020700b0656102c100f00a0480340b100e69400d11500c5050f020401080c404104681c100c034001c45513569a44a1024107070400041000c01080003902004010501081102480002e8082c0d0b0004c1c6030018000b40c22001c071003281c06911302007401d014203140031800f0005960350200002d0000907040c503213016010310b4150600d6003200d03411000100b20060342000d01c0443c0c1c104005003000c010710b090030303642c02e01000428024401008411000503080d45020040c0e10f451303c200850401c911502c6607061000c8246486805001d40305109000496401c00284c2c42c1c80c400040d40e2b02c1c0c5104400d04100011020003400540c059074a41708804046101905260b030907a104034000c01c0c00e0300c1c0741ca1229084d100e59100e0314580750000d1100d140c000f5045042d018603000305e1452140301e4905000c1c00d42e8511804d4202604034428919082540c010003000d00042e0f44004044a114524 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 748170332 1250 748169082 748169089
    0x12030d09200901061b02030a14010b0a080105040201020c13090210050304051b0303040909050c04060605030906090703120e0301091a01060e091b070201090902180405060316150219050d020c 83
    0x2c0a100c0c0300c0028020b070003051030301007050200c4881c2c11b20003400e507140101c040d103c50300700f0174034220f00a02507551070594130041d15240c03030b0203001082400c00a01c2a440c007500080c1d01e800081091600440d41d071040c4000c0e140a40d8895640907030b004060546500d135000c00100340e90011030b0200c4107440703079400486e118500c5c10301d00ca510410050046140900b0840c13044040d09507124201e61300c4c81030a5000e030141e510ba0061034040e01141c0d031003588a1a00606103407030080050080c01c0d058129540900102d800301d041d00405180078100a0801e0f0519000710f401000b01250242028651180c1c10100c0b15114100504072105a07540a50100f8420100800514150f9554445a860245600420701c903040a004483d005050400e8100c0c1d0f145c5540081ea8031040840350300c0c58000002a40c41d10b000c0c481c072a0040010760003016138070760b41c03200c1c030700344046a00aa0075402040954195024800c00910310000c00e0b00b1141c100c550344030700e00715954000c1000c020303001d401060b8081d005404d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 748171582 1250 748170332 748170349
    0x60207061103100b1b012901050307091e0510020a02010810140424080102070309120b061221030f1b0a0305070c060c020303070f08011412030d0920 65
    0x303c0c2e02d04a4004240360500c410305661044818410304900002180d044800c00e10a4920700195082c0c12040707004240700202c1c1a01041104038103200003401444200340d4058503000540d4071218483c684681c2024000c2000e44c0c0d254807480d481075600c4201c3c4020395020403080c5a00d4403c2e00c03458002c0d00d8100102035107034109d011b001808101c09020342c1d0039140c0350f0001f0603000b8544060b030700100d0700040000c0740c46036260807903000d580d000141942010b80c0945040c004042440c00505003120941d84c1d01d107545000f4101c0c501c21030005601b0150384c142031210910b103e10804404142008110082d40141c108961120305c1d02c011200240e0f5000c546000d4000e400c005c822072518003c180075082e0000c00002d80042c0402074904403950000f80c040c0b0500810f0741d895002140c81e8940200d0003000d010481c02c0c240200041c12004207c3c000b280c441c0c01c07070051002c03562201c0741c040c140d01d064a94010300e001c1c425058107124180b401d0041c1c2d03442d00300c0980304064a031101c5050940500040300c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 748172832 1250 748171582 748171591
    0x8071b120201030b0d0c0e010816050603040f050111030a15090b010519090e0c0c0c01090305121606150e150306040b070e0d2f0625050703060207061103 67
    0x41a206602001580700b540400e044c0d007001852840101d08985a1682c0000560045140261070400500ca83c80041200ca1614201140d510f910542000701203022400007800c020a06924051558200142900110061404184140c0d01e0345001d0801c4009420040c2e07110141d424140c2010030740c45031324060b0302004581a1a01da141c4032a00c050b414644d018001a0410020002400315080340c2025025005001c2c5212050f02c0e0007456210354106058041020f0501030180d82c100001400860a120b54041c004d003910746482c540080b0031141410810003c20307081c5082d9000300c0c21142d09440c40103446440c2040d011a95803407031202c000018440b0626410703402040000c00140c0300a6515034811002c1c540400c0400480000c1400340c0090401104c0d2001c2202c400c1c0a40c41035010f00088040c6000340b42c0c0a100c0440c000714010b8880d02c01415040c1070b605010244010030965108961a031040c1240c880980e2030030014000d4000d10b00c102e030014100b564490b40321081a041ea03005 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 748174082 1250 748172832 748172849
    0x506030606091314010c030e010e1c030b0a081b09070806150712172d090c0a0303020a0b0f060f2404080c09090a0803070509150708071b 60
    0x4648078142000540c2c04002d00c42100e2002030303802000014140c1c0381c03001c1c6545041c00041884c19800c180a13054440c000881e032110780c5040c004007081c2c0000204142c04406c0314250580124401c1c4c0110080c041400d030301340d000080c6035800141c035640061080b08d104044c0091444254007401000b01d0400c1c250340800005500f080469498942054000400c100c80c0d1042464030a41d9038030b5505080e555a110742c0071403190402c8030800c00395000016441f150301c05885078481c0540650498071003000c144208412420000205144800c103c0c3d4250007500408800d021640ca2a000359560140e82e13003103450000725004141142c80007240302c4c1c01040024409001e01c0c01d2002030000e540d500c000e010741101c0c400140d000d010200d41e801000a445800050698500c516052201c2c4100c041d282d140580d0089007104003107142e010589030007150b5480c0255494144900184c040120074101d0045540006440d8080280302c1c0c004040c510303c01c0c2c441e032440514a449292203881184111080c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 748175332 1250 748174082 748174093
    0xd0203030705180904080705011a03120d06031407080d05040f050613030c080c010318121d031b100c050c04090f0501050a06081005070215040f050d02030913050603 72
    0x3040d0b07002d400a0010110104210f4418040d40f03000074610400590b420345103200c0001d00201030110038041c07820304070b41502504131f001c501040400e95461402d414042560f202103140c00c00d500180e00074500030750308040012018a031080fa2151904014411900244101041064414042c0f030039501210700850086880c14504010300145900c0111007010311090f0140220000e410702ca418000b50418500525401c289080054203d440e82c0e001003c1c24202621680000340c8050b20300c0c12a2822072900b4014001c8821101009030498001c07264940144d448200802e503002c440c200c998402111803100704903105100303981e2840b40d400040d0081c0c02c100b98401306402c058003c0c005480c4104801d02d0700c4400d9444490850700c2c144d5250060a07256a001c10491a0801040800203d1203804004034240050040c1da1814104400780d585d800042c00a803d2040f0340da4017081250700032003a83d8030b04c2e208800007500d9a00c50800c1c9841042c0c242218443e412582c40340e5441520080c0c000c04 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 748176582 1250 748175332 748175341
    0x2010b12120a0f11010e0d090f0b030c070201110109030804021503130b060d0c09020a090506040e0712091a010503070f0e0c18060c0a0204060e070804110f040e1e0d020303 75
    0x12801c0ca800d030f091509000180c00c5407000c5010906c01c44201a070324070050110380100e40d9005008680e00c1d4854518040e01c52424010820100f0881781c000203015005aa190074510041e20920301d10402011a5441c090b1142c0a16801400c071700c1c4918070031a0f6146c8591442d4100c0c3c00280030a41e4040302d1146154148030014203070340e441d541c01c5407000740400c10314006c070b41d1241103031707052074100d0009282c0100329001403c1c0c202141c14054101102d81c6804c10303090040034071124900405d100100010b444500e5180c011943c444200281c10254111124000d0682d50b05400028170540d03009102c5d8190020fa80001509690180c415440d0003c0d840e0b1100c05513100c603500500111900314000c210b03011619581e001c001d017905055070019040018260040100300d4072543e20500801d85100c04004585500034101d542c4190301020b40307845c9000d201c0120303c2907089008041e030418036180803d8019000090000c4c80d492203881152881d902103984141c9074408040400090390007840401e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 748177832 1250 748176582 748176587
    0xf0b0c120316030e0f1221041a0601090e0a0b030f1903140c030a090e06060a050a05180301151a07020a15050c0303010b03011d011401120f0203010602010b12120a 71
    0x203044c82002400c4980c2c13846655142810054009050f8000c1400058401d0314030200305c8100420203c10520345c1c581d443c098860703005414003108908901c0d4181380008007542c0c00f400d13600300500b1640280048a10f85114504024020119454070912805051305030841000803908910b1103401c549a074501102d90701520030764240b50305a424481c040c4400d00310342030108050b0002c070340c181c0d0b10816000d25002c0840042c40c0c01500560003900704000340c44072107400c14101c500c01c03065440d00c4e44d40e5100243d02818040e820a9449a15509280c0650b90401c084540301c0c040c3c8408004a41c00842140440030b100e2080a0000b504803013017000c104040858105600761b0101caa04040b0b00d072810006001307055510907001a1007000000c0010b220082c0103212a60440a012001320720b2075045c05105829445952503640c1005140d400800110712550003a0700100021f4005640700d50312540084e0181ca4502c0003540161455050207090010000301d480c1541c602c1c400b0185001c6510008 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 748179082 1250 748177832 748177841
    0x5041b140d091a01210302070e09011506080702010c05130504021b2a0402071106030c040509010b0a0e06040b030a0b0616260903070512070f0b0c12031603 68
    0x1501c0d04030340d03244075510101c3e00000c0310802c02c40800507190312a40c1050409160b8080064424040102941504e40044d40018002c02559450008114240c0c5c440d02c11902610510886050f252103420b0002681e540010314940207205c02c0d00244415035160008903041d00508107106c0790168030000400590030194024010b41c00e900162690700443d009076949042c44184003080000e0701030a062a0001000300084408403084500351314004d95903d481c24000c0c0008071161080c0c1001003c60113521242e011500101000351400750b50b580c0d6100c0500d2a60802101600410b00459215a40e0310703000c002c4034103407040004030906648400c040d400c0240506d090258000380200301400319110a00c0b6141c076901e11680c400300451050000f1012007404040c0c00e048084814020050b043c1c0c0c1c04110303041501c4094401800300f14038000c5c0f1614040459100c00c80311001190081108800324000340702600e03550b4200d9032000c00b00d4490035000d110458092003100400025040440e200e03400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 748180332 1250 748179082 748179097
    0x6020609151b1b0c0616110103090804030b09070e070c060b0303090a0e0a0f0603050a120909141915140a1e0321080c09120d031e0905030f0d021603030605041b14 71
    0x100001c1c94100e6554484140d0b006400988093b0b0f00c43e8200040358100300800b4000d4481c0040c095140d0a1100000e014500f0500008090545898105005480130416902c41c03800040914005d0b0f070740c503490f001e0b07071180c02d0301d40c1004203007041648501c90109000e00c0c81241e40c45002402200f009465000000e070340011001c00300014801e00050f6100d0500545140d620301102c0090b6034149200554001c04020301c42d414032906003039903016500b4900f04460103c501010010707103803151840c002541e07040981c210364615000348200380030f100246900041680d1043d2500344000c0380c2d00c86602c00081802050720009092400051160b001140c041d203000500a4034031408408008021070805102e5469038000a42d5070b0052050718085503450001e0009800b410402c42c4040d454158a078803d130091421182c02c00904100071203426811120981490300303206903c55160f00c0c005018040314440d9500c690b04108034200508840d21400b0540035094a0300c2d01c64040404600e9100c3c1c100c0d42 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 748181582 1250 748180332 748180337
    0xa05010507140c191d2205030f13030b1f0603020a03141614030f1828060501080d0c0201210213090606020609151b1b0c06161101 57
    0x1c0c1c900605444918201c02941c800b40e03c40341d139460818004000032254019480601c0c110361090003402c1e85402004030000d820b5071a10702c13940030b42e400c1440c80e41c8502c40c840750f1450710001c2e9481001d03001c402884144c0740706103170311545525000c400040c201550940ea014402035428100511400303a030061000000c01e040101c1c6c0d50092070102008180116001c1c000300101c0d0340d18180d030503403210003404006142101e01d800e504050f080200c083c40000c1c0780c000d100e04e05209081c103000c002c20807407070400c00c841e03200c1e00d03410906108104026820301048460740e04040010036444000f0401041c20501170355841803101154004490344d054403100e21600390542000c001c0e038400d590000340b0f040c0000c0741d940c010203031418a40800302c80d0103501803030440d0020303010300ca001c0c0c8010644000c1c0f00960541d180c0d05807100a00c0ca42050080a00080036041c002070000400c456480052622448036060798528041303a4103001080c401c0c584a0100c1c80040581d000004d0741607400c0811400307061 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 748182832 1250 748181582 748181593
    0xb070903080c0318030d05090d030e121b150301050d0303112d0a020d0c0c0810091e020303033115060503070f060c050102090a06181a030408031515180a0501050714 72
    0xc1c020a1228a2400030030800f03400102540724dc807070380070b51101383c3c7c040191403106124400d814281c0140c0810300815210f44482154401414400d4100032070b441201d40550b44d980d159040240320b100c3d62610701c641825401c1003024204034410060720b00d081c032039801078130314203d103500221640c1c5d05c841000c59503a1011130b40410201d008120b1a29083d0f00c00d5000514840c4604014511104501800328039401181504d0b0050324040280c90b084014000c90402c580a001c00e1512081c540b041c0c10301d0300340c407041101c2003400612030004800f580883d604011031900c0d0000d154541c45075001d50312080c1c000107020041584140c0c850600c2900030000103007802d14a4000444103000c590016001560440500040651259481d0010100c6a660303031004000c0b0114501039010041010b000c3c00000300008005a07000301d02c1000001006001e20710400403488420129001030643c0b8030300200c0060040d5490420001038019210140c44040c01c1141d40d5a885403000c4c1c00401c0030390035000700b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 748184082 1250 748182832 748182857
    0xb0d020906040e0322240804030c0218040201180506180a15050c070906180902060c1204170c030c190b120103140a030c0b070903080c0318030d05090d03 67
    0x51000e0140003d070407140305c800c0001c140080c2e450302a55040046118242c0055500c07280c60100c000b42840d4a070305200150f9034031410182d40c0c011450101a410000c4c0040d4205514450304806100d14400d80300c2589610340c07407800c2d60102079140107241e00308104108410640c041c01162524154004280c034000903168201d20b0400d15030b400800001c540e0105a0550700c0d2020712210016102c291410013405162880421900c402d10b4852420507a85910b0038040d51280710490b60844d144100b100e0203c840c50444a495512912500900c458194440c002107603010075001258a4010001c185440e1403104001c0244001c01c0040c3da40790180310700144a00103032001d040781d0540e440c4002c08642c510700b8240c45a08000089034041e030418416603000075004104148410b421a1404010b0340e5a06419540200160406001000c020a07142214403000000308000e010000e600c0292307010101c00c1c075940b2400c5464020208009209000e01404c0c000400c0308000d020f880e202044050 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 748185332 1250 748184082 748184111
    0x121902090a090212070206040c0302060a14030709090b040b01020601181b050705010b0f09070804050c03010207050a1104020412080c01090f0605040c17120306131104080606040b0d02090604 83
    0x1c0c198400e42c1c090782c012800d00000d07000b10310225442103560001c6c10080c6802d541c0c0a020340c0c13040c00b00070700c120804141e00c00601c0c829450311500d4803034150096504e09003101c02800d400514468046003d091030030812803402d0902680c805030006030010a0981d080071580880300303e021504252844c0ea400243c0440884074585182d4095182c80d00c5a072001e90741880c50039507400d800c8160144042031443e29080c3c40b2502034960122240c03800d80e209480354a0000e0070440ca0042d1694958004103401040c44000f240319440c8601c03510300740d480b11000f50180404c1e0b01a0344140d00c007120b000c003d0702004c01c2c00c10000f8030608090307400000700c1d401301b40e5419141004044060303545036038940c1000304000c07800480002800032250b400c014850402d11541c2c0e2180036801c80c98003e5400703c041142501c45594100403181c04a5003400060206070b4002500c1e0030070b2207400c14034864403010603144d041a10400d100410050720281400d0003980900103110006044640c100f55101481841d109 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 748186582 1250 748185332 748185349
    0x3021314030f01150f08060609060d0f0b10052e0c03050712121a0303090d0314121f03080414061b030406170606030a09260d050106030212190209 64
    0xb950a403038013a00c02d0414196908601c11504648640c1e8442028003181d42c1d6110340b4194010f1040341d0b60304079600e4900d8001680000c0010060a600144041c8040d0103d02408103080e200c06568201000030b4140d504200d515136421005030840e80c0341c42a05ca414070035507082d62000d009040c460b2401c00b003076170307800170182030841d084002550518a40003002c00034040c000154410201d2645202e11501c0002c2c1c50703104d507645d4580b042d14020000340800d8010242808010084031403a5100c0843c007100c6910700c081200d40c007001681c3c41703503503152050000052000b503d40100e40b0504043c10244c0c01a90407054000c21640890301f4007002109060817421801d40d09020700280d0f4459103403030405030485070709450031030058400c007081181c0ca895450540794002c54100000c50b4001070b0741002082c80720303e04141040610010307460000e00c00a5401061541d482c210200020b80c1d0b5104210124040c60340e100001207125008205e05010703c0700504001664070000614200d041390014007a039 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 748187832 1250 748186582 748186601
    0x1050403080a180905070906180801050906040201200712031b0303140606090d060522050a0317010b0a0e0609030f0c0306130203150a02070609060902090703021314030f01 75
    0x90007140b2011140054100540c02055013900a0000b400d0401010300400030a0190030300f0058040004800d142e125885a4001d0045400070040707410302145058491104071070aa0204e00c00d040c0295000d10031864045c440900040034000d072604120803264035840e0b20200b60b040010201403550001c05058021070050b20a0310001007018507090760710201ea4009000c9403003040207210044c0030b526200020241641d1081c03001445030703900320803006034100c2034065480702c1c000c00c003000042000016281604034002c0d1104103070020030307000d003c0fa524024000c54120788401d10400040c180039069008018100510b601d0070803090b00301107460080042120340065120b900401010b0400303100203030f04201400d20400d482c800a4003c29500d0b40140c17840503140100b500001c241c4025681648c50640c2c0c0501d050007a80000e0602c01c1c0034104400059104203000c0001c986420301071b2084030024404100c0b0b80c40d43c0be1410a000070048450986160036004c1c50000042d001020300c50b940d640c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 748189082 1250 748187832 748187837
    0x403020918060703020f0a050d060b032d15040b03010e0d02010f0f06050a0510020712080d0c0c11040b06040801020f130f080307110118090b01021009120e01050403080a 74
    0x107880300c614414606040070340b0003002d03d8410040460b000e001c10044038440c01d21801c0041c1e54000e0101c140d401043c0691007400c00410100030310150b8580e180704051881001c0c0d0804803405040e50b031024218500780d50a00d88102107040079407850519030002c00008000900020300e10401c10001030401d240e80b40f083e00180d5440740f00203d03204031403150040000c3c0e158001c000c15400c0201160a03042e1502945108025030070b6402c081c070344200065806080940d080c2002034841d0f28281c40d03150000c2c1407840d50903041c00038100ba01c0b44100c0074665555082001841511000300c107000080030b00880b281d070001c0f41004040b0304607401b4002011900e81d8500078681d2003c820603010080c0c0700b0382e000681d120084001c10003100d0f0000082e0380041e60801414251120349600599040341901c41120a11555020014400c407c81d40b02440d40c23103083c0c098074500701a98050404403021290020400d030700c1c2d041d084840c584901403400d10440103040c10b41c5050f8498540c0d0f0300a402820700c1800 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 748190332 1250 748189082 748189111
    0x20d230d02190b0910020c07231f0207050312040e1e0109050a0209040f0b012303160e0a080109020f090106050910090b04080303010f050901030c0b0c010204030209 72
    0x564000820030308000806034405024284400001030744a0491400041c0c000d04103040450b89030142403200c20107101000404540c3c603031341550019162070645c843c0c0404280f40c5088039482e0707540b10901c6490000000d0184000404442c0030102120a008a00045200f08130011420391410840c4148600b56a824541c0300c501d040320201240c10010001502440b265a00e15800c041140d0040c2c15900580c00c0481e19a6602000c3d0009028034021240d115060026010413507855034020031100c50213030785a203c56801100001402e0060700b50210a4000402c00038800010220400d0310680103441c145102c1504400022806221600100c1d0207956565410085180401c00d03800088400c1e114050b440d03140200282103170050302c403070a000f11000c5101001c0184a40f0712140038002812525456030385a9156996a030001d00400186000c1c1e6640403e49203450581d05040300e40c0020006050390820451580e650040c0014240c959000c0c003001c030050b030350b0b00c1d140c5101b02d030441107218 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 748191582 1250 748190332 748190393
    0xf35060405060328060b1f030605010f0f03020706060906030c15210e101d07050d3c03080403020c181605040e09250e070309020d 57
    0x108649010349580c0c403a601c05500c2c0c9031108054151301080d0f02004243d9103003c0082c0c18004094111a00d0726031340142180c000403040d1b17509040c1108108441d6030104106500c803001941c1801002042c607011992172450742c403c0700e00c2074000f00f00c00c9100344070100d042e5945510f03403011394100f90003c9a540351482002c0c0107501c69080f040e40c0550b075505e481e030824064445442407507100060f0324038a064803018000441c0c1000c1200054015141034204040c2ca5800c031801800380c4011070610040c0038404001a1034a800714002d040c80d50400c0102103d100845c02601e43c038400e52403426520b4148040c140f8800b044065119a0940207449488482c41d107490000d00303100d52248103500c5280040c03c402c083c4944095117503442040d1149440c01c800c07004030141c845002c3c590103880c22224074010010310102c0403c0c0d03400c0c954459611503128201c5598411040310301e90088140407250071002490562003500200e4909002411440d40a040c80d203443c040d10460340da201504501d1030f0303c00d8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 748192832 1250 748191582 748191589
    0x60a021c2c03181005190e0a0f1805060a090f02030f0c1204030f0314101a030405031c0e1b010e0d0b0114011107030309091b0f3506 58
    0x2200c0c407801d500065450951183e0608000040002010340182c0039202c1c0c161103940144e08565180c9014448441c644c0b80d140c4009201c0e5a20144540c010709118000051880446056000b905c50900c22403503000c80d0280c0303003c000c2c00010000c541c0030001c1d800025004580f40f19100100e6582e620150340ca1400018201d4103d0026101c8800c180d010008491a000d14008082d005a854035041c0e03185c2c5c109401c21005807503034208481c080ca00a605001c00203001d01600310481324440155541296203600308010f40c00203c4010700709401c00c1107005101c0b0040050506601c022110001d031220002c0079151414038805040400c41c20319503090800356802120300345201100301d034405085070b01a551002e41c0ca10612550112640009011003160300400d00001c0c01c0b000d00007100e80666503406c00504c50510f03032040b81072261030030001c6c196031840b0704010308503440c2d540c0350b0070406100c034002204e4800308110039090009280c510b03c0c5404240410400300301d00650740d00004e80c100501003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 748194082 1250 748192832 748192901
    0x19030f03050f01031e062007120507020303030403030c2006150406060c020126090604060c03060f0501050c1e030d1805070501110a02040f09050d11060a021c 69
    0x4110400280b0401080001c2030804590640c4420140280380c260041c0380c0745014141e00301806014640c2c3c1854000c401c8040300240440c00d005900444082d50311100aa66902c20500c010350560402c00c0024003080c040d8204140c03420321032501c0340010148000c1c1c195855582525015960004403d00c840345070b003261991324000080303404104017860300070064084440b16a000f4140800340703000801a07030742802d0882c1c0300e01411001480c149014024251101d208071000c0726050318088600b000c20303121340700b007a094600e000a07924810f41050015070361a0806074820b076a610811441c5640080040003003800e1154071002141c40b1581d040d140c0060301c1011001a18030107600400001041d40002c00100310762082c03c02d50480c038101803525092012400019401504004450b180494107610055240d8081c80595522004145003240c0c541140031052481d81d0000c004251520320030350050019603164060204401030b803c0f07054040e5042120602ca490824180c030034010350410a4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 748195332 1250 748194082 748194091
    0x12022a040c0f0807030b010905030313050a06031103010506030903090301150807080313090e0f0d0210051515030c12040f0506010b0a0f201603020a050d0f120219030f0305 75
    0x90a1200c00002c200043c100360008011508254960782a50340590113000c0b180c0250034042c0903a41d031000342c50300341d0941805911540c1d000d0403402e00d00042441c8244506403a098610000c10300d142d103024200700e4190005007180d1000c2c08104031411a56500341310b08800020550015080035252449050070202d15920035002034000b080510703000c0286202e0001910409040080e1038203071070013801c1c6401e03408180400c1078400d5440222a16800081000000071810002d01281d518480d801507039641036240340c0d0700800303d03907064180c0700d540c0300c051544200c5009809003801201175403881c11030340984083e100c4080d4090244240542409071074090007007000d0702454207100c2500203004286074102401003140e0381d040c0c80881c50000c0c0050314402d5441301185c150307402c401285448140d1510049102e02c150300c20015840c142244031520903500401c0c501071300611a2144040714206110900c114054041700e201106d02c268500300240340695180801285c90b8940501124405070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 748196582 1250 748195332 748195337
    0x513090e0c0420070b040309050303030403030f06060c0209070f2601031109040b1b0403080c060a0e0607090512100203070f02070e040b010909030e100302071109011212022a040c 78
    0x1110380c0160aa20012244c40550014584540d5a02c070700f0126496001504441d40c9400000244004d050740741e08140101e08590008000103a5105815503052501d040001d404c100240005080c15001d0180c5020308105401c101705204000000d4210b46000c00f074501b03d20380055401031090200c1504030080d034003816100581035003403030b0b1030340da0907440300516285d00707084c481c0da61440132400700b001d4500855001030090f4983e03020000c0310b0785440080754191b401624180b11403c030b003000003075094060002a251482000e080c0414890480d42841200e0428407900d24454441c6050348001d5204143e540c0d282e481403904242e0017401c02c0c030550f000c80301d1100c090302840049804841c08a0444040400000b000380040c03400740c1d004e1540c3c1c0720039644207000c84124501703143c058000381466486500c6140035903810b03100300b04145e0400e00621103900c1c00c800c58040018204514166481c88600496034500401c51414415030420010a038661420381c1c42d584150600e4003075112802140e0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 748197832 1250 748196582 748196621
    0x1b031b21050601210203100e0d0c1104020c0106030803070509090c0c1f090b040308180712080f0f070f20030a0204050a0b0306010803040611030c0a030513090e0c04 72
    0x1500c460b60344800600034070482c2e609000803000c4104019149900c503907405001d0701c800d402d41507018001480501c4101500380118511403611520072000d04110300d901101140140c51010107200c001d400c052940c0b0410365035201c021000ca0342c120099403281c1265642d04c0c7d0b03116525070600c0024500907041c58154070083c0903541d4080e9004c01d142c41c008110039000d01c0d00b641e410309108040d0444403001307008150000107110525600c140348a1140c0c154020303401804180d40c00807552031a051042d205060241040c0000090303c0f10f000701112804007842e10304003255a203c0051650020500319400324402203000100240b1802e510b409108440b00504038001d810f01094031455608402442580d8400000b181040140e10180e00e50360080d00b19041ca41e1550a07080d620f40c8540500d001144c440d50b0390f07113a4104000708441506011b00c01608501c0002c0d9001e0b201078210020003002c08010040100c0c0d61031203403142c80401c1c0480d0b402401d0220b039250921044410780003001c02d800411 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 748199082 1250 748197832 748197899
    0xf060d0c0320030a0c050d020c01090201030e031e0304050741130f020408030403061e0501060906110319030212060306010f261203040605060a03030c1b031b 69
    0x140b400d41e07a0188090501045110003440700700c1d01442104244044070740f0102e0009851601580070260180c0b00b038a081140c540d020884c6a52405840030b05149410384000b08034104500c440030f550014424421a406070380c45209480b00403607040b0416003860044e203c920050070712110f00c221410311100071020000004030106400c00500d0808c4400719031584680a940301c2645d044074002c1100c6004e880e2626180c7c41c0c5000a000001c1010a50300d0030110404050105c84c841c00d4100c44e0710f506c8014805151690035100320030100007030342e014002405900c1451448402280c860340a643e070040c1d4500055072900c240d608003411440c080d030700c81c40042c4540315800b81900240c40142540b807241c03002490750703030781e400819507000700300e07030107078900700d48541c100303030015500442c0321382c6052016035501d078140803140c0302e14800a000180040710000100d1040d501c1d003602c01e045985100c00c001c1d145d483c1c58040d00805102aa003032100000100003805100d40100510031042c1e1405030390605 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 748200332 1250 748199082 748199141
    0xe010c17130c120c0905012c010e0112030e0d1103100b010e041a030a03090e090102070305030c090f3115030212070f0905041401020a0c110f060d0c03 66
    0x44a00500000032054036100c0d0510460100210080c40c08005c00d105540e11821807000b00f4480322201c101e04a046000c00451080d01d440c01c0341a9030403141c00d405160328000900c0090b0b41128010b40a00103030044005840d03c0d050000e400103402075000003424031421044c14904901c030f5040164403482c241d18204a60780c801e800528002c82110f011802150914610310602603e40080c2d501d485030f54143c40405030030100b400700310f500040701c60215994065a0500382e10601c400100050310800001d003018080070701901060303501400d8000c0f42007400f00072644100011281d1040b141d03403c00c032880406080d5a01a0720401d44280a00450b0455030b601505640303180030007803144110b07003100c000ba11401c0260100030321840c1c2c03100d000750303a0302e94040d0000c0ca4192400d58400d80030300200b0420500500803201d4404066942414400e00d50b2034051b5184204000360b0751008124015812664803d005070680381c5031a940010100c40b40d00c005011100d035070201405060146000349401c08 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 748201438 1106 748200332 748200353
    0xf0608060405010e0703050601061b05060a2408150a0212011202030c0d1110050c01020d0e0606030a050706050d02070218040204060b160f02040e010c1713 68
    0x649010305d03141c14071400301800355400711004122040c40740051440007100403840040310251640c0311410440290ba0850b065a1a41400707100030b5030854004031194510a15016038900e0900030380d0321010110740b50072580c0c0142d000203c143d00d040c1c048450000c01c0d5100e07c006982c4a1908000c0c41c1075482c41680a485451480906420001801e009460300304810b841c00e0b005007800c016007969101c0440041000911102d42d007040c0900203018080b551032008140714501202642c0b80401c01000103200303601c04022040400e00100e41c41c0160340c2c82d441d084d50b072004403c03c150081e110b8403034000d40021102c4011002e414940043c0f0740a24030071038080c021199130320081c0340c182c01140784204050700340d05007003400540ba165100f201140701520116014420400c0d0500b16100c00d0803000200e8080c0340102d406444920b06982d00079048041040d2130f10860b1140346844 = true := by decide +kernel

theorem cover : BRFrame.Cov 748021582 748201438 := by
  have h0 := BRFrame.cov_init 748021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 748021582 ≤ n) (h2 : n < 748201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
