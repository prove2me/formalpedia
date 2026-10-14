-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3461
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:43:37.956416+00:00
-- url     : https://prove2.me/submissions/e2b2f7d6-7fc7-4d5c-826d-2fb1b68b2e34

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 622302158 ≤ n < 622482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 622303408 1250 622302158 622302167
    0x1170606130f0f060b030f0708090a170c0322080c10050a17010906061e02070308030a020405091302271803040f0e0f0c0c07050d06020d052401170403 66
    0x10b00c0e2101c5035120302a01c10005510300c01c0c90301403c00b001115580346044850400c1c083c001070010010001e90740200001041c02007203007441203a02500319000040350148107941c60050380c048500714000010b913100c201e998280781181400b511004031241c503640c0c5145584070980c107070703402d6001802094032303002c070620032070080085250f2070911b03021410003c3d4445d14440ba00340c201002da580e5601c0c06000c0a038001460080130700000ea0072a018800f103c80c000e4840c013041c88003c0038181e0100c003140700700009030141c401400000e070100318245418558200c0b04240b140c010303801840001c0301d20f12100046952400040750010700d8800680b620000d0542e1400e00d10007422550005020104001a408910000602c0510002c1040742404081c0584030751020b00000000c480c1088089a905404103030102200c070201e44040c018074003814258043e1155a044902c10b0b40740c24100a021b501090243c034801c9841864070581d48030700c0380151182e000b51100b4903801ea03402d000180010340304 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 622304658 1250 622303408 622303421
    0x17040314010c0e010e061902101d121b03030718060518060a020106090e0a05070f06020604150e010c0c050d0e030601120303180b060112050c0d0902040608030409050117060613 77
    0x50202d610b8005030220900c8408040e1f41c4040c0141c009041c0c1c1c8040d440c46000300310358900d50315074190001c414505131a42e14070850113100c161150202e408100030035094200041c0940607000d072596481c2c02c1e000181045c0d02c030034540c82c0000e4001d0380441c04612507019620808260000c0e050704c06048000c00c480358212000c0b039411503403148004110050700340a201c40c0100444000c2080c5a01440d0050910741c6540250150842036001000071950010300c02d47c005401c0810041040f84040c00c000151010f450040c5040d800c2070301111225900c9013508080ca40500141c0d907510554903001c603507000410f0081541640030710010f001800541411401f1144242800034000c0e4001d2080345c8150384080041d00c1c44070803401003042da035801034910728440389564405c02c03071032070407810800c000d000b00b22003a460030384d940c603c107421901d07a0b0f8403060240c943c0c0b80899031115962510710020742024003038622041c06075000700411103030001703d903402014000c2044218610210010009048 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 622305908 1250 622304658 622304687
    0x3091302040b040f080d020a02210a020a030b0a05010f050609011218050709240303031806050a06080c030a051213050a03030c0506180706140717040314010c0e01 71
    0x182040000b03544400480200300030164207101c54040f81c40c01005070708010500520f4000d5400c1440d5580059a8210f940c2071043c82d124292521000043c11980c540222140000d42201c00058080288062079840521070f100c1034106014903170700c1c3c44170041c0c40e0040d4070079150011400c0c00004010340c00b0b0300521000817203038000028120002d15a9051144d1208001c0e140ca4020000c14420400d25014130109020fa2101c030b0411100098004000343c0110303c00601015500c040054809100c0c002c5541510342107035050045013070042074a402001988034145641c0708041c050085804c0200f400d00c1280d81102c05004000721484112400d640480079203040c0c0030300101d02280d141c1d121007183c40514040d94a0700000046071400b6071400102806411440707810000f030b4500b601000aa25082d6070390791404041c000700d03103030040420740030f8094005d01d1081015104000340c0c00e440042d0013201d010701d218024001c2250099403c0380c1c001c43c05400010401c1840c80f599501a1412181215 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 622307158 1250 622305908 622305911
    0x70e0705071113090308010b040b0d020d1d07080c030606090f06060d090b04020418020d030f0302070b16270e060a180c09081906090c26060711030913 66
    0x5440c0000484502154100c509066a944d1118045c154420311940c050010740c6100303850f06044c00060b503030340c0c010303400d000801d650001801c22006405030010b007519030f0700d61201c10090a110065030745130601c0303000d510392520603841040c1c00c0d440d0001d070150060300081c10041c0f40c2d80f40d01542c0341c101e600c000c1285801240c10030055050300307a144203ca01c814015910b001d0982018410041070722442e0412003000c7c0305108c0c00d1400b5030b03541180f20701c200360305080032000d600100360281d019000d44000600003480f008100001c3c910014506c0c0042c2d034980e40c035005e80a45407014003c071405d0010390541d0000c0d04100500800c4c1c089130000740c101000a207010255a52100040c904c410520031540000c1e480c1c16000c8503031504800300c0d40c05072180c3c1014000f2120b08130420510252200d0001e008030382c03182d41380002d110b040a010b0f00641458074510715500d1150300100c4171140b05000780441072060300300003140c0740d01c5404000c02d2514203101561400381440204009030911401811b101d6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 622308408 1250 622307158 622307183
    0x70212071401092906010c03120515210d080702060420060a0302450406170303090615010e10140c010c031401030201020705010c0501090503030f18070e070507 70
    0x40078800e026a048000c04c83e010714046004020056004019000906000510700e960700065046001e250b9201c442540000761540d0f01d541c055859803681c0a4241c1000000110700070b0350041404c0c02042549400440d95504001c410840b460308049a4081c01a00103002050015001101c10540c116042070201510720320040051100d900500548002c00ea0005440300ca0070003010700c0d00c07c2c031014441d1907044007408204060b05100b1060b90b1940b0020002c1b104003569613030383d01000c040c1104a60100c01118881000ca940b9401038803848040c0c4681c40c005034040007044d440c01180c14040e5541e14002d01c00e0400d1090502600c591882401000e400074050511800080d00150115200110f4400342101000e8205e5003510b881c5459047c8550051001d83d03000034541044900a107030240726820103081c000e0040154513402491400004140302120002c6d01c0114012291070355040f01c1624504105907642405120b100c800640110014035018003440150103000e0040c0c0041d41407 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 622309658 1250 622308408 622308413
    0x17071a070f110301180201080702070602100f1805070e15150a02030c010c020c0a0e010b0f16080c010204260a02060f04092f040b09061309022107021207140109 70
    0x17981e403100c8544640d000c00d0040a4203542c0c0c40307100f40e50400070b40d001a1110700d041c444025100d0640c401e46d0070f4040e484491200d810510340c0d02a0921000e1320342c8040217150070b0302e4102c1e10340e0501d03c621a42d582c001c0011440c0083c000005462000000348440700001304406030390a00e8200703590840550105000904c50f0340028090803400c00110341c00b07004d17042030303410802c000c005a541111084520400040c01140c14880c11603035000c410581035612a51007000c485c65150000c20024042c240c0860340c802102c20540142090300c1500720482d40c0c211a5018608440107248c40c0c0d05a0703540b19020307030005414510010300c0d42841c0481801d242c0341e02c4254602c01e072004802d81b00142580c0c2840f02680040110701d840c2d4984c1d18001c801e1502e46080b194183d18044c60044c18424000045e191341b80420251a40c80184407072003065440300c9002c801c0702203407031005270001d0440300d002000401481c408641c40002107008040d0905021903600c5844040800303822070310f40e035903071890201d01 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 622310908 1250 622309658 622309661
    0x61d0705150f0711041107020f0d080729010902091003240b070b0718060e060d0e0102030a060602010522020a030b01031415010b0313061517071a070f110301 69
    0x1645004c3d050103c00c070004402400115901c0c10688191108103005100060b55101e001928172442220300101d402c42030300b00f1000700d102d400f500920008200a5203814a2030592405c810704001c40a5036615a230380329241c8003648070b6880615801601c10b07281038070b1a406544045045c00890010f00d961a80421034002c14103400e030028882c42d803011850804010b0b000751031540c0038501c0d00d442e9080c030342c803080341c1e000104250081000340107481a080e48607440715004d0790b9200301054824801030451481c04da000307510903244031052030f040c0400414020b0050044c0780c001c2c04080303441e0f100f00c0440c0da41082140e0b10b042040744d0000000c0f9000012890b82040103010310701071103180750340e514085810751418040b168424144640b020041004a00c048190380d440300001c2d15203198080c0500e030110003850071000300b40c1c0c41c0403032500c0801c403001d074030a1440d84003150f01d0480301219100c994104d00c014120346010f007141810801c000001e81d291051724100c600c958041003007541154000390 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 622312158 1250 622310908 622310917
    0x22060204060e0307050402090d3806090f071d0a1a1c05240123041d0108062208120604060e19020306010e03070909061d0705150f 57
    0x82941c03104191070f20b414400c1c0c80003042e040b02c00318940142032020482003255041d002d00541404505007041c8052192a0341d50074101c81400b00681c4c071200d0381c103243e8000903150617000b07440c0c50b400550303003100382e1141c42d002c3c232036580769031414051006030390080d01c402c0280a500324070800ba0020340c00817000d12317890032010000076a603210500c4501c0710381a28400c40b40d8200d01400c00b41440304100307220126882100280d407003042c0111200005071220030b800480341080d0f01035901030302003040000014205613410003010b4529004504203694100c1406e0242181c00e0708030f030300071510360400c56855680041d4258040d0000c4001c6460340c200d140c00502a009406891500300a00b07841d241c0b03c1c1402910007107582060a0800012500401500700c1c40152015800404038189038041c0540d030360407181c0142100c1403903441d07039400001340c1170310304040f1080f80c14404641e00d110100d200030f17900c14a44400901d002c5241074200000c41d0076007a00507030303140020048480ca04550700001d1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 622313408 1250 622312158 622312169
    0x140a02030a060c08071403150f130515040902030c10020111120105040612050d08060303190302070c09060506070b1005100c0b0603011a0402070206190c210822060204 73
    0x8004542440c05000c601d001081700c0200030040c80f10583d001c0d0464140c2e90004c580500c041244407440c40031504c1540c120415030707800300001088528040b040e400c0709104d86442181101c1e150004000c1c00241d17010b004c4000e5241d08026a2030311a8100280c0c3c02c050091280300105010080003a040107951003a0a0703000e0034154000103010b503080601441008007a00d910078000c1034a40c4c0c0782c260315100f1992200013007007e181c010030390310741d030400944908509811078902055101d4a01034025800741030101e880020480002034415017606c1880304030f80003d0490f91800c0d121b69582400d5010040c0248025450880c010416840301620725020705090f85982d14408010b0811034036101e0003c083c0d600c44d0b81001106c400305071341804c10440c4080c00390740c0507845034928400560b50f4081daa141d11880001e041c800103400758080c1010100310b020741840c00c018a410180d4807145c4081401e0f650104820501058a904e1404120401140304202003a50341c1d0165441c48103076840b07035121 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 622314658 1250 622313408 622313411
    0x50909101a0a08070f0e070f03050711030415030608030918040804030506130213290103090204150e1303020303070c050a0b0702160503010510030b0606070803100303090503031303140a02030a06 85
    0x40c0880400e403517030013010f000441900c81c01c46c40c1407800100b150480022034000c154559010030307001802920b0b0203000c0d0f081107050320b4440d503c500040e8031494008984600282c02c0900005a401c40881100d800c1d4101501a100b040502000401980409001115460001c006c0080032510038407441d4056003091600c0103643c00c00d8010040d02c201d040c003070800341034a84250980e90a0b8038842c85401e146042084082050001d4010f030020a1101000f940150500c00b0f04822a40002000703001d41e8000c03004183c03142c452101d0030480132051000280983c2c000c0000c038905602a03403011188510030ba003290040c0c000c1d07a503400c80d2040c3c150b0780071001d41d12610581074483e180116041c06004160003c004500d4000f02815110026220141c030382c0d1980004503d168841c2c50854612540000c4480e5a9040c04a0b5000181c4082e210540000f1810940441d16250200403220810407044cca240c0d458110745410050342c8480d4098110342c81190301440050320144400d220072802040d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 622315908 1250 622314658 622314673
    0x10f1106071d1f08060607230f0a051005221101120902031504060b1903060605090c0304350d0e030a0f0f020c060c0115050909101a0a08 60
    0x507004006204800d08511920890403d050a0807011040350b20703c0c00140b0380074003152039603004122a445a10750161a00450050103c001c40c440010782004070a000110b43c1c20000b5846545d440c5c04405000820b590840e10150101101e5508185e801045410900c169904c41000c80c1c00702c016518000c403440003038944001c5c44e56170080030030744824140c81c000380203085003a400a034982c0d1015204440620719030b000700d0280301c040d42c03201c40070321400360000c803045a425605503c4041c10348011680c41d42030100105440c14446903403030140050545c800d04680f00c0d55200d00340001071078404001c24115001e10071004080174004410034880c8802e069a4116502541080e1148544d104003240e0040044c20003e030b6200ca00c0d045c20032407510703007941080c40706042203044c20703991140c0c16484900424980e440b01d01c103501c1548000045210354498507581c0d0f00340140c1000c101e40740c180b50707040014481c03003e6a060700010704142c3c00b0302d21030200391494000107040c0c0079941c01201ea43d510400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 622317158 1250 622315908 622315937
    0x6020a060b0405061c0813030f121701030f0212030a0e0306010e010605091201110d0e0105090c10030b040f091b0e15121903112505010f110607 63
    0x300e0080381c6002a1028031062030310380c0102e21040712010580605030840d686903000e115284082d2070342c0c05022102d604c10190b80382441014000191400d540d0084040039400c05640120405200302c40e188801c411780d6840c45e00c480804814811043c1e0b00603080c166a02940d4070144000c28165800c0d0b260b04081e0b250410a0504d03001c816000190450505030041c8001500b10301070f82c1c040c94040ba4418585a501460140504801d9146151100000c0b800031840e1b041ca410402c4181000c100030011965625100e42d65440d600700d116420170100880000428440e802070741400c0d00c094004503904203070040480450301c0b8007005030342c1200c80b1105001c1c200b410503040002084d007211002103905003090500464003d810034644108090090300780c1c45402804006060450030416040020550801400381c04842c440d0700c201e4054200781104c106102114034044014450715454042e09000042d0340c0da5520900c03202c00c1c008000380c403c81802c0e003000010300c124210740e2110303030708142c01 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 622318408 1250 622317158 622317161
    0x307210e07120b060415030b01090c1d090a05070212031509370e060901060609060f1e021e01020d051b0307031a030a060504020f0603040506011206110406020a06 71
    0x103822628503800702c90300890100d440c0f81d91650300100105c80005040d414001840e10a1195610003800007104100000fa101003907071001c000042d541d19948824101c8001003003840d554000d0b01c6500050400110b0600b400541c485540720310f0710b00484003a08090250380c1c56640044808280c1d04003c000d020300d250a09000040c0c01c0340e1500070082c80f4064144008000c42c0308601c43c100d00140c2c800c1800c6003400780703401c0a00c0741d0700c4410543d40a070901e406058080c001c2402454041140e8500c00a1010300c40e80d0781c1c0340411800c1d0343c2c6900d03842402141601d03040e1000140e070708502c0360083ca500e0110042e0b00950b141c00481c000160703186d59010300c00c07054503801007042c0e0008207644107075140084030400700c03607005060386000104e50b01070151090b0056800815541c040c450403c081c4100485507002c42d01580c0211080c504802c03000d81003186074402186d004000b50442001003241110106007450000c0c401c0700045030070780c000c8220b0382058000d54440401a48416030090034040113 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 622319658 1250 622318408 622318423
    0x30a05040309122102030406050403110307152f1b031c051c23070c060509030c0c030d020a030c080c03180f0f0603061c050703050c0111010501080705060307210e 71
    0x84d03001a5003010f2601101034a0342c0074910001c1c000c03102c0328a40070700b65a000d200c50b8001e0210340721500b0003001042e100500d0701d40b5540108812850344030500d49050605030f81070024000043c0203141070b20440c8a001000b11148004580504c80c000843c101c58000c81c0e901c901070100c07952015101d440306602c4c241c40b40c2c1c802d4000c0c1b513003074a4001c01014103185402d0000c0c1390f15030824002a1a200c055040f14060190038025004515100034401c00c1c01011000707004042e4004211402d9004003001c25880f076016985800240e4800d01071100000c0c0910444c0e40d40300c0c001c0c60b000d030900c2400c00006003503501c0b80110681c513900305c0100d00700c60700d440031f03c1d488610740c04d4641c040c1ca021540003142091201030b00300d501c075905c40404110040201e803031080c0e40384c0c0d01006990301c00b683c03894003a48d15009104118040383c002410310050003814441d06040f83c0c40c10001340182441c06043c080e0542c0007901c260100101ba84607400042c10400307035403502c82118140014074040901c980d5050480d03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 622320908 1250 622319658 622319723
    0x12080603100509070b0a121109030c01260c120a0603030f2118020a090e0606060c0307030c15090b0106090b0a02062403121804050408030a0504030912 66
    0xe48020301c00da4940014020094541c031a08186d52162002815550460b00c0225007400390306002490b5180d0580f8005000110401c0e81150b80340308030080190b802d4414110081c580d048500081d00c4001c1010348080d4214002c2c030003040c908001070350080c500794400c0322090080ca4840204004055010b4072071148800a03240071040d286000301c070307044914039466150b006c0d10740b40d5000ca640c06a503090903540050313009200b812000d0340d07800620043e1402400d2000c1c00e00810300015412300b40081107482034190400514500300b460307941070745c2c559420700c01902c00c84480b5400c00d5907012148900030281d03000b0600d00741290314000c4010910240c980107800060005d000c00020340703030000341ea95000060880e0903a070400c0c03a40e05082007550741180e03007a41071052030602b469410041700209248102c680e0301c640f000301418140000c2d074001380c4004045050070400608074102c1c550085402074440d03e01040d0071130740e07109401010840e003e0290b800900740491154009031541d0940b90300c91 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 622322158 1250 622320908 622320911
    0x204050901290f09130b0a08010504120203070f080706020f041e080c01020d0c05120a08010608090d0e060a0c15060e0618060d0f0506101401090506160206071208060310 74
    0x3401c1e03041d401900034010854040d040701d2403c00180c41c00781e0441b0f040090080d100c2c080c1030342d4650509010b0401a01c00399800c240e1154086206480401110304180d013041009010140795910268903600081c001d54510741d0038800007204030800b1008000a0010b01d9090b0004400c1400f55800324210340e1100505900407101054981d8011802c14880005401c0c010303078240031414a45d052200580b080c0d030782814001400418641c10101950503600c0342e560341c0d0902c1d40c0340d810f01661201c1a0001d8004585c20f640d10540d246041c0c0020090900b8a03c0c00c0008048242d54403410750301c041c11800c2e031080d00c507401441098003040f0519070101c012200c00042d2201c9a002800c42c000c0035001c0703405241035908000a00010b0468464402c4d0b214007140c20900d44040c00742a5110305008141070200e10816052540d0b04c9940740314140e800090016180040c5000b4030084000300c0790f01240c10040504ca03000200d500c0c401010b5041c881c94075404c2c1d0342d15242c41098200408a0440d80699 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 622323408 1250 622322158 622322167
    0x30a0e0f09071b052d0f031e1b070801020301090f0b10030923070614070309090b0118030501231e130501090c03020a092d020405090129 60
    0x503510503112040b1200302d09409803040154202035090524050241000311601c0d551180807a0071754101840d06161503050740d110200000c9620b8807441030740700c8103080205c150860a070034459000107204462841d4143c085c10300f2901c0005044c80c036141e21034845a5030110040000b4599030184402d041d600d0700081049442d0100050361180d680c404402c01c059540000904001c4080c60720207400c061801500c015548151419a44803130361f00459000aa800c07000100c90001d0500752400300368941c444a988a00703107a0180024210b03010020304120212000300380d1404484004400356000d21300100d460712640d5000c0110074140c108500701e0400d040204240e1045034884280c5140220040c0309071034403034034090800d40c6c40a46005c1c203a54640409602000940a000c01c00c0724170a50b8030b6600d8950b01c905050031181c480a1b1541c00540f00a400803280e6848112602c1000045000605054455021174a0090240c21500c0501164640181c0683c01000480070a800455485281 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 622324658 1250 622323408 622323421
    0x90105011a0f071e0816150203090c0f03033016080a0b010311030123100e090907081f060e0c0a080a110c030a11070608010302060c030c030a0e0f09 65
    0x180c411841c000d0f001c501d1011000110404d030001810380c40780c00c1001c190f20b91402c00080200120642001c8903416094000e045a03440240287c900c40e15a00c4003078925540d00c2014030064203105a002e550601040110b0491000b607201d0440380d00c00208035010500111074400f00c02d250000e00a54900b040b001080701c400ea9020b180c080d4000125031010400e035140d0070040e03024001c208500325513a0400310020a0880c061032019812903c0350701e02d110003000402c2403040242c440c0b00441d000501c4048000f48600f460010181c02101c070408540c070040d80e0b00819410454500d009043c610711040402407550890300940e400ba011414101c1014248601c06c40340c98891050003034184412100080c900100e640d101c00c0c08444090034003030362103c070310780c005490364000c032204404501030095400d1190030000744881038405645445080d40d003180c08001c1a50051403051510344020002d4032200c08003840904115001510344410040400c0208182c4da035156220702e028007080c1e010001c4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 622325908 1250 622324658 622324687
    0x7080313210b28020d0209041a061b0f0601121505070516030e09040303050601030f020403050606090c1314040c2d050409020f03180a170a17090105011a 67
    0x2c11403509a111081408007a0821820320020307111095450310208500d005c140d51030f0014280400c08071410001081e0801c2c10754103c08500d20815004171052040764081a00040c1c01c84c0e800e40b400c0f088078444424000801d00d4804240c1000c3d08090040c0d280100300a40b01c036004540d56440d490512207071502a000502e54025030013600c04041c000390202c0c0c00d06000d0130b529920310707001803c8035004d4078250901030041c02e02610520300280c90901c0c205900c05051007a9010f495100300607040503159881008400d040160400e186440304210040c844034a510b4848014071441445c01d1b484112242080704581641c2076410034865070b4a6082d00b6042002c12602d40b030803900741c610b410040426403c0303c16003c0d60b0445841144000b80039a0364580d001d02851083e46005c00c2c41c51004000094aa221400c0c034200511f141c0c0828000ea00c0c6585090240c901c0050515001180c00591540416413443c03d6131841e105941d5a170051015813030391342950414540c2040c04501d8884030440e50301 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 622327158 1250 622325908 622325911
    0x3050601150c1212150503120703050306060d060807081506060315101e032901020303010b0315090103081218070e180a03021b030105060618010207080313210b 70
    0x206000000143c50035041c0c01000c1c611841c2d507441904000721070b0100f8110040e00c2160040612074841c4054080540d2000b00031a03e95a40c5562124203544401d401c1c0004d58204401840489485101c08038180300c0802c455401031203220b00034964a00c0d034810310031041001030a294041c800070402c00041c01d08d65208200070200c1079074001015140032108448200354096148600b03981c04011004003503040d00100d440400850154103003c080c400c0311401046405003080c0903070814401000390342c403071002641d8000e0000800d001c80402003000512603043c242c004860400c00070482d04907129082d035095070b1000d10110344110440d0b0310540329984023814414041660242400102e0050a001301c00507410004001c498044900d854003039280c0004c0c02c2c6948003000c800c5003180c0d00b843c050250a0043da070180600740307011100c0100450700c3c61506c2c45541580321707188000880e8182000100346c404141c0141984d00b506214070384181c4c54415041d0036400c0c421800510120780000e00e100e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 622328408 1250 622327158 622327163
    0x112030509030f01020c1e03040609050d2a060e15090d1103010e2505090a09031b0b1504050c03130309030807031218050a0201231303050601150c 64
    0x90748504064001900c0d04844049000c110f50012541300d00903a030024400c1c3c41401104d031128015642e00009540d00e0145215900020382d0038441041a030800d400155216405200e40881c6c52808411403540d5401c14072540ea421556060304000095000b451060f0242c1c0444d1120f10708030700d905c20401507008111410f4031850044041c0e03810881041d80034044880c000e4002c0c483d40c142c059005840302c0d04451281d5103000107080a00c880100ba900700c1098a500402140301074a50f1094200200b150320070841c1070161f234000040c0da40a200d0101001c0038400d00d60f4041d0b6161152007136241d44c80080341a8011800d0105000c45c8810355402c0c1c0c3d81c03058041c4190344c8410341e107050407140c005032a8005071190347c0014092003803585c00203144030445584002808082030001c0c6e00320141010351409410387c0c210280c0700b80150303c540680220102c041500d02180c2c1c0c82124410b403140d22042d415229003118030f20420802c00c3c2070080b50700500c00342038410f4640d406c1c0703c8040d00c072a4150500 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 622329658 1250 622328408 622328417
    0x1e0e01170c071703010510080108060f04060608060f1008121c09021008061f0c020d11120a0213020406050f031e040510050f09120c01110c0a110603011203 68
    0x10720030084602501c12907038001c04502441c40c000f503a03041040d802801107600480d100a1040c604a0248404904032070240c4010816591400000814200c1c080e008464880c1c640c0380010b000242085013034000c4000180e0042d0500f0003a909210750011544144615048061690340540f20801591241d005000030081c2c48035041808038000e10742800c0080d80111008221400e01d0351100000e03100c3d402c15924103001c0c80640ca00c00703400440c000d400000041c00c5200440040c02d240d0101d040d101d01c01d001c1950102d441c0c00c00030302e600c00320038204450355209400f114103528100440c512140f03100a030440c40c00e820107400400038851204038a80c8c3c000000081107102c044560f00c2080015a00342507070a0741810b19005481e11249044400400c1c2010b0100303404441030710f44c983c0102c4120004001c03203045441191110307001a01028025541c03000b5101c0c02035141401440ba0516050140080c00715a1500a801d190400078070ba00807102440113004150f0080003010115416040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 622330908 1250 622329658 622329661
    0x1006080304270e0303010603140f0106030b0f150903060c03070c1403070807060603050d030e0d0c0f0b0f1603090201050f0702030a060e010204051212090906031603031e0e0117 77
    0x6090002c032040e090448040d1500309841c80c4402e020003c0d60681d0310b150340500412101010003410410162112100368003c14010098a40a5801421a120041c050140b02421500001c540743d140b499640700504c800980802c4900e01408034540c4100c00148440c01d509180800400e403138866a801028800c1074040440244000c0007520b000c19031211540d039458a180c501030014010749e11049030a803081c405042c452a00030b002e14144041644000d040703c040c00d2074120780c44080c07880c082c1c800c00340303002200c0041840d40892030310890401541c01200d0170650b0064031145541500c076410949064a0000180c0e400b404560030703499090905501c81c1054000070381841c18586000340064078005510710020f2041d009801100c03011200a00c50b0300c103505c6843d488907a10300b20303c071102004018122440c9080784020b600802c000c2c007100c0d44410500101d01d01c11005810641c04941032821465002d096896200210034241c605615054425000138160388403804488044001ca00d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 622332158 1250 622330908 622330949
    0x10e04030c0212030d1b03050f04060209040b0303030a020c1e030904050c19020a060f06141306050d050c040506060412031103090a060c02090105060c0615030a0605011401021006080304 81
    0x7141c0c100f50102110a0326602ca0788400a0b1004100141e0300000340b03030540c407030381540030b00910a681c032424100e418401d035541e581d520003000b03502c0080c41c10b510503034601c41e51203251001c1000e18855940c1c22001641c441402540b00c4c9018140303038071030002d1598040c601803d000040f0541d00c03e1982503e011805442c1c003142e10269000d030a100c900800718402c0301d451410350010301d5941f018000c010400160f000341404805603280741c000c4034401a03001403c5151401c2c07620403001d011903215030000b511511a400111b07118088641610268403d6028211901c0d282c0304003508200d00b114540d1401d841d2a8050300200040003000c1c092000c0700018003500325007401215614031004028002c00e40d16800f02600c0e07446031143c107070300801d0248000b0880b0b051039400c0300ca07986941001041580d8a9120215850040500d02c40d054055600c1c0c202c001101806580d0281094425601400b9901d07000203140c45103449018011a0400c042000b0000020084a0640d4055110841030540c040c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 622333408 1250 622332158 622332169
    0x10f1206031a27071208090307120b061c060203060406030c090e1501061b0609020d1110031a1005040e070201050106020f0a0503040902070303090b0924010e04030c02 73
    0xa500c042c20380b40122080c502c14000031540c481c81074042d4102c1038420200c0e8071054400c251070803001e000c1540500e4060000805031520074130240e104001807443d084e01c250109040c001298440242e10440b060010200400c04a42c03079802002507607100741b8600c13000b80d140c01a024501003e012180c5c00408280c05071207540142c2c003c1d6400420b0000d10325541c07007a9500608004105074003a02540078241001411802e0f02d60407214035036208840c207440b414044054401411046030203940d41c0c0c1c803800c0141c640041e0380c080316004100ca14507003c0c1d900103000450901c1c8200c0f50405203010361081074070810002d0b0020080d4203403581800c801f98401c080d25284039507084540b9120300c40d820449119030541045040e10f0003607098802070407265080690702d00104c0c400030302c00e400c1030100f404548120390181c500c5500910300499000c0d0103442300076071020161140c40c2250441344c2058070425210100d04150780c01c180b0f1405503076142844940d405040a0402070801480f041d0440640d60350 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 622334658 1250 622333408 622333421
    0x11040f090f0803060102011a06090103021c0504080d050618220204050a0b0102150c0307030515120a1704080c0d050c0a080a0201020c060c0c04090516091d070302010f12 74
    0x4410245400c024030b08154025400c22213040340107608003840c0410f0503100f04404006510040c0c50242400752500040d000b94011091040e020414190036141c0007989008243c0501d02880703034165982c81007440e40003941c00c0201014007a4007880a503072306a980b002402a4804055a030080c4841303140500b03201202c0300c5280103580b00d07080030113000c564179a40d8071102003400241c08481c0026000da00780302a81c80220b5280d60504001c0c8000b406c1140660030241d4080c1400300035a0001068000069055905218403507c5500c0f200100c1d0402c0074258a002110311028510303810a890700740f403c2e5907801700100303050154078050310400410104210f003410080009040d0298151102c060a03075560303400605a0040c4108507045865091440c102c600001c1c0f001d010b001c82e0010001440701401400d90708580d207214000c1c9440d0421040f0a09034040d080004001c01c12031040700301d01001221000107014141c01400c401c1005030b802a11404040440782070110340071000c402d000004049 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 622335908 1250 622334658 622334663
    0x1b12060f0b220503160513050705032a07050a0b0108010b0312160215030f0109020702091f05091005090a14040f0305040803070309180e070b0c03190207030312050411040f09 76
    0x45e0488500070040705441c2801a140300b540e90900c4142e04844031420380d10305985080c0403860400201c0c41c000300117060f0320000c07041c601c88148102d09024146607164042c2034241c0c0c09800c0750010034100710155548500400c84c4100900034407081c280025190400840c0004506000180522000c03451041e0342c0c0c2111b8001b0252091001e043c04408420343c0308603034032006021100004961000b051098a10280d000740c640d0300180e440c40000c1c20440d035084070b0b280c28040d0018000500f60340da0b0415601c182100c2440f581403c1c81d0034148982e942c2d01030600070b142810002920030541442c80c540760300c0381e04901030040c9800e0706d0030b040c1c0c1d080c42160414840b900000903c001419040305005088510103403102e455084400da0302c90031030b00c03240300411043e0041102008400250f00c0a0b050f04050711050f40d2800345074210300803000600c0003811003d0782211500700b0a05400100f5000703500682070050040345003d60301d00e1020f00c4000d40543c482c42d5150035040503101d10b0b5014404855 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 622337158 1250 622335908 622335913
    0x10b04050a0e060714070809030a0f0c08160b03070e01090902070b0f0f1308210a0b010809160605030709030209130b280c031b12060f0b220503 63
    0x60118a81c0003820074103900e10141c0c400d9001286945110306210035089801d030f03c40500307201c410798a000080d8000280c80b50b061003803d8184010801c3d03460030700d171501c0c400c1d41d140c14000d180c98545130800700c03410780034502c580d586a010460b840c441d004903035104a4a01d0b103076641342c8a6000680d020886500300c04201840412708408000310b180d1007501640c400c01c4041c4040d074995140c0403120b0001c50704044d21000c011019400290300b280507046a1480b8520b460b40c040c0c429a001011500c03c86e0000801a110118014956004003d09400c812644040d02c05100c0d001075440d040e03080e070f1080380100040007000441542c412009000a564010002040c600f001d15040003c000406020340d11100100701107072021080c254540380003040758040e601c45c4109400c80c1ea004141c141c00303810078991111218401c03044181e0000c00013002e142c59044e881035105c6848400c592040d007240514400c040f10a20810342118243c0711300c9605104000869a6840c501b521861590b501690300b61 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 622338408 1250 622337158 622337161
    0x810090219080a061a130f06120b0a112805090d0803101401090303080a0b040e150f01030b182e110f031b0403050a080307030c030605060405040e010b0405 68
    0x304003c242d884203140600d50501401105109005140094074072a030791021212107000400c80c081d4000000440031a40000380c1d039a6960340c903500006611000322680000d010401c80d4020702845600c1711008650a800e04010413216010545054660f410820490710794540700c601c0d204008403482190090072500c948606490b1050682d003007a01c070340404c240c601201256401c0040c03a25409800145d4821410340c0ca0340d1425500240040c000349001901c41c441c0c44004c1d1940d00986000c4021035000b44910b24003103e5800b82c2e5640909012036101081e0010008600101009900038811004a21b52401000c581078545040c0c840c049802ca03e28049690f000342540c61800e0320214000c0d02800b20400400d400300041c41a4001d000c0784000610200d4400580341c00c006820051451045191a0710b03500c584e4500030401c54121180c0350000108285107616020701c80d800c00c0e642c18103002103401e04001402500590042070301980c1d88403002d1614110035003007401104009130040140d03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 622339658 1250 622338408 622338419
    0x21303022427010804020102030f0a0210060305030301061b0f03080601110105010306051017030f07080f160311010203040b0403120b041d061e0109020711100309020310060810090219 80
    0x1e41260302e0846926104540b04111075010b101100c0c07240354140d01962901e030010383d1070402c5800c0840b00008610a4241c00b5002403050311410300598005e0f401143c0f0ad62400070300420496040044003030045580d0411000141c446a210360415030508104610303598400040701d00a8088100103c01c1d03007400000000d010050740b10703d018403c5141d007000625100c1c081e03901c008482032040355065000300140e800106501001c1c00a4074407501d80586410780a40c0241501d8101e440341c00148616103180c47c04154202030406a07202c5850020740c2186040e4a44000200000b807000d0140807011040003100042d07075214203044d01c00104104265445414000840600d13480c01d040d0a10440d40462a407050080441010a4842d032915034141c0c01c04c1c0c4200c0103500089421600c44a4a548910040d955a96414184502586c1c0010050564010107250410715601038100500d042001e01140c080030961000d084d042403400724612a01d03202003107441180c00e41c0c000e0080c2280101050 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 622340908 1250 622339658 622339687
    0x10b1f0302030c1c140601020115031b03080f040e071b032304081e060f010311130f1b050f0703030e0703020a0b0d06060201051611010605060a0507150213030224 71
    0x10805540c075150041c0d481b1001682228207021030401b001c08021810800a000c1e40f200c1c403225410f0fa0640001036030b8907a541c0c41c3c03d1304140c03511000e5000114050050032079403204545d0042003498401c660310040254030030200420480030f800c0291000703d510704000c2c03142c0320a101c1084814455030304c90761086080d889200c0c280c2601e80c040200320040c1003851001070b03140e0059a004400d00c2259207596101d4286a101c0f4a1031900440c803100c2c01c40326142c0c10302c1001c1c440e81000b8400718058208400040c00751641c040100d06121050044002d2401000b080c2c59200b03a040c240016140b0300c0c2c41e0740a00d09540c5501c006c2d403200c0c0018001c141020444040c2807070500f4440c061141580300d400c140d0030307a5811103074800420079007640c0800b03540c0305144c5480c211810703000019000b0b440b400451000d41c0409915008108009010342c200801115444000f041c1c3e88021414602d030892152000d90340307440080c3c030451010008011022050705500303401c400c203090856658070807000466 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 622342158 1250 622340908 622340921
    0x80a0605210606310e07061d01210e01090501181506080c042a052106030705010c030212120f0124050d150b0309010b1f0302030c1c 58
    0x12607a0141c440456441d00742143c0109280c114060440801a19050f224400810700c0c400c050b141d680b581516448248140300300740150941d41d943c00d4482004042c40f001c1c040d240200e031410407132044e1030b051107000129512000006004800301c1c01d2405040d050b800340c0414038014200d0351900c22a60511850480d488141b14404c01802072400400c00e103c10444050781700d5061383e500b009200d14803a107044d45c07120030a01d80d071038990549030541c1140195107181000c0440e0100e4000501c00d6904100c15030110901c0c0c0030010168034502c1c00c0c0b00481e13200c95403445494180700d400c0d08038108140c005c5c44a85512003c1010007a11891211488940840c09480080110020030004203106103501503145803d50a048200008150040c0c1100c00b41d1103551079207080390f505c095070320144540103c070300020b0a40070f14082d2242032500d004c90858400e414050b2145107151260303911743d00c0281d00c8440d620282d080041c2c51390340b0f90b07113400854414803c02e12040c140d07081d01d031410481d681c0d03c4035 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 622343408 1250 622342158 622342219
    0x71e05060c28170a11060403030c0e0a081c091e14090402061b07080307240b0102120d0f0518010c020d0e0405060a091107050f030415080a0605 63
    0x400c18045140e05a0640c107110000240070000c01810405100b010740c0f00074090115a86040300010040d20112814004143c03411000a51100034403001c0f1640000c64000c8d9010444507004980c0c50030304015601d20783c18141304c500c5405401d1045d401c90085c002080101f04050140394400f200807041000d130407680c01380100c001d800c01000c100e035083c2140864441e80d80586968a0510404411400341842f5042e402c824070880002003051003050001e0300302a0302c070b07801c10100d03001006d9034004465507100070702012910700183c500d2581e03030014401d030000c414009031699891038241d1134005011000f0103840068103080c09e02090311f008151035140c8224001c000c002c08d04802d64203d844a20700c209400018941c51020a020300c0e0070b038006034005000030322034840d1030359440c44032043d111100d110310520513011032100c09110301800603407175810401c005145403c0c240705001c0701040310315000381c040000600008908400a90010024150040c81c0b42045081c0d8403014000c492580c4c03c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 622344658 1250 622343408 622343443
    0x30309030115320f0d210e0f01171905040b270309010e0a03060c030b10030c020d030e0a14060a0b09010323101506030c05030405071e05060c 62
    0x10303120320002001d050303050703626240c00055008012030b0401016046103e00e040d8041e00d03003105400010000207041b0044c607406480b8400e075021001000d0841041d0595450182100d099203105036a0321140e01c084465060040050035241c2d000c0a1690410200194180c203181605000c18000d100c5452071096121045a005001c44d17010300d800c030003040498281c1c4030792040c01008520340c003400306842c10f25006005500c200380c1d01d44441040d15007040c03600300804e3395100380f501542080403406a10030380508062040e0b400d210f400035601d041e0305840004050703a0781d24601102c2028807001e040680c004403031188201483c0c14041d1280000da4440c1c1040f807034040b400c142402c00856060403a50410420325820010f90b058240319400c128019115004028503e20001070714443c50b4003111190101c000024242840501101d51420100d0b040c44018800c1000081000030503070142ca003818034820b0303030703040c600302e440d0408010790001c0b58041d4005ca511600f0f25000151385022031814401d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 622345908 1250 622344658 622344689
    0x210d030615050c060105150c032205031204030b042108180a050307080d020f0301030804080c0a0315110408030c011b08070f0e060702060c0c01020c04050c090f030309030115 76
    0x40680b400d10a185800c90030b600141d004001c02e10f0700c41c07c0a2150304c0d42c829200d1826000c04605410350781b0554640d003a614802d208504c810100030348035401b0340801d400801000141241e070f03d555004502c401010360440c40005030030041c400b040c41102c4211510301d007a0100c07034843e014010324005c40e100540000c88024480c201c04001031031102440d08040039601d803080380e842e0108140d0102800380607258080149940c204080790095000f14002c2d104261114100780501c0d00b481c0950302554440c1810f4282403012075280c0050700c89444510400103400c4140079801e1000d400b442d48046110300001c500b41800c42c00640112500c0c00944d5190154040c1400d810b407003e842c1540d0550010700e07810315a0001c00c0c0618500180c41d00002c01d2682800c499600007481a8000018000c80d600040743e42603840d601000144c0b05120222428000ca03d0503200940d0103020301900144a00300001900320107840601c1212210f41c2c015009000308504840703060124100b070305c903140000c1d07005907 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 622347158 1250 622345908 622345949
    0x80306091005010c0308150a0602060a060b041404020a03060f090204050a08011406060a090510091d0114010f090302060d05040b0901090b150f0307090f0e0304050609210d0306 77
    0x21044415a02d058442c99013448407510120f0b081c2000070003140c071001e101d4070708030841e603a00300b000e40050059a004140c585404003c40050b190203038020624941c3c28002807008000407021104001c3d002d03100181c03110041032044002c2c00041d80b14410b4a0038000011400300a5600100300f0f56000756003240540c1e0707444180c0390884e908402180caa2903c9074000c503605242a800916454029103050703030115841c0d03800a003a20100d0410300002c80c1e10aa800c02141801001350f02d121061039417514617035807501109100181c0358008490402040c02c81c05032030640115040406160050200b58851085c40a03c0d00140001e0310246c40d114410301c0000c80043c03050044444081c0e1125499449440e140d001c071990340105102650722449c07856402c09140c03001c01014006208542e008201820404040d40455001c5d621502c0305410402c018071441c3c64440071924581801d607070040324200341443e60a4a88403105407a412030041140c040d04c00e03680b54101c40242c0c0e003546002c904040244 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 622348408 1250 622347158 622347181
    0x91608100b1e0103022b0f050906091015080609030912030310030209040c0b0706150b090105030f071b0c061b050a0f03030e0102040f0815040302120705030706060308030609 76
    0x51100b116001e1000e40d10886510035005010300042c00000d403540703040c0000b2035040c002050312081c1211079840c901c1484030805c601a842d00000342d00047c000504182600644440311103038081e280382e80740e51280e49601c6110003044005d000b01401c2c0e9400d0705000c10714a48070781c041d0040c140b0951074012941d52041020040343d02400d003a4521101c41891582032002d030800c0100266481c07d14200300180100d5400018540d00d441010002002e8099034180c00070072259420810900c101488040038590708102141d402000c7c118914402c0c1c0c1d42c083c001c43d203085022801001b070441400f0b10000300000452210141c0d8100c0d11a0701d25283c0184440c00c60180945c030241c41a4050500c220105407042400c401c240c0c02842c0c0030904003181c031485800d9134400e50020820b80958101000140424802000034240355030810b03100e4141a200203507117002d5100c0b2820f8105001841000300f007010400c80f070b5400d50000051020b981d803400e000f24a90030031141d56015080c0300d00021003801c942c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 622349658 1250 622348408 622348429
    0x717100e07050a0611011404150507050309030703030e0c150a09050316060507230c0405090c010c0b070e09040b091c021b01030f05010803030105030d02070617091608100b 75
    0x103040142418941342084510460724500e824065685004046210003892011486a0b0042a241c04d5102c0440b100c0400c0710320041c0f81004000061041c802c8221020044030402e6415203004030300c980d500280d42d401c108284c0d0043c2d520102048a041d41110100301a01c42c0c11a030f5160034000c90b42d15400d15481b4016010300c0b208000d415001801010b0140b005404058084c07401d40c00b10700780030f010260f5030b500c07c0c0c3c643d040c443c0c0c8042e44500703680c5403074000c141d4003080c030034041c1c180382e00c826002130549160040c0045c0f202925800060b50309100f20030411001000030030216040c10b0508051080c164180d40610481c02803a046074646501400702c180364441d02c1e03000742090b82c0e00c0ba4841c1115040d640c10030b410152107140c5007210f50030074042c25004c0c04581016540d02e5241c6401c151030200c90214280a40d00200d41c208255504130301e071030f54204030003021800143d4896100700c0c140381c1c03540100d07140307819650f1010689100000da0080781003807405080118085003130800c500440d9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 622350908 1250 622349658 622349669
    0x221a04023c0a03091a1807140f0603191a09090f070b0a030b040f02030702010b0a14090c1204030206040c050d081606140a0b010e04020a0e0f030717100e07 68
    0x50411400e80040d110794005a00c00380601c0400c4980081a481042c1d0601d050f982686c902d003507005101900e02051040a0051542c000d801a0018200340400c16040490725120300c580c8010000441281141543c41c401d1600b0b28020017080b6100c035458185600c910311030900580c02d103c00170b045c1882c001a0b0b0440003021000400390035103441442e0307000740d11415101e003c140c0c076441c6105803915a8003c002a012101a016859107400100203003100c924860300b5200d02000d15041102440c0411203880c3c074030003550103e0096a88000c3c0d00c529200305900c003508400358800f0041416030100d040f034002d91292821000c00c0359200304018002c4001203018245080801028402080c00d80751080c481307201e1031000c1400508400080c1d00c03088104c8480c2d444649410100303083c1d60348403814202005044030704506000710003600924100a205d00070b0302808a0180400f580d40c0c080090030300416101213440b5044e010b01c01055114803480c0c0012480604015112401c1900800d2050a503031703 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 622352158 1250 622350908 622351027
    0x30a0501060903020f040504061506080a14010f0e04061d01090312111213051e0105060a0303050913061a0d0f06030f02010f0c1209060e221a0402 64
    0x15055402c00006001c00341080727400c2c994070f100d030880c01c1000d1584403009018548a0840c9032500200071b1041d030346180c18281401d0b80b0761005009400d10903504805170b4820810001c004d9130b0341e1078070310f00500001024440900f4918003800700400c05411680340c091203540c1d00c2140350140344941c0c05544001c0d0413480c150006024024888540840440d0711204c51a0201c5a400c0c0980b10f00e070901072290301c5d40e0000c0e03c1c0d61444407607145090194940240c030559031440e0540c5907440080590060b032074160311441500c0b1400c1c0015045803c020081c0c00e17450f075070031400c444444082c40254006117000c060541048440010410544a4141241c0d003005520810560560045624140569a800501c1403004802c00032400c00b001494510540d07071035140040c0d00300240646900b001203540c81c821480c0508400c0702520703001801c00030440c50b010120340b50403c4170101054240010380d0680143c4007050300c20712107054484464071845641d00342c15082440a80c2803504440d80c0c0c50650949 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 622353408 1250 622352158 622352179
    0x117040b13050a170a0f14031b070203100c0f03060806061012050109060f08240c0c150a0506100e090604060909030c050f01060f14030708060a02030a050106090302 72
    0xd0302850840600d0b4401d00c141c42c101c4142d9503480c0d41030f103480c0d144a580d0081c082100c0c01250741001c001c1e00b48407402d00b004190f010911110002c030740304c0101f600c034005807290440e4040103620004d484a46600800b55214100203446210007400c01100940c0010842c0389842c40300340c002d11a04080c2c3e24010040c01403540c90f0301c11b1024030081040e000d010480c0301a03c00e005021940300e06400f03082e1080001c0340ea1450400c0301004690f240d00010321079040a29105000d400d488142100880b240c000c0581c0c564400500c21180c0c066100c510229018043c0701141d5034481c009494825074101d4020022a01c600c0709100800180a80b160081040120401000d19100c0d0449602680050002c1b610b240c8981c10982aa584110b0840100716002c400303004001c403e012981803850710301e0080103020b01c0c01d102c0307001501031071007070b030303c080300c036140015402c0e1400d004100190807071000301c80c0181402d0301e0110081d172040b545240032901d000c0c004903c240c4170300c09907012a83c0040c000d9460 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 622354658 1250 622353408 622353421
    0xd030c050f03040f1407031203020f180f0604031103060a06030206030c16020d031706100c020f0a03050102040602030a12110f16020405091b100206160215010906050117040b 76
    0x4940c0040c1c015107039405804e42c60b0002400454101201a104102071700050b491850304070410354901156209260040c0000486070300d00d1020f441072001101c10a458400082002c641060613001c00544c00020000c0c0110a00542901b00140c20344180c0484009130b5641d0041400c03500c060200035880b0300704202281d4030480503c060115000e04400c0c0c100705005650001d001003010403002c4000c41d640d1600441460710103413a4076402003013a40d4416060551501c010300740d81c3c017404020300c184941112001c141e11012880e0001e980c0c03100c002c45d42c85840b03040180d07486d0070954039071002494400c408520980140207407403252110b001039070b09241c021600028a900301280b8901050045a05807000d603645000340c50040c2c141002503c1c2e2000412041000c2d06010040c16010310781c00078103e0150340d80042c070a40d200d0b405058020b910707115101c040b400d04224400082038040044008142658207074810001c4034803d1701c455841d509070a60140b180d80e0200d0f03001c2c00300607094000070790 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 622355908 1250 622354658 622354687
    0x190608070e06070b0601030b120606060f161a130c050d03030902150904110408060402040926040513050601090b0c0c04151a070b15042c0d030c05 64
    0x401510509001c2898401800414030319000101d0540314001510148031465030513100e070301111001a0b86521000e801100319540d52040074101a0042c9800204852155100790507159040035048484110010504103036103052103100c844c4143d0400c002c0442c1b0b41d00800c040200b0104e501440e58000940b9050810140104001040c5e0a050305e0701030700c2006945444084921180252600e502c5088210500088403c0c82003240071b07800c8108810301140320001341c0c40c4d070b004d0390480b00031030264000c0c50003130a076009461440700c0c818541d8050002014460000d4010364409440100712103100c1c4448400750b650940e00035021400440d424007500300c080e002003401d60b20b40c40880d0340c1ca803511004101290f0702e4035000c0384102e814410501048804418840da134241d020103003418040140c0790851050000340c480442d400644030802c2071515a6041458000c440003140e100303c080e1004d000c0005c8894600c4000e00c0d000b50740d4420803183c020f10030500b402107203645150820b40b0240e00b03a01d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 622357158 1250 622355908 622355911
    0x503160e0d0204020c010f06050a0302240403170703020c0105040324022109010f02040b0f03090c040203070e010201050604060f031b2d0608040b0c1b030a0c11190608 73
    0x150812400e02144015071101d00040a02945110001407101c0746041f941003140e5560300418451010f0000c100050b0b07580100c28002001550780d000c0761080082c803448210b200d1980010444060701c07000c10f4095000300302405078240a6029556420b0981004490522460000405280d12080140d052808207120034910b0002e040005217040c0b41022071540e42e000e0103940c14440b2000c1d0003005024071083c01440f1018003a03003025400d00781800d000b030390140254100705c000380ea0f02000041d080d08007003000c50704102002d0301c119600d060540c002000e16460100340382c05582800b0210380030703003428400c040803101d9003078550300032500b10f070b68800c0ea1046542c0c075410121b04807400440c4200002c24064012005101075440ca10304d484582900c40c215540403a043c0300c040ca0410bc0826020700300c40f644240500c81099a820440740440c3c0030361940300152000f484003140b0000500c0c4c211007000420341c000c60b00c071101c2c4940882007107280c14010560b0408460105001c01925001d06c4925 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 622358408 1250 622357158 622357187
    0x70c0308220801060501020715080c0703090513090b0f060603070302090102010b100503010501090803030906070e12070b090f030f0a02090402150a050738090a0b09030705070501050316 81
    0x1100e200d090300c1c1500851662600100696556100100030f81d40c0c04001e020010641d08100e030481b18a6594080c10441000384401d02120b0009030041c2014898031011000d050018003017092526001711200080002c00c000b140d86c0380c0a1404110022142905030b403155800928951455032842c02c110041e40250610358155900d941035215241c1c0c942080f842201c44a0382d80d90386940c904400140b0006080d8400c90703080d0802c009000d800c80300410090707401034427070800c808545104d0003c280007400c1c2005122460080d4403000c1040c07502c210003090340c02411140021103500e2401010340382c0245186186840d400000001300508285c0c5486621034001000d4031000008101200062350001c0030100000f41e00140f060104650121900120450304559503010300842c0c00c180400d06401c1039080744448841300003045030070104480000b01b43c2c407100341909401c20318803c81c2e42e900480d40484140c00351b400f000c01e480d413040003a82d00c0342550021101c0740440303c45094990f0110a080d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 622359658 1250 622358408 622358437
    0x70f03050f0d1103040303110c2d030a08090d0e09011a0f0301060c050120070b0c040f03080c010b0607030c0f02210a02030f0f210d0608150a02070c0308 67
    0x8801c00364080c4102c140c2c24148030183c41d40e0b894640340c014111140c010f00d80c18011001d000d1030401d801c00041440c400040507001c0384c002c141c1100c805c0040d01498008100c80d00c4000ba90309a650fa02480f56070007110148111102c44051480a80e4007849800d1f40c9500710219500400c09044070115000641070241c450038944181c0380000c02017a80243c00080c049030094903c40c0410030248140c900c81142e00d580150903c01c005032a00203480f680d9000380c0b821403000041003d40c43c0354022100100903107405145410343d07078039041c0c5454010300c064200d00c0d481d114414159040242c115074031650300d0f68826080700c195540311025080030810130f0741c01108801c0d51101181c800c041c215041000c0000601480354a0f1040601d0310a01c090840c0c03454008101c0c0c03208542e00069526800c2900d41e40da0b858051484072401007500903041c0310403565007000c10000d00c2d01e00210303645404045111014a0607a13958040405078410b130726000f003116521000070804180110007a210780c00c114140b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 622360908 1250 622359658 622359667
    0x110102070815101706190606051206011101150504050a020307140c030903150f130b07030e2103040b0c07050304060503130c0f0f060e090a09050a08030f100605070f03050f 75
    0x9250010001e40b854039042c2d5000500740402d280c1b01052411000320034041c140601c5080000003007141c05010b2841c0c9030865a04080b44140e030003128000c04040030364008100001301507402100090052103158059444c04010890040850003100d10a029a4031895841c51120742c0c1c14501e544140014405408144036585082da81440000b07260307190b00340d4880050600c0300002c10071203009001200c96840400c0d01f5800100481507496008a541c00c2c0041c0c8203000c10900c03800d01304442241c00c100b4041c81d6010415100340006980114043d44801d00e05d680c070038850142c1441440c50140c130542c02804100852071043c4001d45d4040c00c80655416880318958079991940d409420004004a80e840c0a0090f040080e41d504000e03c16490035211006418000c40c60300d000c090580503205407540d12500c240f000420090700fa142d0710802e52a035a00e85800c0c0e0b40c3c80080180d4500800c0080d80f01d001030050320810684058a4010703444041084081d94191861342c40a0780341a44180700f4030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 622362158 1250 622360908 622360919
    0x7051210050a05190b010c020112020706090503031005030a0f0f08090d14010c03090317060103140a051b040e070822030509040606050f07060506062511010207081510 73
    0x1d014020805640d01040c00d0500d9006041242074040d104031481d850f000e4003d00a030b9001200c04021030702800c14800f10a07003035241001910490001a101718142200c01c400c00500000551103000321a4151110548500405498140d207400207010b80d511510500086011881c01d1800300380726500482c680344a00d00407130040c000c1c078001078074980c4004400c810761038400e0003280c00c003403494070f0100b084c268a41d90140c05e42d5120b2a21414170901000059a20b9029034003040c00c1c008000700c00c0c038851800c40070310700140008407440b0303980004841044440d00c00c1c4a051314140c1d0100c03243d000c181ea40b480d808903034800c030041405205100d080c1110100c400103860700e541581c025950656115206800c1c04160380d801d902000422000b000720210019045007a20255039122002241503212100082c0c1c03a402210740e000642d42a03e140b00158149801c04010b1440c40780c941d5043c60407200d0700581c0c581c2e065100c5c1300c00342d0308008400c1080300d44c101000d5a00c50708052000b540d140d00d54 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 622363408 1250 622362158 622362161
    0x60c0215040b0d0e0c100f02011109010f0e030c030a1b0902041a07240c0207050a030f0f081c050405010b04050403050415180605120a0c02030901030236010e1207051210 74
    0x3074901b000818000d1411100c090350a000700c0302e0020600c15100c0c644080321000030480510f40c170a507820040f440d086030629071307414054015010170041c21038a1584003414001900d102410265544d221600400224103d0f2402900c04413080c0ca012020050754500740105298021082200c5c4002034102d5105000a41d0306950326140140200040c885c01c01c25011340b0300310586d041944618001c00e4104000f4000d03500d64188550300c442005c1010140e85004e0055000b000340240080055200010198202da403199214500403002803011285020a01080303d00136140600040c0d0204400c2c0000003007100c440c0303017000c85490102503000d004001c5007000c40b0650090000520000750450381074001c0c085040e04804022030400240360b0241020b540e92180703229071070606801040560214410790000510014200c844824503005841030280210011344420f02151000b4030118150a0004860004280043c0101201424002004a031080440ca0352606104000d80c042d041400e6 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 622364658 1250 622363408 622363429
    0xd020409030305090d08010302060405060c0f0118030f0302090d0204111e040f0510021b0f03030a02070602011d06040b04052d0601060c0b06010f090f060c0215040b0d0e0c 75
    0x19981c0050f0318109083c40604010035440c8400800107000018009aa0703860116400c1b00d404803000c644d01ca400031810f6046c480e4001541d0305552a14540040c0070100c4030400c0031440c4030b50b031454201c180d40300f8182c0c101d01901c0c003032540043c0041d0101005080a520140c0e4004114840a041a5000105040b5080340b070342410b18440000c241040844c10032002c100c0034250403920400c030003c513888000d5803807a142c501002c15200c0c0512601b400d40341d2000d007151140024054950b245030b03400c801703542d86100c0c5c4100001507280ca84141100022180000340c142c449030b001e45125169511a104040005041502c9502481755048015070016084000042c658a200c0700c40c0c0008011480c2404d105a03c40c5082c44100e40f08400011840341000c0d90100c002d00f03204c0c0c04200513420441350164660841349900c43c000c0700101d941030b00301c00079407403541c0f086442043d8410008070004040c025403103094540c1c50706111030b04149140c0d411003604490711317104444080e9207180000d111448c4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 622365908 1250 622364658 622364663
    0x12091110110d02010509030d0b04090209010909120207050d02220501120b06040b100810030b01080f0c04060e040224031e0703060602060705070309030605010603020a092c04020d020409 81
    0x165031400d034050711810b0040c1114840300380001c100925040b07041c5603c902c501e640d03c4c50510f681e110102001d0b5241e074455030900381c003e06001007941e1507500050060070440401e03070300074130101c01c000307100783c030014006054075800f900c40c001c0f5000d035500348a0406180c2d0a0131000e0910100040f045140e03c1c41607600a0800c0c641800c4645444d0070700540702030780504142c1c06075080c01c01d511480d45404a011076801040d2030500326507a2012a003004ea4945504010b2089a980000240c603410000c1c0c038807520ba510b40213503506041040d00f00412a0460320500352140c10440004015181078400925441d20503011074070f50b08200a24181d00f507000700c0c3d07940020209520802c1d045540c0c0c60390560311041ea401e003004014100000030307540c1d503402041841089400144071082600c104a68030003954008018045943c60360b60181c06904110241300014180c10781c0010f6138207040b90f01c0403d0300ea0030410903180700590001803030300400c01002603801c1002c03c40401d0050701c642c411480010b0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 622367158 1250 622365908 622365917
    0x106152721031e0306031502040e1302210d09140d14030d1811040203040f022709010c080702060708131a0f010302282d0b0d061512091110 61
    0x9007186415a4652407e05050315000e00c107010078800f143e0318061043c0c20442e00782d450421034000b8400120329a40704410384191b089400d40c0c0c240710a00000b1301c02d48140316510b1340100a5190007400c04a0f29003115201d51000c82d19600300c0c0810380301a0035054a00c0144162031411103110340b01c50540f8505042031802d00c0e03040800100303004011150030b540210447c0d00f5072860501c1d44a424021006510180c49000006032452105010b1050180e4400242603903801d60318100c50824000c00418040740e010940603000100c1c044d00c04500d6a120b080d080c0c6500e001500c034403c3c10a4480d03028402142d0b0003905102024225644509241c450003a001d405003036903055205000ca080080c8418a42121445e425150070380d02c91884241682c80b4401c584203011030585149070354030303059030908100050818011410b80240c0c8020703e26800205010f22801e90340d640d20403004540c04a4103000503540e80c3d4078111056007504002110381c06250183d0803c92442c000500d0741081054600105 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 622368408 1250 622367158 622367171
    0x230f010c080a27240e040f050114030f0706320309103804050c040303031104060804080d091227260106152721031e03 52
    0x1483c1c9414000c944801140c5984485440c0130b900201c0440c00078150180c91020f024045290351051174852000d040040c030030b00600c8152001c041c010082802009004001c809125141e414005890754610010314002c0010f1881c04104440102c01c40b88103855071155010030300d00740d1159103018006031046051700e90b40da041c0f0800a40c40d040d40994032108090070484e403c4480e20b229000c03500c1d00d247c43d101c0081a10348000503401400c04240c20f013640075140c4028403420000910182098911a8904006012940350140e606004a200e0388001440300c1c00001d0000d489613010f012000c44901000c5600281035071418010b07120f444041001409425007101e804031903c1e850750000264000d40c520303043c10500000c801e03c0c070404141c041491113259050901e5425030248000b4015140f203c40701038048540100141c580e0131600d1240700407820180602e03140304160b60101c84410b03120036150502701100110590f0031003001d60a00540100c105c0080c0c004282c00d0440449a58000544 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 622369658 1250 622368408 622368437
    0x1109040506090c0301062f012315011103070b01030302011a060408100203060d0605090d080a0b03100b01030204030b010f09150e070e040f0f0b0307230f010c080a 71
    0x44034001040c0754410703402c1005014040500e42c08880c15100c051905000d100d100c1e0409034100a890303032500d141400603003e1a143d40e43c040d40004c41d00074188101d9840511080994400e0b4007040d1095181d06e01d00c25080180740d8080c002d030b2800103e403030055034101a080e48030216500030991081d030150751074451892035501060030110303003454100c4605060a04194201784c0d10b0074085194617020307038004042480c0f640c90301441c1d10610352104080c0301d079103007070501c041d20f03913101215880c0420075110125040c02081c2c05641d00805020300108070360760384d4a01c942e0150800c41c8400f170506600704004030104001702c0d1038502a06501250403c0d070ac2c68407080500300c0b50500d10710b0300104e5164400b4010030400c1000c1781e0304a0700074505902e0410072000000c00a0000c545410542490f10307440c2c2c0b0f50255240c220f01e0b041c26080702502c0380b10faa104034403c1e00a4a049003103c075080e118009280030b00e041c0100b170000c84010300d2f201c0302c0e031034141daa0f24505e0b600c02070540011541d90b90202c1403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 622370908 1250 622369658 622369661
    0x50a2307051b0d150c0e0a03080a0206011a030a0c030e070305060414060906011517150109080c0303040e040c0909050313050d03080106030905120a0905010e060f07021210110904 78
    0xc00c20000c1d2800e116035812600c1d10b80c40400700c04c6003038052584520300e0607181c500c58101941490001001c0414241c2c1e24034090a090b0310186900002d40550306c0006407203050b514907400d5598805030020700d55950400d5101c010144a00103e0900d070303444550100c90142000342d0340295226100918180c1803e040a2018600020300050103620990401a040c800407070002c2c1151142041c0d000c001c0c10010707095a02d180301c1e29840c240c000705107040124a06a075820b917002150b0a80b01c0d0103940742c550041a485812079090a6010ba00c1048100915034003e8103d503400750003002030140140c2c540070a681a141c10010550f0380368004034880046500403000c2000500080b145c000310f0314066a8058001039051203900c05043d0f50780c6403842409406d015007040100b49100301540d811944038081d005c180d1074043d01e030014186103145816404c0c0041200e07200843ca0401c98181415603080094034400500070461a0284c84102d4004500a004031032440b403118880170f464040384402c3c0030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 622372158 1250 622370908 622370953
    0x622180e19111c060f091101031103130606030b0408071e0c05040f0f05161706030613081606060e09150601110a0206041e1203050a230705 61
    0xd144510201c00c5100051010000498450068601009500e840c280c907000c40001c602001d030006003030140c101c2000c280e940c08002c440f03104500742ea00703412120700114111101d034a5100700c40300f8100049000e0702c1c4222031840e0098801d000200b40c4070f0b1299107405c0340031400c0d10202e5584201143d04030400c400702c030320203181c911420000709007000c460f224400b0015142c407509026590b60044200502c0c03c98210054411505000380725500b42041d429916640c10722004000504015012411820a0b5402d6004040083c0100541e468011840103280e4141c1411513000c841008160381c00c01c1c1c0d4000703100c03031240103003400a02c251500d0024000007400810b861703595003100d1004115000643c0e040c5400c800f084ca003a40c15210a101d8031850000030440180d48518040740004211010f4604511842e4030300490740c502c80e82e1107200c5440c6800322440100420003d001c8102110b01c40d140410300c041e10031100c0551302031002a00d220070b9000c1241507030140c200000c1400040d51014406 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 622373408 1250 622372158 622372183
    0xb130f0501051c0c0e1302030a0c080111120c0903250501030b01031814011104230d05070e27030c0d020601060504051e191a090622180e 60
    0x1a0710b003007a551140d00964007401380c403245c0350a07080400d01241910103103401169024084900c888010305064007013020700e101c0c014080d82003403a040c220003600c0c400d4030b0f00001c0c0201210021340b41d10702e005a15411030900c040c0c041c82805001c407415051014141100a0f41d00302030b80c1d03400e040000041c02d983d0f5055140f8141410681003a0701030f04c414900380c440a411a81e04031519886e041d0075800350071040a105087c1d2004200451503c60075941c02c40d000308002001b6001b060b5140500c903a000303031060003802c950441e0504000b515130880c402c552044d0043c0c810011040320300c06190340748022590300c0105034004203070280944001c200b0341030760b8901d500050100c1c0d8546440100180b1403070180074000c4281d003282c030802d052001010642c0400090101220340192030200b0100d0741c49101d40310585e01050815080c041512080392540c3c2400b4010780d00d444020030708001f4040701c008038020546d2050000040340c2c254130500a002003030820010912246d000802d902d03000b4078443d00c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 622374658 1250 622373408 622373449
    0x14010e150103020f270907020c0a23060d02040302030613020111070f12060213030b04020901270513120801060e1e01111006080c0907020d0807030b130f050105 70
    0xc0718a42c020020b0750b0b00b9564001042c0c0c1030f8440900742c0203817aa001002560080c101c074051004007600840d0f42d52015105540800c801540d5601601059000780f0860a01c501d40354814002400d00d030000740100744500601516040d0f40390301107440c2850440c0c5440300d403101540c1aa0071980d00c1060610243c0380f006c01404000e05240401214030014420301c50f00703c00522098080150301d4054a20320076100e01e02101165480c2840030980800f220224401d60258001140f50100c2d2252034038540c0c3d22040c078012041e0342c4c240203001444068030509580d03009080b0342000401c020341d01c00c4e200c22039a0390b590f92945044405807140c40c400c074100d1303c19100d080c682584031040081c403226106003440c01c140d1000c4280c03509401c042c103840025101c20b041402c049500301002800f031171007100a40d840e4225070f460303000884c2c8819144009100003403507040820300d154803a8020240c0440002c0610503010a01c0e4400c0080341c42900300c080c40c5a48920040010345410b280b00d2240b044200403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 622375908 1250 622374658 622374667
    0x6020406391b030f2a0e13050102030f011d041a061813020103270210110a0c05310c020106090c17070207050d030302031302180a0b0a0f031514010e15010302 69
    0x801030805045008a01220711b13040001a0400c0e0368481a940b0141c0040c004c540d41d00b85881a1000000700340203c1400101e0b42c800d40c101200c48a030050b03c0346400c001c00c01c02c611154040c030110807001600e01070b03200c0b5010310b900c1c0102080b01b1754039000e440c144c944034400120302d10000d01a18507107a000300120050751000440b400411250140482d41103070441c6082c0c105141c1500c3c0c800f43c241041c403943c807903010b0101c01c10522149080580d0800c44010541117441c00121130090100c000e02c60001001d941061400c003c0390b001403911840c1070001041407620340b01da00c005c46480116050015200f9003c20340300340002c41c1002c1d0085180d201400816040c40b001c144140702201000b41019800000103075001c0424060f01481940188003038602c1c0850786c5240385190064500f401964075040c210300e51450301c2c6800000716205100d60855907444e42d10345030850b464060300380022944540a0590742601040c03c9800b03040c0e60100f080c107a05050f041c1c41420300070a00c49505144c070400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 622377158 1250 622375908 622375973
    0x30301050d0f080d0e0609210a0f1e03060f1a07020d050c03070f03060e06091209040b06031305210318030d060306020406391b030f 58
    0x100d41d00c525001410302e42110100d10f4044440e10840311070000341440c0450398442d14a0100d9094019103400007110303c08070329a0b80d0740d111160000e140d81c1c030211041140820090150300080707442c0b043d40c20b21645103550030059000320404840c0c09000039958610600c0040c00001d242c078058403c1c44e034403014490500074000c0881c4503480e000380c0b040340322111130000c0000402c2400c0e0884000340c00c0e28081a80d5041c21056426180011961309003014a052080407000403010b205d00d1200340240040900b0140601d2554000c01c44203070003948880140034a0b403601c00056000d030040030b5402100540e0f500b009420a40e0704e00460789000d0b40c1c01d984105840400080e6904045404402d14502610b880114a1489907040044150341000310000503c407941e03014104880c842e80b9006840e0481c3d410030b041e4210b0a40303190a4108402c5c52100d2039020b0700070056040383c030501002d0310201508950415544107540225000401a543d4000b000000c1d214040351042c48201c50881a0718603 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 622378408 1250 622377158 622377169
    0x6100806030d03020714030f03042003060711010b1e0102010b0306040c0915030203010f06030506090309010c11030c0613061209020609090603030d0603030c0c08070305030a080c040f06080609010803030105 90
    0x1074442d078109500801e80b10b0a2000100799498503c0d030788022070741d803003094a20915141d00304940c10340d082800002621000d032203071f41c9100e900810080103002583c0c0c0f202c01c2550191340024082c03000e0f40d66101d15601710b8691155426540790904599400c4400c2c03007000a0135101c039030200741e000346c12900c10b100000d00d4041107003058949049000c6070721003420754844000d12259201950542c201103c1e5061a03041c1d91010040d24058000e0303c0261392113801040d920301c90440142d00141348070f4050800b0804030320003042c801c0030080588224080000c0000d100f5000b4a410031140c075003001c000c100503500800701d95180d07a07072420244407044150f000200e00f0b00a084449000f900300340001a80c940e02841114503100e210b030b008100d07140c1c4a040040804030003000440304102018000304010f02e000810408032a4010f00035458001c02000442d40b0b8072000d07144042c140c0c030620021802c01c241d00b01c0007025100fa59108810b9250020030004072340c006900c2200207400070030051005813260b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 622379658 1250 622378408 622378423
    0x709140705160c1d0604050112020d0f0c0303050a031a0a0b1c02031905013003050403170307033e090306100806070806010806010c02010512010b030610080603 70
    0x550808a456100c01a1000c03a102d4440354000d0100d4038004001c03600114030000111600342090300320f00c040d41c4400a20084482c02e01441124070b00300c1d619000140350002000c0c0c00703144523590f6103159084656540500f20400c2d00b040f03020640218815824030b50601c02d0624040c404210703040d80c26041c01c0407866000b1640184007400e00000350540500304019241172144d181764404540c3ca181081d2040d406800c8400100c9031a07040000010780c3c0ca4003880c58003140c1c080208600e0f030300f000aa44912210558000440501800348000404142d2a155071940300041c96034031540c901d0310800c01002c48100c000c451808113001403105540038000354000c1d0707680303070b50484e01c803407003100214100b03014054030300342552600c1030f0810490500724a000045c121500c0a044401903290030100f92402c0b4002c88900740000c0c8d040d80010210340c414003040302c03884d006040513450981018910340d50180242c00c03884180e0130000902110381410102d800c5030290030f180c0006182024030000e600c41c8103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 622380908 1250 622379658 622379671
    0x4140d0f050c0c09044b0f0b0406090c05060307090905070912060f3204030507021206070212040b0f0c03130303031505150304120306091d070914 64
    0x9010034103040204082240848000000b81140e01c071346071a240c410b00002119051031494000814540300c80c42143c0c41d64150003440c112004c036031b940280b104600084c9400d0090340d000c01010030440108600c40c03012030241c2d01604e0b011409004e1818110b21032480ca60046004280c00c10410140640c0824002c040d80c800860101e4140c50f00320007140c07100e0154004031440481240c101c41044681e90015804100e4214240034071000c0745549898507401040c1100601c0644601a09800c100c84a00e03070f005200741000307801c0c00060380100d2907d00f018250902290300c000240714603d50100809100c2c21074900900d4034013801c00010034603900900140e5034024801240301c07091a0b1060003640d0015490b124514015a43c3c1d040040180101500e40b030b01d45044800046108d081c41d410741c0341c1741c0c405021914515103e694401c03201c1d0003070380c2140081554441001c5048035442c0100300f591103c08520005407111034046600345100d83d03000c40045841c1c201c680c105084020a465032018 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 622382158 1250 622380908 622380917
    0x100b0c0319030b120102120106020604020a060e01031517060f07120504020a0b0c0709050a09020d020919060b040e06060901091503021201180c0c0c0b09040209030d0804140d0f 77
    0x464038002d5015000c821000da5008000302c080c0103800e001540a000c18007140001c5585603640c44e0000d03601c4044c1918040e40040046006001c628042d8004820580040c03500007001c03144468506054400b5403c1181541a0280c0c0038444980070055a5002072501d1800c42032400d1000b8054224840d142e8403400e0a80c0720400941556240e111560051200c0b40600341d031004a10b14a980310b247d01c1c050f100e4250b15010214200030404e1040d01c00095001d04030365020810364082110003c401005c41d030700404420801450075019000720401003900b04940c0341c4031401e041020100020003060710380a07000c240220812682d100c040c1600701c80000c194400d1588036040c1c22000784c405d100a0001010480c0000039000c1405240d10440032210901088041a000c6084600d48642072000e0203483c2981c80c14410044840c00a0685090040c401403030100403402103410f0404040074400070401344010401072182140440703000c540700310064440c50560450140c80c24149240031030400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 622383408 1250 622382158 622382197
    0x6080610121119051b0a1a060d02130509010c140433091a190e0a0f0b07030801120506011e05180426032a040e100b0c03 53
    0x7a1034075000c90380801001c12031400c64040183c00506242d000c4143c207102d0b8081400e515030b080c00082030610f25280d11015078208204090710b4050401c2010b000690300c100c10b9055800165590302d91442c004542e91030224081c501402207030708440405010703905008101d90b81c10000c101100440381134404c1c13607450b514000d000644880b045000d18800c2c07400300c400d12607441c43c0e541d002907410342112052045e03c2e144032940074040d40d441c082e0b50162070615081800c100741d0385004155004030018003801d0113400f035a4955650311140e007a903010070195100003841c0800d256002c461140503000662012504541c0c41c0d881c0c6a42c0e0380d0500c944c8a404000e0082ca04510101c44070a00051100070a1034882c1d090318030b06211205c605880449240205042141c014a210304a0f558940303400c5840c28151343d03545405041480e0000521441041403402811310044100081e101900d40700603001c00c546407800404089007000e41000390040402d109001800c00000116040c445100700202e501 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 622384658 1250 622383408 622383431
    0x15032a120b010f021510030b0a0506130b01200f072d03200f12060a0b03061017030c011409120315060913051602060604060f06050309070e040c0608061012 68
    0x41b1030380c1e0b04000c1040702c0000034020742406903080540141400c513a43c0700e4916900c0200c10899105d014581d01150687c02a8540b440346503840da01d02c800780c0c03010f171299098900886810308040b60044100d030000030740418000003c1d29100d00c0e043c05016085030b502e9081d40c0362840700c0e5585103050003410070118a017064540300c04e456241180030103454103c0c03142050094035100d403012200220703020710381000021a4640010000e00841031100205040b9040c20300c07512100f00c0b803003008240b40c401004044407403802441110081000b8010a44640c184011560b0030080032042c3e000107e003060007846207a40c0800703c03031a44c0800c11180746541d0304440b03010441e420703031a00e85000034034600000c10144480e400303000a88001d05070b00750f40c00c82c0d0361042008200d81681c0149034850380285000d0089a00850045810015510444200b55525408541020b00440782100c0800d00d4500400c0003941015105420080403182070301074611200c070042812145000d00803001c0c1d29004848030303 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 622385908 1250 622384658 622384681
    0x20a140d140a0c05070e19110a050906070c08010c080702030a050301151701092408030409090c030512070b0f161b060609060302031615032a120b010f0215 68
    0x10300c0f5500c00c058442450780c1d05e000701c400b030b0011500310440003106850003044034940c1c8240c4030340c0320a868545042c00d480c08411600754000c0110103800400402c00500032402d0000080000c04031140085001410742c04006c2004101416460941d8014046800e80a42100c03c0d40d0569150a11000c50788030501d80071a59214410f0140c0d40d000409030000c84c00b51000d40080d44030700b94008404004440814150920701390910403410b80e60002e200030300421304182c110818031401745880380062922516954244a50b90b41da85844420000b4500c04110142d09056849100018071401500d011100c80c50045000584c0c0d50810401c0c0200001d880d403400d48800d1150340242c02000403d0301c0f140024020b010303c0c0404c0c1d10034400c42c0303c000349044a401088064800d0300c1901000d10b002c03414180c0280c89003625200c1c1c0381009264207000d48440720800c1d82000600c0c5e58210114008010090031902c25210040c100000036650105181e0000303043e0b406485042c0c4980e4465031524800311 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 622387158 1250 622385908 622385927
    0xf020d02060d020a080601080633040806070908150402010c02010f02071e0911190c1e0b061807050405190b03040516050105040315020a030912020a140d140a 69
    0x42c042480800c4400e44d00d580540c0d82440b86e0b400307884840303181d00d55400b00900d040f2501d0080c004200c540c00c3d240f070301c6210552040441158046054103040c0c032a00250305000c0229030300000644c20102c20000d038101046165551603103c2c40a01e0f607030529800003030441c0740140e406418462000c03820300043d44200411030062400100d00850840c0b51203040d44540201e2040c868864145040c4403600402c0008858564001603d1076400c51444581921000900c0300c0aa5a2502105245004c403107089140c050700340c03003036024030b500e03180c103104000c0c0841200011503122190030040014007500001203031b0690f107080702ca96506c54100042d11500402580024080a202005110402000043c04075040c5c641c510b0385e20a50745c603213004403203174043c500c0041e00031410740341c5004030862158010700c0c1540ca0340c600440c81807401e4403007242000e0300b54080c0006030b004008540a0085041e50401010040302c043c0454000c448802440d400400c0c0016803103060009000b10700398018034455 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 622388408 1250 622387158 622387177
    0x12030507060b0f0a0608061906020a03022406010804050708070308071e150f0e160503121207120b1504050a090603020d0b18070b04090c020a1703090316080406021203040f020d0206 79
    0x1234070b2549528000751940102607044000d886651740e40a080f400e1100108036107904911540301300c0d40e54170011204030201030020340e001e000341e40b00808c141006016440145000b0032041e0342d200031624000e40c800d20140da030060384804903601000081ca00c080705c24200c0c087d4a402048018401e211389004141c007010314407a0784581c010f050700c0c111440b81144201c8100f1070642d18102c03029092040b06100f515120000c80d0b00305070002c2e9415001d04000b6078081042074000403101c03000d2010030811000801c20300000c410120f4100043d140a90141d0080c100d0b0100911803a1328542c0407036414841080c00624140a14001440d40f4031480c580d03001c01d100c11030440c3c1c2a1035980013810541c3d40b0030300078511800d0030845030003145400040c0380c0151690000c44051340740c904203462641c40d000a002c0c001a030208000380d0044c3d0a40e0030000c1d1049000707503010b65840d864030388041c4c644003101854405020003482080041952000080081a01680c26030007007052480016458454541103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 622389658 1250 622388408 622388449
    0xf06040906140a1413020f031014030705032a0a0b0304020415080607030905010204080f01061d070c15020403021804030305180a03110712030507060b0f0a060806 71
    0x103801040c58000368222004120450020b0782e40b8028808401224000c884e401c0da01c8814196807401c3c404441c90f42d484003400014109800e00d03541a400354000d82c4c0680100c1c3d05c00340c0912005d203441d402020107032030803130041c402c0c64a0322001c01d031140700c0005180c0d03100c0c0c10b5400c05031800007403c0c44550a910300504401186455011340c08090f042510268041d900e415401c680318100d54154070143c61000b40100300e2542e0702e100441c09841c03400000c4400f55002d00c1700043d540020445503103080c000e00004035002f801c22107650700141d20090850085808401071012360f580101c100342c0003541252400071000c0351041f142020344100d40c40250004500418016405100c02c00f983c0030301d201b5a8248680c1d00d50070600c003001c84001c86011155009102900300003402002c0402d0300c02030420580d425242e5499651840202e014010350104000140060403c0442d10448036020001c0380d81000e050580004101000803900508090200500118003595111841e1032101c1031b00c5a0b0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 622390908 1250 622389658 622389667
    0x303070b07020706030e06010b0403020402130e0907030201030e012d0e030703210b06160302070315020c1218010c050c040603050d02071409040308100b0703020606010807030216110f06 81
    0x14001e60f10303081e9200350000207140050905800360701081860495041403001e508060842c2c0030030009600043c0310402c0103d40b80d0700050700350001e00c0c44074840c180c440c01400c542441d50001600742c400040c8100b08591400d80720847ca0240c5001840b06c50304c0c01a403900076106203070010fa0003002d0303a2a00780d071036100c01304000d2b00301544019400501d05440001221032000e10606509583d03560b580550700c2002449000142903040a004501e20701910449179001e44d25219054084030f0041001091074001450948202041010740b94200300041030500d40038030f29404140030102a0509410040080c01c000c1c1804001c0000802c1004014005c1100d26580e161155441c05051000030160085800020342041c12041c240548030020340305641036502e90b98121110240203140d10700550340c800010483c521101c0103880f58074841d40060003d400d00500141205400030181410180108400300c1941c0c0c0c1410541101640000003040c038800301000101040130610316560032002c04075 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 622392158 1250 622390908 622390921
    0x1703040f15110304090c09060e01020d080c0403020901180c140702100306150f081003020105070206090a152a02011e050d0920040209150306060d0c0c02090a15060e0303070b 76
    0x52200380c0c2d02d1b5554585503092a5100802d80741d410381125502d01503040210888800b5010758002a446145240715a180940308e500040e0b20400c02c3e008501090108406640801e045200300440e95844c0d007003a40154020600140300c034481d00c0070090080b0442ca0844e00d0b420301a81114010340008010f0108200408034010311201e410101c0e40000b03088000828400c9042c1c480140c141c0e501070795010314205250302072000f26804403600f0360701b128120354001040d03a4924604014110155604d03524021355500345200e01218042c00d09140c5014451100103130380004250380c42286003030f500c00c1d5407481c144040e9050300407041c000d425a41803240c02c0d0200b00340c0f4100d45102110080c1142030b0a030301082400101c1c010000c046800c003080080d5506a070900001460b8070100040a40c0e1504960744012019581c5a1000c01c1c00310b10b4140c5c080007103292007504507501080d051010070580c1c000300e03002520740c40d1611810701400308600d038481240c1c40038811100017580140e5030030903a05004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 622393408 1250 622392158 622392161
    0x603050a0213020a0207120809150304060e030f0a080912043008072d0f060c0c0506070c030e032506090f140121061703040f1511030409 60
    0x2140d0480c850110903034010a404418800e0300c0c54403240764010b045550030f00362030000c1e160849400b90340e0301d07105000c0d080003940c039030782c7c24039070f90a81c11031081d2241094039241d81620440f1840d90550340091140c032804084030030541e41c100000749070003070f0142c1b42d10000a040c0042c01c000c0000c9600300240104100103805450316410309203445100c801641b102503240c0d49042040001c2240000b0068900804d0b41e045c2c100d01e034941441c1c50702045451000b02c040c0010142c0c1d40c1200c02e1200c598084081c000e591041e50220181c030700300710780c00c14101d60364151128001401c81007803000c96207004007494032452505124040160890301141e40009000c0302401d201d0007951041c00c90b036a0007148491141e118641180c2010100f10a418100101d000107007207040e0586c0d04200d1203844010403104024100c00340392424401c0002c00c035003005190205041c543c0d46406003035000300401c00960400c0720541e01215104890104100e04514040b507904004d445101c050b840301150110303601115 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 622394658 1250 622393408 622393423
    0x140f0102030907120c06080709120309061106072a02060705010b0906030a240f3e0d0f02070203061008060a050705031302040f020409021209070e0115020a0204060305 73
    0x2140b04039100182d94002030640c0d0119148000c1c41d034003981004204040c06a98110303007120450800c506410748410000048880201069000408950040002c60303003080a425003a403d64015000718a041e81001e04407903d407000214445040080b001daa400000140501059008100c2e42d540e48281c20710502030800f8080051080c402900441c40d140f80000d82050125480907198526004621404403140c2206045a101540302d61a42d4040021882100c0107403901842c1e00c80c3da01e42071560208201c1040810005441076002c0d51401c00c0c450005558000c0c265001c0800c24259001803800a401003100c0250544151000e0040d6a804060320500b95581c0100f100c00540d00c900014055500c191145004201c6c104041648130350754070f0003503981500140000c5003c1032050b4808081340d100750b102110f142da01190f5500480118145240c0048001006000a505000311103200c090103216a85010b008100c066940c01d00901c080049103400900070003055540c0d00b0312585400a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 622395908 1250 622394658 622394671
    0x3080402040c030b03060c03060f06071506060306060212130314100c030b0105180f1011190507050d0c0e011409092814010204090c0207080a02011b140f010203 70
    0x300b01d00484080c0c4a03100d154040d9000500038846900d41c8030444016510141119800c0241903089a0164503520024000c0c01e219038800c0c51140800554a03085880039040030003018103100d810000765500084107a40711101500346603541c01c12342d00c0c0761101940750340028546c507290b130140e082e400c00100d2108010a1000010700800b000110b080f02201c10b071440950100307109000d60030701a07a0828034400c400c0005480c40021204035800901d50403208420351001a0440b0018107450b00c0500184002442c001c5100c0c2404000d07640d61030302d03140365014841c020380e600c1c511501800380904444005101e4003040314070707958488014012011084c0c03031480c064180034011a0b07204400051044040100c982c1c80c0c611440d40958400f0085030800d000d40d851480207000c40c140c20000e20050000740608500010038a4413110040d061a000c3d500011460f00102d01417030250760883c025182c8107100f0600b842c200215840c2241c0c0000c118500944503214640c000301c0c01613415030086000c0c44 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 622397158 1250 622395908 622395911
    0x2180f01150513062703022b020301050a020316110a062d020d0605090915090102090616020a1205120d06030b0405010b010e030c0607060903030e06070f090e2a04050d0308040204 78
    0x1c5d07548415040c00219102c004e400102c91303583c41c088180c04032460102c1401c409200f48800344117400013030035220152074074040c1c50350000c1800b92420034407403025401c0030641061102072000745d082640368120f424001d0413040d01c4551001065007490b44100380003000c55084001310300900c00b4480203420614410030090b2520001141070314200598610a02d103c034020f0520002d11111942c007a40f010740780984a6400713110410466031124080c0c48604030000b40b402c40da0b9030754010001d10382025444600760a131145010300110340b01160454001560b224040e0341c628000800000402050340050524443c80d020b000c200311064101c9540700c0780c01d80c1d6210307080043c10101912a00656821517002104002e900e000415581105000c5802410001050500180344a04180301280c42c1c400146c149210921250342015000020f0049604001031518041c0840c0d07220040f00701141c030f1070b00304100e01201c036103045d80221001780030041c084414a4a988c5005000f810094904900c10f0303 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 622398408 1250 622397158 622397207
    0x215090d172212030c0519060506240406030b01120507020309090c0928030b1315020406082a0d0209030f060403051e0c1902180f0115051306 62
    0x424004094804a2440f15401c98956400760350420081800b2181c5008800c58002424403020450031494045c00021a031441c000040020a030640da00601302c0380c12030b1020038091014030050b20113a503068180041c45a09020058079031a504100c086203042c202010440d04650120140844030001c2d180d9a21584500b4621031981c041e506074580c00450400002d512440c001000c80c83e056842a04c0e0310f03d50340c498603005c040190441e030860056000e24504000c0050706c24440b85031403118001142030a040c12801001050041e090a000440040355043c45220005040f125500010b070702d2940c8112001051000c4d40003205a18842e0184008000818a02083c03c03031065031702d5650540b07465a182c90084151183c804d2415110200384031510404504204c50494084200104406c0400d54070401c0782848007001060100c1000c80184100540c02000c180d040d11015920054038880390a4111070902611069507070100d9018000940ca03074101281f941c404a003041c610504 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 622399658 1250 622398408 622398457
    0x30c16150c0f021c1d0105070501090c050a06050c0606042c013c150308070b0105040f1b031a150c120a0f03020702041103040b0906130215090d17 64
    0x1a080303010203250104405c1e15042000340c1c8022180c041e400e8050400c58140841a06d401e400c44039161801c0b581550101824055858000140c0c0010552490103914145030891080d840c0c20740980001d0245842c4c3c203a181001400d0b81c126002c5082c0c01034900e02c58520405214080d01100b50401c4d1418007600040c0040c45c0d0403482c04101048800100c03507055148020400104006142c1d076490541207080400000da00c0c500418005000d00c00b800101c0d41050f0030041100d0410f541513006601e0311041700c0c4504804050130381d00d82518200005c6113000100c040c0c100e0602c40c4110751748a0307004103040c040c0b402440050519000b11fa4112400c410f00034603c05c12030302c20390455401051a0034400785035035103c0d4004000741440030340040341c0d0304200741d082440707070704160350031100e02c4d01060401c030010508020aa61107944c83d0741c102c03101d00c00c580209100740d205200ea02021203000075410010f0302c681d15181c0710145d003d003050714003a824110003080798108480300036141c0300d0b0410220b05c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 622400908 1250 622399658 622399693
    0x51e1c05031608040b0c0705010801150e130e0d02032701140a03090b07021e1b0402030a0e070816050121050403110105090d0e0402030c16150c0f02 65
    0x4940d00000442c0340011809141c00e58042d500c8046414140410000c43c140f81d035100600503a6142000804a06080100150040c070058010b0010824080b14040106500815101245c1402d69031160390400e11502c0c00058040c001481c031462082c1e2500f07801c0c0d107600200401243c44100914850603105490141c842e01541001a0025401294145c601d00400f00104110f8445040002e1504030035914440c9640c1c04585500140e0081d1070b001603c0c03460364000104500314200504490441454200da900c204245124003450340400043c48086207540b140608000c0141155080c554a100480e074643e40d20945120344a03a20b40001495400750410328101640101d00d0011100710111580c000e0070000e000740d041014100b2055035091080c0305441c0500e042c08064501c07001854406880000c0001e0454003c40c410020060500c4d01e890644000900280d18000114078600349030054803550b0150304515890001c607030b44126003105010341d0f401016001e41d0313000101c031242c400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 622402158 1250 622400908 622400959
    0x17030403051614090c070b0403110c090408030c0703020309060f040f0807080601170313081c08090604142109100201140a0e0a0b0a0207051504120309030504051e 71
    0x20342c1803c0b104003071607a840e1070000103034092a030050f040d04000301910b52071900302c400d880a40c041900e81c501d40e000b0000074491418042e40a44010502d401c069036002c080d4803008080d5005502c002c1841030030544244116601c1c80700c011b0100b505da03003d6030170622040c2e006204901580411080000b100710010540c0401c0b580085c0c054240b44e80b0707024070a03001612956945000340020403c5850081d40301d9044805041c4480051240c144003c03500190b05081109850901c0a00000c026101000088041d4810340c0205039100c8008004105841c0001424103400703100d8040340c2443e80300c484180030b0f01c0903040c01c0f81c18a00c480075040007070382200c0600c6a00200203490b203001861001d072580000007010b680d0b000719581e80c07695884800b048907041e036000d180c85400003054824000f08028000b17200300d90613540752541c1400e170707504a1009588083e0000349601d824000003854042c40946000b81006042da4909142c2092034042036038a00759114807640412004101601c000918030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 622403408 1250 622402158 622402169
    0x120a0b07181406070309090c110c01030e19020402120a0f1808030f0603160305010b090603070b03040f11060d0b030d030b010912020619170106020607140d06170304030516 75
    0x4505082c441e000d01c1140e9204410035402d00035103140c002820b400394440c1041200c2e46a07920501c40450840160400c1c00c0c00d04042d04050401b07161462201c0f010480092090052107568080f281078400b00d80a0302403a440c1e106600801e2003045503015041d040500b15112002c1c0411401c22601c045101d61110900003a180550a01c005901407240b400c00703e8105038028212800811034a140003020403458008441c203944134ac100032040c0c2841003003250080b60860180c5042414403444101c60700005001070311110030b1740401003c0c450128404005140c01611580c1e0b2030f000000c0b120054449219594000e06c2a903040204080c0301c0d100303c40c0c00c0c500583d10400c0980c901500c0a810000c0b6a60a990000c0c04020b0340ba40081858a40c415081c019101d41000340049101c10116480c164402030964114104100b040c90780448660301100a802c48213841d407030b0743c4600b08000c01c401c0d002011800840d50201044c040000054012244030b1421030348400c245000d071001612852081 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 622404658 1250 622403408 622403429
    0xc030a0809010c0201021c030b0f090105030a031d0a03300e06090a08060a1407111504140a08030a060602071505070302120f070b0a050702100b120a0b0718 68
    0xc8003503110f98164201980144100c1c2c00346640700b40341c00c01407040c0010000200b035580b42d104440d030806108d441c071120307022a80b601e011340c503000c08684c641910f604002c00304201110441e01d8141c0d8580300c05c10340302000c1d01c01500c40c1c1c0c990ac3c1212004c4071100c1c80b0050029034085811120761000e10303900010040355a05540403401000f84049a0404915107a02481d000404200c02a007044079030700c2405001408144070300b1070000000d0010b0051b000d03204000d524000714103140310008400ea04034122900340c10301c954450510301a6212107404054145c00b454544e4400e0000c1d14020307502506104104018181e52043c0c10399960f0380e01d120714003000041420003040c0500030409000f04d41e0003401030340c2c440301d00d05999980c6076000c1042000004000f080341c0090000303600c0e1442d880b20201c181003100741000c1001030340e51402c0c80e0a062000c0e48070300425010b41c40c0c0d850389403603076034544003201d6076a0303240e1410801c1500c0c02c8a0703d00016109040d441542071414868030200d500e240c48 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 622405908 1250 622404658 622404667
    0x507120e0c0f011115100312111b0d020319030923040507030e0a15050606040e0a050709120302010e06090304032303040b0d020307020106090e030d02030901090b0112050c030a08 78
    0x56a01d4450b082480399103005d0300c400701c210880c0f00e11540d44140c03403100401046508518101d070f028503113a900c1c00100801150401704894000030600040c4c80100060b040d8010b038040003400c01348203c44001d405001d03100d00281c021045a03060f800491080d00c5a0408135210044a03810601c51500c40000e51220200b8410030300741a80415000b00305c0c2e01c0c3c0800c00200041e02d1a10b025080b1808aa0400b03205071280788698480c8940b135004841106c07007610f000c0c13424020701004440500010701311a034030b20200d18003c0c05261500002d0403d03a64011047e405030801900801d2840b58007002e90081c40000340b1414008000c071030540782d2221022240c1c00c40150f0503007802e000c41c40c036169588010440400c08220b02c078060200bd81c10044096a2458403100090940d4403561015540c6e9040c1080640401d401006031110b500d0100c10040c2c0301d6954424141c05040fa1070406800b0b04201c60001c9842641c1c03911b03c0301d0150250f42110320306111101030503540c2219400140001500340b1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 622407158 1250 622405908 622405939
    0x50c0a0e061302030a020c060c0a080714071103101104031509030503130309080a0f030f03090c06030f0f09140d080c0a0309080702031005090c010201020717090d060507120e0c 77
    0x103000d9500310b00c1700d100041c1080405051a4034100041e14009801600031a80c43c66003607009040341d034007a22515003942c01d0034500948618038080d0b204000c09a0710300e600010060748041000400b503080a01042c04000c442001c404c030503074482d003c00d0f101520300d04902e800b4903805015110101e0360550318149966109205042c01e01c40d0403000700c2c2040520840018203140070051031051500442030303100c810409103800b42414650b0920382d0701b410300b0040b014000c682000d0f00d400441d000b40c200070400310020040e081c020280720361202111840c0460800034840140350700300028032118111099a42502d07000d0320006421592800c0d00102001128031aa11a8000c51312207441032005904112042c1d00180c100070184082c20b01d01940d5400b0003154980c1000840421102070000314503212040d210f10505003801e4458515400c00040e0303030105520f503101002d11242d0400010231036410b103c4c40007005030b03081c0351060f803603142410705854010001144510061100505040ca00480c08 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 622408408 1250 622407158 622407161
    0x42c100209062a011b120c02070603050915040f110117160504080a05420603070803070b150405010518190204081609020a170a06050a03050c0a0e0613 66
    0x1803140105034542c640d6081c41a95003400386248042451781c094038228503c5800401c0c1c0044c10a50301c0040e4201120000710580209101054500a2034017103010b40c4c81d00c001070319180034020b6408a0b0b040c52010842400006500c500c4560b01c601400a14042c41c0030044076081814040e1403103444015020813144900c0908414502600e428040c0c2010740d1034035454107080907900190346503003290103500c032008030500c5801100e41401c0d0300f111098182c01a81e0f0100170000d10040c04501942c00410342c01d64040040d4002840d8030302c12242c2d1013400e880d00c05c00303151007551984031000b81c0c107149a0503483c06000b1107050b1240030f000114882c0ca144000d0180e8000645490310030140a80412210040c900051001e481d0480c006c0c003010002100d030000d5034003d03901800d03880d8414000302e50341c035a04c0314605503000504a0300c02c1164941014280c010005940200c0d032102070000c00104100d00825060b0050a04030389022201d9a81d1074201283d07801110030f594000d0300b6110229154156 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 622409658 1250 622408408 622408447
    0x615091302030a09020a0b0a2c06030103080a08060607020d060c0c08030108010605010e18041205092e0309080919090c020c150a1b02042c10020906 65
    0x10300648542261440520880c0e00c242e8001443e107407600f03100e0042d03041c041c41e0034009100c0030552500c0c0820031200140307100c0e081b04030560800e03001c80c1000080c00c00c000503803041d400c0080c0016035a5a403454003c2d49940b10064680c080760407034001898914258040d14400c4c0d4000d85100d0660030f40d551071038000c003038401c0c404003805250200c42c00410751240155011301200400022140c0c109400580b442c07819103600b510505100b401000c0c61410025410b40250f803007031014541600400c0b0956881c010946003541201e803020081c81140045040300b45840c1e8180c0158031555a07800c0c0c21001e6500301400030340400010003004401d07060134076220240c1280c00d01c0c0d45011980b114000030588400711003820041e8000e94a403c681d140c4200d850703820500341000c00d490b050004001a244090084802d44140c510518280540d02d81c2e030410705501c00c12500481017201030201e2100c05000c042c0d2142e8007442002c6206421071600e1007112001d10b8014245410603611100b41600c5001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 622410908 1250 622409658 622409677
    0xc15040c0611060f071803030f0201061a0f0c0709050f0a0b01171b040504020d05011505031e071b1b06111c02150901020a0e0906090f040206091801031205030615 71
    0x61001880c00a800e1500c040000e58866503270720300c0b80220b107540242551010b40002c4041d0306000e061041034540d0200f101d8039402032200b039503103400c09801c80b14146080359010f0950542000b040002440301071040d2481020105401c02c280c07009100112420040c0000302981d554580d8041007403510302e1024010300841c0500d0640c40c150b2a640441c0036604102c011020741d5403500018000741102d4135180c040326025141890540c5013110350310b412a200424000815001100454081031140c43e103507645990140c100381660100740341c20601d0b501c140c1964100c000c5c2c540380120390203201d290400d01400c8900000e0040070600b070484071403100c1c0020540c0c01d40c440d036803151000d24541304416104060724400107071141803c01d005441d0549400d0001d120b204000d0400c00142c0e0340b004c1c0c01c1c1c3c03c0119011051520303926840821140d01c24a66400c2d80304000440990796502c0318003d040c181e80c4a03408000d440c030807031003041d21540400e480c07072580300d030f40c20054085c00c13400d110207040c0e00fa5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 622412158 1250 622410908 622410917
    0x60c070b130204060b16050f0c010915140c03090a170c041802030105100f05011404060509150301080d031109090c0703020709061404240b09060c15040c0611060f07 72
    0x3659200c1e48100e55100400d00105204e01b071070340206200060049100b08080c0074080d008001d02c0c10002092114203000d55135030301002c0d0003a1951240724006c0c0c000d403800b400c08042d0f81c482d40300d44010b982e60000c9038030320b100703c8400c8000b003120301c0c0928000e10b40710a0880109503000d070b08020080980300c0c0c00103110b10400705e0340182015950034081e540c0109081f05901d4002802c4c4811031803c0b0032550040b40c18410303131951070700104010008a030112a054548940c0301d181842c0000d650b20308100840c1c807125008800410616404110030891404589080141405402008145010705d40a481d0712000d220005120b100300c1c0d40c010a046882841503998140c0c507040800d04580c1c0765003110049002d9a6129411820588500c16944c4501c10140c40c100068181401c0207040c40c0c064004684004031344601551036000a42d42c1811041c0150b0703820f10340306445542080822a816a020406600000f031000e02440c0702c41c4141e12800041d110990303803002d890010401c0908101c0410 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 622413408 1250 622412158 622412171
    0x6030a1116030e12030a05040b252d0c0905190606020c0f09040506061003180501020a1b0308070f091214070b0406050912070f0e0405060c070b130204 66
    0x340041c41c19078655074407a88508902d024450300740300c00915403070302000055100b00a80280301f50010107950032240a00703211b543d0399a42c1c1c480c0c0444070a00422400708841c03c1c9031520104800710710f81328480303214182c1e1419202d442c1015500005403110024101100701c840600801cad071141c12190707116040c0e207107588041c41e102803c0c20480c1d200e6408440141c00c0368044668618029007180c40c0048201d444000c42d09007921a95280c00010304050300c41d21002ea180340c0c041d4041d80103d102c0d4410319003568070740c0d10749080c443d0113035000194100002d07a1600c0c0c2c43d06601e102032885216190141c2c0c41d11010703641c60400b507940008450302d03282402a1100700050124810703500c400494828070202d41400f450095261515005130008031171180c09000600c1810703071110584519000444082103400800c1c1111414002c0d1504041b00314040d120000c1140072900020034003841c42003044070100e6444203070388651030056000080c20b580ca400c0105041d00f880c10700d4a14041d000400000c3d40 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 622414658 1250 622413408 622413427
    0xa0b041406120907080d050c0d0c14010603080d050703020a080a1107060216060b04270f06050106020607020d020d080103150e0f0a03231b01020f0f070b0a0b06030a11 73
    0x30044800600d581e0013061306101d888001d00c50311145181604105041400c01e04a003070311000c2c0c01d150002040104141a800c0c80700002c01c3c5058a076402000304012a00c80c281010254480305102c00311506040100715614428400c13030721ba10045550b040403d031100d0000d000603202d02c2c0a42c5c21410400c1c072400012554a100610720001d100c00d100c0c2c0441001c1c5042000e840312003442c60702c240d19084640150b0001b100540c505407602e00201540c2404e249445c0c405008003000240c00d2900d000f0000c0b80c099000030741c850040e4081c0d001c40d50400c040410482e520306c0c500040e60700003200c10004000041c0103070050850034101c500003140f03c2c0300c0310908514103880030010344540e42c4107a25080903d500407029490020080c2d003218504131042842141038400e07a114060000d00303075582000b4103d420750556100c0c4a03040c1d04c8a580d001044010202d0390410071040d5507400c1a140131076802c00d09413003400c4150b203000d0120781c215500c4100600c003c0c41104514080b000040084466 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 622415908 1250 622414658 622414687
    0x602070b19141327050108070909050a150507121506050d1d3007170408010903082d06040b0402090a2d0608040807020d0206030703050702010b0a0b041406 68
    0x3908541400d60b591100c909540e41110304030b800d8203513034135180c580184a440404202c3c2021b88401801c04507403092207140281c41c3c84002c0601802101c401980b01e0001c08140e0132190046040307944d41c032104045081d6140444015400c3c40c0b0070b04580e91020801a80214082d0110040c11000003509c06644510341c01c0301110b60600f00582c2c1c0094a11151380181c40c904011150f01c84c080584007000440c40f07660a40c8036841004d00707480520100b03074001b9100141110040c0500c00d0091000d02402d180140048105807440c0d42c10004103d080005801c0d41c0c100f91541c207020f6401000e4946034103052000400c00c045045800940030048480c4580b10b5120890081c40b0329489120ba021954880d0a0b150400c0300703c03004009800142005050303404031751542c020340c114800340d90b910346d039200241462140ca0402034116802200b0411306a41540c002407140c40b05800922117815410204070440015019080d9404014407050000603441404510425405014180b404010414002 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 622417158 1250 622415908 622415947
    0x190504170c0d02071a07060b0f10020601080c04090f1b0f060e0f0301050103080a120b0405090609011b0f030e010e030c0d030f0c0519020a080a03060602070b1914 71
    0x1119988a5582d01d40055810045400148000c0800c4a00c403103000a044e000e5118088000d001207481c4d02c2a030103565a0f1a850504030000209081d541d405421b4010307448031001d20600d5111f00460203140c0b0503081501440b291070b5809048010018215038072101402603001003030014624000c80410724032580130049001d007070300e0740b21906050302c01001c010940054196540c0240d06150040000440303c1c4182e07001000b607810309510440ca03020000d0002c00c40c1910041e400360428003408220100072035031600401d015002400030f000c1c1c20f100e00444541034000c250005e00282410a161391003603112034841081302001082c4500b00e41c07852482c0d50000c129858041c0c0145404130207082d0144544044070349180700a004201200001034000d000310241500400716079411141228401c1c00071981140d405240107481d0641d1450050090205002e4400584250a80410290b83c0030054800b001040c0425581c40f11190f203044650424031f100c072101c0080f041c040c1d001c44a170f8119181 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 622418408 1250 622417158 622417177
    0xc0d1401120b0c12010b0a030b0a12031107080712050313060f0801060311030a0221010902091e0907200609010f11070c03061e020f12060919050417 65
    0x40310420301810050316400b0050101c1800d02d00030043c4c5000b100101d22540c1c1100c14200341c1c9611440e007110305030050b00d0800800e80e4131079814980813440e0503200300e041007414007035a1802c0c0c1c0c50640d80c2140d69100c60900556415034050101000340c0303560020304800492060b02900c0c00c0ac2442c4001102c0c01245401c001c001c01c000c6410a039071940c1c400c0b07110b80141414601405a100e0142d0101c00920010740105103081d00056800c90f0003085011994120741c0b82003c40c81d640d039440012000a4100b00d1030079105003821400c0c1c40620300f02d106054101d01e00100a41c515468184094404140c0c01d00055050314504600802c92241400381505c606900000420b0040c1c0d01c10035801101e03903144064021803420b12240e0301145209020030250f07907222034001041c2601964481d0f0004100407501591800020745c16140000d010203090202c07440300c0882100e0311000d0070007080310b0040703c0c202d40030809211043c81040207038024680040c020844110500752034240100242d0004010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 622419658 1250 622418408 622418429
    0xf080405040b1c021507050d0c030e060a20010b150909071d2206170c09040f0f031b0b04020f0906011202130b0c0610060509090c0d1401 60
    0x304040c1c01c05001d400b42d005022160b5101420240c00f20007003442441c440030380201c0e40300c1c2501591940c0c004c202c03900c41d0b8000045902c0c1540052000744843d00b920300131000a105402e001d80c2a062807810350703450140300d4490b43d09458803040442012440582c500c1415034070362242c0380090311003080d80389564031600f82c5c0990380d06800c03041c02494040604904100244404244203200d4044100e4500d0042212505c0c030461240604121a01c0c14000080c2107d03c8d01030300150485500800040d20940d802c21348588150210800120765401c45018100700302c011454000510b5000c61806054842d0801e880c440280c2210881c05040044045901c444190140700c103600e0240c2500b0800301c4100e90208084c90a00c00003000c80102c80c14040d4101c1d00400c80007141100c040c40720016252002d802d6444140300d81034590b80e01c034151179155034405000008140544103008442810b0406401039040351100c065800d100e92040340039054242d07540d54031041a42204080c14000c0c00302864 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 622420908 1250 622419658 622419667
    0x20702040e15011d0a020306010c0b010602240906131704180e0a051b0301240312080702150408090904050105010f0806160f020307060c050406122310030f08 69
    0x290b0001c07400103800040b240c0d4915004c1421100c000084a07502000c1d01c00c025844e9102e000042e141130304407040041600a03940b0001c03540f15070004000b40a2100c2d40b02c8403200a5040301c0700c002c2e0395000d8034001d006810800002d0210621184000081482aa0980600210020707950001d030070035000700c44603064840200345081c41d6809507580340075114000c0c003ea030303805946143d540c10240d4011f00141108074070f0060940d4080d407021900701034681c490030034180030f4a2110101a9640000c071120f00d2140050b40d03007644200c881320b1040b45107400a10101c40302c01030f603415a070b0008000301c8100714100701090f000d17201c841d0300c1405284100008902c03035042055185590707590341c11107425980080f041154008003c10071481d03141160078444a0007008020890462003802c1700540940d04080d0980a42a0311000074400c039201c0350f540000009016002070b050721525407413480c40551000c101040e82d14250f5010b82c0200f00156256130103070340ca43e00c407481401c100d8002d4480107030114 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 622422158 1250 622420908 622420933
    0x306020f0301062c3105060102060108061302221802010f03021309050c0c03070807030e0607051b03030904240504050105060703030e0a02060408160905090706030f020702040e 77
    0x26021100352020807103860080246200d4083c0180c1c0c0b0300d018480c0440700c5500f140c0742c0e1001c000c00c0304005c01040030a4021108258500606002d448441c0188900c400010b04103001240c414002e00d5040c540c000e903010aa001c000c0005038075201880e5001a500069001d5030b0280f00306405001d94040000e440c0003640005050b041244001905043c01004108400703920140650199090f95000180036200c010900d04580240e20202c41c00c0c1c4000590340c014004d5520290803001c0c403a6030340f0304180c140c100501c1800e000710b86008140b5442107003008aa902c908161030300c04003000d01141d00b443d0590000030180c6002c91484415400c800382d4841c080221500e102d000b4000603a01031089515000c04640d182c4542c407006010541d8402110410460600200c074400c0d40041107a130312107403070b0740c0700c00e4464095141d0840e2840780103c002507043e459026113441101180003410103103181c00b03015400343c4042d50014039010750802c61000140d40318401c80b041c01c45040001d0442c2c80307010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 622423408 1250 622422158 622422167
    0x80f19051509090615061303121d03010c0f050304050c1906030e030703200c1e01030f151502030c01060306020c06091903120b0405040503031b0c0c0111070306020f030106 75
    0x7812215013038000800308055007000210a442e00c82c1c0569141e03543c1c07209580380e840081c0c201d4000802c0000300030301c0407422aa0080000264107900c003241d2101c02e0032601014200c416103c134407c041040a420014a58001c2000e036510900031401d0703030601c64203600046c00001d00381d0030703c900190090206214a691502c1642d0199407544003c602d0640c440e1405030070140b425079041803e100811000b4900c205c02e2102c10300d0300202812148020603411030061071144000f01c17842c0020324248002c11019514050075100d81c0d521100b0403603d45c18104540303103c034240c003441c9080d4401046800207400013442400015402108010b85400c20b850f010703810520003510070403980e40b02401200d00c0d2010a80300c0f8101175458200000e00d4407003007110002410103003c6940d40107140004020900002200861241d507000c01005440300a20314444010301031101c0224041e0b100c903a20344c55035401134003900c400515010172180c155130b81e941e0305800e0364024030f9403203618034010004000c9180c00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 622424658 1250 622423408 622423411
    0xf0307260c180a090c0207350304081911011b0204050703060e16180e07050307030902030a050d230708070203031c09020f040e100c031d1b0a0501080f19051509 70
    0x81803c101c88d0150701c0110209000c8544403001c4000b2000c583c410b88020007041120020240b0109440001c4050980e0b0382c0e040c4d0b038105c0140c0f60303000c1411004609604c00c28070240040007d00104540c0d84103502408000d000003043c940c141a0340d920086031490300021030340e204201502c080c1c0207541800340010114042c0d4181c5824044000d5810303c03010125120700c0d0392008140c0b400d07035200e5992030401c038007800400c4400303905800360134074030030520002150142401503a03440301e0451070050300000c14a091401002034094009000c1d4030000340955008001060000381220700384a01004041905820070500d02a1075540e4205101142030150b00604660750444040080c1d841600105488003582e5000c0b00c51aa641c2c83c08040c0b04e03004e54496941040a203100300380306480c6010256450200301d0350600080c2441c1d00c85407251400d01e080506883e8180d6420b085903e0750005140c82c114081d11983e41c800540ea040c180712280343c403a00e881007014002582d00e1030300007001e00018000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 622425908 1250 622424658 622424669
    0xd11070504180611030609130201142802030a02070608090703020901080f0c010212030a050711030309101a0a1203030b150d0506030a2111030f0307260c180a090c0207 73
    0x4d0070310420000307581d80e002c0e080d80f20303a00c0000c0b02c6811106100480b5044d50841c5619031b10000030030103403140356000d04050f124075030786803458910240194080c0d980b4000d401744074006901260f001e21180b4850088107800030404030441c0c24403600c030741c0000c20528003600f06603500d134000c000341000e400c4200404403c07500280040c0a00300040403040005110003001080c0841c0c60f280458005032154002c0d03111802240300380ca882e81801c000c0292142d24090782d041c403c6003003011000058100314084054683c0c0208980000361030000883c0068a1101d0181c050669410f15400c0300c1d202d03c0c0c00f2012007080598000d0741c3c1e003070b03030000034088550142140f0301907400000d501d40086d036610003540d040b518a0001000303817092040d04551064110705031079503d000c003040360a03402404d84041d502925043d20f07000304001e44000c260106000b60b030841030800810758040b9a802e500c0600611720112030701d0308095002c1c007840c0400d07000003450b840109119503c3c48103101156050040201915 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 622427158 1250 622425908 622425941
    0x30a03230402011b080d0510050301200d180f0812011707140333130302150c070803090c0406090b01020a0611130b2206020d110705041806 61
    0x702500000d000030040b610b40b52102141141070010721092405480c010700b00400148098a444083c07415070303e00c1481058000c3d800c00014403160b16801da0507044520078015554100f88025864030701a020300100402264201050070340890f40b429510f007242406002c480396101e0354404855105a0145e014140d00c00500c0010103d01d580483c54008403400956041e10458508001a090180051140d903000c12f01c2108100444045a07401690200c0200c203840c080d0360b5450021558039641f60001c006030499000380c25a130044160182d04910111040e034280b01d0f03503036580e5843e07501c10344108105620440c28a01c5070b00d010300680b40500450340c0c003031145040120000c0d5988440020003852161035000190390f09010340c00b52000110f01911010101360303110580f00007a0300902c00101145d10700365003c00c03031000120341c01c1e0455400354003c00c03112042d08005c4900c05107400001c1841c1c0204080094a0769480c043c07200421841030615110b030700346203803081c22500840795459181 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 622428408 1250 622427158 622427161
    0x2120a020702030a17040f0f0305060a020304080403032a08180604050303040b0f0c1c020f031213020109032418020607020d0f05031b010e06040c0b0706020c030a0323 73
    0x1030b140464000c14195110300b61021111710750240041c5801160040300184540a0000440401c0005000b045038080c0c810303540c9686031800428182d200484014148903c100310070000a8851a88998500e0509001d010010304410301e851006400050a4030743d6030000c2008044080c0e21040d00c43c40145c111a454505031801d00400e45a0185100d10418000007180246051a07800100d8025038804c07003d4810501c460b1b03440015191010b1807000041c03140050341141d442c1e001003143c1e41041c0f5020799080a039100003584071014040c4a00f2810864419400400070b00e0340340c40c1d0068070344200004090791062038200c9044480e581182d10741500021242009619a61f003110b0020f034058942c0c1c40c5212150900b81c3d104440700b4002002480300081c4890032110f683c3c1c0f5080c00030341e114002d1007442c141414a580e5220269000340c0239182640007000300d520400000c020040c8034200241c1441403140956045801980100001c03e07110304084c01c0d0000d008420310b0071818000700c9010503 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 622429658 1250 622428408 622428413
    0x212090f120c030702030109030908070f080303040b0a0e0d0807140f09010c0f240605060702030c13060e010e0105030f0616031802091302030c010c03020303063102120a0207 76
    0x48128094a880101c003000842200d211001e00c210b0361842d130098001d0180884611f002042e0440a01c600100ca000306031003c28201800380707820044030088801141107440d1ba480366501030f8409401100717000c0c0c0e90050726190400c00e02840200b01682d4440c01000d1800304000751913854081600b8070080000c00802200c52895003d50350000003e01e40b020000e121841c041c010080503403005401c0034950680b04840300c560810345030200c020040188055603403142444000d005407c4001c0d07168010b000c40b1802400d04d03890400d03000c80c10314001700702c0720358851100c0c3e0f40f440c0130707000020b0f00c10704600148800e08040110a01c42514500281010b02c0c1065044800060070040e4108264a50748020700c040441841c1d25945a0018103c0b8940d003021007800c0410507010200300d01901031240c4040c11580a00720850030990903030003031455955050100081d203150301080c03211f241d4103084584010104041034482c00d040b0701d0001680c0d4001c0340c2c910303210755500401c2c000c885070040003200300 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 622430908 1250 622429658 622429663
    0xd140708090a20030c0303070c080c0d050a17250b09060403080c0706021b100c030606020a0201030b19080312151008100905070302090109210221010f0212090f 70
    0x10104056030300f0701000b003d040000f418a520a1844e60713040c440403c0d84c805015820507007a048501e01811202d030940704906008072a6407002002c0d0142e0800c407c51004242c20000e071320700200b606e84c405032038a010340407080d94a0020440900d551300500007803800300448841c000741c0042e44c9a00a01070781c9032542e00103140c054010844807414001040d17000030080550140e5003140107400c2c09080c5500d102481c0c5070b4800d20303000c4204d06103046c2904807490b18000e100740c07000ea030f00903405071142d0b110580054018050f81080300b80c00007011420b26204400c0c40d42c40d0406400a200a10358643d15903413040c9106038040d0070441d40b150031a102c4111a0380f1030701c80041000b00390600c0c000950318010181c2d504030890340149052420b086c00c214015034503034010b0400a009072514801140c9801c1000c100c00c00780d14114443e010700c55016000752038409071298041e500c550900242d0880b03403444900391107401138405400c1d40c0110301d800714005a56802640001900010409c9540b414401075 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 622432158 1250 622430908 622430933
    0x6080102161a0f04080a350f0108030306100903020301020d0903180f030b070e1008091002090a06031805031c1a090412111c0806060a0e0402090103020d140708090a 72
    0x249100c00c0010712131030240c0501602c0128800446441e4001c60040c0000c052040140b8800e904601d0b0100004c1c1462880034001c40c142c0e032b8088000c40c01c581d1040c052200031150503100030b051000c0c00f4070000050f5804d000408027884503040110f0310307000d140b40181011143d04010a451140c080e03062100310305550700b8034112501b018105169031296101500c140d00411b85040c0c202840e00303013407114540c00802c0c550040350314008540c1d403400e03500f01c004201d001e55400e05c1e070310030f45645042109a109801c01e50343c80c914049070b550402031603600c2e54915403101403011002c0c211400c601c0b981100e58800d8010740440801e14540751004203000840340368000340000c161518060064942c14072403848440f2188a04086451000030030059010008400c903c0000042d0608002003403802d0020980c0c3c034031031090711890341c80c00300d880401019420070081a81010750070b204c010405110303400740302c03000c1000070380100d83c905103000018506200100510071a40c0540d80500c0060800c00822 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 622433408 1250 622432158 622432163
    0x61a09040c030e0f010606110d170c0f030a06030c061d040e0309060c030c0607020d0c1202011116110103021806160503030420012105070306080102161a0f04 69
    0x5414640c07a6003540100080c0304265224071504c8030071500c01d18158030100c00d5030391640f1401038100b070380c4a0040d505c0c01070b40590300c0062900104000052040101241c0002060580380d080181c14038a60203142c20844081000e82d49984081051103140007155002d40794500d80740d07c000040041424a03800348015403401581d4816881ca46150244266240c110380100144d81d60340c0364600c0c140d900c0d041020000c045008a501041106000103400202d82c52035465a00090a4584920440a031442d000700c055540301c4041d1413144c0801001001c2c0704503640f840c0c20541002d400c2144109040100150502d481000241505202a29090001c0b10202c80e505e540b010700d20510203a13100c200d68020a0f40c840841031004020800b004440c4610070b00400102c0052140e00440701d06c940442c0c0c3c0c5200c2a01c04006200700e249680101c0c0c1c0c04402e43c2404074484e036460442c5422a0702048501100e50111605e100410000c50658522501d154405110070306065146440751071029200 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 622434658 1250 622433408 622433411
    0x8030a081503010608071203080604021326010504030809240105040911150405091e0a020313150e01060501031a10021f14060105070c03240e07050103061a0904 70
    0x1c00540b0740e001d4003c813016180080503210303000c2c0c3d00e00744400d4400c4039080443c0842d81c1c041c0095800c7c203080c400d0310080d0a2180c42c002c840c51030b00110448031075500c4941403190b00c00f1000c0d40010030090148034010362180c0c0d1020b00d580b521500301400c01c200684130207440111102400034450410b000700d419030300221000910780c881c1d4588000021440840d00d900310f55440c6007000120b03610700242c0110341080e5100082a13a40c80f0300d0300c0300114a0300380056080120300102c1c9400d0246d078050366012060903c3d082c403012541c1c4030300544d685500c60341d01446071980c0702d10020102c05c0c002c0b00010308083c00c0034042643e9000000604c2d90301d20b0941c43c052001c1c000b02c40001031080000780c028601ca01e2042502c05030281c00f10003d0039070388111404265004011940325403180c070072035120a070043d003c10246400c69071441c04c1944600500503d050b11038200b0040130b601c030321400361058074a00c02885820b20306400035003550300c9039102d0403150503000100000c030040a0100c1c0c2048404990 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 622435908 1250 622434658 622434691
    0x1a0a0c05070b0f1e010803090f0a0605070602090409150b040b1206010506070503041a04080706050a05030f09010b1002012316050f0409180501050a02040b0a03020c0c030f07060908030a08 82
    0xa28060404011301403d02407240c0a000044614020000301101401a44d034900d0b40318078601804005602c0380704203400160101304030408291154050600700400510220700200e99440740160000c0e00c5521402c400e5640044c8100c3d23190034031502680407025185da020a500340707810592100b5051140a015100005d03a103000c03c2014070450f400b91102c25010b80c0c848c140c0700c00300c00060708107006040b00c500c55003101190040c0130300251503c00d480d40d6500c5280d0354a071404030113a003001404001d119034031803000a2180c0e4030a03946966500a6a000080901d06006080c2e001c0c031055854060307040c103104c1800141c03030a440ea0041e02e140320342001540d40c01d0108103e40584944c1c0d0000c2e08040c50241000040c4001c044448101030044000303104945801c50040c00b00c1c4201c1c890080000000c0224600c00c90181e0007620b40201420141c8030541c0e0100007280c145200510406800e4101002c180072a40c1c22241d0807001d002034000031804c1004075500940508000351244041d8a10081e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 622437158 1250 622435908 622435921
    0xb090102090a0e0106030c0311070201030b030708121210050303160507030b0c2d19171f06050306060a0e0d0c0305010b030f0a0804120f1a0a0c05070b0f 67
    0x40480300d407a00701800041c156683c031a081105000203000e12400070303041101d0800302d54032034020510350550f9900f40515040302e40e030055008044900e005900343c0210f840024040c03005110b1541c142041d554030741d07030340c812140325070342132640080400024000b80d4a00740003940340001640c0d080c120f00c1c424620600d0079804c05a290105992005005032600c030104101044501e016242d10a007111604e050b4116804101c1502c0720032f100941c1e42d20805110408240d04183d0b80d400740c1207490b0500c80c80440444424100b21b50007100c0070303270b031070849108131040040700d91194000401ca81c0c500389003142010800122140300386920602001800c00298035255a100729158140341d104194000403544d82ca001c2e800780c13404a065a20900508040b100000c50201c1c40314075045d48440d140c2d20785030820a00f40f4160245040545070306914021110020707407903800c51120b03408603001c090304c2441e01d078820341c00740c8010b59140e2040100c2800508002609090361981001c1d81440d402d4080e51660b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 622438408 1250 622437158 622437161
    0x60207080403080c0d090e0405120315130606020c030a2001030b100f0e0d1a07020f070605040302190e0a0b15130f0806011d0405031201091a19030b0901 67
    0x90b0000341c5160f000240840d58401c0000d4400d403e03a0b059115460710b00e82e500030740302c0c2e484030454000e410354100c4040e86a4604009005541c01281c0c1d600c00c040420b41d10303010070851040500800907076541c1d490f06002d1250100140a01d00c00110002c05041c10640d83e00e03e220380c0c0f4480382011405104032a810a680250803900c0c0c1108098180303450040d0060006005600c1c4441131000300303403180c007080320034204021191000354010f18070502c9007580488507005844018100d004502030503543c0d141c001e800340312200040c5190341d01c2580300d07403d41c0100310003100e0500201d8a80d100ca90401c01886e0401040c07180c1c00001001c1c00100c106030003001c650440c00c01c0300686040304001401901c20146d0540b40403e40b9405000400899214490b117a500c0c0001c0c050702d000c0800740e0300150785403140391a41c541d01511650680e4108030003800d500e02c07064005e0700a0085607841c3c0c021000c4d50344035403140c80c1c05154111920494195500c14408080302d081c000900000e0007800000c044c14800d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 622439658 1250 622438408 622438417
    0x1060f03122105060f0915011b0b0103080304030305070203090f28150e040b01021e0f060711190b0703092121200a1e020f01140c0706020708 62
    0x2c80651010314003808140900401c0304440480c4210000024a2000d042222400e4440c2021740c0207255180406401950380385c90010003071080340340e594080000128842c48a81c021442244100c1c0c8909003460060107070340000303104100315402800b080a665603180c0500030f04903026101c141407d005098200c44038001340242c06142d0298141c0010015038620384038911b01041d5940c4041c04064000304010350304142030302c0f03005030711103a600703420322000f030301e01020001c144403c965010134024143c0b810b05d201152200041580e450340403034501170500080390141040911042101c0d4280e8840c0d11208015000104046e40d48207810200f24003684040c0ba100c0c40000d40c6220010040301c010a00c41c4041126161034602d1023000081624900400504141001c03040300002101c802c0709060b5080f1800101c100f0500384614080082d000520f2605018282d0180101c402072894403070030342e004c22182c00c84004084c404c002c29070803500b0585641c10b52200c8096540d60395814620210700a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 622440908 1250 622439658 622439687
    0x1a0f04121e0c15110607090501020f0601050d0204111605100501060f2703060e07030c050901120303020913020a080115050a0806060a18080312010e06030309010e210f010e01060f0312 80
    0x45d41003403041460f0010030300021034100341c0c21034200d80381e42d00b07809844c0c4200784150390b0461420060341c0018907094001c02124003c1e1440181880400b0307550408240125400b42c0d00ea0300200c8a02d000300c0d2081c003c07030b8050510f0703003004a403603d66000c009001801c40030044002a903c1ca0a042e40c207400034406200a42e00a00c082c810100c0e04101291a02a548000c803038250718051f00080034100244074a0407682621400c0f858031a89450079400f96100c1d02110364041c2c107003c0124102100d91001d441c80741c64130b0382d94250645c10040710083e1b418280d003030b08091040900266030000da0000e100c43c0d00a01c140c030185e880d40307000401914021104410b80c908018848008148814008040c4c80c034141e81d9000e0050b40d0360380b00c1824040304415940e25801d80c10410100b24194041c002c10702444401500d0800d28600125040007094070030a850a4582c21131100300034151001d000d40c02c030020f00fa0b4003c10009141014540c5421050310000704825946a03861000380d025458900c103420 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 622442158 1250 622440908 622440913
    0x6061713020103060f0b0d0b2b030e1f0e1c060b030a0501050412180b040303031a030d02010207140705010806150d0507080403030f0c091a0f04121e0c1511 68
    0x26103603040b9042c0794001f46e05080a0a1800c00c00340814500702581201c045c4090b1945011755100f04a901c1102603500d9040d0b052210342c03190422070713803580310340f0001002503140c800c0c41660b1920303c009e041d0f000d4029030364480e480600c40c811101c00e0143c103503901640d00900000d021400b0070040707802c14200200c003a04c50b51900c03081000384400006000c0440c2069034420358000001c0c020a0a941403d024006504006100c00e0000900a074081600108102c1c10303401c8403418100060b00d84492640803074010703500441da9104000f161940581c0210464018203c02e508040000b041084003d09841c40b4600703003101a48441030000c102c803030714020954240000c0c58000c10140644000303a070102d0001e0726202401e0260b2030b0f07511440c0b0143c8040d0f036401710818903085040000c12218014010500d4040100c2c045a449000040c80140a0030000100010190501e107042c002e04000b20f41c00c5903401c1e40088009201000240c0c03d4036100840c01d50107402918040350310300e80020258a051 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 622443408 1250 622442158 622442189
    0x60f12010c02061006050309100c0c051c09050d02090a02160803012936030109050a0b130804060c03050904050f010906080d05090f060705061003060606171302010306 73
    0xd590100d011071003002c20122041540d540c91720120307603510040351030031070541003900c1a24050040c2e4020309024107840ca060092070341c0030b442d4142803540c070241d0301d00100000e542e62169990003140c404000d1404032180d040c05c0d503444e00820302060005040704c07501ca40c0042e01e48041200d040b030f505440f51700448040c2d12076850340c0103002e60580640c01e034000c07004c01c18240441019031504030f502c5482c29049000c4240c0b1084008060b40d9000c0151200c8541c9031602990b19480c00d00c40e1481c41c502a0000f40344030f84480c12300305540351010702400e10031a4400b9416000c81c1c51402100c003220b0203441e0000ca40b01107400d007141c041c010051859840f508010900c41800c1c40d400d00b03941130300c800c800204039544c0d40b41d00080c2d856071401028004a0014001c4003c03626000c0f0b604400d4900151050340f44c012240d0b1014140344007240d0200203091055014014441a4400c52002c1c09041c280300b2512603018190505800d03000b40032030129000290401d0869120b600040700504100c1c1901444 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 622444658 1250 622443408 622443431
    0x5040302070b19080a05071b020f03012f04050607030806040204031e03080c0a0e120114070206100806060604170f01020a0c1a0606040b0a09050d0c0e0a05010e060f1201 74
    0x1d02510003a03d0002000d04010a042d160710340718441c00b0711500d07101c580401c913869400090420140c10280d0f0b20031030010011041d528207000714190420700007440c17270510f01d000014004051184030483d03d0032605010070700ca59203500d4211460160142422200c1d9902e480018000e842039800003007090511090030300902800c480120f8090340b081d151280182e80d01000001640148601e00c00001d03022150060305040001c01c10307108011020020030b4114484500c044054800c1e42c10360010b9000c14200200c0e250b840c045800901800005080c150804030001401d50040313028040318003555080000021200b00000e0b4010006170009540350380d03204501414108017203009032003814003c52403102c00307005070120902c1500d0040246e400c00c0d0074211100b1058002c19040c005100142c60702007a03507510810400341c0148a0300c206200241407221815182c44094410030034075043c0401804180c2070800706651000d4243c52011b614003800d000240690384a01d8054215440c20401c01c15 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 622445908 1250 622444658 622444687
    0x405181306140603061308090f0102010209060c0c01080702070b04091a13061703130e06032802040c02030c0c13180b0108010606082827030e030106120605040302070b 73
    0x4600e43c00c40c192007140d0703030360081440380c214001c2000f00104c0d801c004542d9a03141803103c1d00c04405c0107100050a1102580225525620500c04100d050344404604011581d01820460740264544040c054051804a18003014060744c01208022071702d07500d240344801c200c0d45040b145148000c00c0850000c40000e07081d40100201e0050400d80c07002c4402480388811300100321101e0030400030801000e82c2c13510481050000d00900140d1741400386642009a0794007400211281c003580044c3d04010040c148108011039003a68003901c20b42d0820f0010316001c81012402c0d174080035080c0c0d240400071841090401c02072551900e070b6004404a20022410b04c2081403c86050394582c9000300085610b4a000350b881c100101c40c1052040e08450240703a02c242601d103600c41e11185c003240410390b40d500301d141c0c0032000407040390100075080859038134050ad507000d0604c11007190150003c000460400007614030718800b190f005000c00b80c40e100402e040500c00c0000c0402051800d42240d01c80d10140400301 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 622447158 1250 622445908 622445911
    0x50325080a030b030f0c091f081b0f0406050d1113111b01020903030a180506040e070f1b170408030f071704120210020a0501240b040518130614 63
    0x10701a100b00d05da0324540c00800035915055040041c030a08056450303020382d41c0305000c0364134107086100c84524001105c000400c25071400603000b10ac0d03c2c1c0d24140e03080511008441301c003003551107641007010411158072910740c480040368000108081d91984080451076030104005090b50140c0341c8440d0510000200014049070500c001180d0001c0341c819126609034014a044507a00d07170001c00078504803a00650b40000c013121340040c9401c61964820004006411551102c0e46451144081215207a80449440444462401c005582000c0c2030f441124258129100a00c1d00358a07e000141c0103e00d6002c0d500145400300469984520342c129030041d6400002003100c610071001c281103c0c0484020544e0300741d490494000145403010340070891400164150f10b8258003407107a00e80d000c41e2080c021000242c90001080701148030184143c1c01c07400b81c3e43e000e1151020b0911080c40309649651484021402d1031810307a42d0341d01c507601001c1d4508420000240308d10b242294089066a0602000307 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 622448408 1250 622447158 622447181
    0x14130c09050106090501181503060e0609070203160c030b04141b1323011e05031203070503062b150c02070e0a2403061107050325080a03 60
    0x941025569034426815a0001c0c0a40da0100e41c05103c103129651042d410511120070300400b03030340c88590b941c00022131881d0802e240e100003034644a0900c1045248820280c101c5402d0360100c09525102d03000a4130b9008000507000b0f290f0741025040188056241408090340d0401c509400d58105498600c0740030824041c40340103406132110700c10300c0c04548120481c0c5d40402614a019a0b0b00200c03003400200614551842c1e4841d4940c100612a196080b4036800b1380246840703482040700302e0990303030007e0550341d00c40c40c803d83c402099070350213001101c15240c0003000340c01c00c55140e40315a00000c80d41c866404c600b0351101c000400c403030030152816990000307060084400c10323195145e1045007400c0d94aa0406000580c0c000201003201102c540d2a40781c0c00701c00d21070005080c480d03c00c800c00c20000c008900d4081c40d1007004050092050901c1384500b03d40f141e0903107624100b1281c1d503550f2039002e1071020440a401c50641d0a45c285031004100304c88a40c405144c90f5038442c0c44102034028450351008 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 622449658 1250 622448408 622448423
    0xb03010312020f070e0c0d0f0e010e01020f090904020d0f051614090f04060e0a060b03010b06161101020304051005030405211803010605100203070317220203011413 72
    0xd80181400843c4520203002020054070025042607a151200032014050785c0f42e6902c100100401320b807991045000005110304081000a0366030711f45801c7d00c0080c0c1010046910400001d40010031100c2100c090070020703100441e5990f00e03400001e10002c40c0c40c0000c0c1403903400e4110902000b501041c03490311040500e480b10300391364030340c854441d100a5404015421110141c0843d04020000c4081903105100e04008a0321980d68219507050820b00c6c90121a040e466080c10030440ca020b02402a1751082900c0440c2001e550a01554055284100107040c00045024181c0740e42d109004a6010f070070007070720b031160380700303100c01c0041c035950040341c1c1502c1501a10300420460113541a4080780c0185052070a400c8c0140b200483e01c00c0800184034981c990343c1c0d40d0300000e407900d0300c001e108011013558019580751102d03818040e00c101111641407901170502d101b00006500036948800403940c012001c0125046280f0100340181804078541070807002c0c41c01000110144540b5099240d442401d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 622450908 1250 622449658 622449683
    0x906030308040c151d030a05120d2316030e030714010b040905030d1503020d030903050f07210f0b090601050112092102070e010803030609010522020d0f05010b030103 73
    0x10300c1351000741c0b1350b100e0000211685002c4c0140c542030640e54040c040e0040980b101016503580381440c0c035200010000310802c01144c03582c091390141c030440014520a000811140340807503185e02510700020015480300308041c40b044140c2e032199200c00400d0f0002c2c01201e60b203941c40c0c20585010045440c0d140c040e5804d040b004070483c14180200441c1603400b000030350074480c0003660354001e41035041d00321403c1c0c09800800409031b50b031010f601250900070349800d40320038110f042c05030509820300051101a0304c281340c1001030000d00c0c0d480c2c000c001036807075001a80d4a030394a080380025a18450203000c0c05960020b002c81030102085450407075800344c0300d0080c8800c00ba48034005a600d900701c090440e5050310840004045060004010b9505500c180c68a035502c842d8900594030017070b04640c619910120400049040841c0161b0240c00115408181c60503480071380001101c180708456040341d000300c3d81c05200302c0c0700d421503251044002002d0100d980c40303564084190700300348402c1d24400b20780103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 622452158 1250 622450908 622450919
    0x2060a0c05122d01090c08090d0c0303020a050c0d110c100903110109120b0601080705030408071407091409060c040308031803191d100906030e01060906030308040c 72
    0x10211002c0303501c88034820009980e02c1d5007a92140507000c0c041140845000421800c80d070304144414060440603100041030b1410f020b0003400000000c02e1600594821a00d6000352074120b000b072502207505140c05a51203010b80c20803569400b03089890300311480b9400d4000c144da070304450380700c10004032401210303a00d044140801c207002e2a14649040481c40401c0300b0f00108012000b01d03803600741c040c100703020030ba0f648800064030441c0c0d8810607030700d07041070b4403d00c117156904c452003e800000505e012402c600b4a929008424492014000c0c05020a900174524001050007144014805003508011002e941180006207040c03c560b643c4d114000d9000040d103d1070b041090b00c0541340c200d40310703034156a03440c5800d40d003220340e02e2020427081c80b00380407a6902c0c1184e9000e81c2c0100581e560b450a621000800340c000c0c041e20800c52500c04d024003a0003055140c0d0003c5420300300e0b0343d10301e404501d8541e02c50110f4018180f9800c0550020300701103007c401e05400c500494010b502caa08034108180d5a41c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 622453408 1250 622452158 622452167
    0x1125140a03080c0f09010c081207120506060403080904050a200d0e0303090712060609020301090912030b03030d0b010e060301080705130213140105090406060305090d050301032a0e0702060a0c 84
    0x2900075043c019000d01841c4000e51080031f0361002d46106102c42440c00302224090003409104581c1c240c00661101080c54000701036001e0f05800c1441503034064101030541e03640f80310601442a04038050b59130381002400d10342d00381e080001960342469840e005008a440c00c1400780e800109284000c07410551928012070001084078410300300300010300019801c24440d075400c0c5164a07800c0d40c1d1581c68040c00301ea038400900c0254001d0102c00b000180703590041ca488801e031884045a80c05040c60065542c00a44001c03049600548500c0c60003c1d00a13405401a80e10f43d031a0000031750400c8000c00080b800a40009903102558001c030f40e94907203024210103000c1a0303c42c60405c04902070101c0401c00001420480240c019101411b21606208201001c1011503105a00c0707400040d4580080c0500960107004060046500740b4210b0b1a640c15074803083d6020120b026114143c2d0890b042e4030342c181b0700c0e201c5110003401100c0b1030300e6940d0038403141c001d40e180019202105c9142c6801804030515029 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 622454658 1250 622453408 622453417
    0x9020921100e160e060117132402030a09060b0103020702011409042a09120812101215060f0b18041409010e1c0e010305040809030a030903151125140a03080c 69
    0xe0703600304031001d50755500c080740109c90301c0da004094a000440c08015031880e0020790310035001c6030000102084103043c208151141d00c22501d0515204000d10405030340c4c04810700a00e503d09280f5160390b2400080801e0044c01e01c0135040358182400401d03203e22098619a041440340c11f80c0d81d10303221036160003805a50b00c00c2c1d4040280aa86e0400024030745508400c1ca030381c0d120180802803903182e07035030b0007103010581d411084c01c684200b80c18072200452001c610404018040401013820985e040503010ba01c20b10421182240d0f080121007812031503a100d41124130007004941e454416414440f402c14080c02030040c0245250140400c01070448104550b4240040915610384402c070301104010740050070b0182095480c050108244003941d2010850250401d01c00c0d03407202402d0746142041c9078800d1140b4980c4000742d00304480c10721465004002d270b4000d07041302c40c09088c001c5c0300c0e000e941c2504455068000d1140c545852002d420a001141a800c0503010741c80700b043c507070354904410302039106 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 622455908 1250 622454658 622454671
    0x11040b0a03021801050f120721020c0d080105010c020609030c120f10020a0c020409030903120905010201050c0c0715090306090305091e090c070204020f0409020921100e160e060117 79
    0x3d042c804001c502c0d01f406c001c15001540b034203000035010b400041e26100d41c00074041440c0c1d101c0d0001184402c0c003070100816089440240707004540c40d41000f000920036071100740041d114040100d030340c60290b507040c4a045402c21004140740003044104103415192a00c02c030000c20036001d485442c2c81300b000701d80215000b02490350358245c00c0107015803c000080c402d441040c1c003005541c01c8007200003a100700100e155180c40d52240420541303080c0009080d900300a0a04e502c8100a009030b0201c040001000401c2c3c1d01c0e02c81e0a80540081201c04540e0403655910280c81035007065030100a050700900209201c2c0070588440d40000b03100c0c84040b0307140c4040c4c0c8449030029440340002d0076082000300038100f039603c000c1001d45024032081c03102205800540108152039800100d1806070b1429080705640381542d6502102c1071900700c9251503d82003444110b094032602d074442a00e40100a200b03c0308003284a15500f40389a8036202207585488048840714007141c2e00340d982c0d5a2108140e210b2034031511 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 622457158 1250 622455908 622455937
    0x90109020a050d0c022122030b0430090f05120c010e03031605061f03050601060e0d080a0309172a15010e1b0a0503070311040b0a0302180105 62
    0x1505180e80d14000d00c4004100c4007180a4203002071111600c000e0801203107a0030050240c1c458100d13100e805601f8030302c42103100034140d2011017040040c83c03011a89a0040d04031a0404280141c050054a250411202e0308114261185080502900031461f0000d9400706103281c000720351540188003404030964641400d40c0e21002c1d1080c1c20b0b600c41c04554094100c0941030b2806d000040b00da58003c07403180070080314142c104804000303030041d030b141801c0440840c0521090400d441d5840c0c10b074441e03006005440c00c0281818107403040791656900301a039a0f50111030740b0307520002d4403401002050040d10880d2a41d2050030303461002010081a40c0d8504a620711251200506042d0403d0700400b50400794070700d011390300c649203900626000083c02030080801c14202882c008401070350049854525040082060206482490740036054a50202807410001101100301d0403103030245c01594000300c074525000902c94010303907158002e00a0320742a0380403041c0c051611001503401d800385040030b1039420f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 622458408 1250 622457158 622457167
    0x6070c030506070c080d0b060f04030606031a07120902010e090a0f050c09030d0c11041d0d0201050112080306180108030a0e180424060b07110a03050d031109040603030905090109020a05 81
    0x440301d0b40601c0440c00001c123201e14010455241c01c0c25a0010b900a641d6595600070030001d0040e1905401080810300985103586d1411550140c00050409102c0f070050355984002c6e070071a4050504900903800041c1402460314028030381001411700d201d07134402103d003444040b403040314829060703e8291000601030450035409503002c582d04110030005540c01081c0980612180d00e030f601c40c00e2840071843d00324a02540780c806609103400315004190302168504001040320710b0a201d80301c04000c2c1e10080b0141d581c1ca89000180d1324910011030011819482c000000d0750400000081c6400b00070341d00e64a141400f0841009140c0100802103010401e514001400107241d294480c1044040c620900d101c0454000d0000c04035011174010310b800140c0081c0000a2141ea0908245c0560040740d104074000d007145d64003621f500307190700300350103061b244c1203142c1113440600142c940010001d042086620396034100244030b089240300702d40c020f40c9840f0000c2040c1c0018021104c0001844c0c441501d007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 622459658 1250 622458408 622458427
    0x40f02030c2215050612011d060609010e0423070905010908100e0a120206010e150a05011206030f080304020901061103070807080918041e0b0c130506070c030506070c08 74
    0x3d014420150344110000c22808102070b07031490098240010352004d82017141d030500500000001e0513074180d8207000390800c00c2240ca40c0c1e0b01821242194030a2034004413407242840401c02522611103100f1007015114080320f06609450f01b0288180303031070390315110341c1b0342c4d00e070015642c4413814020441e984d001440380d8484040c941d040344440d6030300f68044402c03012041e00c601c0038246a880004c00140c00010041007500c03907c0e40da03240c2213030040f403c030354689030a90000b0b010030104d44500b0303043c000c1d800911001780c4130359402900116000020114081640c0c6001e01aaa1040b1800c80c841c1003103400100d41da40c450f1244400900c00d1000a615121a03502c6454190b085104112041c003810005c280e01511a001444030b04003220498080a080c41d2401c0040c81403800f211107004030300407845402194000b40242d03080000078104c259944801408411030040c00d42220b07420400000b89282003007076001010b0100c9008100343c03000c40e01e94040c104e83c2828403043c05010340c8801d0104468 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 622460908 1250 622459658 622459661
    0x80a17040f06230f15030303010e0f0106030e0a0f111905150309120c011e150503030306030309011409061605101103042009010b0406080c040b03011806030803040f02030c22 76
    0x3c105801702030a0019500c1c401c0040d10b0b6a100740c218054090304d040c24800305512480341c080c007500782d40c02e080c0180f109051286603100201240505400c41a10b40d000134004003044080210070f01030010003010500c424800b1091116115860040c401c10a481800040c80c0043d81c2c001c5080c0c1000c0e0258103007103100b1006540110f0032a9946d55a03460b1105d1086040040c54032100a00001c0420303104104081440c200c1c04940c032450083d00300700200009a034002c41111071540e02400c040b81140d810101e09009800b4100c0b1494100000098947d14040c105110b0b18201e4030881c110b6005114003502a02030310505071410860400500100b030001d21111200d10440540c60041c14210b40f118000034030b0540203078016040c40c64000350510070b195000d5586980410103440051030185080e036a007015100510507a05100301032252403500b00f402c1d8010314000d5411415243d100c1c00c2c14106071103901c580c590100d2103407282c40b11200503400d1440301050030344580d41101e404502c1a01c00d400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 622462158 1250 622460908 622460911
    0x803040201080c091903140a0b06040e1905011d01060f05040b0f04060311031015172104230906100309080d02070b01050303040b07080a17040f06230f 66
    0x1405001d06100d10005174848100001c1c01040402608841c2491400d003c2100d54204441980c90307006a4181e00100e12141c0110f604150203a80000d41040381c2d15a050800040c0c03204000c541006030341285c00e0250542100c0d450300581103031078802c403400c00201400c8602c14880c422100ca003040d810411440e0a40c4416000d52015141c014528801000541102c0d0325400403950188006c00d070082c14101005014041c80b010780d02040941249d00c0240c00c2c807841c0d80f11b503803003046003540d1104172603c0501040607900b10900c0d103c01d82c1005040d81030440d4000f401540c000c01c07003240070f242900070756088001903c0310150040034691200d078140021a004640e0303450a050301c900c414000902c2032002402040f0070350100580b15461458203070207111060344002d1080d401400140901a041412540f25640c402035265850b0750700c2c1d0041e0b62000000c10b490004034981c20400c0140903a140d0049003c902c904c45c01c000d400440e00d900304541e040c2e00c81003803050405900069450058800e01e5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 622463408 1250 622462158 622462171
    0x102281e0503070311070b160c020a031106190806010e0108060d141216020406050a0e070302180909010e0708030406050d150b070c03171c02130807080a1b03080304020108 75
    0x480d03484001145111170b80d0200c81d0880d00480e8080c100551680c03000304a001540040c5400c0c2d1030481c00e900006e2120340c8500004e003112191070900110341d80c03034004840311801002e2078945078260200c0c0c0a4600b420850b01240480d41c60007041708907601c00d043c89482107400034590851405141c41ea40c0451900a4808040e40300c1c450f15032040c0c000d1072014203909a0020824400c9601c43d1040c1f000b950350a900143c0542d400750800d0001302000302810380d2214040c6030050320b41e400b179000f90321442807402175260009103000038083c1c0400b041d00103020946400040311512941c0314400f43d902d20407031203860b000985c248002210841103801a1241c41001e84030441c1e610b40394400c4000e241d00c840c00803946822804000c0042141900701e01d074401241e904254140051208810150103084001c07100c5144d00140000c268525455107501800b108030451710529164483c00d9610464100203a880b0031100050300702e110301c60f101c582c0030307298801c0210b410740d151540103603504100500350 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 622464658 1250 622463408 622463411
    0xa061a0a12051501170702060f04030302040e0421080c0910030e150612030306150c010e070e240f09130803040c03020f031501170f0102281e05030703 66
    0x31040c1c40080d80035140c01015900740b00040c007142c0070000740c5032503d602c5100340c131aa0200100100705802148079603101300c202c00035015958407450101d00a10441d00560a100001c006000c20f00c07000c401290034900d16442e45035106c0d10510b0f42a540d03030404840054407240f0801002c40c0078149032340a6410b08600c1d081c0859510a0420041c1c01d000301000e144052411982c1004038518044111506201031100614550b0400c100422900088a1007007881c1000c0010901404030007584502c49202c50030090300c1c556501d446500a0b0b1880c2912426000120403850700703400e204003211881414401000c0d408113103d0300d02030021040e0002d00e0a074007540e001c060f0501042154004520480c0b0401e1114221401c45c410040b0304000450518007035070000c448596590130240030340c0d05480d9034514900c10841d052810506c4c10820524600d425400480c800c0130280b1000002c034500300c601001702000741c8025208035040c0c1d1044190880c03004603500710b80304084c0148019078010f10280760 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 622465908 1250 622464658 622464677
    0x6030f1e0304030506130201021903120b060708030f04030e040b03070e1b0d060807120206071401020c030a0201020d0b0114030106110703020d14010507050c280c15080a061a0a 77
    0x90344c0e4140b07a01140c01000c4d41030180100b104640c0c0c1800441e1107544681d0641c030990000c0e4600800d5414101c00c00307200f6641d40c4192080c10f51b940000d940c81603511403201d40d80d9184c40020400d00c490152001c902003000029202c0700303440c09000b1080e11441c0600240b0540c0c1c5410808030341c01c0800f500140004204500409920400e0070007800d20046030f21003c1200d0b46400c24203858034403943c4c42981d0a1913900000e00060b901c043c2110071160300014054203040200103803500912501c441301c0030700c2c8000640510b00c150190060556501e8000c420804d00882c0310054420b00e00c0308688680b07144c41040140402c60280080e140151807100440c0c01554a075400301e190600310120569080500c500c241d03007101400d01909611035040e00e003150901a0b01021140e981200081000c440b43c614071112883e040f41d80c071040213064005040c2031100e65038000c2c0031140c280551481c0c00060b00d83d0b00060382c5041e40e0180340120344241d992810740d035445a024105503046044c0e1a8104030b01c03030b507 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 622467158 1250 622465908 622465913
    0x706090f0609050f0d080f13020a1e081207081b0c030709060905061509010309020102010b0405040605040203070e090715200313081c03050402060403060603050601090506030f1e030403 81
    0x205402e00716100d0030080c003003500650009841c1100c51003030300e0100306001c0c0401c4180c00c460662036421074440700820010320f54501c00030f0201c07031403a0089141190b030040f01032840703800e03d405042100d49040546d491310f101c40310705c10424482d2190142041d0700c2007002103420440c000784503410130b511005440c444080f000c0000e0400700c6c60b500031258261200000c0c0f20122451040da5003013502107136081c090300142c002c0401d09014612011b0706044d0703107140d01c400703590007034000141c4148014010030561625161020061009480c1a4082d115501020804110540b2003038003c008000042034118600311507114032140400000080045207620049000210314007124002c4400c00a0364440d031030300d4a044100380390b039489500306901c29001c0c8041d070407030f03401150702c1c400f951306d00030501d0780d154004122148226032005040364508240003061260200d03415069905204091140d512924101682c2d41400f1110b81480e8100040d05800322606500e94000c1052400c240c0741800d039a038 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 622468408 1250 622467158 622467161
    0x1709031b1212061e0121020c0a0507030317040803011e0506120702061617070e03030705030702010306050117282f0703021005060102212109030706090f06 68
    0xd1039048540000b9105000c1680343c5401014610400c0000040e003603208a000201300d064000b00c000035000749000002c640c0a1560100d0700904103890485540c00c0d1980380c1955141904d1100782c2c0000c1d0303901c0c240420940c203036180382d00503600b04415a045034200700a50b0411844800364505507000726100040c107484040c083e0210040d20428450702c1d1a0a01c000f83c100140241205080109048005d40c0690031814107401141c942810000716542c0400a0744c441740030000039581071002142e00820032000000400d9030a10030ba905212003541d81005481c20341c001d040003403911343c00c1e0740011120945e050300440c44101001d0b0080c01c00400c105c8250490341540c200014090380d03080d40022a070030f80405000190400c5a60b50b2500d007658030000d482c0d400032500380c40c8440d103030300103e00a80e1007042008008018100340c405148038244c40240c690f80141c03404100d003140507440c152504411403000c0d10990b00750019626101e82c0b41e60382001007103080001c460b219007540030000030880d103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 622469658 1250 622468408 622468417
    0x102091003091b08030d05040219121709100c1a0123030c09040311070317040608130b060f06040b0c150a06060f08060103020d0515011709031b12 64
    0xe85000642125078200514140303010651500d0f03121000e041000b5040000049680010b55440b00140e551214400103800841c6c00c2c0409a0342025014082030701c4e20302d400001802032180e964228004080201038505000307400c0a40c2e0300c0403c1c0714469900900550038140c0491003001c841c4c07038041000051400d4000b082e080b9418461901c0081d00c11089118106c84018000310000c110f542441400524414001040142081924105004280010481880910751200f00403d031290064800205030308140b0030355000804500204014101042044030010b070003128070201643c80100f40f208034185011100c0d0030020030007000600c00e4011010704a45d14101014000710a0818941c0c80d00c10700c042c2040c18481e1030008100200c6401a21004200901d8203200c002c40d664100164001c2c051003c02115290a1404010111401c007118003080301e42625084105051140a10f02e511421900140306900410112664030411403484400d500000304a9074600c04613100103001703420 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 622470908 1250 622469658 622469689
    0xe0d080c0c01020a02060d1524032301091d030c070f051804030c020112050403030b010f0201110f0708090d0501021224010305091911180708040311010209 68
    0x10216224119a80c14000358049403401d02c020701c0c01d8007007030300052100d10501d120502c1c0310750b54000a054072810400c0e100c0c0100705810343d02e0340301a030070a142c410040c01000028000f0b407400403032540640b04c158101200480034030340754002d6802d01d03070b1305802014001c080302c1c010a0040f10800c128030041000300015480b440191442910708000036480403c5600110f100c0c1100f035040300105e80c6c542000c80d6000b5050301c6c00343d80599481c001a559418402c20b0031001c1030400003004180358250b005801e1151082e42c0340341e82c215a41ca0200d080300d46520a201d5109410094214040c00300809421100c1c002c0c0021450311115900061462180c001e04030307102d94020880d25108980d080955074440300a213010040350070040b800e0b418581f07103814040d040c1640c0303d0100c1c0301d00008001c0001040400c4000d42c0380005030b070502c001d160000d540b903244280140c240d021181030000e48814007480c01078032030070304d40e0300c0307559094902ea041c543c6c200344030b507500b072100c2c4101d96640d0340ea0350910304 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 622472158 1250 622470908 622470923
    0x5071103131701020301081c030f110a020f030f07061e020c07090f0b0114072102330403110a0602360a090209030a080d020c06010f0608040b04030e0d 66
    0x51034a0209480800e07101800c100d184d1040c4010003140b240810f00c981c0c900420107003038002c8025844140d00800e410010300110500d012680c8c0314107607a8000401100041c3c1d02180e5400800d0001c2650741d00c03404c1541c00b2448020701003000055204e0b00100e02c01e552050340e00412000180080381260000e100c90380e10341d800b150082244403064401c85088004051041c00314200707410029229074420780c4802800c440c00520241885104130904000100c410804440091420402542e03402119a44070fa08001c3ea011200c00c18940c41088211600800c10441580d403031303440948407060850081d0641c1d014015880e0b002400350b10040500685001d5425070403003030746014010310386650300c00154429903111003070250354034084154100c58803c000582d4520052010900301070065800800d001c8020404000040c0940c000c1d0541404803400c0b605260707690100c10740700f20407510464000c240f5560110740413410b00d45500707900a000341841074055580d0008507219010320a0140c5060 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 622473408 1250 622472158 622472197
    0x906010e2e0c0c121220010603030e15030f01030b0403020a120804120216050f0415090b0f0a0303051905041d010602100608060112031106011805100605070605071103 73
    0x3003403d207180300283c040e0b11124500c00b1005d5880013503034200d5800160506c000000d03d002c241402207400f80c40780340c80000903c01c19070303280360140c104410501c83c0352251111401c41c2001c40b400c1425640300b40064082a10241d2070b40c0c50300c3c0303c60000030300300340c04600810948401040c3c006220034041b00407980d5803c40343c0713894204160282514a4070a0031504804c00440d240c140c141c006074107864003101c4204144000c1c40000b002810004036000700004007030000101c0010036071000050b00c8013078442c14140300c0390100b0000170f0051800024041202401003200c0d84904d5401a24070010078248145851b071103104000081d00d004520303280003d000e90040c01001da043c000d855a074558240244055030605255a171100b00500801035034007400e0388940f003810f12034400c02d60000b842406440340d80d6103a110280c100940d0b100302d003c0c614213080c045201c0795a042101c5040364210f595013410203070959184400303800007170320000401a0504030b00b16044801d0008100e0401343d607044a816 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 622474658 1250 622473408 622473413
    0x4143001050f04020603150102071a191701150e040603060c020f030310031e0b1303030c021519060810090507050a0f05120f030d090209060906010e2e0c 67
    0xa41c0d4000b0000c24802509200f0b000058862a00b580d4104007001551600d0010010040b45400b10307a0348505911003100c2c0380711103800c00300710040240818180800c0c08188c1443c00642e17000440214241d0400040070041110f8403242c41240700e9101c05203000410700c5280c0f40041c00343c601982042e20107070751f01c9039903103035807601000a601501c100201650039031400101115a4071050b10018118141c950f49002e114121925001e1185900110440080c00c0004840583d040c012100300c4c007091809002980050001034080d21501c0110503100c0d0705e5803016280d4001442c44210300440340e854000114002c002402500312890140740001030640341030030000c1c80c00300c20b6070043d070107014802020b02a02e200c03a001a01030301e2040c0c8841c00c020100c0f2401500c7c00300c0414900d12280808226440ca040c4590003c00902e8000c94a144864540000304824004180c43c0580401c14200d040c560900b000b041c0c11500301c036040540601c40451214250503107541100780c0e800211021409800c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 622475908 1250 622474658 622474661
    0x90312120f040b070c11030d020d090605040f0b160203300909060d0804090501080d17092a03031b070f0e130c120606030b0106020c030304143001 64
    0x1803040d5401d612000d03604158407503103103000001d0030100400180a10110601031100520507a103c805011505d030440e10b410002e488030700a840e4180024600c000014086104400b03440c19901010f039004142440e00c1c03600d00540d40070001400c496110055540d01580d0b09003c035090300d02d402c2d0428409501d400c00030702030300c4034015003c400c45c0d1428030450900707440c0c20104d0f5500c010152900c00201c0203c0c248040e03140a0b981c1f03e040c400703080400200b41d2070004500c0c92910900790300d4000c074160300315040c040c21501c11030f0b040c021a072100b0070540340540e0401c0900c8807014424402540b40d141f500120b429540442ea41d44c200007041c5040103800c0d24100010001400344400c2c010040b41002445031040310b024207200040451251510103000c206540d40000f011600f084a1800d50b1a161000c09030603144001e0b0342090000000007401800419242150031009000e5841c103801c0511380c44086110b00905a00724500140740d2504000d0204000d140c100b003200402d15409840210a0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 622477158 1250 622475908 622475911
    0x703050106020703031e050f0403030c02040b04061d18030d060311090f131e0303090b0601021b060715021c05130f08091201050703290a06120209031212 67
    0x504550000f1002c0002c00c1c0e10150310302000d40c0400844004480511080310107004406000c03040d54000134002041641041c1307820140340c42503605108074500202000103c600d21712410114100c0364241c280c1c0e060002000544c080540c19410410000c82c11000b455500b0cc0c458005079160307224414010b0088515000c180d0480889403040c0c9860001c1c01100405000780c201040308076203024802c20807580d00b000940340c030013002d4140c80361422810000d0241c12080030683c2c0b401c0d074000104495520110340340c10600034490070507440d0760700903051040545c0500b00036a1480c140c1d903411082c001c001d000510807020200c1d0004610034010b42d40404503600501514403020a02e0a01000295940315011886130014501a11440d82c0c0300450380017000c003402d1840d0703940b914040000903501903100e4500e100d00c000d0840c2c0d01d8440001101d540f9180728102c583c2c015050300c403c1103003510411614a001441007005410a981007020925043d1100f1401a0f0345d00c0c0842e06417050108070b88120b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 622478408 1250 622477158 622477169
    0x906061205100b1804020f0a1209020609130209180405070602070513090503090d060e0f0c18062817190b09071211010201200409050411030a0b07030501 67
    0x4020500b0085081c181240d183d2068120b401008204a003013000d645211980d1842c0c003400a45d85c9101c0601a18150b41c00491004042942c104495554500910607070400c01ea006e0030103842c0a030300c00b04000400d0007449001014035002c01444140b9240d0100c58950ba5034584116903690a10745482d50030000140c02020031940000810803241d503841e6240d0780c080450220024501403241400e80c01e41c4103202209410071110b40c600b1080021550245640c03490030b074140c2d80c10180e58410107840349105141a13900451100d603400d01205e03106505900120003c1465619100b883e403c0d41c08440701100214118240c58810801400c1d05080601e001c00340401800003843c1c0c0c00300e044400d08041002078034084040300042c00b012000c0080e480580f80c4025000607240003880d191800f031407800300c0d550040d402d101e400c8005907607250802e0200b19030402107500305400c0c00361503001410018025150407070740c2400282c1a44042c400301060324002c09107020360307107031454001d42038441c181d018 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 622479658 1250 622478408 622478411
    0x607050a0501021b161e080f06010305250314070e07020c10090e042301021c0e0105011d040213020307030e0d020606011211130b07052e0c030f0609060612 68
    0x103c80c6150201c240082030b100d0403401d01a40e0301c8800300100401c601030b0000c110351310403235903d000040c3e4009a40da0407a84102c0444208540203610075801a164a03204022420703492010320005080e13030005000d00c1c20072011260307540e0343d5004c0c1c40310342007080e1000805a00032151000090602c2402401000b52509203140c60f00c0c500b04814441c00f80c0148003030100003400c810a080041c0c3d0110000790080364400039500c50445180041c00801d0f40488144418038201804545000c1802028100c1d102c01021880c0300680c42c20010038424024070407648420204a441680340b29440998090302c000e540001c4c80c0d51030a40018038000301403c46c02d041d58803004c10803005a83c80b0140e00414072500201240740c1da20958070782e01901a01b91005908c1e0604500400c0c045c4500010301011801101181c2c0640498030000380329401c440d450320404c9007143e000121030403203900403104043d003a290006004440040440c00c840712600000c0200c0d842e8401088a2030340102d4100042d084c1010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 622480908 1250 622479658 622479673
    0x604050606040b09190609090e0c030c120a15020301080105130816140703081c0213030201081e090d120216021212071a0112030206070503060607050a0501021b 70
    0x41c1d00d80520300c82c55008080008110728903031035201c554904800b007a089480d0041c0c49080280481100340038002140d031400342070401d50500007032000c3d00c6040140103446c0700c40c0f0840a000c1480f074901561517062040d20410f90001e44517126850501030300842c01a207030f5042c030010030f007914400b030108880807411070942c00c0030520034411030310103a40441d003009410340203140c820a8050b940c5000159402900c00000900c00c080c0024010540346400d05107841e06c0c044440c008074010b02c84054510008110140010b5000c2c00351260880e030070f815103144002c0420000c1e0039550003102ca0a90540002c505c10110b01c1e0807641510254081000542c2049803943c5800c8001620080291003018011481c2d10725140900c011a222403003007c1c496621481c03070a00048603141d0200307c580c41b4000e880000381d98480320400c0002503902d54064007154a528104840c00e41000e880d075988a42c0802c556000141e00708040701d40680700300e001589032101502c2401154049802c8035042c0d030046c08 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 622482014 1106 622480908 622480921
    0xc1c171e120a0e0a110618030d020d0906020c18040303140903030411220b040f060602010e0607050301150f0318051f1a010c0614040f0308060405 64
    0x1014440c080f0901d011540e545940180500017900c0002001c1c22441c0c83d600900c0302c82d00a1000d090140c074814002800c000b07201c006030015a200ba0604420a5085082c1c40001c1078a40040c10f191280b9001203440820304001075039001001c000003804040c02503120940709109a00d40381014034020500d55075940c011b40e002d035a282d1b44000c58040e945010050401d4140058400200b061480070040f03020b032004018032503009484522024200140340314040040c1010750001c900d0342c84034500241030520182001d02048001c0006001815400302c249140144a117014031003103c00000c2140141016103904000f0940031350a0310501c0f0001505440c01251040c98000c1808040c594800729164444107010b4100c80e03a01101203036002da0000030004e4002c0c40701107550702601e12010541c110032201220b00c800401c01c55428140c1c0100c900c3d074480e109580400650078080c = true := by decide +kernel

theorem cover : BRFrame.Cov 622302158 622482014 := by
  have h0 := BRFrame.cov_init 622302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 622302158 ≤ n) (h2 : n < 622482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
