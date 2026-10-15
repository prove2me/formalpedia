-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4365
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:23:17.51742+00:00
-- url     : https://prove2.me/submissions/5a090f5f-a127-4a6e-bbe1-db40437ac53b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 784892086 ≤ n < 785071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 784893336 1250 784892086 784892093
    0x8060c0a0f3911030c0102070510170907090f0b030a06110d0f05160513060f1202040e0402030c030c0a0308090f06070803070e0d0308010605030403091707030c0b030402060313030c 79
    0x103929401c07601e9822440c840c9410902c0183c070740340480b0500980141144500060000b07443c1d03002405101e01c01c4185002e140d607003501c80c0032483c60191120b17000d1503440c01d100703220b41e951306240d1140080705424078070032168518960003982e000100140c01070000711300580d5110050710400d03001d850440014401864154418051844000c0c140b003400500d40c01e240b83c001c04600d00d401951010311400b0882c48402c0c503410302c4124103c41c0c1d146030502d0841e4038018100c0711045691005904c060020801150040707500d49002d010358821802c44200c03008280505860f1380d19201d01603440034054908001158186004201c4240b00074440381107442404d0002d0603c1d0048401075545810100800420941001c03051800c048110b03203105044030b555500038400c0780140585410004c0100c0443c0801d4022003464001e490700d40710520741128102c1410342da8480e42d1000781c0341584036240004219503d04101c0c0c1c000d50300070380800d2031030b17580310321415000c903140f00c04904002d00c000440022 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 784894586 1250 784893336 784893407
    0x1110a030204061209080a110c0301060f08160806060409061d030a08010b0304020a03021c120206060114040b0a0c0222060321020a140c0d060608060c0a0f 68
    0x401125440058a980c00c0140c000d007801000f81e403040c4d9080c036218000010803122000c0d558001c04900d40001440020146581065400d40c1e00781d40560a1200c0401d4081e001e0300140f050780d40000840f40741d0b04024480307684041c01c5203e0360441e40c0010001c00c86170b0501d9040b0495960269101060b41e0300c06160040c070700c8a00d54940506500f01142d0000115072042c101401000c650140a0650419400048443c099440024030030081c003595081d0315801922440c0d502900100b280040c8604140040c0d1140d1088400701d000500545203450040c002d1003e840c25120a11055414840700e000b00391480c3c0d90040d416607000301410305414a501140f621880340000002010030124910316050510000d0780c0400580c2601c1c0c18880e041042c2c0c005032194006130807800d245d80321b403c80d5401f00d0410022140440d0855501e030003180a0255640100c001c035141c480890350250366407800804507004030100c40001820860a4a1240380b01e40030413884054a035114a803d1400240041c00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 784895836 1250 784894586 784894597
    0x10f2a0203120405010e01050c121305030319080a060609050d05010e0f07061209030c0219050d060e0609010b180c0909010305100f0606051b031918120b0f090111 71
    0x700c0c1e0b00006402c4c4180d50f404070080e05c21000c2070a2450170980c050400c561500180340040c820703150041005078032210a034a801e0002c02c1c014050341da6600840044200f070000001c02003003c02e41d00703c042106507406d4400c1d04215492592810030683c14101000300b12120030206031215925040140007070711081c440224042e101c00c008040c400d15100c0050110900d80302e0011000345481d6106011941014401040d16130454819070802c01c81c0c00407200b001c01c2034000310f401c030b82e88518090800c160741d0710600d00020980101c40e09541c0c1c2d00c0415090b104070600e900d81181000013064407280c10441d100d070304000600c070301c031b42030111200100d022040245c1c0280d0700d036800503a0f905010b0000784941000c4201d080e0742031045500700640038116115a443c041000c1082000e003460811062081e0307421003844040c9e031190f10407030080041403000c40314107c02c0c4480021000040b014055a03415016541c00549104142d50703000701103545140c01459040c0c1552500d15240d030f003956501c020b10 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 784897086 1250 784895836 784895863
    0x9020f090415080d02070e06040f0905100c080f0709170102070b070e10030605150c150a020c060a090506041112070303120b040207050c0f0d0f060c0e010f2a0203 71
    0x28030701c80c03070080d001389011140320080d02036400c4800144204500c481040d988610b0594011400f003450b4441c040080140603400b51080c05002c91030a8203803c01d4110a984600311b54401c1d07560340740c2510300f043c80c1000f620046d0200709442ca081154030282a104c0140540c10000182451069104d080c0504d50481e421f0002404180781b085e15440c00c40c0034441c0c0d6440c685400c015031400c01c0d010510640c0c20085458102c400801c2000d00c110040181c1049000501c3d04814142021034103030300a034002d010120050b00901c80004c82c0d881d52441084076070b5070080002e150948540e12040e94008110080f0750300f00d206c07010b0b0303015500e1042100400451081d560500c07510f6048000d041150b4a04a45a1156004012110110b800025140e02100c402c0340e20075240301d0010002210100300110040c50810b03022204401d00000307500200e0720704066140da518498000004440b0103070010105804111249503007601c018034111800021104001d4040c0c0c0310b1840c1c9c00081c81c1c904000800b0703 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 784898336 1250 784897086 784897121
    0x20c180129070f1703040f02011101090510091214040303050f09120a0507080f0a060c03020c1e06060d02091501020309040e0a020f010c0305040e06030a140303270709020f0904 77
    0x1008210906040c4800041020403860550030541e9400002c007d000c00083e04100d08003907185002c0d2421b61244020b29400021500c0800c0b03500d0405000c0c00d8017110030384030b0524690b050107155004003c3c420120011304c0c00c0302c0c42e05095a40a446641000380184a03800081c0191034440c1c50300051400c00105000040034490094034102d0314110b055008280941c2041ca44c10010603000204025055031200011602110384c1c1c400710001d004040030389046116041100d0f5401e40d0f101c2a4101e200e0000b0107841040d5240000e100703803070010401c000d4200b01c4070750008031a41072540d046002c3d0081481601e2a0004240000d0240d40c0365203801c030059000346151104600d0b281120794851942070a10b541c410540f074402814900491003101c02ca0314001d000520150b40c01c4c4014500313550700c01a816115603502d011290799406c11140c1e9000050241d0708980c1035148111170354503898842c00200f4485d402c20709104060340103030801c0211101c0921a4024541e80d902078030401203440b1140 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 784899586 1250 784898336 784898363
    0x5040c05091201061809060e0607050d1a010c02040c03090c090f0e07030b04080703180906030b060114250614060a120b041707060c030606020c18012907 67
    0x401c89410012000030b034290780f4207241041044ca1216288440c088a40780029010042c7e09281001d010304144034030241c0500400c1001d0280c1000140c0b01074000f03107404001c00005a03840d0b64010044c00071042c0410914404500189400d402000300c003211440c020641c0d80c000d41d183c50101089400c230050b503e8554200c03071160407042c4102c65444280400520301c552641d04c0d117980854000d4009410038a001030003009060140302c4030310309079518080b0107451a0390703449900010000d500003200c0f802450f60114100d03603c6240300821910074282070301d00d081c003060a00302407130880d60b180018907007243c804100490264450301a00c100740102d00f811902d051820071080c0d1010790400c0f80700c5224000c40c030000c00c1c40e018490b50b100307610404401c002c143c0804900d036103000c0c16400600309400c00c000340503c1135254120a08035144c0e5021240e4075215041003010005244805400a00448004102417071a010550410307424841d8186e03030703416a48403500c84652041c2c00a4800130441c200 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 784900836 1250 784899586 784899589
    0x715260c0d1e0e0a0c030201030b0303070f05030a1d10081810020a08010e010b04140406090c0921050a060203060105040305070602011b030203130f02030f101413080d051005040c0509 80
    0x80c02c680110380f08060000b40c040d82c3c0c0e541c2020826404040d04040d03481c810540141ca007042140d1950b50445000c881510701842c05d181d4a51004202030005443c14886680c111104120b00c2a80c5030f00805401842c031064a040b188a1802007503503a050315905960850b600050168042c400c002a0700035948045c1950041c1c050401070784030310f01180520004001300015581900c06403000360f040e00b00080146000500900001c3e0000b80c6e5152400d21179554454102c0865022101d04070207483d09040000391039420703140e182c4c1c0003802a8029901c1c600015000e640150307400141414414101900e90300c40c1407610308181c2101016171340d0b0340040c1d411880f000c81e0541511180d8901545145440d40342c1c5c080d01c51807440028035840b00c544440d421950140440c48104250100b2121400c1000142030003401d0201a410054200c6201240a1717040a201c980c21a035044402a843c0c82c40c0700c00508020000100014191003000f0000708242c0c2c0c880c05859030000444ea00c0d551111203200 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 784902086 1250 784900836 784900841
    0x4060303121a0307060c050309091302040e1c110111030c04030c050307150e01090b0f0717071a07170708090f070f050105090f030703050715260c0d1e 66
    0x9400c05280042c0d00c50042c02d50780021081c00b5910649009682001e43c1c0c500a459030183e8100d4541c00030440b010480d40da0454903111191074022581440701910710b020351603c1e2503042d00080625450340502c404124020b07881e1482c2040800000a80c442c00b40b042e450b200d400a0700c040100348000641041400704030310760b14001e000d04602424480d0b02d082c0b803604000d210b2814001c03c0c0502c0038a0203110f0b82c02850f8002c001d00740010a5a90f40303523500001a01e66105180071680010110f101c5141d072007640d0161104030303911021001c01140c00d0700044d804d04200601d180c0801c401c41d412461043d8403460080d01403085601c0780ea8003070611201c805c0c10003d950486d0b9459a01c0b07240d00b000b52150031080001190400c0c00c0c61030791010f000d0042101c2400caa01043d80622841d01d00000b04200004c0100c120303411058101c0a1f44018982103540e508200c405101040601c900310944440e42026aa080015008010f2170714014056102c2510350303c0e00c000000308494412501c40e0032060 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 784903336 1250 784902086 784902101
    0x1110705062a12040e0403120510080d050403020f090910150501080c0c10020c0a060e0a110913060b0409050f0114060a081009020a1707031a01050913060b0406030312 73
    0x45001d000c0c3c1d6107141d0564042405584945180c0080001c081001e050066021007112440040280607070b18088040d4140a400341c881d400c564030541c41d42180781881181520181ea0340140f6201503c20810104801281c0186c010100f0340550501e40034116090b200c0c91084820f83e08800083c1854040003503d0a00c1c020310980c00c4040c1008081c00b00b003000708d02211842c25212005894211102d8154030744074904030000c202900d071507180300781c0c4400028081584c610030f54140f0400708011050041484040e40c540e0707488062807030308d9400074000c3d03008481e00345809000082d480314a51100e921307081d00110042d2059540c0c2450040002002c0030f090b40c0300380c0945000c01007510f06503400c3d55404001d00910507841c1c1e9030552008550b2240105402040701030048449800c2440310942ca62884d884103c900c000ca112502c01e0041104403120b04944d0010716440d0a5919580c950504004c03201c400c4490b103035503000c1c0b0181541c0390712400c0d0245009544001608030080b10000c112040f0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 784904586 1250 784903336 784903417
    0x501091103130b041112030d1d07090504050111070f02011d0f280b03090706030b0a060813080a090911030f0103030c080403050312060103290111070506 67
    0x1001004091401110424042640100d800e8900d681310705114920507040c00c400c03644021010b10069060704000054684100024000c10094041006502070350041c0e45590781a82c10180080211144503486554010300450000c19154040264001681c0c42514100c0300d0101d0400788406559000060321854100c0040c0d003480803e03140e0000d1004481d95201034440c000003190301503803841e04004105a00c8103007204034422900c56400c00c8440e00f0442c7c00380f07442c1c8165800050450311034000e00c250100c01170300d05c01c6d03c0b44c1026401c0340d4882004014101550401050ba800030352240e00504036001a9030700d08001c1420a00c0540c19600c01200c221099141030040c0184501074034900380c110b80c0d02d41410030a401481c9803030300d400d000741d5002502e035000110700b0501c82616884190301c6403409036010044180700c07118003000102901000d0401301c02c2e042080350294054040360450046080031609280d584200088030f90b80803441030b03c14010860280e0340204ca4160040201919 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 784905836 1250 784904586 784904621
    0x60b010216140406054f0b060702120106060207061814120304140f120c01050a02010b092d070c020108070e10200d050d0906060f030303050109 63
    0x2000d40107142241c098062021030004149810704965a44e9120b507005000181501400c8010070150000100400148075010141d00d8102c02a24880c654a0101c007902e5440311003102d802c00c1904001010000f80007a0010b00802800000d41d8800c8510f480e84140e0500100d07110b41020301c001c3c1046150790143c0700b8800900c134081c14500502803520280c0d1481d500d10300c031000baa6400214404800d04040380c00d40400240400d184400d22010341401c481511003460b0504444240a500d00c8050a1904260490102046590300c81c2d801400c090555200118000c209200001d1080d4020780b490020180e200f10f00e40740c9200305120424402070304031010386d414508100050324800c09180024104403490000541960144441101e0360902400e03c0c0c03450281e010010700386680140b11540411b02a030013041511100003030501c0400b000e65201420050220301c8400907001150781240c00c903486440100c0c100314000c0e0a000110300a5901040c00e52600325006c040707440035810300004a8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 784907086 1250 784905836 784905853
    0x30b1206190605031207060b1201050609010b0711040c05041508090c010201060303080a091509080307110714010804020604090e030d0605310e1218090402030d0c0314030c0403060b0102 81
    0x136804120382c0450800713040c003150398445034901480240300400d10b0b00e5008000301070070f428400c0158022482940e06946040b0183d03203403d10700c02e0500030038000030460900c00d01c189585086c560050718200710a41007041c14281c40d003445012001c059003e00c8005443c001c03c200400c0c504000051101c070082c0000c00c140360440d20000c24000d8001e02640341541c60716000c000300700019403910280c6050040400140c0e26910b0910a0740c2d0007070b511000096020103641501d08400b007032140841ba401041c41498000b12001921820350050040c1d82c000c805000020b6840181d020f00411240f102c4069541c1e0640d0010010071680070750411406405254541d07410314401e2440f890b03104020b01e10b408003801031840c00802500d40012200c180340500d0600c03034115001c1c280505020b10404030340c0c02081c3d42400c01c4c0300035150108c602940c594050440d200301c25000c0c01c05000341c00d0081c60080414176983e180010f07580c0c020346080c001600f0000e010400d0016038800d0b0b408140c404d1000d0013100 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 784908336 1250 784907086 784907089
    0xf09010302012313121a150d11030708060f28022206050901030b0402131502070f080a0c1d0a0c0201151805010b120412030b1206190605 60
    0x994003078049250710051603908000c001a00d0980d15240c3c8507544403c0b4554075500f0320006840c07440021248103600071042d45211800c18200d9100c2c41c51f031080c009040704d0301700c10040084500c010584441e41244c0b15502152402d10064001d801c010b00280a282860300d04544c542500410055591380501030000040200e900e10f11a520004413000d611030003001c18000c11800070110084850803d042e00194054110028000c5000b007600c082082d90882000e00050340328846e0310445601d0502818070011003240049051200c59204444032940c841511400e02c01c40341d000188030b5485604540104001409290090203225808825010145c40324010404c2c020307101c00340064881810300203551007540107090342d0000740d902c4090141e40d00d110314144000c001d1041d82043c20407002103405001c2e00704840c0121035210307400c22a5512a142c0d014884c43c810310038810036031101151651940c1e81d00c030701600e80c000e407000b901e511705180d14120743c13000103031013003084441c02c0c1703003082185 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 784909586 1250 784908336 784908347
    0x110409050709170a060b13090b0f01060306080c06031e0a0b0f01030e150702160e1b031b0304060f060303050a11060105010f11010f0501080321060a12050a080c0102090f0901030201 79
    0xaa0394025004249403000c0c80000d0703100800f20648611a6142c03610690520a21003580350203a000041210701c9a41c880360124160ed606002e44015a03200034880c81160800000440d400a510b211850401000048070140424103682600640303807a407900103000d00e850f130106080300400342400c00c020040030407519143d4402c60f8800071001444000106514002c0c000552107408050b04180b0403503c91207907981d0210103540e10a0170400d000405240e101d20f400c101c3c2d00806040482852020000d448a0b03c203500051003103900300e0302c41100359070800312401000080d5129803901901c0d241d030000300400031041d008620002d61310410040100d640c000134040140c0400b40340c030380c0e09503c030f200c005409842c20003a00880c10303240000001e1002e902101801c5032020903a564125000119000c0c41c6c4001d040c1d034070703d0f488141203100700400e09030614a240f08502c10002e43d10740c2d007400d032942c02003508030984280aa035000034000c4554039102041180c0c0e8141219559115415070b00000c14 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 784910836 1250 784909586 784909603
    0x80111040f0b090d051e100203150603040302152404050f15190f030c0803030603031c0f0903080a0b0102012a1110060303140903120d11040905070917 66
    0x62030440020f02440540b100d06060450310380010443e40c485034007138050301c10b61640340920304440c010702c51804d03e0361140d80203c03409030303030202820b84c050310b180010410326501c0900b08506504c038150b14503100924541000b80309a00300d0749c02c080b40150014200c102005004200c5105620346070401c4120710481c81081e800440e0711092840c0036402901250354004c28070300080c03031803614000000d02d040e10b0250100503a03101301c500c1030005903500e01807580e902050300c1ca55403640044c402d030340d148003c015411010780030001010411010092102d401c41e8442401a070000e0500e00810529008074056201c401c1d8082c40200101005211043d00c0c05c140744030b1000003405000341036100944500c00b07407021001c0420581d00f40c0650200c02c500141141c1c0300032000700b84485a8510301c2a4031801b99004c083d406405021144000b0ba45810250321001c0c00c003005039541c00030440c84124060250010b00030701800081d40342032010016068513500d9006000c032030650040b002c101d110110340480c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 784912086 1250 784910836 784910849
    0x17031e09150d0f02070501061d010617040f080d0e01110a05030a1503021507110a081e01020d060306060305060901020a0504091512030c1a010602030f16050304080304080111040f 78
    0x180c403540442100302c0500401402401994004540141407050660012040391480505441015403019002020820912403400400e030b140221045210310703482c3d07032917015108990100850341d0f01d03501c24143c1c3d0444243c00528980c0c4e042081081c1800b440707010740c60101582d10b00c0c10210044130080a61000412810100341c49948200c08880110701d400050b60703006245d400d44030f82c0c4c44080740a81e00800c0080d28070200002d5080d8290602d4034580007a0790f0b80e07c01600030029401c09402060340210904081507600704081202200b8610815002d14403600011408615606109140c01006072031104243d10410215002c01d8000741220300711031008070041510650101d450500b0302c019408030b0860a0140105003c059122070880102071140803640031034038503207031101c10502d401d00405000da40100142c410300080c550141c4407980811100306030250490f40c8050560301716900941540e40301240c2400030321303021f0191b42515080c0c180024101440c003030a8114608241c810341 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 784913336 1250 784912086 784912129
    0x2070b040b010b0c0c0f030a080309251d180d02100509010b06160f0215120f01050108150423010807290705190c060f050f0d0c0917031e09 61
    0xb9140c03500c02303018010130140c01c41003598a92401008042c0c84110360800c01c220120524440e001a403003020342d100070740d55081c046112003110040c0703484a0202c0909041601c100d1502d00c280b080340104000d05010400c0d034050504083e0442102c402d84001820080301641002c03001c0ca180c0d200e000989184040300070010002e0815410840c1a000c0241400303508610b040f84044000f6a6080040c03556148112108159654601c01408a00800c2c01003600248489001c07400d4405101d0080b0074076907000704005040305404060301c4501c0c949010202c0d00703ca4603001001014014455000101402030008a0401da0b80c0c0d127101070440f245404c1c00e840da8011940c5005d00104100c041010660308603454100400d506240c04000c003c1e125040002d0481d0207030340181842641501c00d812002ea03452800c00d0352285100004e00320a6141c04108002e07800002095040d402000360002010b5000d1550b414101d20300950303146103103d800c05404801c014501c1e0580300ca02c0d00034150030042804 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 784914586 1250 784913336 784913359
    0xd080f04111206010603021e160b06040e100b0907020a03020606010c03110d0210051f05040f020f0f0a09142413080715170403050901030f02070b040b010b0c0c 70
    0x24204200505006031070301c07034040081170703032a01075000f003450020a200304009588206010f2070b2611034a149102510080340c42c0d600007540f0b409003145c11040040012601041c0d0b403078000d1038004195000504903407514820b202c41d0400380c0c80c0981054840c40640b92000140c0c4000c1d59803000a080c280c1040041c84281080c10b102d401c111881007580c03c143d50401045201c020340c0c483c85961400c088514100114400c40c1c420305611040e050741c048a006414548400c00000340360104845148507003c0008640c1c03400c456004100343d40b1104051502c1d00a4808001d200001d55049a01d500d0361103c5281900d554040d140104895490201203502507030b41d800707805038094a031040c403103d0245c1c071010604600105020040da141c201d0358020350100b00d003080b0344c8074000d0070741040c0c800c20740401b090100313104000038020402d0604022540c0d000400400040b603014542c140c0d11103170002c040c082000700480500f0b004245c50b01d80542411507100040d40c030740040d60444d0348100c806920 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 784915836 1250 784914586 784914589
    0x905151f090515030a110406020a06090f060204031b09090b060d03020f160303030f0903170403051215030f0d050a031512050d110f07052b140d080f0411 67
    0x1d454024102c090041a03020b42084015907040e0000d452036030015043c40e5412401c0f80d1241d00f40c82c1220740c95070090403a211982c40d500001e021002098943c1e01c01400e0120104c0c4450000340b008500c1241d9000701c008451080005c124090f0b001a42c095003407503030356408036079203a80341900060b040300c46603000071591800342d05e4005880c402c0615405110800340d0030000314003800c0200c0e402900c05108004040c0d1180741140c00403d402000316900341c0c00088042504141607a01500c24240320745807081c40e0704c0000e66113804543c403024240c0c0d0842100002d04050200420b08801c0d4001088072a0b0550009096802270f444500105540d0310003c041c0c0c02c1c904a89240103101e070440109002c6201d090060325a100c030140e18001c20f00091585400c0c200010700085203212640160801604209c10408031703e014182581c5403034001404000480c00c84502541454440d2040310b0f00090482605410305124484101c01d21540300c00f0031001c1b400b103001c01c2d540704d0791003211011344806400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 784917086 1250 784915836 784915847
    0xd1508030915090d111306092304050a06111225020309090f0a09081303020f0102120d05070e030102181003020906181c050a0b0606030c1b190308010905151f 69
    0x145046c070f4140b240000f00404254001c446078600303245915a1009048034450085505460013491035220400d10004101a607001c04840e45c82034001c6854107010020401c10041c0aa8007912021801010b0000b41c1880d010251305140d42d60000d5810018240001040840000c02004410343c00c080001d10400c1564041d10f80c040e40700107101e488074803440351810023410350b000881c02145000481c00e19980000f9560030525802c071405803a01c40004000c5024050140060301448010591005a540c0c02c0c009030615a0401f4203400c0c070b240d4480c08000d00641d440d00d0800515104006d1400c150700d4940840300c441b482850840451031040d004513074400490300c0e070881c4581c4010068001c001d4082100c28525025000d0401c29071120070030000248010f0791000501002001134134401f5290f042c001550000a5090301d840320b07018400084074008809045000402c0c4c0001400565058815288c00c140071840501001107030001042d034a0125071100802132110f8108540c2840c8910b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 784918336 1250 784917086 784917109
    0x60703270609050909060919030201110a02010f110a050706090c0e041b1e030b090a0b0a0c0201060f080a17070f0f0618050606060d1508030915090d11 66
    0xc410251249503a80001012034040d401010b12555500010030040711002841c1c0d8010388200003d0051402ca01c0e0150310805032441086056540344c0610300403000d1810054010b1b10314079000071075000748038017511088400e41d40c102c50302e1501c1448400012503210301035a138a194810800034007842c0905000208900645c4166840c140c0a010402080101e00d14190f56602c124001405142c07900b1207100030980e0380724000b190706010003040002ca440c003c900c9802c450200c0035503901e80020748804241d4903088400403038292300d51084241e000e40c24418900117020311920864854244000940c070b606410380c01511800020100c40798a0462208907a80d06a104292400c078040341d1a100380c000b0120f80b0103035406458009030380000890495010922540b0002900407075903280c2c10804c4603040705841442180d0f54180340c1001420b11801c8101030480c0e940210340710100b0744104554420f1402e40c00790b82070010f0016034400d844009802102175030050f100503810480c80c0c0441d01c00c1014 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 784919586 1250 784918336 784918397
    0x507050d150b0a030c02061003080f180306090601050f120d14131e0902030421021905010504020a05191202010c2001030e010218090408040f0b0a0906030b060703 71
    0x25698483c541541c4034000d810013640035110240d0760090359a080700203520010303180100030085440c0d05142c074001800151054003410388408140f00220f1306d81101102c0d05c031030a0b4840c030018080c628003d0754910f81d420080f9070389483e80100110700e6441e0a03544a100f001e00ca44c81c0d1216088003550400e444c00d801c040d040c0305682507a00c0114103488140c2180c0e1044000300d080d00442c0c030b000c0078000c42e441540c00200401d500ca0391402c061640c080a24001800c6004040c0880c4810351111140346903240100004078aa08203801080044202c66110380c3c4141c004003268401c00c2000c413422412154020f0820400080c00c2c00103030380050382014000d0400750380110340100b05c4801c00380389208040a9030100039002c25410254200d1007403000710b02c16504003000399641445c0140b1010f80c424400c2034000e003025540c07280e5150012261700701e030042c3d5070045015001c40e5484511034000b0304c85441d05000764034a0302c02043d05840741d540040c003040500b00c01428165100c810b9440d0740d00c2d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 784920836 1250 784919586 784919609
    0x3100515090f0f01060c02010f0c031b0c0f0605130314070302060f0a08071d191e090b03062203031b050d11040617100b180906040507050d15 62
    0x52010842d1030599040b00d078195001205400400e050384204401a24268180c540c20f50320603aa610954100c1d11203c01202000006d03200d10301c0204c911030018510900c5041c1c031919443c10400300d03c2d00da40d40740c0c000ca4100001401541860310916604800b00d0341c010303400000c490180e114490404c10250400780d000000041e604d07182c030744410005c01d04070280756140c5200391101081180c8050001c401da84000b00304220170b800c45d10b003822014041c2803104c00150001c540c0c80d46045241001c0fa050901d00341e048420400c00d0102c0d038003840000c860110090060361800c4206907040034040490b01c074040c03540e543e05204140c000da008403a00305000c201d00d500250000bd0003003540e0721076038200d4101810304015011146507001a074094075201d0f10343c40104519402c0c00d1040307440040c644e207100705142400041e1030040c1c0c8000d000d600c6030710800c29150b807008030030b10026800c00f4040a0003103282c4001c1202582e8000d0594013944d8680b500420703880c800132107001140301603801103040c009 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 784922086 1250 784920836 784920841
    0xa0b04030c0201030b01020f0d0f03021b06041e05030d0b01050c011a1c0b0705030702250f0b12062115040b48030711010b03010204050310051509 64
    0x5030050380c07203140d9034803da90500c0300120b6a001203884400c203003507404081d440354544c090ba040c081e2910710755035012803400505007a5400001c42c507503010a400e869040e04a0310501041c01920450f0050240c3ca401240c00300b91915654035036248900e01c203003a80369a0302c003200b40c581c2c1e2081d021a40c210410000a10410b001034814030081c00b5001c100c40c0c401c2c4100005d1149202084c0b0709110b03401d070001c207036100f140d4612400b940c00d0380c4010240000c5025010280442d02c80c0c1810b01c000c075014060800c4040390401d4240440015a40c101c0240c07800e00307001c1001192000c4207003c1d03024206844104039001800d4041ca401c1100708891011130154441c1035080303050b0258114825400741044200c251989070003c0d09914810781e00f110f00945030000759205140c44940c0d14901d4030340740203400440c006802c0d4200f007500141d0766440012490076402c5001042401012031007035007200214500f030300e000c000990752821006054002920b5900296000194204020002e10040c000c1c90355403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 784923336 1250 784922086 784922093
    0xb0f1606050105030d020d02070e041109070e0301051b0a0c06152d061d0d060c05070201090503010506011706040e190c0f12083a0513110904050a0b04 66
    0x400c02401071500901c10701702c0d0340c00002d1000900c4508403106c0c2d0043c054141c246040085640c100038800d54150850151140e1640c550030002480343c68299585071074203c1e82000c140c2036807009400381c1540b164117482d1512895809041b1100c001507410030840100c854034011002d03103a03201451400300400d00b40041d169860140b490004c9074145507402c142c1040840120a820305401071100143c24030728051900f6240c886c0360030311010020f00c54100c107402959500c00f60f41011050388005880851a9801c6507040400e0304043d040843c0203110514000d40001c2070b201900070654010315502001c20025200d03580400e044c10100320a5562102c0d050741d100c004110601c03c2144c1802201000052501c114510f8000741d030011490102e050f192070b00d80900e03941140f07160604650b104100c20003540012102c0052460307003007011400f0408001021002c9410041c850011a0798202e00040080c2154800e65078410701221542e110741c40c0c50602c10320b000c000004c010a081411818441030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 784924586 1250 784923336 784923341
    0x1002030705070f080304050909250312080405030f1c0204142403060d230f011104183305040c030b0d080a0c020306040f0507050604060203040b0f1606 66
    0xc040c061001c0300c80655441208201d196010320690480d030b00184014085403501541240c0c02441120840380c114110014850350007000490440d601c0707141c014208200301e10300e4603400707581c0c405040c10740366031400e910f400d51a48110b100c01b0040760700c001001c00400a106282c000d1820204904640341c0d5244e09000920340e00501c2c5851166082030b90140d2002c510048801001a90001d46800e43d01c0703080c02d2107905d010b14602102d80c00e452600e1080c090910000c0b2100164a58000b0304980f040403401c1400c441d01030303052506100302000140030f4010070480000d901807404200150702c2084561546207061b6550300c100c000c2981401b089003905108a03480c00343c070000ca604014000480b081603007281c804004454002c1c00f040074610108503817001500d1290564200340c490702d007182e1700090a001003110107d6500c1e04440030441800070800154010b00002d48516107001e0030948040e54900982c807429110384400141c40e419a02c0a030f0036100380c070344170401440c00061145060b501 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 784925836 1250 784924586 784924597
    0x40c0e091e062a070b061305070306150f140f040b030a06030c2312010b06040306020d06090605010504030b090c0a260c1e0411070f051204051e0f100203 67
    0x15403c086800f900804210b002c5079409035509070916441c00f416a92800950f0714001d25507940082c00f00c2e00031100c200a8020b451042030b160360001043c0f41041110317902e4000340c003405070070030410f454034459064100313010007043e080c0550020744860300f01d02203031030340e01c1b55401c041c804002c0030043c4195107816420107402c0d24400e03a0450200d0f9110181070810303503404024009402d042048079644c0c1c0c201460100c0e82c00d802c1c2e10010454001901c0070882c5680076500031201b00340c1c005000c00d84001c40d4403030f1102404002c0c409018076072812000034800c0c010b40c0005882d448030f0300041440f180c010000a03100315400b40402031000e41d01d895407142c05158900e42c000c410000844150b0140c004105030542c08070040840c0e003003142182481d04001e48003000150080e41d2810b1205124080304083d099441c0303d07040303c0070350344454a070407400d103201e10b0804036007840140020b0003203503980040d102a241056a450301410031400001b01c80364500c40f01d454001c100450b01700300c2d66074040010030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 784927086 1250 784925836 784925851
    0x9050115080d020102030c19030e03130905150102030301050909070f0e040201030c02060c1c0e010207060506030d02070302180a090b07032009060d0905030f19030e06040c0e091e06 79
    0x11800b03040c004080e4281d12040f41c60b142e044004012428081031140e0200100d01118540007452440d500640380c6140d020b1001c0d01c4541aa10300d040011280728042c4a50000c0040c6078402c520803200000f039520b0106020f00d500c640c15580000f814410200555001040301c0d080c142c60440e5a00c072200c40741c2d4815641030b800a804d01c10041d480c45e00008031140152075491415240ca1881744280304460303d54485001020384039501c0d292055000d001074410b9a00500e00001c007801d00008162900c9410b070501015900201320800140e5521044070904920b100715400d403540d1980c01c1c40e00241859040200710906407000d204010340e050f840007207106e40c921140301c003c280a082442140c0903040295030301030010010a03400b42035681080d030302d003441072040b03134140320071100c88858581017400460240340d5043e80340c60784950705004281c1c0c0390044801521070350810740c50310503840146001e00c147c05d001c50004a00391001c01c00605c4060050400740625130031880610544441040e43e014 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 784928336 1250 784927086 784927093
    0x102130b030712090605041a15061c0203010b040801060f0b0426010911100c11101812020f0f131d031204050609120403120203040b161505061509040905011508 70
    0x210610521641c154000d044189c5035082a0f11a001040100e903c2011b400a081b40c882035510810b840d5800914003071701201c541d646e1910700f809030060031075511398010200000c0106040007803002440446090b5131940c0009060000300e80d00c859898043c009000c500da618040c1102c051001041da0794150b02402c4a4060100054440480d54119089006006c0c1880b8001c0c1540c24a002c030004c4c0b5286981e82404141c0c00f64100250b03298081d50360282074850320740c81130402107142804c80c074400c0d9001100e404c210704070204003044011542c010500740e034a0342c0710a0040d03214203078010096003081e100100d959450010707400702c56040042c0e0782241d09102d4180855a150310114040d111001122803c0d070905180d621070b8043e10800300040d500b03500041001040401034080102800030a82e949010000040c0c80c1c20108070400540080003545018180042542c0703010b00480601c2c5c800907080e0b212003c0c0b500007001803c010000400561900d510010002e500c100114220360410060303 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 784929586 1250 784928336 784928363
    0xa230a0e1f02030d0504051c080106080702031306211e0609062d150f02060a05040206190225230a05010f0c0b010618080102130b03071209060504 64
    0x14103164600031258035000da00f09006440c10f01d4040c3e1301942c1e02a00550803501e0038480a515400c604114100c040c00040101005200d0b40c0d800c6105140c0010300c501c011480d06907100ea8180c3c51032814060b200822410700c410850400e0528160704400e01e01010400004480074800401d00010104803402d00c1c1c1000710020f071106041c8256003c80d0500c2440c1c071814018070101541580c0b59a60710384074803081000206a580078040c048031040007648642c005202200406483c003c00142182c103118141740820006841c0c04007541c000014500d01c0c3d07004141124000d1313007000940c0b10320607900b48070840342c100034424400f07501003140c070310008011507441210304c0400c19031005015030340c0228996404202300d5104101c0b90680750b0152901117550107981d41d481c0321500007030b40640000384c1c0402d45043c84009141c0c07000000c04e1150f000310320344400900794030501d07009842100800c80c030100c00158000c0c060b1710070600d08103680e1000c2114400c2d510380b030001084250343c10341d40080036298 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 784930836 1250 784929586 784929619
    0x20102070b0105060c1504030c0b0609070906050a0509130b090903030708060d0c030807060e0c06090109090f150603020d05011710050a1d070e090a080a230a0e 70
    0xc5603030503500069955141d80c24641444515030000c080030449205000c541c2c111200c40085050185100e0f035182d881921140c1031071641c8480191090344107007424414040c3c7c040d0031101402c1210780b0390411603114609540e054807240983d0400303541181e1031400519404504d54030012405500700d4523403900786c54440340156030303000490726040441c0300744000c2110751501c1130b9041c80c0c0d40d2195900410141d240d5580c21050342050204640403500c0b488240400300e0306204d100d0b01c01c8015500103043c50101e0b4002003650f142841740351091680c80c00c034449c0400880d0070a40d280050038243e041c485643d900024000e601001400f5551403504001140c1c80140c1c01d51820100c8040008120508021a4680092078050820807200343d40d0140600d00c107200d8240c4010f04001c1c140a42040d40c0381070b2040320f4620b801810051250403000700c140004d031144094400d20b8009240c419880da01c6a801410b0242419015525a50012445103110780d0300078090002c002043d14112061180d000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 784932086 1250 784930836 784930841
    0x70818012306041413080d0f091406062209020a031b0906050301020301060f05180a0807030c0509071e020f010f050a0e0109120e010e04050a02071704030c050f21100c0201 75
    0x190311703800c17040f40e401072000810500c201502030400b0800c0009000e68240b0a544226a214041140c20a0741d0142c04031000384240a031591001040d61030303030094090172a00d8184800030701c074003100041d518525682551159800030000d584c1c00307107040d108034140301c2074081c221104c1e115190742142000310100317a0381418000e8074122502510b031a4005c0141d20000d4a06801016411030010003850502c095507032040c007000000c218000c0540002410350410003401022608903070300882c038031400d0003070341f952000c041301c0f51304090744204002d01c080340c0e0102c4c14502e1a06804d041c17507080400003000c5010560006028031a03c10041010707021004c68103080c0c400e4680060040c003480000b030424240290f81c0c900c1c031400145081c00011403044001400c545043d605864007560228601003046062864044d095003105209414186169503824580340c40d409800d00842421075101d5540c1c50b80400f00402440b0303064040004022503c03000da452170106007080e1460b042444640c000c40c0180b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 784933336 1250 784932086 784932091
    0x2092a16020306011a0f18100e0427060c020708010c020c01031416120b15030f060d17210403030b0a0501140d020a1412010302180708180123060414 65
    0xc22a843c205500c0414422841d041480d120903440c7d14188648655a2405425587c3c9038181e00e401d036a60490f0014082240d203843d900c641407a2181c0b080d0f0801c1a80d021490203e20742c40040030481e4070049004a041800039440290150300309088182c00c1600030a000d08900c00071703030b401c100d82c0b5000c481c8078010240035110541c00c03508100111007100d1140702c06d1900c400c0007402c0441d6040202002c50301c0c03000302c140804510030010040c44a1031085400068010310115140d0026200c46c0d00c4542581074800c0181c08000c4001810000311600401e441241c248510071921700d9203058200500a07040507842c082c03040074120300221f09980690032070048a02424035090600c41c81440d0000250b200403003050038090341c49580c4421800840c021300c0c1c03040540700b003007219501d188140308460104e107070520726001e00c0340101b202250f07005202c20b40c0700002e01c40c40c054800400c00014010f0050405528500a0f03100080d202561700c03030f103a140640f005440800c00803503546800c01c1e00d070a05 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 784934586 1250 784933336 784933379
    0x10b0d030503070c11060f03040b01270f0618020c060c03160c08070f1b051503040204020307180605040e0f090d140408150109150302092a1602030601 66
    0x52012903800351003074413600071281c4210700d15012400b420780042e440d600001000d030485080041080204007014032a540102035810440c02d80315405d032008500310b4840424803030b1080d42c80c003050003802c9075500718100800c003a003800c06545c482c1c9016680a50303c001110b006521400020a0290002c441168410b02c420409003000d100c495404480ea042900d2068401074400e025800110f00414440341c4887e100c1c00e030a00107001502021a8045100c0d4081d510174110b8043c8031000384008012a50311603030450f801a96030355452410380d40344000c0f40d1140790044c500030010500d15009802401a50f0601070340300e04030b81e507640d01c40104120450784034003550005441c4400040c041c10440d01c1d00c01028541030b040c07a403035401d09845c007944200c007403207070f120004010041c0c001139106010002e607509000c1d5004c60304640105220f110080c0540c2c2d828196601194403404200c01c640545411b03d1001a5076505407280e030f031802040c02d04060780f1a00030b420000998601820700f12500d00e03103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 784935836 1250 784934586 784934597
    0x91e0f0504020c10150806010b03040f230a060c030f0225080c012c0f0d05030a020705060411120a0519080417250f050d0c03020918010b0d03 62
    0x245001c0c84041d420404021030079105121255040709034030b02540c40854544c0c03030001c1c1d00d9450072101900d0900306900450380d0b41e0b010030602022071100e41c4602c031102d41107038601e0036000501ca003040307000201007007020186c001c0320105010030800d41c019113100911503409025450307d85010800324414040d908204104004240c9545c000000441d940640140d03192400e140d00f0060607820344152894400c07441d6084014449200c0461040600d003900600051015511590303289644240700d030b940205004000c00040c00301d0f0b040390100c03801380741d20030161a8107003407626280022580511101c2c0c401d000c0b24242d40b160040002c3c0303031204035812500078080b00e1880c441920700221200c0d400e80d0301580801c80810311013200061080007840d035900500342000304510207004c212030310420524454101c2020050b989900300d003481030b40d00841d0303d480c1148c0145000d50b03180d1000c0c0e0009411480301402c01c600716540a4141281501b200f00034400d001c0c684040203040d504a00300200802c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 784937086 1250 784935836 784935839
    0x606080601141f030b130c030f0209130e0c030a0302011d12031302010e041805120c071e03060c020a05190f0b100305010e0a020a150804150f0606091e0f 67
    0x1c64541401a8015541000103480c1641c3c808560721600c040000a041600c9800009031f4650620900d101050008021403c102041e000a00f19000c0e107a40d80c581c1075201c1c0e03540786c000c40c1c007404444044200103003103481c0503042e842d020b4003900041d120925001c480d0f107001e0304450000b040e9003d003804401029444c681c3c542181c02a41001c1c401c05a0411407015066500780d2202e10a8103400306140110510640141c54180d00d40200b40000c0006000140907000c0520700024510050704c0b0502800b480310304182c1c0c512108404130790f1014000c18204a8214000794022075040e550901890036078201e0420800d6100b40c110304c201c802052154003540d90720100e4000c02a041e006021504000b000700c3e0740e9100d00342920106e5107c010141c21800998003107244c2229044024841449455900300c4c8168000c0c100ba90020800f5014201101c5e06140c1c0003915400340002c02c519120800c0b809840b05001840e910f0113000714110055498000030f5540014010403044506190382000340a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 784938336 1250 784937086 784937119
    0xc21060403050f070204110c0c1f0f0311030403270e070305091e010606110115330c02040c02010509330f0603010b0a0b07030e120a060608060114 64
    0x141c1c84881c2c22443c20606006101c0141e0716802180206005900c0203500d8803208044641050000b4520714070500c10403241c050040014050034000807028240040e10010744002074015201444000124071000410031003010f8002145d104103007581500a540d614070300f5009200400140140078001c03214200050b080d92081e0803c0398007601201c26101107050000715101d004001c2001c04450340d44070350080c045a9400070b039035030315103800c9002817001c0c0c1c020000007080c14035036000b50100100900708140000344206800060302541040d4444841203c510040c503550345058128452820300344540714152050061901410081001c1c00e0049a0780803000420544501071600d6901c2d884002d20004548001040c8140b0000b189031000f031410134109400c40c1c00d2910802e02c1488484800e001060000080d500d5060741400d03c00c040d01010b400003011050542c4650301540300c1c1c12982001c01c10550800030031194944101e624a90300c0d07049084800880384078403508004441c0d119800e0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 784939586 1250 784938336 784938347
    0x610020a0611040b0a030b130b0a12031701060509030d08091b120f01053c040c12050c0f01030b100309060b030601080f07060305190b0a170c21060403 66
    0x140c1003030702c5043c1c03800b07644d00301000c1c143c4c10051546002c250b031060100c0450410248a41710107004c010104142010040001e00003940e0b40140e40d1594100385502c001c01d806241403065601c40380e07070f010b9919a500c460040007030740844032142c003902401003c9440380e401034089902505900c2c003d8540810043c241c2c10048100c1c0200e1a4480002c0c80c115403992002d0180c419000200070000c1518641418204805800030030348041400c980003542d5260300b02029104900c030709402071801d4548460828048251680c0c0000186200f0070440c507040010000d0300c101100001d58011041149d04030066003142c8103a00c80c10380249900740052000c034405d03400952014800c43c000903405000b440800e143c100b09822140c4c7e29071041d5100340150204010f000000d080ca442c080c4528076000c128002d4180090303000052564403560840903a54510b12241d01926001e002d01c06202100d0f000d01d50750b019a004c0650165160b01030b01d41085000010106400321281e004240645440e682240d8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 784940836 1250 784939586 784939601
    0x3030305090c0a09150b04030b06102304050118051c050106080d020c0120100c050c1f0c0e0d1b0f0e10120c0302091e1008060610020a06 60
    0x8140154181008280e59080030b01c0007608885600080c0b1070202000191220004d41000016040907c1f04000080749510b456030b1004041d00e540d40005c6452100740d070f1501a45089100c42d2425401d0002e103030080502401c100c45d000d07a40c6031485641440c001d06405602d016460f0080e445204ea0bc0c1c1419404001c4032050307214100000d0340580d5820000d092103400100c00005802503450b00303002c1c1d0b138400b0280302c1e0500c0c00c10f19540e00c0d10700c05541e03959601500541d02c2c803030303a141c139000c0650500940036505458442000e42d080c802c41d92100100d00c08550b92007042841c07500d0140e2031010310480e82d500d0854009403c0281e0b4000d0f90721581c0c166050b00c200103000100c0c0c40c0c1d01040d90400341d113043d0020507128203005c200b800c10f500d060301051130a03004020008190074850001c1240c010f2150102da4050b0380e0000203441d0380d04490100880000845041c0204805001002c040c400c10741c012204103200342c92075500c1d480100890400886140360059104148035008603205a11810 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 784942086 1250 784940836 784940851
    0x5040e0c0405060f1206160f0801030f03031b0c1202070509010905091c0206150f0d02010807030225140601060c0809030a0b0a0f0515030a1b091d010f060b0403030305 73
    0x70741c65103481c0060b00700e1160809603005034201500303120080351821f5000d6102905c50525038a83c4041c80d40007400c9070414030001d081c9284142c40c01c0705140c065417000c02c1d0b05201405550f02018242000303440122844030855800c100341221180051000c900541070f1075009062100c10b07481c00361110041e15000d8551003090080007044801c2d020141c01c07852596440f0b4014007818030781500c80500c40182032a155000301d82c1c803015401d00b41e491412402005609007460202c1d078440b12001c070024000c10000448010030882100005100e210580200911030b1181d841103140c000481d0780c84d09020712030000400c8100c0341240c0042d40c550080d056420010f02200c140810680702d6469208064031a08280c039511103007508201414010a036100503103a50a0105540d50400700c0c0d56403038000c8029000c040d0755800718115145101546004010414042c0545aa800c1e1500d040b00101b00e43c44503079610f4015258419120b6000300c00480e40241415400d2600e5910140c000e40b10040042 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 784943336 1250 784942086 784942099
    0xc0c1302040e010f03031b020d0204090c0e0c0706051602070506220b040509090c01080c250b09060901060b070f1a10140d080d0e12030c090a05040e0c040506 69
    0x210b00e002640056900900464105010440c41d5060240c10f50100c00074201d0310502440c101c901503160021b120305002d80c141e90000c1c04c0b40c054141100c88081540106440c40034010a201c0407055001c060f00b6014041d03041000756442e01203001c00140380354111400035030040541000580342080103803812100c03100200150714a841180c1185400b641c01135030320310750085000d124a0401a801c150b00921450040615a8104001800d20784004181201c1c08200003160b0100790031000b08030320b443c0c2410280b04003c0895103030409469508a6071504a4855140000c03480c0e4014000e8804481103c54114a04441e076101c204624003050001e482200155a910340381680124031507200345813150316415610300b8000e09500004140d091144601c4505003e040401d4818049407601110030341c0010b14440b41e00402e0b030400002200f8007041c280040304000480315110f004050343c10007103840d030062685030000c01048591206412216601445151800e41480d9004540218000701413 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 784944586 1250 784943336 784943339
    0x1b110114040914011401020105240a080a080c06060109350d09030204050a02130b0c070816090506010504121709040c21090f0b04080d0e010506011101020c0c130204 72
    0x464103950b00c00000300122070f01da800400090200040c940d0300a5003d200a03c46420082c0da00c5500c13846000302800707a11080550b015442c0e980f5140700c40242810b406950301d4140c00d04103c40690400010021300b809040300068a542c410b00e820002e40d0281e20300044642c1d081c50b40b80501951002c440c0d030464104820a00c00400100105044101c0568030240c03414114030501c815108040e00c20102c0500511040c81c0c14480c0901d90380c203a46c5100d0b02940c036950700f915002c0c80c001c0564000582e50080071060100c2ca20030a4140040ea504003c0a000988641004582d90b103e580320309410101001031503000107039008036240303103110078207500340c2011000e10015040311218808100071480d01e2505035241c141e0706002c4400540801010003240c121512281c0300c900002c03400520b0000700c5000a810003216909448820307581803c104510204822118002c3c00140c4901e8081040762401818140050085071f03190003c00d40540443c00002050000410510240014240d000e010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 784945836 1250 784944586 784944599
    0x920030309030613030e0a17070801060503031605030f13030b1b0a05090a03020907020d1106040f02010c030302041d041e021e0109030803071e020d140d150305010c1b11011404 77
    0x182c07c1d0290001c2d1030703010703c41b140c18120980b0f404129405114140d0503c05c0c101f0040c0e0700031095035074601940c40c0d500d4102010345480350462061505400c200303080801d000c251f00000d52942c0d000d4038030904160749507845032030052042003040410941046810003076135203101c1c0314130064030101001030250350071151640d001980d1a103084407040c005900421050f00b030203621151100484486101428660030640c9849141660158001c2d05000e144d451140415110f941103171f00400500d1081d01c6030b0118a01c0f00d20180c00306032030942d040480b41c51100c0003440c0018101d0711181d401004600e41012494080340d505800810b018180082c080000010481c000029482000c0e50b584800d640c020300020f0140c29041544000d04650090703502c00812a042010510001150301140d900d8512031060040503016820080c000c00c200c03510000200041500009108141600c4441c074036103441081801201070b5841c00b80c55040201c00c91850b0303501a00307240134265044e042c00c4d0301c0d09440d0705 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 784947086 1250 784945836 784945849
    0x140d0c030203160309110402030c0f04090b281707030212030d05010e011514041805061c0206071416061d010302040e0f0a020d0920030309030613030e 66
    0x20406408290000100065119010500301100c03100d8241002000059250a28200d01c01c0685c1750080d0b5000000c55004e400d40810b03035004024410a5070394640d10b60801d40042e103c49100140540c40540740444003603902c56280710500001c00003680c45605d400300c0d541c035400222444243e14080c0900200c0035031078031304034a0400824070000790780c0d40082d0641442108c805901c10044000c0740c000601069620400c440c1c0291000e2400b02030200110801c200b45110b540d01403a00746e0102d440c04a65401c060304661b200d40c2c4d0454003210401000717140011106c8800f40d00941c80841001b045c0001800a40030002000165044602e190352094000020a045130443c0c0c01150051b900414544103c9a202840e24800e02c1c055060625104580f0b940b408007a024217400c14001c2c00240030314059074103441d40641808402d00004c1d20908040608034840102d0254110b03030400f20403541e050010803a0302c42c0e50081c00912540e41c0701441003c01807921103080b010420791922400c0303140c8c0c0710f0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 784948336 1250 784947086 784947101
    0x30a060b010e06070c030c0515030c091503130c0b03060a03020402030415092105190c05150c04080f070509160504090f05070e040e191a0106030507020d0302030f0601140d 75
    0x41810744d90990a5007012a061400b55000d184a180c80070302d201c1c1222790400690742c010508001207911941d0f5500000d00d03080503c0081060b00d0000710070003400400200c01910668002e503020000c0c03d85416003207202d84070484290f0f4002084000400041c28903600a55010b8012916160003a1150250000761928000305481e26500171000030b10340300d10203491000300c11140c11300526202d1882d100e271140281440302001449103a801c1e640901000b440840c10390315059544040518006a0014554001740070706103080c030a003034203000340c084000307404000d40300d0052030080340d680c4403249001d1965814503908100310013803200090310030381406400109500c4480102c0c05181011008081070b00320460584198100040701d0744042d0302282c108410007100b00031146110850804504400c5094002d4215014101c000550705a040d405240680c466600b41c805000e106801142070307010076150032940c850744070080b41981d1300030020120745914403102d140c1815000701e2190100c4102 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 784949586 1250 784948336 784948343
    0x1309020c0336090901020706050f0115082a0d0905030306090c07020d20030613030e0306070210090311030c060a0b03030c03030402040b0109080a0c23030a060b010e0607 74
    0x2240100900000307404560300c640812502d840c1010001d0192071401034810790007801445040045070403500c00307404440c10035821010610546c20555440c00f0b400c2024030800c0e881d400c014907030b60000341c840c000403070140c00100e0780c0a14044410400b1008820794030075110801c01c00704001d41200401c0c1c054460080d000304007441c2c0b280761900a00c251030900030a2945c600c1e10070485480140d0f07a000d281442d054101d60038078044d2800401210003080d10008195042c07041408124090340d02e000c03400c00c2e451007540c88100c1c0d0310302c420074580c1d290015100304015070014440743c9031500701680f004d0b090900926003101160a0100010300316444294030081a411200800002c0840c034010080c40035815001136140040c0083381607228003029000038400e58960100c40c003a17038803a2900300050510b070410388075001035500d024a0203c900d407142d031803613282c0c000200c1c0e14000c0d51502c3c204074031809400f078014100203a455200800701c018005050050340c909070041900c5003c00391800512 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 784950836 1250 784949586 784949593
    0x180c090a09030e0a0302031e011e0509010f15090b0123030609071b030c080c03280305070c021002011b0f090807060c080d1107121b0b0c1309020c 64
    0x1d607410010184200c0c600810f01501c880e010070001620000790410a140c8507805468180c400001024007400c40203043c4121070071000d46c0b0403841d200540c41035020b0310790b980007004650b010340342c0b2005881400c50b0104003e030341c07144104210002034011040c1c00005142800007040c144503040c00e0307140303209588041080f02008025140c102514803540003540c40c1400d0640d40301450030100d5242d0040c60007406c01103000c4100c0100240c40342602c01580d422001c3d00d48441c0c00200107441004e50b0540e0100a8400e90206c654442c020702c03925020b807042c0c1d40ca961008015400340600340e002c00c04098215035031001285c0d0791414400c1c00400714495643c520b0403401041100400c1c3c0c42c240c0e08071038041d4008800400ca60f50b00039500790b82c1c856000398210b894a8003859041d00500c40d10121080d000800100e81003004500d051096009405071a070303011000c42188440c50b03800880400604000f0010040b42071300480d071024000d0f0340c041e180b42d00c840c6511201c201c010fa03000250000010760 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 784952086 1250 784950836 784950851
    0x101505030c0a23030c0a14010207290a18140a050103050c180316080106050108160903140102130b0a080f07050910030b060a0801050a1706180c090a 65
    0x34040c45044000c007021600c2c2882d45040450300d10543d81007085441c8100c003583e0f03001c00d080c0c41c14032006094000042000401c2951003d0342542844041e445d580180103290001c40c5400c01102108170075041e4080501c2200205080e440b044d43c044004041840001400c071031040380c00c1030b607a030050002d04900e07034880d140b40000c1c4803910300b040d00003d040c18104000c1005081c155001e60300100038841d64000a120180b011034240200700c1703500d01c60030301c000101203801041500113a08840c3d082e40c0c0d41140b40d60f000c182c2181602d2499042e40000ca02da01d003040400e11403003684071248900b40006142c904007500f4510724a01940c805040c1d40c1000c510880c4103a0883d00f40c9a2020416000c150b0b98a0400ca00030503a1040803032840c072844401d581081500e109600900d4015000b4000c0c1e41da641500d8009005030800b40f0070b136031003240e01c55404180303804182c0b40114050309110040c0441d481d60030521002c81000810205140718503101e5546982d02c1c0500580141456180000c441c03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 784953336 1250 784952086 784952089
    0x1b030c20090105010c05030315010c02030d020714040207020f130204080d110d02030408060f28090c080f0304060c06020f160c060201110316140a050a0305060d02150309101505 77
    0x718030590000d814000703607100c0000491030200403260b00150a0403401b444007080340040e01d1150342d00030060340604c12140d06903030a80d000036604d41500c003840c0481402d207103080f040005900c9840d034004c0d040452205039450074240b400545200035045000982003035120003074945090742e00714012000811040c2e08413400f840910064038440414030185290a0800c0d4409588850191004030b400740c042c3c001410080102504000d08003010440f0070000f0005514000642003203003050302d500c1c1c0004400602d418000982c0c401c442d000c3d030069401c00f80b40c804190344050702800c050300d00e20f4081100180f030350102d00c000c0841400c1e0b4658080e07912004d080825079100c0ca40c01240c1568034103152505190540d2058a1784103c2c0e807020001302ca401080100c500d08010030b0f6280c07069a011504158403078009024080c0300c00c00c0d540c100807607034901c0100242c071400c074107000e5004206000d0384003120b04280c0c02141d1201d080011135040c1d10031886507000700c0d100f081c00340c0d018003e980e200340b00700d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 784954586 1250 784953336 784953349
    0x7030e1c03050f0c040608090c10081602060403080105040e0c0613210c210c26070b0301030303110c0a060203040c1211010e010c0b0c0309060112031b030c20 69
    0x205418920381340100200380d062183e8005c4405102c291000503000a0041107454034408010b40040c40c1071000c3c1c44050442c400544500321415140030400c0d80701c0d440000c4203071049401d9940e1b401c10f41d2902c000d010003042e0b681800301072401054000503982e10384200428100c22445080107805217400710100c011b030302d4841c1a10781240f0300f0342100c001c00c2c104008601511450300251920b050a41109601e40c07103114002098a070b40c0300300008101c8401020401403c3c11a1016084107110004694803514680a4503d00e80010720041c0080f80c420341c040f0b002e9503041c01c4a1480e04034080c551915004406401700d811640000420040013008006c0c50b004180100e00c8458030314072680ca0780b101081e010f07109810004025008106680300d00c19030481940c104280304064103140c10b0b0044903500c222205422446100000a500c4500302c3c01400c0c92501955404c0b00000010500603000c0070114060302080f540300c0e41000442c10425a0204503c2030300c8501401280e80d0301401340 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 784955836 1250 784954586 784954591
    0x1707121e0b010c051b040612140d0908062d010f061739070803040605070809030a1d0402030a0b01030501080c0109180e030f0301061103040302010f030507030e1c0305 73
    0x4000c84083c0030b2002440c0000d2040201940000480d070001040e4089002411a41d0003400c1c0484040c08080c00d201c00e001c490783e007251818040d55101d44082600341c4084115100741c4509511850000e00d0b035107000c0c01ea51506034011400d007000c10040e150402424802038101040083c1d603d54100544c40e0011100329a010b10903809506529100000c41130310b0710b4800d014043c00b141704180e600414449124140500312545149484414606040310141c0007210111503451411010402150180709114458101c1d40c0c000c0d4641850b008040340e28000c8078004c1d940d03569410802d045107079900d0014500c1904580d100103103020200d0001000c0d038106074400d00a0f030f0441d000103400b41e41d00c414003c0c165002c12500c2c10500c811007a40c1002481484905040d41c00b000c2081350003095000000c6040b9180e5030b581101081e0300b6190a600c0303100c1d500c40207000c140d0f07441100c2e221038004d4010780c0d808003207401c0015401d4520340c4130500f804c010803001c84410a075040610740c403a415216054 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 784957086 1250 784955836 784955839
    0x816030c0f0e0a080f0c0f0406080601050d14060f04050d0809060105060f0702040c09051201180201030c11060903130b0c03090f03120c060115030b011707121e0b 71
    0x11904100c03040140c8030a403140c01d0740c030801c20038140420b480e4640002c41c0c0028800708044032480300750071117203d4442108030441031103003400c1149101249054040d03181510ac00c0d001810446e46003100300f1014001004084440071820000307050141002c0c0452881001d4403070700351b01c15141910702241800c82c980881820f000ba40000d2203070300340b00020124152502520020b03a59003260794845224003600800035072017030a20381c1c1c0010103030f484040041144c0040d100040c0256031103484900340da401070b000c1402ca03120315035044003662094100c04000039003820021041981105030b40e003001802c03542c5141e02d51001986450340b4000a06810060036090101030070600c5952603e03440c3e11904c10328501c5401012851259942c040c08404040000400015580c96070810300c10344516091107062290702d0b0310306440c80c0c198040e025007029580b05030f569046034444a9480300c00d400c0d0241c100401c100318503800801c40f02d005d11680010741050001080160740e03c1d80c000081c0c8003402c0019 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 784958336 1250 784957086 784957091
    0x60504030e180721020c0307030e060408030304020d14010525020714060c030f04030302250b1903110c03040510020d0c060b0f0a0b0909060a080c06091807081603 71
    0x440b4480c0c10038126040103203490064083c40580a408416540d2200952950703840000c01e110500030000003002e016200f601d409840241460030081e06009074851603031103400810000b00186844061192824419404d4880d19401c002006007101e9048400382540321010102d0f00041d11045400d91344030301607100401501c0c3c10043d1400740c00d007030820850302a070b82c04141e00401660030300c00d0300d81d0219070b01d20030768403140d1701c0c01d00968481040d041c6481c00c4d40105d01810721042803d421600750307040c680c581407901e80900310300ae020a1549514030100341c3d482e4240b0758070750716100c000c0c00350800c800001c607100ca062800304500c80e01003e40380c105540c01030641400341c54028000480541d0050030001c3ca2521074808116600184400740342d001002c080f01041c50806c040241c00b603042c00780d031007441030703511542400244140ca0149605640c450340080071945083e0700102103200002e0220041c40c1194165000121030a54440020600c114200902180c140400b50218211441c05 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 784959586 1250 784958336 784958359
    0xa02030a2a14210a060f120318051003060305010b10080408071a1e070f020715090b040902040602060a0207150908120916120b0109050403110703060504030e 69
    0x840c840c006660714000c148058101d02030301e440c40e0b1038190703800b140600030f070300300f60100420041c00d4845048a071010780600d48000860806502008501581c0107040d14440000341510259440c1800721520f0103041500f101c0031802e911400c00200d03540140c0d0300c01045040c01c51030701e9801e40b065a5000c900503803242520b40c2d5056030050000f50060307040700c940d81d50f40300c15041111a1803840303003940510f01428410f000c1d036004004419000b0b0200b020a0120170340707442004a8942c1d4540c420503005a0281b079040c00104404d56006082c4901c505012411a540e0703003903040142c003d81c0c0250f0030a40d0220301040a181c040c08619440301070340c10114036010843e590446107440788618802410b698403080d10801c0309810440d03040001d50f07200c56481d80307402c030f10306a902e0400109a11028801c0d44001441d8520110903000785a808481d511003030f0b00b44200400241030082c410f03020025400c5056401c002e042c0700c003101550080001080e5031509080107400e03e03e14100650040c4021000c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 784960836 1250 784959586 784959641
    0x5041409060402062104080a080f07020d080709050d080d060e070c0602030406060305031902010606091a25030908070506091311090406090b1207181e02030a02030a 72
    0x2409903002c1d0303040741d1307440e210620740e9116000042c1d0301c4011949400c0704401e1000b0700840174050722034984150755040240c6d803844000000501d0985a101c0564407104078004c01c6030007003004660164251405e9088540d03611b002415240715900155070300705001403000366071102c5003e080050b1646910351104c50900c800010012010404042d0050350302002142c04c00500da00720400a507081000c5070384032841c2078081c08980554001100c0590710b4500d00003002ca000c4d46041044078109180380c500c074440a683c0c20fa056015280a0600034034811400c00c62510340016001e04a0103a941c02c43d03103904024016150040e25040030b445064107210010099031290181e480d452320444002c40c4c44505440207401d00e00074400d65980c4581003800208030080280c2c4442c0c1040e40851b0481e40300d203170101003183c8840c040e0165090000c000810125040519000030408007000200c2112a0b0f20b50300000049030010b5981000b0b10790008148002d4110a0049490f0306940402c010000d440081 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 784962086 1250 784960836 784960843
    0x8180106120c142101150b0310080706052a0312040506090316020f0a0e01120302060f06060702150d061410020d021c120609051801060515090d061505041409 69
    0x10709132007864080d0840d0040c894020740050440840d11040e01c0c01142d02d8044907181604121140c44440f8608200001d00d6080051040100c0c0c081e0388903d441c0c803c0d14151403405000003e031031a466088824400c1c041c3d00300b00700421601110211860850400345401c4d07040507400b07440701c040c030b41c014000c0540030b00c42e022000741015030450341500301140c0d040c04150400b449510114a0758080400040e0b503221700820024154820b900340c170046e6a17094030600c1e00c42c100359a40d40c2c220074140208001818024044410303400000b8455040007041683d010960303c551f0402c02189420f0034029003d1f007080d608803080340c142c90015007071100c6030040003582d0315080f0807800c0031159070742c3e09a141280034048485a103150301d207040c00002e8a5554482c06402c0954507901360705814041c0ea12140c070107100d840d00f682c00081c10380c001c1d001da8003544100da0b00124605079200000d200c2100010725588a2a032001c440d1020202c1542d24081c200411075040302d2080c010940b2400c1003202000010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 784963336 1250 784962086 784962109
    0x20601090e010e070602100c03050c04030b1306020a03090b07020a021302030709081c0e011806050a11060906070801090917031308030c03010e01090b030d08180106120c14 75
    0x200c0c00a66a4401c1c07911501502e007010074480303d401514008100d5950115041c1c420b140405814450b034080c08008800f1180c1c100ca008000c81401d000510014051110070394004514885071142c1e07030303626242c00080740d11116102c008a9540d06e010740070040c042841962200840c0080d01c0210703203680224400c03514160f040e0302c94590000000d410a400b500002024000000442d00050031040080003c110307036800b9000491031404200b9020f41c410440a5007000c240f9581c0300c40d0500d07244040c2c0e06500326454000a103ca000d03000a4403810170402a486210880018462410f22100141070102d0607000301c0c180ba41400050808180020b4182942d000b00b80042a81c0c0e560f40d4031141002030b6071460080c4208400400e100d0203410503000b45040e540307480341200302039903155540021500b0380c45209030103030480e080c0203080c03600480500c0c1e41701e01c104a5050b20700003a803440790308446550300040d4035242070b81c0720182448202d1201034050b1442d0028503900040440c0000c0c2206c625 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 784964586 1250 784963336 784963349
    0xd0815180f04030318140106140a0902030402010e270a050606090f13020703050c0705060405090115090f091d031216090911030403021b01050d02090a0b070812090a03020601 76
    0x20710000c2402c05110380e01c030401c540d2522016144003613031441c11000c03081c81000399552560820070080f80c1c2d00e1485e1919801da440092400651916004e00700019400080040c2c0c184015510804020380f280c8801d00754600003000c00302168060741806910442010f019518150b182400b0000c0b262039440803100b6920301122100c058003460b500086244a4441070504014000700742c1208140d003240c080e0950801c18001e4412190f00c984c14030419004600c103559026205a00402c00707000c6906582032401c071545088098070f070700c5040c1340f002c01580d944040007450380c1d07404070401140180c0d40800c49229078005145400c0305c03000c3c1c8111800700034041c2421401d5040103404080e0045001c40001c207000ba070180712101c4081c8402c004c6070401c84040d000b50003140904402985880c0b20132001103c161103450a00500503030780c03030003900018045900a80d00384404592100044060042c0b03038401d40e251561150130007003840c40d107180036207850016803000d51401d0009030007040e01419140d1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 784965836 1250 784964586 784964611
    0x11d010516230c01020712050a06110d0c020d03061d0703020a120e0106150f080c030606040302330a4814120904020c0106080d081518 59
    0xa050614028100514000707401c901d10000c40c2c10080c002c83c00114000f4240c0039605016039409403c180340141402c008c1c04c542105500d100010301942c00340c9501c40c18020740c6800c00c1d07002c0402d582100c10543c403c8000d41c0c031500b8007900303040c0d0602034100980100d590155401034401c3c03000c0032001c4003500d078005051f000304102d036501d44100b6016106030a1001c042c07007042e500c05803c600a0025004403100007001c1155460080d008040c4a00c404c00d03585d690030040e542e1844040d141e50000303413100d9880f46c0c1c00c02002003d640e5207001c02c3c8502004c0d443d94140c044401036103d100c80240300101050032014401c0e42c07402e907007052031490340c2c40d01d4064030f00c0c40188800602d00100c001c0d0301400c8082105058098041424030b4041418a11888200030170103460109143d40d500000312443d4800000c002d40485800c06401500341e00780c00200104915846030001030030a1240e440c1c58000a00d01010091f4141d903284000424402c1031310300341282c4920180c43ca949840041482000c0750 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 784967086 1250 784965836 784965877
    0x60509060706180f110103110c06060103150b042318070f1b200109120206070204020c030408030c0c0415090b0f100201090308090606090103020108041a040809011d0105 74
    0x100d03040b48030143c00754081261304e00100c0b01c0c03511000d062005d04104e40020703d40801c80f00102d4105e022280d85800800040070340d5070302c80004401801d0070080f03140700b02d01d03115000a103401c0c60303501410280842400d00e014203607660940359030000e04040e1407481002c4020b00310200e1044081140d4001d10a4504551002c1608209443c41080d44501c034150301c171540303184010b01400704180c428402c608460404a00da850700115540445402440040c1c41d5508081c40140f401c10020042e81c7c2c400f07040503040c8013600c0701c8030b811034000340e011490b10340002174480c01140c0180300382d45002c902140c00300b00508410a0402c2031000b503019034164950340c0c0020703880795544c0c85007400607180c0040030380294130840d4034024080c0030f90010860205030719002142172450701189291091030040c18102950707103960011200301201a00907201d000c04040b101a074010781c4c901c420b2040380500081c07503850003880c000500e030440241554000c0d00c42504048056a80801241d0303444200c0410803030800c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 784968336 1250 784967086 784967111
    0x1e01020c0a050d030813080a0306150c020f1201110c070f09020408061603020903010906020d1103040f0b0403090906030b07090b0a1e0e0d0f1406010b030c071a0907080106060509060706 81
    0x11b00c80c201800e500008204541441d0345908010103882d44062600030780a40d02e1005c1c3c2e0380c0c02c558503000b0f40c0003070034914407072590801a690500802e410070000c1078610550809a9841d408030f44044000d4128000a02c0001185180400103242a090451801d4600400c8582b6420054001120401c07071640c3c10350218070a80581d10031030340083c020011010203107882802580264644201141040744000072081e240c03003540e20960b003000921482c0409a0340701038005078001c02c11410302108110101761035850b4450400134620804071070203d4102101c02905010031644200c011340020861481801d601c600a0b114201d82d1503141038008980c0101621070482c40d0030b160350400000b0103000c0500c42e40c40003420078103000f00c4801e1000d030810340403191100303403d00035940311050805c080780500100308018896a8042c0204484140380c402588145000c1940c0101c0d00354400042442455002e228210040c5243d00f4241e01c2c01104c1300200340c550044110141c04941e607451030801c1c8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 784969586 1250 784968336 784968361
    0x5091f030b04020d05030a0e100c08070602070615090f05180a14120a0903110a05060f030603100c080402030c01020f0d05280903050c10080a0b0a051e01020c0a050d0308 74
    0x2640e40041900c0d114114144000d048003000c104082c440c00075031089c003102d6030260188011450f00154401d2404900740c482902a6001050840e4034554800c13004411050114108000d084129004101c4403c0c5e07261302000e945000e80403004400303401c54948101d01c40096116440360317001c044152515101d82d5268140701110040c80e07074031000000d4410460364040400c2c404d681c410048080440382060034801240c01d14050315402410410014503010440d41c09180e20080c0101110980f0b400c040c6000c0584000c1c60080700842c2d0301100b4841145010f2140001000c4203100a0246008809180750b68844000a0105012000614100b00d0611201e00b061486804107200301201901800500040b4a880140d0300d501461082840714a010311900c862500700f540c6255558540400c900b0050018103074981c2e002d29000c80c0010682c542c03a00480390f10005584401d280c5003c140060b080040d00b0b01e4240c130a00300444c0a004954030040c40400058061602c424199918032201c000e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 784970836 1250 784969586 784969609
    0x18061b080414030708030408060f09070f0e06011b03091502010b040e03040608100b0a030b030a1704230913020316080102130b0307020a0b0901060f09050105091f030b0402 75
    0x12460005800b088603910b04080e903011081c1601121856655010420381307030b0140c1c1c0202c0c89141c01c41400724622102000005802c403a031941036460003551146c1d00301581145034003030000c83c4121402c10041c0e40c6c228980b90400310901204810050040d40e000f8001071950098440031703ca5201e104030f01c14400d6000312a24403014204002c2014041c50040d601d0b0401c1c40b407100003031a06000550640e00c003001c400200c8401e02070701800c00000070000c3d000750808104094141c0b00e000d0504003c01c481c0034580301d240c40e113028a03d90716404d00102c0014111605074031803515a0580c00702ca500c0e00e444002c1580b000703011103003942c1e40b240c03840000e0408041840f0f00c22160050580071803280b40c10350062611044034440e40408540d550034885c0d081c0011100d0700c0c056008080c01d00d002c645000c3c03090342d101c0b004000018103241c803900c10750b40b040807a800c5041e289940307600510550030035116154200000010783d220250006040310080041da000041903c000c1002107011034035403010501 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 784972086 1250 784970836 784970843
    0xd0308010603023f070203131503110a0e01120e1009020307030203030406080f1501050d0515040906060f091401032004090f03030c05030c071e02060708071218061b 72
    0x1104c80804860005950020160442000000d90302003090140000205e5001418030f03a4247c07021803a10340301440d02c0c01c1e0b605c003510038107131075080c600340b10015403000300380405840e104d40d01c400d129000010a0b082900c8a00743c1d0003458140d81c0e1495100005e600c49920500c5030020650f031b0054070201e0705094960f0b0000f500b43c4004500480c080f078112032400e02c54441c10310750004a41d01c0415032042d418000c289039012a40030003003610408520b401055103d00410400c203071140070f1001107011146004c034240c1d1026070301c44007401900c46498900340140383c00d46083c003400d4651800908001010b21004003006a10081041718080b002141c00307803004024020002d807501d504141d8101c3c4c0000c04201c001914245000c00058001c1d41030720f0080403050764030350503c07a49030303940749103800040000103448005000c80c40050755680d00411070503100349091501d60032185061030f42c01c076a00054100384602c00960308400800c0c0301d103a070b088681b58a0002280c0c030703140d003400710b10410051018 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 784973336 1250 784972086 784972147
    0x91d0c04120506070e030102120f15150c07170304150e04090b04020909060f070c020409080706060314030301180504020402070c09021b1b0d1e050106140d030801060302 74
    0x305002c004a4218800c40040e11000005110f49003010700300e21a0f50080c0d450f1010b801c0108011016030001c05a01600c0340d040a1100664140050041042e1601040c0c0000c030010f05200100e0090185100030a200030001c48100301c400240c41d100d000300c0c005d40500301402815881c90902c501e40181455a01400030020b20010b4182001036a004940590044440d2404110504000510319101c0c08070b10310300c90169200e1513811101c0d00780680d03099074040e44584002c404202d2100090021520400b00050007500c0e500e4901844c82401103030507665003003880100306a1203096801200d40702c03212400240d07a900c0f0b2000070001e014151001d410b8101c8000046203020b0b042d401811150f0740501440c040a02e280c41035a0340d66401130a45410120000c208400307410044d4000300d410344601100000d0003031000c1c003000003100c802401d86950b9158102089003001b80d071206649044103443c07024815102d40c8001c1c10080c410712400d0304041e400030350f00000b244040b400100014101141 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 784974586 1250 784973336 784973369
    0xc04030b13021f17180f0d0e01080f0a02031801020309010f0b06091c140313090b010503011d07030b030d0518061606020c0307062a091d0c04 62
    0x1031a6075408512012806010500c00f001c0001d901c404000c3d2444400c0e40d07a01409400d00d40c8800090794000d4003104103111007162810b080c0700e091010707081070f8030020b005206802005000412074481c1c5c112581c14040c0c503101b8003445021081007150f10030069003002d6581d0b200d914584142c0b0400030788000b841e51001c0f0078011300250640011001101d06401884103c09640801c8514480c2004a17984071640d80c9440ea284104103451808030742c0511078990340d078410403250505680c8060707000c1b00c42200e801400d11684031544202c1038401002c2c0707402425581005140c049420003600d44c096100045000107082c1d51080c1c2143d0314028014090320178104050b50042d00680001d03140070080d420841500d0344909203071042d5003030800b0000d00490aa0010384600000f90b000c0e0342a180c060008000c69004204a40200352030880c6118100046107102d40000703003818100d400310300400c90b0b001c03800c20811142c10340c41500384000180c0190591600000c01d0a02d00c0350742d000c0840070320000361 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 784975836 1250 784974586 784974601
    0x70305070c1710021c0e031911010e0c0105030411030f070f0f12081c060504060b070506130507140111010509010b01080106050702010f0c03030b03070e1f050a0b030c04030b 76
    0x5410b40400b00c1c8412211030f03800c0465100241d01500035280e4070580c1d1121219040b0100d90828602d10034018141c924260741c80c0d080c000f6003207110030114007281c030703801a0740b0085000f4070a03601c0008440025018503441840000d2145c48050001381c460340440011030700c556814000e00117941220703002c441c0bc1aa541c02620000311140c41140c0700d40c0c1054000284010800b1142038051ba844441c81e450140f0010041d80240104010845135982c1d910000c03030103440342c0c454031014004c0d004003503440c0c000f01c4c81c04500d01000105000d803d44e1038903481c0800200c00042c1301c3c1c10303148200017440c0c3d04c0e0301150040711454000046450b185d800c2206103c2100010751040140540aa849284903070b203940742175490344120786000340029060102007210a11078261070750424030a140c01b0440c00a003070300284c500451340e00103c00d01c030a64405d1084880c48810b502c000426400303812401c442c68100001c0d0701d200da91060005980c4000001188c0b03003150000c07070f0003640d40a0007404250401c0345 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 784977086 1250 784975836 784975859
    0xa1d011a090406060e031b0d0602031b0a020a02040c0e0a0302041e1811101d1c0b0a06051e0d050c0d06050105030c0a0b090d080f07150615090902070305070c 69
    0x80f03540d005e0f000701032031501d070b058861f00e10030113100c0003078001400030015aa800d030081d4401080480f408140b0303c88042410240302c01001404e0040e401000c2c4200d003401000100c1d02a0900d072400d002048031141c03000d8550305062001ca9804450014071070b844070380141c060312051810709444601d404030755000c00c0112120916800d0260304403503104d00d09481404001c51806c0716a0000c50850121250300750824050325181c110060b000b410103601d4900d0140c511080082d085a035040002c1c00c10800c9052441400014003084605694a03100e0a181c001c0766280040c5242c0100c1e030000082d0180030b0f08010700c0c15407190107001c10b04241514240040104400c0c09214824004c5009805042ca481240001940c01100d20145440c03030100c2001039031031810400311a81041030006682c206465409046100c2c0202e18481c08003072084e200d80d08a420540142e210042d40315141c4000c180d000c00c40c0030039250100340c016600c0b030b402d04094840b8000c17a80c0003402680091400310f540503c05 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 784978336 1250 784977086 784977107
    0x1202160915060503010e150d02130926090d260301090b030111161a0a0b0f04090b130c09020a030204060e09070219020103140906060a1d011a09040606 66
    0x40408500740d500c8100c03c440354070082c07040c002211051008a449070700904603d019040004006c0010086658080340243c0c9201c40b495100641d10383c500824410302c45141c02c0016a041d42c8030480020691072800c00f80602400203000d0160007410404002600c0301d41c82c00d10001031030362031300d40100140c100c8483c2d100f4055142c0f02424400e034904c1a00301401220106803d01c0959030a1800c402c80311001e07a144143c2c180c4d01216051844042d40c069941813602a17444404046800301d940420321000050500b03110f40910321301200c040109407643c1405070030136049034661003a10343c2414589030824181e00140e8803039100096100c0c040b6010350040c4125a12510b80020100696007001800c030350444164001d80c00070030580441a0842e00103e41c0350f80305040000d4000e9580466841a460846419469038003c00030700074203203490b433040001440c2d00111501441c101c041541c4800b441840343c0500d50303c5d004c02c40e54641840c0750a031084d0603000f410030080c403641c03104000c0501090 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 784979586 1250 784978336 784978361
    0x4080102190f0302040e042405040303021803030909070e060d020406020102030403090b0c0a110d0f0c060206011a120a02040905191803050919030203061807060e090412021609 77
    0x100b8002c1c9224034000d0003a00c040b03503202d111802c0140d03a19240d44141340d5000000c2150301342d140d80701c50020348440c807400740034a009540068544800c0c02d03c9025144600f01c1c4588254403c3c850550196550841c0c290f2201305444d021400d1a540f40126825000786140c0354042400450086100c40c4e0543c041c5204034040d5175182c0b401581c5005aa526116141404007244c00070710745074001c14a9a01705004007400904a0728a4640b5600c3c0c40e82e4689401c0030840303e00d10740f030604200f040d03410001c442c0035024004040101d0340350584500450300c10601c45202da1150040004c3c4404d10b668140c030f004141c1700d0f800f8800c40c07428001181c06001e01030240104103240420001450030700c202203420150703040d02d50301d2805218200300056500606088201d181c203012011006032424000d150140c404c1010340b20341e00c0889910035060075001c0d004138003040600203032040c046e5204481150004d822503043d421440c0b0401c4102c1c14140c0b24403034605010b0722007400059a1045501c130306820900b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 784980836 1250 784979586 784979597
    0x30d050708100311090403090504021303120f021932120f040303030b1201292b1b08030a11060f01170f070e070e19060c080408010219 59
    0x116070240e00b410009501000d040c1d02060300001c0c00a0504222a0b50454080d0602400103170356003001406036401040c03c02145060b40d001001008050201185c01341040e0800007005101e02d200255206000540c01c035204920700c1c031100070f01034030036450302c0b40d804014009501000d0101506c091000c241c00c0790149031141d2920344030740400190549280da542d0245040c0784c01d01d16141100640041500254001844564094584824030405c4121380040b1f00d45001011084030445e516180a52803e01640000ca030303034007110042e0000300d005d0034052040b4240c01d10160034a01c5c2c800105840400070090200d4010400902c00405005030200c41e90701d121803010449100c80d2140c2c0162040e14601c0e200c0d40040c004603144d0954590251070480807500d641c840d000c031052414250b980002c2c80c030782020050040090f4003c0e40f2001d00d59054030020b00a4082e410f1a0560b40c18520070724041204c52407680041040380301c1120003d1044c24000d640b10044603c104e50100207404082c40401c1c4e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 784982086 1250 784980836 784980841
    0x706060510090f0623070f0b0a20031806090c030c180f0702030f13030b13230109020405090607080702070b1e040b0d06030611072004090203030d050708 67
    0x900c12100c54041d03d03008010180303000d24100c000d03034000842c1c0340c04003004c1d104c0c20300c0c1d50003c0386100040d1182c036029020f5400200d0711810054264607000d80a03009141c14200103540007003130070600d04603a50810009a58a0759000c05040140c00f000b03042c0901070041c0c400b03108000c6400542e40d10900f0f4103c0a4910082008080004c1411100940301003083c0c001c000854004e0b5010201d0740c030140600699140c400f2002e1658070503440034180d05402c8115aa0510600c0f05460002d54003501918042c140d101e070984904c2510f84940c0a000c40b45200300c85640d8210f4000c4d04051125517014105208170b0030900c02494554008580c4030002400040000b2085480001d07020119031019102610b03000c2c42d21a01d00201e5130b6040e0010480c0c07020000001d19030440001460104944000011598150300d024019501ca42224056888003444000041055804104100a0584407603132402c4034480100300584030254000c0c2d450301011030b1b009650f800d0740d0081489902d982e910001c055 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 784983336 1250 784982086 784982119
    0xc080c0105010f0914011a1608030702240a111e0d050709030b040b100e0a0b040c11030f0d0e010e0d0206071d0105070c08070b0c210f16050307060605 66
    0x440e42c2c070994945c3d21420300010400e01884140e0a170110071249103542c0341c00000511616000c5180504a03040c1c500001000380b00365040c0010b05424041c0c81c40e006400c0b04151b2004600800600b407440c80c1c036900c40e482504000d40d00110f4803000c0c40c04881e01d1660000740301000c915007048060220860400001503059403040110708241e03580700c004c01d035441e00c4136102d01c0d0340301e030000740302c031400131152031001c11201160103010744038529041d40490104506814041941c4010840e10300b030004a19503600383c1ca502005580303031060700f915050303120804402880c0c0909100302203c0425481d01c2080c0780032482c00b04d0040350580722031302118071540361175004554091186015400800b0313504160402584100020680c450180800d500307080c4d00c1300303012802d060036503000c9010000c0c001000c04815000344a021b03012a26507248450b0300540b50b00c08030151191840c14803201d0800150118070386003140da030548194000045986a403103030700c3c182000308603c3c000c8031700c140581307002074290 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 784984586 1250 784983336 784983341
    0x3120408190b0f070215040609021009080d0309020f1906090e010501050706020a050c1506120f0a0602090a0305031305090604050411060307140706020a140c07030803070c080c0105010f09 82
    0x240c2e80c480c0e01d2403800e40e2203600318556075001900303080c218092900c518080b100546181e82c000d500a040029a4030560301c10072469501401da18428400c00401c10042000040f8140d44a9040b030306000c107289000b840054001d8910340d000030b42c0241000b00e000e04200e181c4002030141c9682e92140d02209071501444014a00e09105a0380040d50800143d0001203440e0050024074810b810401e0802201003105420554500c40c807200120300c90041024500d04041c54080f03880903080606068407646c0c410540301d01d05600050445c1d0340001d6483d0551f1500c2030001300941c0c1180a032500e03140c0c0000180246241403040760310407408000071810b0f41c80e1a1180e80e0140340e001d070814006c0c1d0034210910055400081ca01c100f44010072070740c042101408401040d0301803280000690702c0f10003a4010300703c1a103003e003016000205000c4c0c0b8031840c5001460b00141d035001100c10b074403603843c248200d820041c1644000c1813500c000c0b9002c02c0076001504120305980984070144070f01c0e500c440300c0c4e204 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 784985836 1250 784984586 784984633
    0xe01180915120c120602162f09010e0403170c0705010b010807020c0405060f100305060a060c0c06121104080c03070e06011413092309061003030f020c03120408 70
    0x40d04928030f20410001200c2e0004900151141101605202c0e42c3d842da801c84240700c0f00142da044106001d24510010079002e0300c117050103401d03030003910040440017040101105016150601e000c5901140502d8041c1c03c000e149443c498034000c103241ba006504c035001d500700e080308507025801d140f1600119801070880ca403140100f58000d01410403024100000742002900b015045502d60301c0a00301ca0305c078104403029411040d10301007401e08140c005d10105d20010382c009020000c466054400143c004c8420b04211175a91808400c2c0c0704009020400901c80d40e03903d410175201c0040c00040524000c690500b071154200d09550340d0650314145001181404c850540c001200b020f2011240400e07100a400710101c20001d40f008541c0382c07a41e07002112810b8410070f000310240500e404550800390b4016922001d0031014107101d082c8101e11002d00842400010240b107050804400b030107208001921001c07400408840b0421400e008001c3c041d40300b80074a10701030003140ea0390080200c013001d5014 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 784987086 1250 784985836 784985843
    0x21317030711010507030c020310020901140723032a10110d0908040503060f0f090a03120e16030b0106021603020f121002071b05010201090b04030e0118091512 70
    0x5200b480c07000c00444207a80030a9084003030010f007007903031405030f1030821882a4035034030480016500c80c600400076010325414414002e0130b6008001013000122a2824000340d000c1c1a41d54107202030800c42ea007030460042c4da009101d40c403c081000305540f1381c0d41ca040c070360881956080c0d601210b40c2815480c10f441c40c3c545652000e200401448460440c0d40d4070500d1402d005089803410b003511040041e0070200266102d40d2404031032014002a4603101101981003200d81000340f850349440e0360051b1020344074909208075581d0f1104a40301e8070f001400078040e80f004006806020603240d1410720000c800078051100103200d03404400c2c8030011208030701d0080d00c2d001440141c3d00b846c50070030850494104c55000a8a010310174400c41388103028005044d50921400c8110390003e00901c03500cc10314001d034440f0b411a0304100340c03000402c400180840d00030b5094503003440114103403401650348028001c15125103400c0000300040c4400d9a622060315503031200700308040f0741d41d101400e0b60151003103031024 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 784988336 1250 784987086 784987103
    0x1031208151017090607030b0a0f090f06120506070206090106051f0509060c010f050f2e1d061005030603071e090c0314100b0f0f09040213170307 64
    0x8065440e09862001e02c1100c140380629886081d07141c51044003105407541c0c442944030340c2c1488515901070044403152101942c01c142d40b82c4c80c060441707422540602c10128550b42e10100034800343c50320f42141001d403a09204d11001c0b02a00d1401c03030760381d0104441c0c460050240e030000c00c0082d076041c00342008440c0010b0040d8104100c10301d18000e003070340300804c100174043d003000103501d591030f24400b4007001c41c2c80c50000140c0d140500c800c4825a940100004420002c4be020444030026000d0b10110b0300000c2c04102c6001451840072900c403001c1a0012921800030700c0404000507001d021041c80b8000070b554031a070180030308105490720301051320b00d20b034940c100381401e00544001c00c182405030306580d50307141d280720381d500550421100d016070301400098031072404884002da807060300c035082030703005c440d004078a4500031824030107024591403601c01a5001440704c0b46000103609445079004014002c66603102075035079aa2012005100c1c4842d454000c50725031406200100a0345d81d9a034028044 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 784989586 1250 784988336 784988371
    0x6070206090619020f010f0507050715090b191d03160f0b01090e0609060108031c0f0e0a050d02011406040905100c120e03040320010c080f0301031208 66
    0x3041a00d03040300450303541001083c0103081c210300c144a0303c0301424007507801400b5078010554406081d40d05861f031584140307041c401889481907000b02200d5121350001c6043c001c0c12201d1281e00d002d440401009403494080b603083c4514918492040740c2c00d11100c010070041007501d89445841004503841800e841d400c2402001003003501c40c1a1014441d01c40c018035403a155403070b511001e180d0380a130080007000d0350fa8010b00310b04210800405030410641c2008103520761425a0540e928407076a40b8058418041103520a81d0790010b400034081c82203514404d00c50070044407006983d84010f20400d41e1503105044400c01c04c0c41c010710034000d8800343d412400a455503a0018070004c0c10302044204c80c1c51040140101c0007003520b100303141e1b82006995565030007460400200058a0141da100c1c1c0301a0010081040001d100260090407010b640700305a0242803403c00503039582205d0701d006003c900e030000310103605e5044040154140c901c241144220000c103800110740f100c004450000b03000303405800 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 784990836 1250 784989586 784989589
    0x4060807080318031005090109030e0d2301020c0105090a0515100308030403090503010f0c0e06131e0f300503030f06040b0607030206160c030207090c020316080324060702 75
    0x400b038942d00c1000d02120f00c1045e841c000a800c039201100d110107565503400c088401c15500940d8006943c10448001160b002c040c1c542c100b810301c0000280544800b1400c0f00d8230006401c1d01070311843e0300c4504c000c0040d407402c44040b0741c6404003001c084a19010341516410541da150118a00504924200c000c213030341550748008035613101901c144d040c00325020f400511981c1c01d01540348602940000481c110002c00d20140150b1008820144500720600c41c2e025800c401c1c0c50034900300c42c56082c0c805401140490300022010482d001105108a120404500c0b094044805040040c4520505010048554000c040c03444207103802040380d003080001c01c2110030341d103e034290440002440000e000340100001941c95000c0c0e10110302613004042040100d646284224076004500c0c2042c44564106030b80082d1549054041c130301c10f9a0f81d030300c819242c1c94400c2040d03901d00c00d107d501c00340d41503665042c07118440d002201c40000300300390407000c004181710400319000c8151014100c6070500e00d50b6070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 784992086 1250 784990836 784990867
    0x40e010e01180c09110a030b06120103110f061e0d152d03020f0103050403121a0102010b120d0f0903050d09091d060c25031e0c030801050f120d0e040608070803 70
    0x941180d109d00c080c4031104403110f414985900030351017840001040f41d08801840542c0c1c070034900e65449514140132602c403018201c0384c01c083c14904100180c0ea01e200b0880c4e002d0080800f400801000c081810020401c02604000411704419441c244030b8051084007456220783c0c10350000a400440200c10380d0b515500a07000076030020b101e8145818054480d40c03241d0f04907041c4801710000e910019000c000f03256028820358007042025100714124240a004840c0e5030411020444c1c00c03c82d03182901d030b0200c2d1203a2100009194040142c80a130034201c1702c01045201180030700081280f81483d06104044048201825918030401411141e031b168481c6000541140b100150300f0700500000d284440b4201400002d0a40300f901c2e1024440a4074184030032141144641c80e060000079010360002c01d81100080341116421180202824031010101d50340200c4107044c0e002a00c15040680d6041e5080003d89118103003e480c00c001c450380e50f070445035580c0200e101d620940c0d002000081440001381 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 784993336 1250 784992086 784992101
    0x9060c0f1d01051c18030201022d1603050f0c0a060c23030702121b0d090e010e060111060403030e0f1b101407110f1806040e010e01180c09110a03 64
    0x25400141c10340b1034803007000305c0110440c0b0441c0142d50004641e4000300890410211000c0c1042103611680c1030580090300034810030080300308072110803c038901010700c150116034201901110064039115000c00d02039650284600c101c42c954103110100d0700d07140c4a04174202c00300720702444090001c01a46400002a40060b104030b04600400c0302c40420051240c0c001c080200c14581c1c400c52041030302803d075040500b0f0100c52070421100b8013080007619400000390781901c1880349801c00c079464690041e1200208620f100c035050046008010a060701544003c0b02160b2003002d0b07611003090f4810b026200c1203200c007650100f1210360603510140c1003004501c45000204d040407030002d020106204016002a881201c500c003024884d1507450500840b40d52414009a1310400340c6a900045c1120200c2d0080005014a40d20301a0503644a13003500041a1200344c00c0080003283c071085943c04170742e51141c0301540c49100742d9170f0020b0308052520822034000d48490b1b80c02d0502d128900d0031405800c08 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 784994586 1250 784993336 784993387
    0x309050c2107061106090a0804090203070203120c070b0f190b0d081306030e0a210c1403070b130308010e041b240206010305030409090609060c0f1d0105 67
    0x5120010402590800050b805800716444548403408411080e514000000703151604039000045000d0000d0212815581981c0e0328010158aa03518402c00b00c0c95801584902d028408442c024003120301c902900420103180a150000420380c0d40d1b1b0294200700400f901c203100c2412020326200040c50031a4016496084000c0502d03040c49a59240c034900c03500024070030394108035803040810082d070b054499a40d500088074003034115805140c40344611007120111441c03030001d07240c40380d12803180304800010340c15a0140c01c00c8200042e802c0d600d0359940011100303c0c2c25400810205004410114400291a5050342d40c100035038201005685034042c054001c94504200649000f131820401101c04040c0c034044c0030003040f140c0303c0703620160704440c0c0c4e40c4400300f550810f0300188049180801202e0556050b000d02060f191654035201e802800e59600c040d0409142046054031281d2003901d4001e0321020b60344403001c190321802c0c4050485a0342d113801d801705d001000b22914000403807018800b41c400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 784995836 1250 784994586 784994629
    0x260f1b07210c05060703020c18010303230d06030605010527040f02031c1805041b11030405060309010203100506180f0a12050a061104060c1511070b10060309050c 71
    0x20f0350004a03013542c002d00002c4015801c0001c40100d14101641c0b140c0211100300040d00b029403443d2030160003000400310542c1031911614503503542000002c100c400300b814000c810000d1039a241007000c0107040070300410384503040d11405500d48103800c10f03c10004180740c906d0b02620f030303c4035520b401651005900c12a010300480f000c001a1210510030b98504114030b0f03d892100b1b088108001d003285071540c0006220703c0ca840841d411441c94110851494861414844105101e1005480c55801241e0040794406400820002420030640182d402600203441803055603071a24208422402412203c1ca0985030100d001811841d1924130710101e042e01030103000c0c41e641c41d07220340c9084d55804102a2040c0d030004c00b02404011991041402d141040c00d00d0900b003a041190050180c0000d00340500920030405070f11b407145055a024118840e40c2d442d400d81c1c0d408852900e100b5882085a15250188000703000080d20343c006e0141103182c03075203d0040e19498a066040054107000c503202c1c0310b5605c5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 784997086 1250 784995836 784995839
    0x120e240315121507140a030b060c0708011a0d02150a0c141c0f090b030901060801050f090f0d0c0305180325090e0604260f1b07210c 58
    0xc44511106282c03510101c064184401210a2207142060182207001003003419541441d54611903801d8503c000801d00d00411b030b000c0b24500286040c0503c07001c41c4154091a080051030100c154061249149864218000051344800304101c1c3e400c14400a03400100c84500e11280351074090042c092030140e070030040700700c818944440d054142e02c2c40c40741e00e2940c400d030800364400c104405811700c564858603000f180c080104500510a654510a00c0c80001d004404900303c02c0c001e40041d005000e10070000c00807490700b000b004035581410f072680d4410780a010000308403d4804a40155400c1c1c0b161a18111000c4941d403c9802e0b9029080124413200e40e1006000709a80500810020343c03407004500310a20040b0180c0741c0c0c0c840b0b240d4000041e0a19041034218030840204545070b2050308484910148800200d03280140f144000c00191102d02c0007856109544d078400160021050384c844801c000c100c4891301c26504c461074002c00d0f01d41c042143e0154001080480d0b9030f88640c0c8111100103ca5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 784998336 1250 784997086 784997089
    0x308090703050a0b010305150c04180f05070f080702010207030e0d060e011a0114070b010603090516030b010f0e060915131103061002061b070c12120e240315 69
    0xd00c40c0781d0111504d1828600410502c4010400240c1422208210f5091414840300007074041c8100d11030488405ca0044840100d42201c0c0d12010030180722110134800c5151081d0003c2c01c140d018681c90001c2550748012503101881442503400e01070b456101d845000221000f044000d0418580c1160550744500c01100049000c0c05a00400f14440c42d8a009448040f0009022464500d5641081140510080c40030403210314441c1d04544050400080c00a50307800c100b07080c9106020342c01c00d42100c000001007003010042087d41210400c034880700380c15403030b03202100c1c1e505010b84e441c9a00c1864000420340c410034007080b00c54590001011100554080b503010300c1590024081340003805400f1081240604000d8000c100da02c0b050b10180141d171a148003441040101c103885840d4080010840d4410042e0340b1200170041c190f116aa0024503915140030315003604000240000100701d0048030805082070404425050300c0184c0103086403a01c1c491014440d04010081c0c0320700f1916080e00c0072035 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 784999586 1250 784998336 784998343
    0x30923030318040b10091a040e070804020103180506060111010e011104030c060c0b0103030e0f0406180f0b03072306130f06052b0e0105070c1a0601050304030809070305 74
    0x1282e01c1418206103440b4480b041200316030600f10154041d1a9100154906580c4442050156030228004035000d21807100c0304541402036400c90070b412000c01c401d10061581050000b4440c502c00d03a418460f408200031104101c0040ca0300c01816581b240f8041030b2150b014000c0483c10310709410001a5810440c035000e420b580000022582446000905200380110030482e04003407c030760705089625800d1507860701c419000501c0042c0411954141e000d896503900540d41802e40002041403207119103415220350003400e00001c070743d4002d1500e20502c1c156003c6024101c4030200040107048968038204a072034040840101901c441032520705030607010383c0d40b00082c001c402d10020900961a09014000c841c1091503040b140512606001e441003c0c005800c0119401c50407500b500590b54000d07500790080c04007002c5510555081401308129580d00454604209000703a0400d1028284140003585003d026240540010800c000042c04a40584000c41d00482c0840440d4400e650b2070711420b04 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 785000836 1250 784999586 784999597
    0x20c09071709010501030c2304060308030708150105180607050a030206190b0f010f020114040b090c01110309010e0102120a0207090c020c0a0e060f15120903070309230303 75
    0x1042030000c0c010086900c0086060303000b41928003c0250354155100c515200d1854840c001024041007604106110100c030791540ca500080c0040c03045603140c3c81c004505400445001b0000741d07410740001c080183c0b00d2403aa08015040c2c440300e24101c0700c4401c0900c6500c500b410590482ea041204000040c420081420590b0095000d0700050920b517500000c1d41c0101003124071114106040000130355561050311400902c04d08000300200d44041c016400350040e66040641940c5c0d950401041c454100003a5200790b000c80b091f680011602d00065858402c01e240552041d4010b00503046554014101034407041014012100c21603100f401c400c406a1002540c980160001c2c88100082100741c0960043c01c1e40b24005403504c00b4141b80810b84da6004c900c9622480c228603070105101d9200c04088182004014041014291080c0c600401d5540003189054061492270002201202e010091390300e12607050741c3d05108980f420700135940941c5410900c81d80305a01010008055800300018030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 785002086 1250 785000836 785000851
    0x30702211204110f03100e1606022d0609071a0a02060f040507030c03030f091a1c0f020412020f0109031a0a0b040207121416031b0f05150604150312020c09 68
    0x222502e00d0098241230505904843c407560010340030520040da00411030811104030030b45090104510010700100003445050380e04e0442c0648000d00c141c00e60042095000d40b841c0304088034200d0b031008031005a61154602c0782c00160030910101c0e80100c1016034068015004004070f4a40d40d450381c48641502620303600840200d010421400f11150b08860f00c0b00040c0700c00c0512402d4003805400c5078106100392101903006000e1244240204001e90307010154143c4010421500d4948500c2c500110034034854003130340310b00c031446400c06280d84070301e4404080d698480f041e40761081c034600c028200f1800280406c095540c44c0c0c03904c05440d0300c49102420099004811a50001d541124040e0004418800c803e1441104011010f11b0006140c001c00302c1540c10300c4d128000d682a071000000b5403400c038900820714210100410180040001e00261411204013040041d8481c7c4041100300c464a110752003241030301c44000c002195000c413070090840740c5401515a9500e0040004030300c0b6078229541c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 785003336 1250 785002086 785002091
    0x6020711010206012c130c121a01050f040c17070c051c0509060717030f0a0f0603050d050d090b0406140a0218010c030e04060801150b0f0d1808030702211204110f0310 73
    0x5105202c5027014610a03170952443c6040b03154104400718080f45442011980a80d469480f82e0517458400c0203403190820000c0071030440741c104004010444c1017250400e6840d4070852140340b1009400000041500b0b0081d201ca51400e0007943c2802055045454160f4520345124210f40043c03583e00011031040c560b161508600c0d10304074400d074080b01c424181c0d804425152000501c001080062040200603403800e2658130340c0c500342c540d9800380028a000510b0900c00e98240000c20480303821903085418582c50765038003030b603c41030b080040b805000d02c1c16138804c0c43d10708000d00390f500603c1c40c0001c15001e454446500800c0f240494159012980b2402c1e0341da646522200e080c1e00e18526a0002d080110380c0c551410300c0c0350200f8152030081c0e1103840c21842d600c1820317058280000c108a180207138440c0202e512850800c801035207482a0001401d065205c40703104d200c944c4030f1001140c07180b6000500704c8007a1b8840b0703112015002c08403030409400142c01c0f605200c3e90790f010885680c29810f0702801 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 785004586 1250 785003336 785003369
    0x1011070b12160f020a080f090a0801020306030d0f08010e1b0c07060f031503080a02030714030c0d110318030709020d0605040b010306051305040201030906020711010206012c130c 78
    0x1007a0700391414000582c20420511a544003450b0f005c944900341c80e0300036280584403c481c00300b0342128030540c40c80b154415120030300082c0c8064107401542c4141d20032810340e100080b500809542212100c11204001115200140f211000300345005801c40302c20012411103992500c0080015403061018030b04a034415001044980e9204049580f00d22040ca41400150304d00703070304055072100303900000301480e9001c0f8800300c0340e40c42041991a0700750050a21080078003464419500c82c0d011500010039401186045d00d8854000c00c4130261a525143c01185408141d00d40c2090344c40d41207940f6039150141c1e250008200c00d2500183c110910040400101c05240c08200401c941580d1803450605041c20405c01c81d80c1c1da090240c01803990702c100b001c034042d903540c80120014108444020722480c40401d0780400c0c85600200ca03e03942c04280c084490598030380c003400c030480d1500300c40e200c110000f03401e48050b0264044207944e0030102400b4400042902d6640f038161404840d00040c210075581401c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 785005836 1250 785004586 785004601
    0x201020717030f09011b03091403030705070b09030415050a090f080f071211280e0403020105090a050c0f03030903031b06070e03070303031122060e0f1011070b12 71
    0x2449803c44c42c10002084034000f10811030700001c00755404030052503a00c41510003440410600c07180365502010940e03550b4506500f0290894101107000c7d80c50004140024094500000841303054070412141c0d40415000410101c070399601114111042264134800005e003842e5441c1e140c4040c1000300042e0030b980c0b180c1c80003a482d0000d90351015501140081d09040804c403845001404d20205480f000f0000303941a0081d800c00c52110845081000c840b200092900201c408a0b4011032003640244015100c3e5100d00b0380d10160040080e11680141e50010b0180ca0302c4481201503c00c060152804c1c10004000a410350704015207140a0044618110003054010700c212a400240c60030420b45021560002c40c0c0c1d41c05e400c0c00700034145559000d080c91040c514000b40d0b185810300795a0b1501c040e030005100f01640c0010b120b0480031a01d08501e03d842441c0414441420740d41c0580220034006100c517040741d420a003146124030500400798007145501009000b040c1210920315002000d080c1101c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 785007086 1250 785005836 785005861
    0x308091207061e0212030f27010c080a02120f151305010303090519150c12020a0326060f191d0f010b16051204080114060a0503031603020102071703 65
    0x90f180045400c044419081c0e40911800d994100e40001240511b0340d4515102402d514040140141c04042d1450405a2030205400501941245a461504503101d402c2000180e00a1400e2550b00c0b9811200103405c032041160302d01d40c00310001d000002800003101c045a81e000042490b4010315440b24014414140c000705c182d0003c0c00c06840c2d0800721520303603d4004411034103000c0c2e4400c246800001000c002d01c524003200d1305542100b032144000d100543c004e951640001d80441c0401c51040c4080d49400140b01081d011000c00341c8105840e54441c400c01c50001c0e8000c00c81a4020301e0711004440d40840030401101811441484150a159403c0650003103000108610b030002905001800400a80b10543c0c405030150718030740260003001e1400138100301000c3c40003042440c01040004000905400c86031307402041c02c00c2c0d207440740c0b500c00a20201d4111401950340543c4100402030b81c9545419105206a01910005040c0900c3c1d558040310000c40307508104820340c000c01404040750400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 785008336 1250 785007086 785007137
    0xa0c1416020a0b090607060207021f0203030a0f050106020a03080c0d0504230c0105090f0a09150504110c060708190507030b1201050124120609020c071202060301030809120706 77
    0x103210380e003000c0341300001810720721401e00020300d00394000c5508011034070b480c400081070301050601603140f808001e00081d600c0d001294101c140c20309146940003080102d214444c103841d2168080c01c145400c0e43c03800c0d04c0c1614060460614a8820413542c12012458417411707000703d2050308180d0420080c2071009c0e20200f500e2420110300e80055680f44241d07a0042c0480e815404151526081d241c0c400000684071413030707035103c119034601b400080c1e03030040d0441031100c1c103594040364104280300b503440911850303024010b004052a88240049084107000b5185181c1c010100180007c114200c5075102042d00c0c0141d4001c00400c0e186e2088002d82d00d4003001450f4502c1001f4000c00440d89094089000c4006800c90143d619805c1408400d015100c0d018800381b4190a68090006990329120f070402540010344d0005a800750340d0001c0b0320003082d110107d0200e50003c14040c1181d00b191641d4002c0d5110104c8e8a5100d01016844040c2460900c03080004044607210040d900c40461b4040005e642359 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 785009586 1250 785008336 785008349
    0x50a08030a020d08130b0403020f150709080604080f0c0a06111201050619050d0e070e040c050108041a150316180603020a140415120614010e0a0c1416020a 68
    0x450104617800040c14821080d017904070040203100d841e035080980c1031000343c030800300d081d001b0710071000f4042420580b8140610615998a2032141e920100b107a103031f100a0f40c0c003d0201c0340c10049581c5180104010b02a141001002d80b42d12101c142c1e201030460700c420900d038051a00c0800c03d6840345c0b4400d61124014041990031925010015a1041c0410341140b091028804041045211420b00d070f031101c4a54050380049500d09a11a542c054017401d0480d81203070000c2109101050952142c1c244074011907012110081c031241d20300c1014403d00000b0a00d2018003120031500545d66020044042180d124452030901d86013414840d2105140c101401840b2505260301000180c07150200b00301252441503209040c89014000035015040700c0c000d01c0c0401c2500d072404200c3d032201e030740e085124500c11381081240110603e540b615040003489101d01a140784400100a13150700e820444040d00945000190303e21402a1803185400003c610034003c101d010140d011420443c00701c0c00503050 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 785010836 1250 785009586 785009597
    0x50711161a0a02100c030b04020c21120f041a0c0d0c09210602040e07020f0d020105040201140705150907061103041511010213120317040302060106030e0304050a08030a020d 76
    0x56800c00a1358403071001c0c030584162541c0b06440724050384a58460245000010700a55903070946416195a0b45001c103225001a1000425600c002c40f18070101c90b1070425200c0408601c0c0d8411022600ca628024016101408148006002c0c2c040c00241c183c46800c004171242d450707040c214002c404840c000c00c415410704c070302c00500344800c2c40802c420340c000c807561445181c1070090628248010780580e51200010b8000081804120b64000ca040706a103031052040750f010114181e001c03402d840050f200a40810f907076000040c00680308000900314503024500701c480649445090000103c401c035901d0465800485043c00820b81c06070300c008403c00350000440c1081e09208011414607a209500c1c002d010542134425030105080d010b81e03243c00301c0858a0041c5980d2200b07820203000c0341103801c5000131a4001003555009440c500c02d4011074040d40104200e070f0070288240d004001c0482807081510040c0000502c5070740354500600509404009107444114035076019141c080c601008004ac0807 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 785012086 1250 785010836 785010847
    0x304060b0d031d04110703020309090a150909060e0d0306060e06041404090203150a0204062006012102190801150806060103150905070804110d0203030d050711161a 72
    0xd51000440c2e040704683c40c1510004402a80010000d01c003450f40d0358441d18001c201d1400781500803000c0c000e040030545a89119a0303441040008440140e0f248184281490200b03100074034460b441108014481d84001402a07110040d06103040d07031281010000039114842840b64a40c009004401c0201c02e4840310f0405040145018118021900c01801a680c072001d00c410740d6004c0103070280c080078000c860b24060800c0e5030f8000183d4010b00684000c0f0f044855413040b00c014001e07000e0849112807001e080d01381d00f000c0852000e042d00003081d40c44005170700704900150340c650744804280512051550402841c113443c0c10709550422142c107803ca20b901408000701c079000705550750b014000f46000184014404070b01e0340f00d039129800c0203424a2402e010090f03078940000a141c01385001d1042c455070703840e501003000450322031000000c1d0035800031300007075800385002c0d000030341c000001c3e0a04035440308414420a20b0004421203810709443c640c40d0400c200c004041441c1c180c807540b80903040c5080c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 785013336 1250 785012086 785012093
    0x50909011b031812170a1a01260c0c010212010806070e0d2a090f140105030709051b03090a0311120301050d03111f1b1707091a0304060b0d 61
    0x2440c1044041c20080030700601420f050f101720105800c040f900c01e813000d014140650550000c10a1202c01302c2c0000101c0200c1001e503018000d402e0864600e030000c0c01c48480540e0b50700f84580c0e0041c201424044e410301500326110001e0020b06280304800614403070360341c54801842d1519002600c0d42042c480ca412002005880305083c100449800c01d0100603c0202d842d00030425620980140801c00d030201d4001c031350b1315500d030080c4008203040001400101031808012030440020711034260f041e4041841006004d02c540c0010754086014240100140c0b80c0b00c40d1215a035100700d0362052250000c42d030200806401040001c0d101c2c40c60001887c60100307174211008148410f0040f18030800b004041c1d032041500c50407028600070408000c2e9060310710307600540171507480b04285c1e03880480d0070850315103414200b41450307855000180e540c48a00c0b900c1c4404d0208070800181c42c0d041000769400d0045944054400b01e030200145050b1451b6503842d080c1486800c42c8c444c0f10b84544204c0a540020011 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 785014586 1250 785013336 785013371
    0xd15020901021006030206040b160606090905061b041202010507050105091e010207120c02040f1d12032208070503030103031d091e071b0b090105070504180213050909011b03 76
    0x5a03001270400582d2891201c075001684505180020b18907030410601203241c849940110000c4c07807090040310400c1d103502c58624640112954508407240003480304001d80801c850003010f01e140107050603407624840f03031541400e6034030072204440c15a0200303269500b40b480c0d40c81039005000e00040214208a113664450140c5040510b04604000e00305403040706560300c590207034001d001181000c210748601d00100c0501c94418245c4031519004002201d02c1c180c2c02c00c03048900c04c0002c1445450500ca44840110300400c1c40441038a110300c007131100f540051010801980614001d0301c60307641c2c00103104440001802c813100604c0c0200038000500c2501d02c404040d080c140203004888080f107544c0d03440119203000c850f07902c44090848401e00c03502403200707803030800b802000035400a000641d03900720305030381a1069104680c0c5130800c0081c0c0f41d4098a0310303406403880e156000f506000c01d030754a400060088d0003d03909101140d5540c0c60100c04100c0c0f0781442071082e210f5007014007020300e03044013407070702d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 785015836 1250 785014586 785014589
    0x90b1207020d1b20030a061b020c0901120302160e0103051207030804031d04110304020a090908070f1505090309010e0f060702040b04020702060a172a090d1502090102100603020604 79
    0x1013004e80300c0e0550404000c1010120f440c001c0074041350f0a0035214100100035010702c880c228042640c441071140101c0c40400c3e07411080101a0800c6510b91908105140c2030280c040244d046000c0c00001070b40501200502c03400402c03691450080550540c18010f061410000c010706d107030a13081061800090300062fa007644103405007004904040304c0032610b081040c407240380702ea00614159040041c8542000914001e0f0f00941c0c541c49020740301e420042c1202d01080d405040800c09110b43d05c00640440242c0c05520f1096000700601c21a1500c504140e54040e44c000d203003a000443c0180d0607580c0182010402d2008480d001907102c4000081103a17031003129406030003039444510003030050f102d5130100d03600c403540500f200c2d580322141d039001000c0c0320700c0170005060780c048038000c1505522440c0324040c000300c0310f41ca846e880034184010892558488080250400c5c41a0341e03d8000c6002181c2a003412003c0000240e5180281c0c0e000a040c030400039a004041d40c5400010320241c1c07030f018103450 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 785017086 1250 785015836 785015843
    0x90308070509120f032101030f080a05041509031a01060807030b040204080d05030912030c0a030c02250f1a07120c080c070e0106030b1807090b1207020d1b 68
    0x595610100c4045000303c0d4401c40958450b2013440006040c04500100918240d10307842010f075070140c8601002c6805030b5007880b004d4a40c40c0c0c02465000807030905801000266100d0402c9803270140d444071840301490410301250f0108000d804104140503001401000b003c0c5402c0f0103002d01d40c10054040c08140000d4101c604155448014443c56140c45d41218080e0043e00c0441d084e41509030001041d561080320340001030700450094100c0b0b0340c10f28007546e0140d1070065900d410700040f203804400800800c03000004520a0a109074a40d454000c910065012081c2c0103d00c10780c2402c0c107145a60340c0b654450070184080d01900340303c44070002c081e246036950100c103075030301643c4401044841700a035541c003034030140000580e0311855200003106012118160b50150640ea62030700309a04039420f801c00d864002d80b11084010001c0300b0302c4d59543e07200000307003403052a060301ca03050300043d41c000d01c407600403c2c80c0c4442030101c0e0607010050044c0074a084d2031700c0000e1007140c0303c02018035002c1c460000c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 785018336 1250 785017086 785017097
    0x90f0e032a01090b01080102070c051203030601030203100308071b06090503100e030c070920040b191b03020609150c0f0f07060f1b0e10050c100510150309030807 71
    0x50001c15000e402140c8003e4025008001950712564002d000313520a20301280c5807541d8190018141c14010742c3d5034003040440c809103085659650041d0041c0d03100824104541403162400300c0000c0800020301f000d00c1c0102c80e000000101c6240c0034900e0318940c0c00c1f00d010301c12440800c000903940001c0030354940c100c40e040415241080c0c0c66007455401809901e02c5240242d1030085501d1026601200d030580c110502008114038801c900c41645c071460280c0c644c141c0701040460b8240441d070380b01c485c1400c504e140440c4d41008111007180c00c0e941403030080340180c01400600001100821030080014040c00d0107003220308096050307025622403813940c07155260002c20350f0354550042e902982c3c44a81c10076010300224611000e600c1c01880c3c0044e541514880c6440305140c2c0a11070440111591005801d090f024102c0703401c25141c1380c011700414400c4d0b00c500514040110014002c250142a04a514800ca00d003424580110084160400d00c00c0524000041c1d001c41c0c2e00502c060342080380c40c20b10 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 785019586 1250 785018336 785018407
    0xd270611030702040c080910020313030c1109011701232703040e0405150c09150403080403110a0b0a0804020d02031912030b063a06090f0e03 62
    0xd050460198050195000d450229109645500015818883e50350082981d0007078801903604003c81c042540c0380481001d03201c4d40d19001a014050186155002d40101044120314000181810a098204550781c120382e4084e2001140d003401001d0940c0e01d50b004502c200b0980f4880720f031615600401003200d1104900110184800102482c4c03a1401c0f0b95003941d56490b00e49048074121481964121040d22442388040042c51100700b03401d00034031194a00610f41070089003000840001011031950350b41d0208000400a21148000d000461150292a001106940421108240b55030200b5100e84080051030211a48910200d500690403500c3d14902d02850002c03916050590301d081e60003000000e059000d008142103000c20001c95650709205000e904018031000340120344600315524000031040f0244540469075505582c03450300d9500d070050701da203880801d5030020f0703000384030041d41c62410401904440c0940d020f21079174100203510780304030002c2d840c05c080d40c0180c100300960004100c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 785020836 1250 785019586 785019617
    0x60206011d100938090a0c03060806040f060b0a0623070803090f010b03030f1801030b130516050301050d060903021009030207140102071a03090c0a06020d2706 70
    0x701e50000d00034002040014040313184804903950074444a800c1d440c14003150702c40c2440031400d0100000035003d001d0f0b03002601c4552400000c2e100c4600e2600a154480c80c011452030400c11490388142c1c05072401e8054142c0d64108041110740360450240240d5940c4002e011090300032620b1103a000700030100e03101108406d804e0400d540606103004066550000034840d0401c0002200d04d01100040020880a55640c0405a8134425854070400c10001807000c403070654090900030103030000605000c51106056400141e026052000e14410315a80d4401c1c00b20081201209420f24991420710074910b50411000421512041c50300506c0e6075100d03020070301094424004902d007402c156100f80030390480c80c60301a40311201c81c050071140100c0c9a803c4503a640c8001610710449003110580d00c400c4600ea403643d0031550000300440c00030711581c40c02031025102e0a0020700103003003a0f80a01001068007500414003448890500103ca100743e40303542c0001c01507503d802c1100c0c09400d2800b4840000700703 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 785022086 1250 785020836 785020861
    0x70e1806010311240d0f0e0c091b0705070e22080723011a0f060412050c19090c020a03020d18091103060102100e07030206030613050106020c030106060206011d 70
    0x40840d11000c0124010000350390102e000d05400f0b000603900f80000746186c443c01c3e040340c160701081c1119034480c0c010324070a030504c54040f50700000203c841240340300c24960041b03410f6015600848042d8005c1408000658a1200e21a044905048002804032402c50020540303640200040c00700d1000041c038500f0407044981c020100800580050401800c143c08a4020045200300c0c41c0440392034200c4000710b10341070740d60b840300440c020005400c00d402c202c0641e038040f901d500101e406110740c10703100c02c4680d1412241014501842400c200300b41c1058242d1040d02d215a03543c0065600c4440740c1e40000b0b4000c50302020f4182c007460203001811552505040305c003400e40c84080d400b450b06180384200270000b80154030486007030b0200d844490b402c80c030103c00c4800702c3c2e800c3c00e00c91b08070360307020b0006140000041d600990001d206510070f140f154240004c0300c03000e90200c40540d001c030030250b40c541820b020380f600030026030000d007846614005820082c003034502c3d5000604550500080c072203410382c8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 785023336 1250 785022086 785022109
    0x20607050c1501031407120f060e0312040b07110309030a08090a09060312092705070309061401030c0b120609070c050708030a08010906140d050f0a05070e1806010311 73
    0x500b0b207a50b10f5696410320b07070519000c0b81d074456624001c00c040464041505030882e8086a80002004a81510b81d11b07400c0042095240d0100300f400104107052600070491665802207024a600c0491811709220141059540c90000c801035041030101c142c0982c1c001c21003645c196000700460380c0d1844540002070100f5107a07080400d1003490700e0000b00510640e003260000303520103501d440e200540c45500c2d00040e400c7e0101921421a40d689901c02d010314150441e640044075420003117042c0400d030b942c003401c0e949900701401d0030030035040c010028032001071030280062514070b0046181c40d030200b03074465a10000900060090303c410011803500391046a0411540f074000003692846a01d40004275240c0c0d11078110131001904c00702c004100c480e060301c900c50441c0c0000d120b4000d10340101052040320342007000103a6041c0944500421032250502c40004405d100f07401170074480c1d0400c454a6480311010b00000089422612288180711000520a040d2a0054448207000810b040045c6201180 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 785024586 1250 785023336 785023363
    0x1b061810150810020705010c0504050307120510111c050601200c27010b0f091306030b0705120a0501030c0e0414120a0e0301141b0d061d09010c020607050c 68
    0x900108242d83c2603ea4041c10f5a24407500c001c1c401c444101008a4007070180b40150396040e04600c5041042400050170f0070040ca02c5081910340c0e00c02031100c80e404942d100e2181c104003440010b0300700425000907007201303901d034800481002a824010002000400e40b440b094440b1000d260010096010401c502a660000200740ca400031440d0500c54000403100d0444c015030b58008130020400b00300307000a840c010a599001c2c5400e0a02000800c01c0c4202e0048207404010b0b516034010010440b1055031601c1500c50341c072003c0da20003100c80c21702076515009041241407880c4c04010302c0010045135180c011038284980c206026100c500b003000700d180200d0800621071040303500d2215480c02c038401400d5a0030035500c03101442d08100c1c0916080e61110404501c03450101d500245408240d211546c28401c1165441c0341808090141d420407129036800130007104c408400355038100346402240c160300643c018020301c608040c100c1c011b595860050031020911002080c09440704800700092450201d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 785025836 1250 785024586 785024593
    0x507020705011b24180b060307090204080319020f030301060804021c030215070909050c0405090c04030b06010f11011a10140f0a030e031b0618101508 66
    0x4000501964601440c4550307070100b0b5501c44540d001e5040c070201890000d4000424402c40c0d02c0705060102c0c050403800c00c004402d80c0e10b5040760303405c04045c2901c1044a04c20010f40b082d030304129080601d00801584005245070042106005048012003940d19070b19010001d050111001c440581c1403100103e41290f052002000004c1c600d03030b0203200d007409103000381d4070b004054140303006001c50f8203a03109018026910540115124800101c50580d21084903c0c01e43d00258543d140c10083d00d00030344440d103200201050500561a000781e425801001c403800c02c03441c16107596100c0800300c10040440341401340884070000401c4c0207481c00c00f007908a850081107a031820003c0d200070000131455480c0114482000c3e5051103004840b81c1d05401ca44400d52401c0c84613903641400e4a038007840d241e0041603202c901c0240c2c9020704001810b00c4900504444081c00c1c0c140c040a464404018848036403450706810030300041c00007180c044a0314802c55004070307071100418003000c101c0103030303034031003041c034070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 785027086 1250 785025836 785025841
    0x30e0904050319030203070c0b040809180a0e0f070b0a05040308030f07020f010608150402310b190b03040f0b07030e0f0607050901051b010606030f0b0306011410020a0605 75
    0x780070004120050300030342c00090464000780120203d0100304c503003070080f942883c160000f05594001c0700f94494443c21840c0e140003071030b0300071905080100b01d418402103417440902c40d802150f0700444002e100200c0c0104130035050406140c0c0d5843d000c0c442d615050100040041401c1d10401c2113034085c641180c4803035520b05080c202031120003c22200100140180051690040418080d460480d24141c000302154450004012000540038104983c048603d60303002264401084208170b00c1c0650b5146a005a02040e00f03420950707801040d03403403258402070030303011401304440c5904080c3c8204c0c0742c829480f5a1586000d441d15444890041c046800341020070044c00d074160041d00700102500c2c151220042c0990800380d542c101134544c0c40100d10107100c410f41c1544103c010740594401140d000b05a104100580380c02c482e8150031400000e92200cae1680c2181c2ca16004402d18041d00743c00408442d0305d019030b070004030b100b01a0b04034401c6c2007901640600d24802c100713000e000c90304418100441d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 785028336 1250 785027086 785027093
    0x1b051804030f03060e0105131806060315021e1b07030503180d02060f030403021e0c0406060e030705121203010f0f0602060103050d0f170f07090909050a020d030e0904 73
    0x40821601100002c19016805028901c6030107a10211030380340841c044240d0030041040050507200c49030344940d69680018642d42d540000815802074040c5100258003421400c00d03040c1d408000305d41d0844107004100c40c14800d5140b491400039140501c50454503104a901080324108803015004035071300c203409003c018014040003e0441302c8210484a115481c0b0000340811080c5160020754000402d01108445420303000055900034400d1050301c924503059145089003404282008025510880c4d581c3c00030b0900d40300d000051314260034205e1401c80c0500c002655a409409818001c241d24090745084e220100110039491048409068032586c46080310b4030000394a00c80d00114007569240043c8a80c0042070702c07410707250040c01a21608070440020340f20002c01003690410082d01000b40c08a9050600c03000340120344482038a4082c1c201454001d10348019a0080d04500d468404218001200000c004d101c9540c182e03a04256601c01e82000d0701c003918820900c9400250420400040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 785029586 1250 785028336 785028379
    0x12030a110412030f0e042003060f031b030c040621150e031305060703082a04030605060307050301050c2a0a210509011b051c0302042d031b05 62
    0x4c0b1a0b2941e5001c106440000801098920343d074100c187e58000601241d45001009004540c801c1c0f010b42500024201d50f2301103842c4c800030b48602d078440c044c030114400b4289414042882200400c41c2c00307000060400c00780707401c9043c1f18500e10000c0c54100e04010f0421200e255035400c607443d8084100110401400119101d81c0080c103a140c00918201e80841d991411109951000746c01d81c0d24008155500d80c03600f6428200c0c502000c1c030892401104903c00c0002c0e07001080a503200701004101400d0070414185090341c00d0f003002d4400d034145020083e4144114096030803081076501850003018859080e801108500c0030303054528000d1400080074030000005004149154682510401507810b80c100da20f80079441090740000d13844500c1c460404c5904200703980c9613025005441d04160881321589200d0045c02d001000301b1380101e010400c842a00392022105140301020035120464000101242030007030200400c19003030704241d4a601a245001c95020b0800506100d81e4a000900031308503 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 785030836 1250 785029586 785029607
    0x706261e07032408120c01092108090f030a0302070305070506070f09060305160c0303021210050f040605281205030d0b0f10210f02071412030a11041203 67
    0x502180302d18200c3d2a0b400c6202e1070804491901c0064100700412912116903135012202c08203181d0340711026070b00800d0520015680c140d500b034542901d00f8100341c42c05840c10700010701049081e040a400c0f0030074810007008403510707078540d8500142d603417206240c01d80f0b440c011103402410b81e1043c5010428119080420b4100301281512802c030541c1d0f0b20001101600d8007252081581c0b0301d05403800d900c0c1e0380070b18840d1070840c0c070905001d0300746a030002041045074070449814000b0400d009040140b401e148400110703002c0180e40034061681060b0100d8074a8610300d45220140d2528104030700b1604103000143d010700301c1018255020405070828a540390081410012928a8500d02c110a03140c1411a10704040000d49801c61014201c81306450300c030ba141c0440d019080001c1031030300701200b462003542c07007600b18003800607110107403410000b040550300c0c480d4001991000044e021424103000c03d030707588013450039804241503021811a29031030107540e004c14000d05a1980140805800c0340d0b04c0d02 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 785032086 1250 785030836 785030861
    0x801091401141302010c03090e070e0a170601030206030a0905071707050a03052104080a030c060b0307030b0a11045f060c0319020706261e0703 63
    0x3180c4501111145008101524214010100c02500f00c005500031100f100049010741000343c1541e68800c44062030314012545c0d40b0026606042040c918944141e9100c01b0301540044000702800010748150b45141c10f000184c800d2a02000180400041d41c014210055001d02500c48840d82d030108803020740003086100c2d5142c01903040108440c10800220022640c00030003c040c006172200340031060391050659004500d04c20840860501020810303003a400744a0b48d5000454848ca0a040c01112495031130355200e0b8000704070030400304000001464014440040014045010040d00d2410b485150701c0100700c2c4441142c0102004032886544400019140442c0d402880d140d0300481c0c0c580304001090b80000f114422076030203008080800c1c0c04003402414851a2440201d40c451a68004169400034140c00b0642c2e0141560b040c81084024003da0801e905800441c0200d04901003040344c40341940d2081c8400100100c2106000c6443c11002c0401c000040c14207203070050244c908202840d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 785033336 1250 785032086 785032091
    0x150d020d0c060804150911010806030c0406060e010801440d050301140d032c09090607021006030309030303020904021e0a0e0906060a080907030614190c0c030f03060801091401 77
    0x10700030701c0f40c07400341c00310b100c7d48505010b070715405600040d20100400741c00c058062054001d040c0d2140c5541c8074900c05000c05d61110390b1a104000001401110305030400c0f00c211962051100f140b40442000391100d41c0803452701441c00800c45100f170010300380c6100901c46445800b41452405400c0310065043c2e8803428081c004254655041c4491801c4542006001402411000c07460b0b100305c403103007012064050044100e5069000018000c50000d81d9203070020b8010000303110b517042d01041400140303080c030807041c001140ba584010304100000d20000c1c06168000070f0082e06951030f58107e8400c440f00d5140311214107940801d030b100307a07001031680b2004901500c080c05110f1070b110120070702c82d2200504081c6840d10300102241c01000251141c0902e11403081d0120014034280030b07020141c400040800a1894542004410070084200006501c3d141400306102d8503132211a01041c2901802c0c1f030104a0b0085004800800fa03690020100d0b5190000550802c0703a40c0d010304151041c100d000703 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 785034586 1250 785033336 785033363
    0xd05070b0310081614060405090406020a03240302040203100803070c030308010602030f03010b131517060105030702100c1107060c0210081603111204111008150d020d0c060804 77
    0x1441d544d007032030080001c0c1422000b00d0030420012491040ca121190107480281019611000300310030510544d01203074240e40200e95030400c03542c0340c495032000182000200301300021283c0c1a200301c0c40107010213401030783c0000015844500100300100142140d8040784e03500c020300e00702445000308a00044000a05101c00000c40e94030010030743e600c0699045140740f540e440e00342d80303003d2035004c1611007002d161440c0002503000d0440701d0100c421440c54803400c00b105102c1234040d41840c2c000748041d052003410b00a001c0c00030341c0007a0341c4002c1045030200150440c4c1c5920140c0f11000e180440c00101c0c80ba000000c240b4503403000c0a840349500c00e407403541d400c50140a007600c000702d00712807441d02d0502492000d0140d900c6a08050401d84030075025600d0480e4000400b914000304490a40c0e0301c504c20441c4840e03900f80710f10005400b01051801e400c2501f4411460082c9005007088144581d0489000409655810f0000d5580b946c0c080c010400940c0d94080143c0000b1088a0507078007072aa41d1003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 785035836 1250 785034586 785034599
    0x20114150a1505090607062316020d080601110f0712030801050906010c1209090f02030711060f070f110601030c0807060f020c01080c090a03052d0c010c020d05070b0310 74
    0x4800040c20640f203041c201882c02c2d05206080d04062000e60302551240c0018540001c900c041031241400c0101014151405417030000c8030321300710f21f9440115840002c210103080c0c1d01c5600503803c071000340b80c4008081d100400705443c100039100c1f91340036800b4a8000003103c1c40080300001c5011b20079282c4040583c1e0350300410401d42e004071800c5000c11105840b040c001075030b0140310714410310700381807800c061f540341c280d80da0446200820300d5914079400400d1080464120b6040040401d040740104081d240c600400d042c241c0010700f0941c02c7c040c6030320b43e54074070601402c0e0300d0f2500d503c45d0007254060f40c6d403403c02e0a03910a0b075100d0100280030320000403400d54460b00c41c2a2810400360018a00e01c44d0711001103078140300c02805030254000038041d00d00682d0b546000040118042e80040542d005088034100102c80c016070451503c400e0300c946038016a40c08218084203010034204540003003100d0001c40c4802c96001030003001800703024408102e482d030f040082c0d40640800010848a10303107130710 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 785037086 1250 785035836 785035859
    0x5031314190807151202040b0702120d0c150b12210708250609060c030b1210020322060501031106120a0e1f020403260307050901020114150a 62
    0xa032203481d00900320030b0000190090461090300144c5c542040c3d082082038101c4201d80042d000003900401c0003840310f043d40ba1666084850040701d401400500c41210f43c00350120f041d08000a1070121002c0c1072042c8010315030b000da51028405000514403612038121282c071100c60002c0c103070054144800900300c40c03620009440c805503201e10b8851401d60490f00303040000e40b0881120704680c03440340d03104000401da4096408407900c20180031031520302504000c0c05455401c49054010390f0321001c0c00600400000f00759021251150006a4030b072600c1d04800c014010340c3c1c081038200c02400d0714030300030851543d005034100d9004401c07110f00c004942d030803c4903a2254190340d4514101d17241c08100b034581c580d405541c2041183c0116484400551000d101c07048200103090b1505a0208003002400102e0800482c01c880c04807070004800810306800c134031400050136400801c480480d802000ea4000d510940c8815031039a80301c0c00d20314200040c0a4441710404030f6a000e2500f1450000d408450741 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 785038336 1250 785037086 785037089
    0x31d0a060f06060e0d03050d0603021003050f061c0b04020406030b04230c1008070c050d0906110f0703030828050603010b1f0e0303120703023609040503131419 70
    0x2803c5008007012506c00302c4443d0402d660706282c05650315000801603941c444800320208440d200031940349812a003020207442c00a220900a0007801001c6900c0001810320007500c50740040d034107156803124004180100911f810003401e180800f0148014001101100c6001c00001214418410342c003481d174907120f94498481c0c5400c810001a4046164050300300182c0c4401d051030115840806c5481d41450f10ba0f00c40c1a40c000b161503101d0500c0140c0d03001c466440c8002d50307200240440603111400d03640e11410b0748409001c0280e0080414000b641056001c4556041c030042ca2541041c5c19440d80010a070a581052181d8605141d4030351a0410745501c1048240c4064000b0300c81841441c161654154011866898081000000414403140d076000b801442d9a640060700d40c4003100200300d41d080c6403c0a01e500ca5000550007018000082080c11044400e584a03030460300e4514103540796004a00300c1e45030014402c003004c1001c0902302c594801c202c8040f500c4501040d29151f010f0307120702c40da = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 785039586 1250 785038336 785038339
    0x1002031b010f230a0c14090103090203010c05030a0c0801051318060e100515090106110f0708010506030606030303150d06020c010e1f0c0206010b0f0903070b0a09060e030d031d0a060f06060e 83
    0x54209408071b01942c48090228a070303044c1804140c5400950010303003192030003c100c40100c0c1003c402d102507104240300e04100294681400030b419410b02000802c900c9001c441c1c2040280c0740c1030401c0036141003041c01c030220313940030a00740300c0081049145a1100a1080544500e170703d880300080b00300e00d0070502030300d400e180079004100036402c00354201c0e120003840b4406010351042044a404540c0b080089a004006160000032141001c904240c184040540b2140c407aa00500038020b0f40c0031103001030024030008840703140a034105454420040e00441c2010b008a501e4148402c950a00100341c0c950929211489040780030f42c0c01d9901421208501d10440059100b680103000366a01c1c640100300c044a5241c141e400c2880740710019182507813a070003680d014400854030030001c07600019034402900450130300700c40f103a110b080801d47d160719045011003055111a0030181003001c02c4c0103000d81103441802d41d14a8042418480c000c0d120308100c12501e5482d0071000600c09200d0400c0c0d0000c11b00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 785040836 1250 785039586 785039597
    0x10c030c05070204050601022a0f0609011706150c01200f07020d15060b0a021501060e01080424060305300c0114130605061002031b010f230a0c 63
    0xb16002e0000400c8000d1205041d80f00704034124203080080d8101243c010307000c0c0442585a0b10483c1400100c00d00450b5003030003050301344aa400246e80020489450130b182e490030300c2a41e0b40ea1070004240900220040380700c40c2001480c101300d01d2040d000940c4010f49152800590207000352844428031544039850300c202000e2114000501d80001103080540c01004034040c0b000800c0155400c81d4044d90020403496800144120707240d0701400186440e0000940e190b00a47c903007a005083d1075516825281003111400000e000c1103e1481d102c0c8412091079208210318030710040980c01008039000030755491080b4000c5601040c4186640c0d0081c2c65100c01d00307003d14030b040d4250034a075001041c0d40f451355501c400c0080703a66000d4000712403060101150040d9024250f0910b034088072400b03000640a0101400350103c944d80000c02c0321112070009103190400991a050140185082c034009802c0ba42000c80302680341a8121070541d411107600d04d500c0086c1c640e041541e081702d00080d648004140c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 785042086 1250 785040836 785040847
    0x20907080c0f0c010f0216020a4514010f05040e07120507080d05130504051308030a0207020901150306380405190801060602030f0720061b010c030c05 66
    0xb0310384003d007000c1c3c5a50800440c03075035110411602603811000401c2d625441000300c0509618100c46480700521a000c00d1a19168080088041171640e17821140ba2030000c02c511036a0345050849440c4504c00ca1070b50400c154040d102500860940a11401c1401403c020002c2141d1800b403080c41c400c8400100108007151800d20007149010100a0940746402014000250180188074003448111180e40302c568412030300c1d600340c4040003070b40c010705d00071407400341004a4694100503000480d030300515140d440e039440f611400d01034821541e00941200480b0000030700c3c4a41e00080d42d855541a8030181b040e16200c0384512074240d5607980c2c020500c1aa49401940300b00007503501142c41a1031541c040c0b40c19254401324003044c8004a06460070032004004000d041c17028480c0070003174061803028628040a502c0a0402806403110240c40d40034840003030f4085205144c8a100041c002500440c0c41e00324080c03d070226140da040100c50ba550801000c0c1040c03030f1107489104510803440d02d4850604 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 785043336 1250 785042086 785042107
    0xd0804060c02160314101a2124060907080c0703050f030f16020102030105100e040b0d0f03080603010618020310050a2603070209011710090b04020907080c 68
    0x608100041d98150302a154400c0c210036041d10341c10000e9070040030301a090f903504141e014904101d00d10302c0c5034800e161509000400c0711003070005c1800202228a032030400b45a0440e040741d030614255001551241038036401d03d9000044c21140404244004002555140310038041840c008864a0300000c403444005005c03480110050075201e8081c3c034180c5c1c1270140541d50100c03103520030790b501543c802c400c10420403c038129400e10740c1c198619100039400c6501d00008210911034181e100014420300d05d821503655255070b4030901003198010b02d980d40300405801c0102e807150448406a00040203000041d01e14201402200100d98038121041c0040789030f404518000d407c00350082c1e4045410103c0041c0030360b10340000c40f0240c04503a00d805101d0b11400300310f448510b075411070450160800d1160b0700150380c60284050464044c045000c1d003096180c80200d0610744543c800711000d6103003400c910203004507801310a00c550700c01c0e0340e1988aa15124001e4418100c1100c4031686200c0070054010320 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 785044586 1250 785043336 785043341
    0x120c0405061e010503090a05031b19051b04020c010f2903060103030503070201230717010b0a1107030f080403120215160903050a05030d15120204021602061207020c030d080406 77
    0x1b043c0c0705825900d030703215542d40d500c0c01c5074401c101c1d44589076055215072202e014240035503111250050740b00b61000078160354890f182c040c003510310954002c4810700c525807601d072601181d1601d90104000c01070842c0344131070034000301150310b10381758820050b00c810143c10f81100143d550f8114001d00418103a861560104c42550000b8044401c55489850340c5182201c040040140e503603610416024504d0316290040400d5004425400d01401a900402011501d00b044501c030102c0780ca06481c004a682c185140b070400d843c0d00080400b649106100705005110f00540309a07845410043d140507800c0d8000c0341e0790784440c48041028034464000c9413007007009540224070381e05181841ca94003603580d03c3d00c40c1040d41654050b1443c0d0070004080303250500c0c034401c9070b40d003a483c01551030b5003e0414403101030b070105107140240a1a40060b410304850420400c1d2100f01e50300802841d6030303080140039085120420380c9d1000151241248100304d80c0740200d41c0c1c220203002640c40a0581d0b89a4540002 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 785045836 1250 785044586 785044591
    0x12031704030e10090e060330070c0b0301150509060a0e12030d15120812102d06051602130204050904050a05120405100815120c0405061e010503 63
    0x6100c1001d4405610f0b84903007030036481104440d2913401d0402d141410b1036401c480c000701118072a03003104140704464550040b22035211320000440840042c5054480300c01c03482580e001038a6620741480c0080c40c0000c2130021410303502d2600a001c0b000e4403a110075641c0740030700d44d84950300510034000f943c4031910404409200f0800108800440d12492807540d003551f114680050159448080c01c048840103520181c000f440c2c2c045000e4800780c501c1c2c441c0d481e107000780c001460b000601c00000c2a92850701028000143c24011300e10f040039a0000c00000000780078925000c0300c42002d43c00090076a0041045e180c1c488100c003400da07529000e0703900700700c00503070b00340400700300164240001b040584802c400c05215620803002852008090700f0b0803132808101c0303e4281c540c41002c1000740321540300c03402d691403a2800c60500e124107488103c42104250300090040790010741700c00041c0e48100002a0204c180ea40541e4100100c0d01d82c2c100b80162110088401c080c81901b510343ea2141754802d00041d503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 785047086 1250 785045836 785045843
    0x30d051303231c060b030a0b0a14010e01210c0e13050c09040b0103061805091b0102030d09020f090a1e020301030c03021009120503030f090d080406051302040603150612031704 77
    0x6440383e05d85224408541042c1c6e019004035503070729410000d504040202201409070380801d00110300d00200001c0c41e0040b4500d0003070400080000480f41e80300314036030012540a440c0350505c801c1d2408200207026034000829284503090041c40e1510070b072107074852903000302d01003080245000e0904040c0009400b850600d641010760f01c10740064442c080c0c034000302c44071701c0004000c03440e820020161840c1c011924070300d41c0111192440480140e800004954146501e40e602180f0011207000290054884114290308444c4140401041c0616035201c9032020610300a203030603903469184108101d00003404010200040000180054601840c0c1039008908a1501014140e150506080349200200040b205d9034408024801415007020b507440e40600d0761402422900100100100002e10241000d403407544d03203030081a4840c07404511404402d40241003440300640d6803030840068607088605c50f4800d0b10b0a0f0010900050502c450403a460309030f03070380c4885da44100c152944500c0020700100c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 785048336 1250 785047086 785047091
    0xf070903230303090a0c060503100905040213020d0c030c110a0204020c070b070c05011403040b0f090c04090302030d14070f0e0415170c191403030d051303231c 70
    0x20000d1040c100015407046010501808442511b860201c1c0c4220058000c0c10510100303108101e000d00044501c0d1003141c06050000c1451344460021440d2107142c00c82d0104040c0c000585030300c2e0314130717650020114004203a03070410610003411411211000c80711403e036400c3c0c001f08002005450070390042c00030000302806681444e07076039400c2000c942d80b2000c012034002072540010440b545e042a441b4003806110710f85540386103030664800b44400d400510b908014480603001c6849004200032000f01000301904c100001006401c010f540ea800000ea81c044007030030b011401040784200100c460107466203441d0303080740150304101905d6105440400c03c2e085a41e9a0808035032100d05140c00008041e20b00c1d481015802c580d03016030600c030106164900440d000064a0010300f00c04c10b4400c102d40101c000c240220700311400090442c070842d8124002c0500302000e11080c90b00c201c1401141070f03c01e807216841e9003150000c1c2001840d5a03506042044000e1100902851829582282e01001c49030f00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 785049586 1250 785048336 785048393
    0xc12170603010218061312030801080f0601050a0504180206030c0d0605040608030f0705010908070807060e06070e0d0f0209100e090a0309030b191b020f07080a06180b0108010c080f070903 82
    0x503192041f440d403009070002a0900010000543d09200d0740c3c0340084001c025025542c10301c030200384141600e20800c2d020b40e68a44c00e1144c540310002036040ca05038010302c16079480c1401c0c6100069030700701c50488600035141c0000002c1c589040d10402c2c0481e104007010f9402c0000c5440c4980c8590803c0005032040d5403113407511000035081100804090b0301c1100e000c8d449441c0d0381803007011a51109045005940120700784405c071900040028074145040324099056001071918400e0300a000200a40044486091007082c540441c09481612288110800c440da42c0008050740c0308060b82001d404207420714001d1020038060504140c1c00003508905802d11828822402d04407a10801c1240d00c0068100700e03c0c81c200c1d41841242200404c20000b800c00340c0c10110410748070024140300030a115959070710300e0f00700d21180c0003510000750480441d14196968904190280040d100b800d0001015003000801c40c03418603a80314000c001d26550301c0722440c00d6a0300e0559250046030500c000591002c038 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 785050836 1250 785049586 785049599
    0x260f06120601080102120a05191a041107050c060a0512061c051b0f09010e10050d0605041104020c0c04050a020f0d0e0f06040317070c121706030102180613 68
    0x2076140280468000107949034101c000d0040c009a01401d002c0c00300e0300704070921070341082d07000d207041603408018030019031111088105285c2080070008150445d0030820b40c495400d101c000030741301d081c2c055400c1d641c40c4601c074410070607980b0819a024000c0385047c01800c00e10320341c907140785610403806007041c2c0514501c07507001c6508800c0d0403070482d12540000b000080d069810020100300000641c0d80d08000800c140000e507045005004182c44030300301c000040e80207149410004010b210240581d417001c03d590400b240501421517041d0380400140212410508240c0700b128890310801d0040c00060700304808000c00f81002030a0229020740a0000d90010b01030b541c0200040e08150718000303090805d07071500e10300301180c0c001801c0c03c0d42c0016080001180d00705034044110b000708903005c1a19a260313041910000d01310840600340d500210145e404458100300032641c48001c1c040c2c000066641c2c04101800c0c1d03c1195102010003060310708088860230518041c010351030002c0280d0903600d4a400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 785052086 1250 785050836 785050843
    0x4081213091a1906020a0f020a0e070206010e01051c080c0a150c03050901090c060c05210c0105090a0201120b06090d0506061c030804030f03020c0f030a260f0612 71
    0xc108902c0d0400120980500d18003481050030954054085440f1145498000fa40301c0b0722403003015107140c07800c650440c115500c82e050b89001e01a80c1d94914503600303020320b000359588801d021380410101682d0004c40c007032500b54000d02c0481c0c030305d1001003a20b0140da035514500f41c01254007041244184515040004c034100c5040c98041005000081e1620742d0b404010141c1c1d10203001d4880d00d034035084401011403051000c0d00182c0b003403030900706110081880c2030f40c9010180102100d1002d040195001101a01c400a103c01c0c2802c034000e10198440800b0349071506481e0344001c0c007044118403074030103000700c07038000a203c030400800031400c0860000101c0c00905404004444070b0f00918100021171625a0b08814000000c1c1c007100c86403001564007401200c00900003400b40840380d0b0840300c000d4800c0e01180c0c0040e03022025194425840c00c0c03010b41d00c0d00321500c03400106100e5010019011448201c0f44000780c4414180c816580b20080281000310001d0802604000301c110080e0700200c081 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 785053336 1250 785052086 785052101
    0x3030f0e0a08030c150c03160c14010501091409072913051005030c092124130302070b070305040b030129090d0b06040b040c020f010f020408121309 65
    0xc00146a807135503070450240c2400243d10750003111041315018825107404950540f50b10100740009448081e0b40e191086e00d10710b00040700100f15041901c4890110301e019044103040b140b0490080c80f8140c4298005109500308851220071030740300c04801c0180c4411100c086504080204000814400341e2071001e90a91007001030342078003405540c04016a0401464880100360545010350450a10281420301c52091046040c4540381000c180741a02a0502000510300107041c101c61061219549800d03040b41e032000030602e122600070000c1c2d02c3c88005000a0300240d4503601414519081014841a54200c1d141c1902042428800420f5441c9194005c40c080c12603517525040254400070130311145c41e0f11041d1800da0785800e201080f25074030742c81070001c1c549034440301c844102c1d0b8400d80402e0080036422485640700f418181d21010b880e40204901007400f41e020028446441500c0d516010b82c40359225280c203d6101c9a002400a44804041e04d0340c0f1080223106ca4980391748980c40016034030f26 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 785054586 1250 785053336 785053349
    0x6060f0905010f05010f140319050a050f0a0b0f011b2f06160321051e0f0709170a0506010b271003021608030a14010801140103030f0e0a 60
    0x40350014000c00e003c1545010007000d0910b041000340070b00d13050040c068180c100c1440c0c1c20000c08004079401c0112044402c800c112540c4040005242c0b0a1109001d05020b4400076070455014010840d000401e000b50480300c000605222100d400e02001110a89841c60740c41031600b61300c0c1046800500d0742c1141580c0d85e40c200020f1036001142c0c40044034101140c01c0070341d1249000f04003280415111242014850790907040c40007003141c40d00f081d64410303c601d44e16040020b14020030000d000c07082000d80301c0296860090b18105a0310240542003266058400c0c03008610280010000742000c0c4141c4050031f0bc03003c040d1181c90549540d11840c2400a070000501200041509070741c81c8541581c24011045950101c0d494110701c00124000144034290f190415030000b90030807809017051451450340e0341c8400c031030741d403442c00f21100801011a04000202050a90000030f82088140a103040c50801d002c4000001e910359036040c1c80d04040c0007040c60030b01880c901100001d0396060100e4005121 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 785055836 1250 785054586 785054591
    0x20d090302030307201002030a020d0c050d0b0406080604084801022701090b0f0406090e01061d0a081b01020105160e0402070212062e0e0403030906060f09 68
    0x140100085d101043d1a4a2100603012400c0c00640c0c401c40040c1000c0407151117140140d403610384031400e00c042e100700c2044c940628200204800801e90100052903510303082c602c20060380041c00100025610b0318460b01c95554032200108001c5417102c401401d041c03908080803201c020103104a1204050008206002c411503103a01c9002d10398008055440c4100d203000851038519003080d101441c0c40800300c1c41010144e8012940c12690050807014060f12126007003036100d0b041d44600c0d90f000d600c40e0045400140001d6000600340c0d9592003001c1c182c0f907603170b20744c2c114688204c2d42443c0315600680e0003580c003595078070307000030440300c103000c01002500090324682404546000180c20340d0700141210300b17980602880b03040710325445080000902d00031036015a444a184c000a0803030b05101c0c82c030541c0c0340030788007e00290107030b240b40d0080c100c3c408901e0190940c180310f48410a0781c2d858410b02e41c01d08220000200001d2081d4401241c061044000040c0c0e1520f49480082d0200d036a0004403003140e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 785057086 1250 785055836 785055841
    0xa080a0605060420090913120804050717010b04060b13180f0e060702010c090812070507080303090610081908130b030c071b05150a0905040c0507031d0109140301020d0903020303 78
    0x4015800a80c0400c01c01d280e00a070120360307903510390301d0108c0711092000c000c00c40001c0740410400b40100c41c000c04200c1d0600364002200d007401d40c020720381a07500c14800e610703010001660003407110984282065691980b030499142202c202c0c40c0032034400d0340c11052507407807540000c004540e104407035203400114000c02c1c4070714083c40702900312504881600700780300080b1020000e94200003040160f118115011584400389032401500d05032051b0841c0344140804020010040000580d940c0311b841d000c0b04200301144c0c0c2d085125150031000c280198105040400d00004c154130300d004000e48003d0300700401005035101005c03041c942043d100b41a81003400100a01031001030300400b40c802d56442c200c842c2c860b10b0300000031103110385500058111540800c0030080b0364002c0c5050001044090700500c030304240b14400800d603510190045011034401003040100d4010039280c4007000c034040e11102e542a0501c9202809000c6010142d54951f400b000030100e130250f54014880c0051003900119101e0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 785058336 1250 785057086 785057089
    0x51b010f23040b2806080109030f0903030e15091e1323091005070203091e0306010302040e0a050316050c0315070c030915020a0506060a080a060506042009 68
    0x2501d0710759065090074400501001c2001c1400c440e0304071400319402c00840d01042c01e00e00d254041c1052503001c0030700e4201e0000b0200019042200254480d0b80c40d5040c0c858501000c1d01c030160180000b40000d2401c1c1456002070518070002e44d074140303d102896003007440400010f10f5004a0340c46249052201051004c22410400942e900380d6130342c0744040c17060a0301c1096100239014408803d0030034007036007004903c07202414801d042c0480d02c2c8030020f11091820290103552540450001409041c01d20080c0c40301d00707000e440d0181802c40040140c05264659000c000280940c0c0c07203212554003d001020000030410001091007080b41100340c40d10580c2400c007541003400020780b20f406604192501010040000c40d2075500105506000c1e418001d070703080c110754400054000d4601c8111400000c201d8907000192000c00d207104604903046a600c410502441051034440c1d044c5950000d070356200000c03026045150300000292000951050401d03600c4810078200700840341c10107001030340140c01d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 785059586 1250 785058336 785058371
    0xc0106080616020a0209150d060203061c120e0109080118061a0306180309122a0f01030f0b031c02061303090b090f060d020405030610080d051b010f 65
    0x104802c04042184050010082d480310100740c0002d01c18200880001c03003210300ea00300c024003082e01a15140303528201d0300d0704038000e41c01034074024418580091050129141030405041c0300d6440504040c240701c1c0d09030192000310300c0c001741c81d0500490340300200b41c80009110307140008070740740d0f585000403d080c1840b40845208880d0200854400f900c56401078400180c0142c10455090200e074241c1d248180041c11405111400360380122140441c1e01e80e49000103c07548015401d6080d50401082c00501d40042c07507806c03850b141c029403c1480c1d60400d60080e4443c840340c01d800b42e000300303030a065500024100306141d2540640100c51080580482d80d0401100c0c0e4410310911004060510300e44000d09002c2092080350300000b000102d9159648644036445901c50010f8660b60f141d41081d44680f0194005014180c000e00c1507600146549072035081c0d10045030901c00c01740c003400b500c1d46030484041d40001008650041c0c500d44500010100b44120b40402d02c001030000350710715002e440d90a8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 785060836 1250 785059586 785059591
    0x40e010213030209061212180a060807030e06040302060619050a0305030703021c0203040521060a1d01020f0307030e1905030304060b100e010302031003080c06040b010510081b040801020c01060806 86
    0x3510115400301030440c0005040042c4510f4906125200c0481d56088031800d02c08d4200b96402400b502d2002500d2a08041c419000f455039840134460b070740c80c0341503c030b40c0ca442c2198003038016800080400c1441c1050020343d81ea01ca900030b0404409900c0d5404600c041d03c0035402200c19134000900102859810700030010a150200f4400409100c4400c00a64901450207150b114000703e107a090f01c540c2d18482c20340c41c82c41461041d621903141031140c46004141200d040302e1094000050203008000602c21210a5040101610306544030803d0840051130480203070401407251508400d840c241c500d4101903230070f01c0f5000071560307441c0501c0d143d410f4940305804507004d00c0c81140041940794011043c0b04140301c081c0380041e107a54822144100111a40d0b10140c520540014903031811100490020f1245024500c0e140aca44d0341c600510004181c80710512001929940209440090001d012510781c0886544c20741801d441f003807001c0c01c82e4032a42250409039582c281c00c0204000c14481542d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 785062086 1250 785060836 785060839
    0x40b07050a030807180501140d050a0b0a0801020702010c11150c011b0c0f1b3201080402090a1e02030c0703020c030705060a050d0617071d01031a06040e01021303020906 74
    0x60700741c030862001481ca442c5c140240c5040c021140c402004c8041c4d100700742c0341080390124062006090070008100200030000d80940550920312003c07560100500840d035045606a40744240d482c00e603111780009412102c0c040d9444950740400c032001c4445000905004d0f198140005000c544440d0a20700d030f811510014418002407550400201b0030160740e054005422454080740e00d640d041d06090701d0009500040d002406100485d511200003107103041000c1c500520314540360300340d4001910307690f2040301c0096100e0301c004005000040e00760424444020003628080081c04080d00b1a4166001140e407406a098007007043d00034541c0c10000600e1022056014040035800d210100f0030742e00c2801603000c180000080c04d1452038510ba444403000340a00c000325400306008580d0305480b13207054401d42d0403002445003044a0b2414001180c0c0c107d030360105103904030698043c031200c500e440c000d0207a0781c0301d9541d480303e0220003421700003440d219a00e013001d010610300394810410b040030003a0155 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 785063336 1250 785062086 785062097
    0x51e060a0e0a1a09130b090105090d12140c0306040b09040b130c03050d050403050d051c27060e011811010809030d060306051602031c0203070302040b07050a030807 72
    0x200001c404104009030410340c901004910550920a80d0300030b0141403000640184a24081255203030f100030491003200c1c03140100084c2c0d61a0443c0040c03d070b80c4150761040d0f668202520505095000d4189030b403041709117210219408141c205081c4440070200d490602c0b6030710010802240745010300c62050000740448240326541860345a40c421004010600194400854120401d1050406803c0010340e881000c40762a0801044011f04035002031004580900c03030f4002004c01d29002d501690351140703204440c021403900101150000d0714180514402903004600ca04051000807494203031890f020300c2d401b00d10404410b000e04d0031110005600381c800350f40c0000313202c0026005a0507000055003440c10b0708045d140d84411a08510030040f1a0392150310740b03200041000400d8000b144104e0850600300304426040d60207070303143d00c00c4500e0b60342d0880c98200c280203040000e60146400c00710b0f900e801400c01d5150002d55200f07501a9900307039815400003552030308051380074100b103a0015003031401 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 785064586 1250 785063336 785063339
    0x150e040905070306050907050a031a070c12030207060b041b09060906090b030a1b031a01210507050d06120512040b040902070302030702040903110715120519051e060a 73
    0x109500c42c542e5000080c00952901e0100e50b6a107401c1249001801e0300400c817030001c17550303441c00c56110113203d446a0001100200002c0165009002c08481d41d5084060920503408040c0110000e40c441f20044400d941d4982c540f0001e501e4a06c103100042d06042d4403410901420540544044000d510600801210f60401d010090707200100e802212683c43c0030756240c0c0c50302c0720888094051f02e11280f41e001d003009005008158183c024044103420700d600f10b0003140110004440310b2800c0440c1550288280e881261350104540c0030541c410201c0ca00a41407074084a588800e40f40c0b00e034001d442c814841c800417401c3c41070900480c041512802ca9481c5400d140c00d070301c00000c0c0034620070280e400b607021881c0402d0600a02c00c0303079041640108204101041d80c9800b80a82e8500d4205120078401d50601149040440c02010a400041e0300c40e5114034540e03111003409803100030020300a55048400032000c14505000c0c29000320301410080700f054651a045140300340e0011304107417140314032460 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 785065836 1250 785064586 785064593
    0x92112170f06030a060f110a080f010b0403030806130b060a03020715020301120b10030231050f15030a020a08010209010f09030f031d1201291f140301150e0409 70
    0x1c030300701150b50003171001c108003807440d400b0f00007042540c1414040d0307800052801c04c515446081c040c407031501c480d00000c03e1b980710340f84440940510302004011071a6000400e00c5440e1071800e01d19014266180424542116400b20f01c60790003a40c44600880d402190782c0c02085624452030740009064801181150300d000000c00120440c401c001c0c0088070007202040c038800060800782c001c0c68002c2c19814140c0d0282c1c200180c55800701108107840c500303008100c1d84020542c02994040c108900107617131070f40ca8200c0d407050750054482080d03502d0b1207100d00c460f006032100c2aa1800405140c00010780b034802000005d01840300c894007180c20040020800d1001034170944826100d940c0502c0e00385680210105900c00c16102408502c0d0b0000e00d0b1140001d204905400100381000711440607004851818070502c4503250080107281e00081000d000d80d84c616020040d00c100030686e03d402e01c400f001486210039190701c00c2c0c00c1411581051402591410340081c00710081c520140c0d000c0041c4044c645 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 785067086 1250 785065836 785065843
    0x9100809280320060411120a0c03060f06031a011a0301080a0b0c07050102070b0103060b040209131802100f1e1d04060f08012901092112170f0603 64
    0x2004040c090070b40f81c3d001c010701040740d5100f035840c1d60b28111070042c00e25040200100080c034000b2403040c4403010aa40107000702003042564650301c0010748200c0c0d4110f0352064040d020000d001100c0d04e41e103a03c004041010513840140860001d0f1008915504000c542c868107107245030800c042440c10801084200b00c002108003000e90041603d9115448103071041c5c0480c4110580600107600100701681880094800e00f8100e0380309080810090920000780000d034060204031a074403c010b02045009001c1c15001034001c181e401106070071440c0382e03031700083c039003c6414403c400007229000740c8061076810003d5003103400c2000c0c4926501420542d40100178001500d159404d40004260701401d649941d082200a0b0040400041c012a101c1000500070b0403141c1454404186410b00009000c18484c080440303500103950f00d841241c101540d400440d082800d2404800d040c021003000460b440300100d08099800350703101c2c8010030310868031038103014002c0c11000481d2036800900c00716a4000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 785068336 1250 785067086 785067163
    0x4031b0b041d1003171c0b0a0501030b0301060b0708070605010501050702060417070b0a050904050a023108100c03050601030c022d0102030703200a02070b0f09100809 73
    0x2c2c1d2102195035071030b0030742000d90f0810f030720040241d2001c000303c2400840903009403142c0c1d41c0300000d40408540002000094801022506801c020300200a00c8554425005184544000340001c81c01c01eaa844448400b50300030141901c0f08400482c0040c100615805120300600003460f265081594a4000030b1345071003203114440c268100c031300000e44030320bc043c410f01c0b00030316280d00410303180c048440001c1c180341e100321212031166252500240b0100b209100ba601803050b52801d40d00c0d02484009180c190807040d0364040c1c207441715070000044880080041c1050300f03c40035030115800446407405000c2d2000030340403038140750070300040121099000410341c00f150b8800100506485c00040b041160007000d80f00c0003c9940000104585145c05412017042030000514074124440010b0010400c0d01500c500000180c00030703401004050202c0c00640342c4042480ca03001c0c80c00065500082e001783e8900b42c0600030840000c20448541e50071302040300035000d41c2e03400403207100e280c041d400d40c2c40681 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 785069586 1250 785068336 785068379
    0x5040b01170a022d06034804030b010e130b061306030c080f0a0b0705130506070f0c1502120a0203070c060804021e092a04031b0b04 58
    0x240800310749800c02c2003a04100e0b60007034161040400090080c8101c5801a20180d104070a82282c8035514108001103038414a03101c92003441d0200328480e510303240040c2802001460040744449194030802c00c441c400e071200084100c590b40e0b4690300c0c01308030602050780b0030280807115908200b18903551100340c152080d032000900b040380d91540f000400811605070241c0586160240200401140c0710482d419180c1c50822500c4500040c41708560f600701c00d202c014003028420010540960080000e840f680306c02295000b00d9a0b00c07200418515003000c0f1050301c42540201d0a4420b00003101c000700701400c42c4034200a1400c00040010303503505001c001892000c0710000383d40023854070074015222226481250140e600c0da4a240c02020b001060380c06031701c22501e1483c01042007404d00c03c501c00e00c01016114010b13950b640517410500e10004140441181140b4004c1403800140400500103103100309130400d070118a42c4c054000089079500200040c8000308014802c0342031030519080c10258 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 785070836 1250 785069586 785069609
    0x8061e090d180b040803070203190f060e07091419020a051c0f0c170f060904030e01120c0320040b07170409050a0b090f010b0301170c0d1a0a05040b01 66
    0x5803850b403802800442d0744a940110b10105000c500c80b0004070061501c0760007202164290716044400d20980c042ca06001018013050103070034070005855400c2007046c03010400030f075503c90384e541030b20005841030302082d8002c0551081c2008148420350380804594000c4000442c1060f030121000b80451241c100c000308401903035045003402100d141c01410044101200c10301c00d0320011030018088110303400c1400080c0b10711034000b80e21740f561089881c1c821040100406415101d6840684064940a071802e0420500346490401c40c4818000c119466a06583c00501c801c059480b0005000a0280d4403410860800041018800850550301d100b030300000452000c3e8080b4481603020320555010b80e20590901b82007080001d62640110b901c0c038010b0303c6038143c5950703070380c00145071030001d000f28502e030f030300c24001031081d810326003644000c0c06074400031191503459420024510048410301202c2d1400d002d403000090f01114404281c01001000e024405400d19a03280580d148050040312000310 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 785071942 1106 785070836 785070857
    0xd0f1b0621060914061e030a14190c082a100507203f01090605150307060207062c060d1a03070501120b04060506030108061e090d 57
    0x380234020320401a96410030105191601205510524118800401c00071981c084441e010b072070082409440c080b00c691400311240c40d2040110341f00849410301c1d200581440c0790810045800080740442c440b42140c841c001c0d1007000d03091800603d2452408000080040542441520b1a400404c1004540c0100c00c00640408910201d02c24052000911901d82460041ca00100208080e08682c46240076078106937400030441c060308440d071009250800c00c41c0c004100c0c0d40080d212040c90200081c1c81384081c200160407080c000301c210120100030b8104a074511100030318040e19400c122400d40300412100a0308030402400d10b441c01e5041c40d00103002c00850784142d444030884011190008050407102e020ba42c5c1003a10785501161698524000e54040c1407518020901c910784502d85501c001d4030401640b01000740481030080e070200c046860281840e1505150791082c = true := by decide +kernel

theorem cover : BRFrame.Cov 784892086 785071942 := by
  have h0 := BRFrame.cov_init 784892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 784892086 ≤ n) (h2 : n < 785071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
