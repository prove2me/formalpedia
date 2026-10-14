-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0832
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:02:57.865396+00:00
-- url     : https://prove2.me/submissions/61875433-af5a-4c15-a9ec-04e5f2668925

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 149460431 ≤ n < 149640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 149461681 1250 149460431 149460433
    0x180117040303290907031a0307090c02070e0417030709030f0b160201180b100e090303061c03090b13031410050702070e0c090103020c2b0509010c02010e0a0503 70
    0x142060700e4040d01401e0300300210320080c0140724003110528503100140030303594001410720049443c3c5043c10b40040c5081501c1e0440300e0750074140709000b52810050341d030080c83d02c610001141d0b010700340d00a080401a4112200e0b40e000070042c00041800c0c4034000901c2030002c504c0070340d0f0b130300d450105545248090740000e01c2400b952182e00c2c140085240414840c41c102400341c18051048134080b822107420001c0a50b2220503803c01c940803038202a040c0394802003800812046030780b100c4c40ca0309143c8044071400c0c10381d8400004c109413401c0100250040451140c00d0301c0e8088580d903405031494006000d070a500c585e020074421089402c15071044015900441c83d04001510391038a0380d110101d41111003210340c10078007c00d4446100040c180d00700c0d10b03a040e40da142c58451030b075110b11560001d09098100754090007182510f007000c1c4a01c0c0d074981248488203803100000c83c50046841b014100107000d204050010b4001643c000f1100501700f030f130918044100041e0400054407103510354200c40d0705 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 149462931 1250 149461681 149461727
    0x90909031204050109171c05060105210402040b090103210c0c08030a02010b010809030703030515040606020d021009080a0c0204140109090606120507030b131a0f0906010501051801 79
    0xc3c03200c194021000c10340609440341041c16111755110300c1c0d20035503800181d00c0240302c1d19080c0c0c00819602c11342d00400140341480c0b5000740032a070707840d0120100031103a08090b03600061200310701c1c140c4144d01c4090700070f03503031841c4541c5152070346200c0201c00e010420003032400c0c40d500307068540300b070422084840d0b02c821042845602c1d0f000d02517a039000302d45070780003640c6490a90109980160000780c450404039008510b001c410f0343d821000752002074903100920001c5440c0d0a0142e40341e0281c1c90240025900030060a9082500245012952150045028544104580480d03800350449050344501d081894814086201141c014040215a10400d203013440c00442d010200f03802c40f4030194014001440308030f845407149014821040c400400560115900300001411440e102d41e2041c4141c01400006219440b8501941e440c2100308011640309420409500d00d0b01e2511604500769a006003015030506001800300c0c840c00656280c000503001003401262701c60f0700d0f1081010108000012 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 149464181 1250 149462931 149462933
    0x70f03020a020a0b0d0f0e0706030b0301020906160302070b092d030a1b06110a02150c1f110901080c0d1e0507030c0507200d060507200a020303090909031204 69
    0x4e06908954080741115040104c2081402214080c031070306440d541025024140c42e100c401d50050040c49007c5400d0754080c85000016071324030f000f405000002081c002844501c51070000e08198640e0440e0315440707024000321106495080e401c951213080e00204a0a0741000b03013081000500e9510300d40c1d030611075642c40c00e080020b01904800c4d220440c604402045072141010703a03002010a50489190344a4000c01c0054508031039911349402d00d00040c1c600d0600459a02c80c246200b501c950800c2d54400802d21101200303910a00165490f0810032505000300b5200003003994801a1050754808400328101e0124040c650117070307104080c1c514480750518241207074107001d09011a081e6010926150750540f80d14081d200701c5a646030b001e003072030a5013030442c0c00d01a040440102019040740e8074800120010700940303c0e075406a0241c3c0c0300c00c0a100c1d000b09090b810b8a80c185078903101c1da0811008500141c03000010342d15689800c856203042c1c0e58448060364a18056060b00e40800240041400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 149465431 1250 149464181 149464199
    0x703060608011a0f0f070f050303061e03031b0f0d02010608070b070317040c030b010e2403070b0702120111040602100501050f060c0c0a0f080f0a0305070f03020a020a 73
    0x41160031944890019a81e0380412501080450541c61040d000c1000242c0d02c4c64a8600288002030001200f00d08000e4151078490b45038480d02c400b25280c1c1d00003c20f000c41c0345031031182901016030849020b014980c0b6400440e88034080c142811088406c0c10209110902c0103000c2902c01042150444010500c01040280681107500c6640280e02540001042640202c1c2c00c4400301501a01d82c09c0301501c211544421000d00208161070118070364002000107000003d545000344128413490140d0701b004100d525901002a100b0f20b4031124030454459907131404590700c0100c1d0716060000fa281d0440b40082086c41d44180d020b10025440e085154021000c0c90000c0c1007900c18950842d504c1c1940100b181e8110742080c001c0e59403040e0a00700c1c0400c00c0c90400000c100c44540d29040e41c0400b600705000c500b80c2c45198000001a103171a000c140724800b000c2200c5210120b0b460000d1007009030988000e40700c0e00c160600541200c103083d03100c20030b16000f004a20090b990290100d0445030b940c0d1344c05 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 149466681 1250 149465431 149465441
    0x30c02130b0406090903020d08040302030408030406050c0d11071a0d05010b0301060809060f1302040f060602011a01031a090606160f1a0402030c0103020d24030308130330050703 78
    0x610540c0342120104d42030002e84220340c0f00540c15001000d22010300001954107210080c41141144410403010408140a1002d00028621900c85035151038029004605014201c40f07a90104141410b84038803d8100051030f0b0212000c1c154a41c6a464201d1310b841c1180c815005182002400d14000242511116000394126841603584421a80382c50900313076100c210035190050500701c0b04004c9842c50f64142c0309818418801800001e441101080306c006441d40303680580d01603503450200f0480103005c0c0b42401071a0b9424070341080805050400710a00e2400d529085001e08186000200c554980e1011a01c40c40c9268001c201c0030700e5a442d00c00c6940c2150b000c01c44184c1506c42000ca030402c1031034051405194020054401202390200440c001c0d04280a4032500d01e403074500d0401d40886d0038206060f0b40184086a1464609605000d000654050400303c02d07650491040404aa0301c07140c50301c1101820041812042c40c80e00310560b100340c2d00c00031540c510345401d0900110540550203 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 149467931 1250 149466681 149466701
    0xa02190507060e090c0304030e0609041404032010020a02070314010614040b031e0c12060f0c041505070c050a12050d020102091005130e07020a0c09020702010912030c0213 75
    0x240082141801d040c031130401015104400755120600100300040e000b80c0d01c14140f4400548200c0c100704407038001400b03480f170b0544d85586002ea40800c0c4014035134001c00f45288190000d1059410502e91a070941d5113541203c4584140c0d80c0c0820b540e25034500c2801048002c680129508000126006a06008141d00e2060028000045c05494103c5c10f1501403001c8800c00103000c0c200240300c60380840807000c40050000014050300003650240c1d0b07551404460b08840d07500081080b407a00c620380580b0f07d1030150208188a2090000308048020020100c090429500d01036459a40520700b02c11160742d0341c0c00107540441a107102040c4050b4106413004014040d40c2254025010580c3c10f1b4202c1c4200c641c85500442414107000c1c000b8000c00007028020012001007141e036503141c1e031611110302c0c107656000041e0424411001030000460007440034008680c4114608261580081c240100c14407801540c0d507401d001c0d10041c1402003494010882d000740031a1400101c0030303000d100401c0c0c0505 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 149469181 1250 149467931 149467937
    0x10e010e03070e0f250906030203070c06020a0207031505010e07120e03040e150a05011b0212030408010e0610050307050108071b060f0c02031201031b03060c0504060e0d12050a0219050706 82
    0x4401d041c2c49030415170403211412641c850703040d65418031318220041d5000620b00014004202c40c24000140b10348000c000c0180b071030380540352003421890041c1d00d2400c1d4886001c003441c1864014000c42802980b600d4000b110303410f0228203080c40c10000c0303024106000c445100c0d80400700300044c4a41e00f81c0c422a10070340c2da9580c401c2c0004814410080705005500034180000c6003803801c8010610740000c00c0b407a03c2e0004000755000c400541e9401d25650040e04a91038a9458800c05d5402203800c104054201c4241c1d050010150f0401e8003080e51541030344106410068040e01040916008022110040311202c299a80d00201814001e001c0d0400c0c20240b01414640042044510310100941c0c44581c51014004410b0746175031039003e402d601e0444c650000000031100003000032400e00c0740c0812450140c803480d4a032840d1034409492001a0031800e4001c0c3c80015040c1e000a499403408180300e083c1d030403d19100c514098040780b40016030782e403030416500c170341c2441014010001035401c101d030602d507 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 149470431 1250 149469181 149469211
    0x8060c16080a090302011b0b0c0306040222060305090f0a1712100303090f141203120f19110703080a0608030a020a0b071404090515040603060218030c010e010e03070e0f 74
    0x1c4001284c0050940141588a200c0082407270182400e004580000c130041016043c55001d0481d0010143c5461102d030348a0390411040020940500a2030743c8107001001602c000000510350310b85505007010300800c01c010b50444100c0841d0303124151001000c0c25503400b400d0f0720704407800c01030300402c1e13010035800b04000007000590b8084d1002c06606031400c483c2c00003e075626044c10b01c04c0300710b084103040d22180828030100c05908000c244451140e080c442e441c45050500b003495030082c40495003041d0704507051542400910503280b0407034010b65031500e040c20965a0380c80ca20002040c0541040c2241e0100050541e85180e000580c0c255032070054168110a440368041030302c248264104001c01140284070801810002e0342c07244d41d0202c001104040d10501980000f001c4446603001107881c941e003c0b41c02d55040440c1c1e4182c400d0580d0640040a0501000c40040d09903860003107114100210341d03254003c1510180021801071030b1140d0007108904242107945c0190f0002c275095002580c410f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 149471681 1250 149470431 149470457
    0x1030e0105010501020d08091002280203090907050903010e01062c0f010501050c0c0a09060303080a050403120e030405060313050d08011d071e02030a03110408060c16080a09030201 79
    0x10301c40d282c1201c0058004042403000000d040c7c0d2902001456034071540120580100703114042d000900c40700c40d0b8442ca8040f00074800360b15404501c0c0701c0084600b154005e01858080c3c0e158550195004451807c145840f8444040002d02401c01c89203000019428405c000401038411a03054169492250800030090800ca00d02c010111084078508101080c0000410003540520000c1078003060583c2920070342c0d0800c070041501440e00344c0c0a240744c0c80d641c3c002013091543c409800c42d0452000401804a030611b510002d02014006501104031599241102d0b0714400400c02c5070f0042c07034082c1400d0b4070303441d2900f0307040e00340208028140d40500031065400240352007511110305880000100e400e0b080105e900102820b01c0041400c0203000c3c0300081210000c4800d4074880d03520a59034005d503564410321000a080d030b070f00c8181460700d845045c0030a008110010401c0c3e41d00c02c1d460b441064803100d04800c2c5103070b4511b481c00050300d800c50020359801d85c507a02c07814203800d0ba8001e0b25501110001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 149472931 1250 149471681 149471683
    0x16021305191a090903120c0306011103091f0903170c06010611060a0203040f08220b090d0b04020121050105031c02031611130e07080a02011b0f140303040201030e 71
    0x3200001c1d0480020b0b11484051841c01500741d80d00b20002504413410026100c0e6060020304090f2031182100344048100305031581e1007248540c41e81c140c04055410040c0060115801d0b100c2d448281c001e483c0c00141c03041480c3d105000740300045401c4030700001c05040c42c0403009002c8e0301c0780100202500481c8008150399000d0740c842600c0888420080509540d11801c400007904003402c01c43e207500765805402c0108900b80082c040360213468105c1e200c4c1001c0503003080140721951740031300b1415005100110f0b00f641d0b002802d10795950806c980508a568510040740c0090700401552103c05507081449151401580a141a02c40c10742c00c588481803100401000b05041d0380040005a00c1001605028203100201229151083d02d03000c601000c82c40019940209200d04904c1159594079403c0c1d401d8010070561009206900140c0200c8044c1c0c0c0008006251240c034030070b0b00700700d4407003401d00304400300c105040c203d5084581096121340d541741c087e44030741c81034031700380d00090038501c52460a0b04 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 149474181 1250 149472931 149472941
    0x1021c0e0d02120c030f0307030b03010501051c03080a02040503011509111315020705030613050c0913140c1003020a030b0f060306120a050a050a02011701060806061602130519 77
    0x8190000d00d603d450201d404840c0754880c0c01c4c03e80160005028180b100c01291000d1405000261000704400c581c8000345821170b541640141e01c254141c0074902c0d60b0301d0062000c4c0030100e4052070700c0e0505540b00074809002c0d200d69441650190318180c868905036103078500c13481c2598107800d820f000c50b400312041d00f0441e000f29100f0158011000104209990250b020310810440500585440313a580b01c00290400784110380d00c14001c140d1812a00401c602400170009801040740c1c460a1414241e0349000203500e03060009081c540217452280a0b45010402e824171503c00400001c1d801540725002400317500440d414101107410000c18404900c0c09596422510300060324543c21903603007904000110040000c505424001d401418010032424842081c0e41030043c0700902c1446a18800180303001110000341e2041344140c001480400e92000005030032034011142c030394907820308246910010b222848001d600c680002c02c5c0102070207213608258801ccd10701c0c10b03802c8042105501514290342d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 149475431 1250 149474181 149474203
    0xb0906180c130e070b09030d0504150f110303010609170a050c0105160204060906051804050606100509030609100506010306060509300c030c040b0906101101021c0e 72
    0x40c000780900d144600b0001e8001c45201040007011450001c4800e0441c2015041d4001c1c0350301020025040a103070608100c5146024058641181740c41c4c54488004a0b510141040b9420044003c882c0d0901078458466551000000400c0ea542c2c0d5031340703044c0582210103d106003c07210220084810341040d003c00c4600300190440040d044030107108004480f170368811121000803640804140c000350725030f840345c18050303c0d00520004004d4100300821034000c83d08182c4100000031130042100055001c030700907402510668040d5000f0b281c03c10152904e005070742c2c80d80c0c1c16100c1d074000c01664a0000508460f05c40000c041044103440d50001181035451b24003520020507070400030620740d41008001c0c8200d2240c500740c0714a1002e814494264014482e45120303006601100c92740c0e404e0714050200008440007103508008144d503100104404803030051400e449109040c000d504094000ca84814a4202c281d008541c1c44000c10526070000c81e94070365022a803440c1c103076040c142403000207489180c2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 149476681 1250 149475431 149475433
    0x210a09030c1b090c03020c010f0207021c050c040c030b0a080309060a0e0604030501020703050423090a2c01060e0109021206061c05070801090509120a050a0c050a0b090618 75
    0x180550b0321440d4141a9181d0301d002d0303400300a01c0010303610b4164850a801c001c61550050790ba601e9a2004a095071000d5001c0c05955204100fa20010381d2844807910500038141c030740c81407071540790921509200031061401e80180c109400c140c004c1d075142e80500f082200440c0d400030301c2500da04030999a805100320994100e4000c2103082c2c2c1c80c030301800c04500155802000d440c5026101d03684c80703081e60000c4908a011810106d03040c8100203240e41d80500c03811011006000ca90340902c0051001d8402901014103540d032009441d40980c858043d2003024400c1c1e007400c2c01c00d0440c05000354002c0c9a00c0c824544640c111000100700b1500500849120180d001c07216656a1104020003140e41d0013004440c0e0620040341c8106400003c0380180f52140380035032074000e075a61410b2140400e41d100100340346000d401c001c40c2d21850703041ea07800341e40c0503260314681180c50750015002650380c0c40020f107001d441842000048800c100045e001c00f4030600305201980c01a840350400c04c0d600c0f6105103059403030b0f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 149477931 1250 149476681 149476697
    0x510050c0a05093d02213a0e030306060405090613090804060e0d03020a03051806070503070201030c02060f06011b1a04020301150b0304020f0a0803210a0903 69
    0x29051040b0098800c119000b010528035075030301d16521103c2100e00b08050100903070007100011404070303045809034682040c00030b0241903000308503414081c900c24103952550840400d840c00d030303101114007680041d0301ca0390007140c2e80c88031428460360041c4586152101c450801d0441c01340e25a0110949000d2400908000e0800741013800300200c5c048000c2c281074208070342c03c507103410f1211a4091800060300501c42c84c0e960300e007018030040c09910340c0d4041c107005400d0940001c0c0040d0740020010f04858040c50320070b450b1070360000c040005070700050000360300540210328801800b030080018108540f00b40c03002c0002c900440c00a0381c032042c08a40801841c180e000c000f803030035401500b07038205030038043c00421200e800ca07580c0d060310540702e8217002c160350f0380d110100411414244205886450840300082000d4903200710807080b480003c0c4000c1c010701d0013049020302c035200c01d010b0201514004081da03442d201103e61100030404520901000c0c0e4880101103002c800031403103102e03046901a911a02 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 149479181 1250 149477931 149477947
    0x90d09050d021206040b04110d02010c170c010609020d06060c083106180602011e09060207050f0a0b010b0f03040318030b0705041d07050a1206150305040510050c 71
    0x50803420400182e0300710464910007401c0000a20400b88603a114818100342c90401c8e01704005030140c0000c007540240710b800c0001d00540c0c0c003e01c00c08481c540c8a41c244840e1001040764403005e0140019500c0e0660802d600450074007116000303445501c0009500f0045907035188000c0320942c404a80c060240c030810400394401c501d04404240320840154010b0907486024030180e151030380f150b4070150000700c0c03900401808030390491b05107005000d6840203000310200003000a00700e84601c8030b1864102d039a080c00c03108000c00c90b0165100305411405a940140f4407144090721b45e0740c000c01c101c0d4a8140840040380c0c50f90f00c1001e860908a40406090450b40d95660035101c0c042e15040080c4440e4101c1000400240c0030b115146c440d0302141d81c1c45484500c0c0852b02c491028070905041c2011010901b00008558403401751903810320246803940399909001c61400007000c0076009034035040c00a03004400b1940d05600701c00d020324442c8003200c048900b03083ca0201112000d07142e0038420041003003104 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 149480431 1250 149479181 149479189
    0xf060e1f12091b0501110a05100b030c030a03111e060703020f09040c020318010302070203060402090612100603020a09050405060f090106090203090109110d0804060507061e0f05090d0905 82
    0x1a60790495070300001c100c000c9884400960340160080b04407592100740a201d03550f44002150206400d040080c0350015503030ba601520340ea10340c5400b460300e80d507460503500c50380c0d0204201c8079480e5019065803000d15107810700400481e41d0404082652059603070303050791104094200d00c141c00c1d200300605070644816000702d0203075111104142a11074203010070000c0341eaa621801e105210160000e6590b040d01d00b10343c40c011028406800d05052051241001503140404d040c4da0107a41141e2900c0c0030355803c1c2c0002c25424104210354054810342d40c0c041f6030001c299000c0d4040d280201d6200141c6079460035007005550044600400d02c2d0007090110700c01d00002d0700002d070040615800446c0c400d8981d04420106e800440300300002769124030940060081c3c0740d44640c0808e0042d00d0b50381d00d26a42d521404e501e4815032180bc402c0110010750b00c428854183d00554100c036101100b40048545c0c0b034111000f40017610444141e081c0f401000c00e90503e00091000208035550311402c1c116490300b8200 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 149481681 1250 149480431 149480447
    0xc16030807150905030a0906030f061202060a20070614030106050d050a0b130501030c0503011808030411100806130b030a06090203030c1207060c08010e19150f060e1f 73
    0x8a110b5680707507048240051014805412944102ea80d0821180d18016001f820349511016045080b4604502400051a0800c0b40cbc160590156192036640c209454116a1140805204641c105825030a01740c210808110078088800755a01c0510781801640b41c805644003e104400104100700710403140030b40140c000c0d030b50048581c0400120071141c64041940c40004541030005584e0300e070018000c00203c201080c020f00000c0d0000c00070f07565480d0000c0341c4031107a9100600340c1e135070110003e020058400a2080f01c00300182030703001110102c034000762009405941c507501c184fc0300814621004001e1040c04040d03040100200030040490311160010b1013008026a010700041000c4100c3e44820011061001203492a55a4800f01ea0404004480490100c0000c0007404001040301c0090300c1c4c0d0f40d0f42c104017181c644016103112074607540c0051807050108440090307640e100280e05012108500101c611a844100d05800c2036000c00045102000d41c02c01c10f24000140710041c1d07807080e00e130 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 149482931 1250 149481681 149481713
    0xa0e040c030b07020102121806010302091b0a050702010806091513060825080303010f210605090f0c0405011203051e1c0609090b010314120c01020c16030807 69
    0x400000a03100e40b9030840703008044401d080540e400280700e80840c1e51403040280d105d03081c20038030038210b0810a0265103421061101031311a105000120300140400d0340d140405d49030000740c55948601c54034024081d034001c00020390115040310f00207565410118030b440c0c0b00707800d40c0f070b10094400c402508004989038007070034240d94160f07030f13410101b0641001c124420300b21403605003560030b10f115030084150561b2190003210701a00b051004010400c819403018043d160801e862020000b540788500801011141000d405681008284110311102059100e50a02900142c420511100003407005030750f82031203401c0d00c40b080d100d001400320348118050305444400340c144240c1c40c0c0c0c0700800242c4642001c0c4001ca601e410751001042c5039105482000c1c01404108018000c0100da921962240c050521024001c2d5100510480308030805001750220780d03208080a0f41c03901c0d54070100500070340100795412980d11401e2480413000c50b00d1148041142d500103000d919054032a91201e07100014900 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 149484181 1250 149482931 149482943
    0x13031103070b040b010302030610031104020a03110d0b13090312150509040b0601020105070f02030a0c060b1302070b090a020306182404050c011e0e0a0e10030b070305060a0e04 77
    0x701c5400610280681c50245000d801400815415801014104403020780360800803c0104010000030782942d140f00e48844040310b0041c3c036030580e403809401421b043c503003a540000c40080c00d0b010700341040c0d110a40109003941ea00c038a1040360b00c0754808903405032001601187e5544510003a83c001074000390710700b0a204039010b10300341e61240403816400d810344013183e8070700c111400c2242d6940d0910070301d503100c02c5c5450800d00c802c0c0c40c180301079101c0c4583c0444408120081c0b660394184805a0401c0d45584409030500d102250541c0303102000b03401211040f40e00d42c4100000c142020380000f1007201d00390300100509681c0d2103940d0500002011160702100c14000ca40080f1900981c4000740240315150f1490100d80f80703130901d0701600b001e0607405014140a00b88207180c01710f49141814040c100980d0504803050014030000030103442c080d50080c00d010b0650010820140880c00c990f20482c0d118032011001501d407550140c0568800711040d5803c074841840402600300b1452209800c280648 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 149485431 1250 149484181 149484187
    0x1510050a120807050d08070f0f090608040201111902030f03191d030303040303020d0b100503270304140109080a02010813020103180b070f08130b18011b0806010813031103 75
    0x207074500d4140885003117514040740884042007000d0b5082584000c80c09018a4003400e103d01c038800c00382c8450071034044c0e903040115100000d0116401100c48040c100c411004840342c820f00c2420303d204000403000d040b030003401005e50020155100000703942194141d089494000116070104941c2c070b02d68841212107100031103601c01c0250320240000c500407402036078050303500e038440580d14080c0c50b0307030b40380860151508610312102240d01c541503070b8000140c440c0d41180700d2a1000d0300040c210540400342c0f141d00001030005440c1c03292610440703011078280c8540660a41c1c420001e0349070403044001902082680707000851001d4258030308440644141000950880004c5040758040302da00c0701180d905801c08240201250409500c001c540001c0c60034088070300d0090500704040d042d51314001d040304210300c0480c0c1c0e444908803d02e000e03103d0040007000380032906604400004000005040130842c60f5020038441c1d446414030f58403c3d4098150380b44420655075040704d03190710060080c05180024 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 149486681 1250 149485431 149485433
    0x40c020a0b07020309040b0607051005071107080709270f03030e060f09060a090215030604060506070b070f090b0a080c040b0414090c09030a0318050a03051510050a120807 75
    0x64101c0600920b0903a00540e101d1464900707101c02c41d00d8042e1040d10980061105600040000500311410301c9584000719841c1c441410a480ca60156074445085001c0c02030049240b000004482049900c240750901c10000391003800c0b10920100140c2e1480b11500e5088403000c2544d403420040300034840c0c0b0b400030f00d81002075405400e1400984d1840d00505850050102503002003006c0394003c01c0d610004c10000c0f480383d00003082087d84014130500c031b40f80030002030001e6440d0b41c0198001d02016001d0355a41016140903044202c0894050010400380700e1851025882401c070344041d100c840442070300d800740c5942c003071b20b142100400e03400e40300e54104808150740008402510003801005083d10309100754104010580400502c00c544d4103505011a42c415603001550303020158050910040410300e40030350070912515a00000e40081010714000100400002c0040e03d0314050440c2403580c1d02e4041d04aa10040349109013540302501610078058100081d0103060394500c2810424600105 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 149487931 1250 149486681 149486693
    0x3091c140c0a0228121707050619050601050304081305030f010b0108011e260111070210090b0d1e0606090608010b09130203090109050a050c0a050406080705040c020a 73
    0x420051903116070070900310442107080629040e400d904c45040507034102d01d040546003403181041e01c01e8140762580740325070106100f043c051101c40001110f410550350305542c1405541d6640c1500e0780c00c9070884000ca40e90343e0405500c50300d0b014450503941d061035500d941d142e07140d90703810141b840140c0241207040011203540402070f08040905140011444068400015050660503809155a20038044249000380c05181e42d1a0585914a40407a44410300101e0301c1658440b10403800710343d6282081c00b0344d00308200b00190016520890b100c1a03281381c42c13541220484214800d05003020400d0008814605c05608032601080b60303844100c1c1c0303506a40215900340c42c00340e071021010031103142050080e640d021001602405005405514140303272040480c05040c51025045d43c400e90100201d044000c003900700e0451280c1020454414406c1d504080741c841d000c50580621130ba514000c002054201030041c4c5003200c07a82d0300640385952a04c170601010f02055800342c13007107000e646680000189 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 149489181 1250 149487931 149487937
    0xb03070e0607150608160911030a20030c120a0905060402040c27090605030712060b012c0a05030c1f02070b030a450314040b0903100203091c14 63
    0x1600043c4184000c100800e0b9031b00b2003c0d0030029805080c100d4020440340c074603040f81d0300007a03401e000003513800d04040d00c00400b0104003482c5108103000428030514803076101c0680711400850071100c2c0592141c4000c43d0403280501d40003401500040b0008025143c5940700071003240681c00e000c028031f90307803242100c842042000c442e0031155486200b44030f0301d841403003118050300042e0700504941c0c2c00c2c410000640c00c103c40005281d151241140802a4810080b0f601840c0300002095030b10600c0900c2c40c000c1c3d208480540e0302900681c040001d00f03141c00103101010420141400c01c2c02e209041c00741eaa6400040c001500790302c10080b000900302418001148508100740c5c2c0058810101030b44502080c1d910061504150000c1c50000c40550400a007e208911003610700c00304003f1600d42600c103841d179020907801c0c0010100740000e41c6501d803002001e058034101c060f120301044001e1303850100e000944010320a9070248a40c11009445104e07440155401418004000d281e550055030141d8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 149490431 1250 149489181 149489189
    0x30b060910030e011d0105190509030f03040c2c10060e060f070803040302060a050c0304031d210a05100608070515070507030f150c0f0c060f02030915010b03070e06071506 75
    0x11f90340d902000807604401c44000b40c1001090000c0c82135050a80d000f0760741e805180c20108103500000085406c02c01804a050000d100d41d80c085000e030b00c1c0c40c1907000c0c51215101e01c00f11454494600203281c2000c80912141a600d240d07e0f00310302c40e00b6403401d21141c0e070007088420003e608204003138004034002c48051485184640d004260610b4410071200c00c0c1c44016000c4040d401003441800700080d044a04d440400f803074042120342641403617001a80c00c40e10142c440621620030340b944000584003098440580e8003034002c80700214410140c1c40c007142e402c1c0c820080b032508445000d00140c503196050420240c250420790f820300f001c40d1105410034082d944100d9140a001d2146010040c10300560360a088004c07604005030001a04058000da02d6250940b0030055000d04010800005600402008848003c01c40d101e1a01349100b590f100444400411411144000064070104840c120780c0b04402c1540c2d00502812080d0910102c0c0e001203004650355481250504013000103445198018 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 149491681 1250 149490431 149490433
    0x9040609061e08070323160b0d06120c05010807050d0e03030f011202010804020906010903150c1b080a14070501090606061808150c07080a020d030b060910030e011d 72
    0x103a05200007201c0d2412560700c1001144c0001400700081480d08450150004180d000c251986649411441c04c06941c0851041e01d600010808513101c00403402400c45900e940d001002980e4031481040521024440010f203035882041d41480340d540b14609160308059141041c1381005c401554242c00d5035400074946078550310200c00c0005000c4c0c3d5001440c0101951612750307030001340c030380c00081c03003008010b0019000740300100216101d40d216440c820010754000d05925298200002103002400403005000c2c00907056032030420040014101c60f80c800d0385d00c8280c0b0f506d0644001d00035560071005c00c810109070f89042c02802d000c03e90070300503035840d28031940d00010348500300403000d001c1c10224031f1001c6005e030485200340201c0c00001610502e0f000e003010450490703943d07655031550328414541c009140d50340106c3c0c3d10002940000700115011010344041c84103280b00800c1c0102c900412025592112102c1041044035010341d0003080d01400a600200b016240b05106040b08100c1e1a8040c47c6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 149492931 1250 149491681 149491709
    0xe2a0d0302160b0708030f220f020a0509010501080a0b0406030606080303090105100f14060d0c090602070803031006030213030b090c0117010e010303050d0b0306130b090f120904060906 81
    0x1c0b0001841400000d41981c0c0a001d08011098a030751100e40030090245400401c81004030303401030042d240300c6402c14001003002c030f8400140d2500000345500d00a04070b0180e94401e50110b098644448154142c402c10794403000c50755100041e4402038004040425049035595101001007001801010054070020000f180c0d2400c1a44a00e421110b00415519150413106424031401031032285d07100c01c4444952080e403c800f100c40c0011300034801c81070f07058042840c0503003121480382c02c01c041d6011140150240d03032202e5038031480640c40384000c0758642d18001c00c0b0041403081350300a034041d05405184440440400703441ba500e03401c5030a42540d00300d1640d880303c0c410090f60369002d00714006100740710080030340a52400150520207031042c0030007001d20a01040c2c001d81c0b149668089801c0440050807610355051107078854a2600c0c4011055a45240701e40c005621910300040c031043c3d50600c40010080c84107444403019280d040748444c02e5009440320b600042422050107100042d00c20b81c0c100304a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 149494181 1250 149492931 149492953
    0x90218011503060501020319030204090203010306140115050403020d03111b030c27130615240807050a09082a0d030c0204020d0e030d090302010c030e2a0d0302 70
    0x241d4615007508000305400c1030424003503640d021050341c00c0183c45070680c10071100e8060307040d00a0300594100b03051031403000c00000f050040941100d035641da529080c2548603604e4101c419029040b4000707000100340100070803c01806d10307a420b8a280da0081c03800c0d0031047c00c65030006003800f815048c11006060300e9160000903141c10b11080d094030000f00ca00c554883d802c2003400204d2034800b4000b003110003400b80020820100c0700c0664030181d038814003c10241d481c040340c40385600307910b0098030300b1880b0001045060070301d100c034121741d0441941c49006287c0c2e144d000440b200da001a94050401c446188001a110801c20042c88070220100d01090940840582d54203405110011a881020f40c03102c0040403a0308500da14540e00c0e01900e015a48000d204000d0b0050140c000d21050b6034800040d1020030303000140d000c00c0055209900900c20000450000c41c155100081c601e034142e00a02003095890600100c1815072990002400301c84111580014000c0d004c00308083c0d02503002451030715 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 149495431 1250 149494181 149494199
    0xb060405060105070309151b03110105060a03020d0204050403030b030d0206010e0702031306030b0f0904061d070501120e0a02120d090b03190e1c0504031a010506070f0609021801 78
    0x9640101c0a01c0e2841c2440d1064074020102c002a10900d12442c4008000180507449a44c1c0200e40781c000c0e21508000300f1541c9001003140c0c000b07200394080c552828010442d10f150072148481202e40042c186e40030081584c00f00001048090804c81c1415600c0d4100300a9450a02001d15400036940240650750302d440310030640d105008181c0011508200b00425212403501e2183c8151001881c00040841c40100402d1380300e881198250344c4070000000300020080d15421111020310303410701419150241d8148079079102014091507010484040903012880f4060f0311030708030291442d0441e090054903801141002081c103030300700c1040d0440c00380d03071081540208002c80200310380f0000503d03500e448480d50040001003240303840030644890107500c01030000c2041e5080c0c80800c070031b10000000242005803250344603110480d8a01c4d01c0d0f028503c104800c4103100b50494801070101403034280c0715a0f034000300021504089410a0b603400410016031602d21040c409a09203021420265040c10800 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 149496681 1250 149495431 149495441
    0x140c04030507080102090a15110109240e1c03020d060909120809121b070602010203071202091e030f0109240902030c0405070e030318090708071b06090f0b0604 70
    0x540d0380740c0c1c0104001d00d8562641c01d200c404803007191990340123481c1d0004080700c40b40d205d0700e140049507007000c40b00f005102500200780000c484d80e42d0300790302c2e41c0c1481c4e07600e109580c0f8121041159070000c000c19401150844035856250041c0c4c03138014a0200003544c41c10884441d0707040340300340981c0d8a000404020b84103005070b958620350f0030032002c03904c0d000c109c041c0d40c2d810b4224901c60744000403d49100304d0043c001c140700300300c0e840802d42e218182c603814000e000303410441c0c03084009001c00842400403400e0344202d038035030000076110b00541f8440d0501080c2220504810a81601c2080b00020703003038000380328250302640304000c0c0d4402143c061610703480728840071041c1128540380c01542c100681e4000380800702403806440201d120f0355100c006a4084070200080b58050000040a42c1c4021040c406403880140c1180c200c0340c2d030303221a401203400300c100311001e0b40450007900240503e2102c8910010760248164400705a07004d04d55900513001403100070072140c10384400c0c01c0c00352601d0300e4091 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 149497931 1250 149496681 149496689
    0x70503010308030c18040207060b0f0103200a140c07061d0607060b1906080906100b07030507020f04061e0e07020a0b1b0714060601081003080a03140c04030507 70
    0x1811941035441d00d507094400504031035107807075000640d41da003580c07600d0a11a00d030310024070854076804c450030080c01404c03d0000140c030451080d072070101558000c5c13040080c40c85a105000703007522605502c801d600d034818491203060211b4000c0c01624000964000c1402c0901c440107085800d00d0150054900405140c00036144011103186540b95100d49041d1441c29411000100c4d0b170075a000d007c15104902c0d03101e801c1c4c400f03d00000119901e600143c08501034544101102c260b0717074500c42d0780c3d03000701d02c240686420080108031180101c2e02c46e0001d0a2490300007400c03250440a450300040072203a5030f6000d2480c105400105c845400b103040140070050018903021a01883c0c213200c0251104080300000b440e0b500410081b40311400c2c210302d0030401040441902e5518641c80c01c6c44101c83d13042d4001c9005074403450380000c00030f5200d200b603940140003106846010a055940b030f100150000001e50040580c3e500c0b0b0446100f04655416014445950400b981c0c1d5003541841802c00016401c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 149499181 1250 149497931 149497937
    0xc27020418050a0908131d1303081e07090305011b050a0c14010c0309021903170a030b030d03020a09090209090406090c090e030910080f150303040302040609060303030507 75
    0x420414401080c40a0709040710366500091540d803540d566400410009a010340f140402164018521115009041c00e885698112422110104041600064044805d60100d025058041d00068010380c141a0003105421070001000043c06100640300b43c12074540e000a0501e00f010014802c0a215007442d9407a001607011600050440c040d00a1040002ea801006100002ea1060190340d4098280d8044a10000d001003041c40b61300030040e126a1905074440c585000b00040d003000c1d40e081500c22203510841d004640d48a495034550b04d034004000203010703d515040040103955040c040d03c291049940c9005807030706800400280405080d0b0454081a0320402140c0c860380d44914803e90b001e0342c0038030b020425075843d02d4220210041c5a1208440d10b0410802c540c0c168404809094050001d0b00e070047c01c0801688103e40f00b00007070b14442030f407400440c0861030a038100880301c0c0c401200581224a0180d59502213801c482c129403007400072a42c1c0c0d181c14400c0645c140a03c54201700707186 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 149500431 1250 149499181 149499187
    0xe0405040b011a0906040b04030614012912190e010c020606130b13050f0f060609040b0103061d0a050907180e0a080705010b040b03030f040905040f0c2702 68
    0x40e030740c60410003042c041c0c5200301801841505400b1001c0040314003010014000c992240c1e6283e852030080d4010380001c441050800fa000700c5072449110320503040f00c2402000200109820001000c1c1600356160030040140030480d440080700481c0e12107014203c1c00225510035001103250104a500d070482c00301c410790402403020000b6500181c019040a421aa414902c0440c81c0c2c10000a0500f00011500114049484d485004c950341c0281d100c0d4601280854181d6210340707a01201c048121802d541c801002e100c1c55a450501d079101f2074002e4010304001489988402c05103d44141e20b580054040350007408100c603080d414044d160f0098007002c010000d150034205000d5494503403038002519075070b640400300d055034002c125036515290015031469442180f401d00d1806041804070090103181004020021030030008115200a110786229905150404000780c000c0c3c01c1c040d00a40c0c03000415a4954007003244529000c008110b02a10003861014406480803206412050404003078414 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 149501681 1250 149500431 149500433
    0x21203031302010e0d05060708070f020601030c03031115090a0c1502070314030d0204090920090105060c010f020d020c0d09030213020f072001140403051902031207120e040504 77
    0x58007041082a5090a10403900400d00b40441c01c0424a0440a441481003600b8483d02a40005106004501c50f544104005544510a036a121400e1000420b04044d120b010408603201d034240034803000c01c4ca8150380002a644a440e00c180c4030548552000e40c01c1402070071b04010b154400f400040500407001030300d1040d00b842c080d4940c141c43c0f10240042080e1000a01c42d50300a1040b51110044036a0864035680c4603001c5500401d500d41c070072110005018a00d003110402c120001400c26001080e41030541c2c2030505100141d040300071044100d41d21000800004c46d201c0c0050001b88030341c69001a12003040160951401c449203500505100003410140090b851340b8401d481000d902480240e034491141c010108288035140001d46140007040c0242899446984c04801c6041c2c2680c43c40c100c0d00c004ca008645a110702e100061160b03003e960003042c03050080c000441454001070542e03d14212071640c0d5400d56001d17000c200c850116485404000c02e40107083c0501011082e00e081180303181c6 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 149502931 1250 149501681 149501701
    0x7020414071b0506060d02030f1603061d0607110c0d06050a0c080c121012140606040e03071203021e0904060608070c02041a04060803040504180b01180f021602120303 73
    0x409800c046c007824100000c0410754504010071880301111030100c4868100308040544408040e000c21102e140c03c1c0305030b141c031102484c1081d205410840010b44100d4555544c19120503050960103102c038081c0400d079050030756400c110805118003550010490f8500320700c0710003c9440c070601c0803050203100c105001d40c85205000340c40d03210350100041c0c00c541e100e0002906500d04264440e03004240c1000c001810000303182400c03108001000115802c0c0d0f2101d10070003040d1510040c041249500520107172004c81c0b68001d2114002d04c85080051038014540c04226185241154440d500900055185d038681800c0c0700d81402050705251040f51303030038145001030034011550000380c45a622166a504c00b2094100351458076480140204940ca6035400c10701d40700d41181c03007030f03500c114034020000705c01c1c03003050400c042103030380c06900c51219a0030406d8820041803d00c0b44200407999903109a0346c1c410a034030060040746080d100c0c44101d0f00552040012941e441800040340350800d100f0b100031286 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 149504181 1250 149502931 149502943
    0x90d080c0403081804091101110607020a020d15020a180b120c1e130905091908131a030402090604090507151809051602030a050d1107020414071b05 65
    0x80e00400e01d0707540700030360503071a1050421020b844d0383c032a10b031080e0f500820604100084c0800020b80340d1200d141003200199803600003c81c5e07a6800340c0c002ca43c00b54010f14045c0e003e50b200c01c0c8915082c030a104d0b9108644400c03078001020740380100f20005005032860682c0c2c020310b001450b81e545090320f00040d15401409075100540004c1e03000d0408140482000d62500c11292107014802c41982c440c3c001030440003056000e8031800243e14039040205200d030001060f00c040c001d8419071940710550481d9039440941c1e01c82c88101c81c8481311325034041030402070301082b400d900c110440800d8680c01d09004100c4101d4029207581c0c4580d140414070f0001800105a031000c0392450140c8411107907140c00252065448148045501c1c1d0341c4900c0820140f5a40c0e001034041ca01680e94070300d01039641002640c2d81c0c480c640c1104042402849006182111500703d005042c000200d90f90414007250b02060580e110596414100d41100007000340380350b407080e415034543c0b4030900099414110358962a071980 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 149505431 1250 149504181 149504183
    0xa180303090201020307021504150504081203091905010207110405072a0614070e0607032f06090601060e0414010b030c0c070305010b040c03020a0e0d030908030a08090d080c0403 78
    0x540c407009640156070003401035074643c5401038006407182c0d10030540c240065005000e00030480e052489056240c5204205440540d041c0c80018074150455480c400342035003005086c1d100605c82c0e0b260300000c980030601703001d640d540308a001585070390280c0780440340701c0e038440c10703070390245141000704070300c0c161b1140c1c0a0750394451004e25505200040201158901001600030b000c2504144c1c1e108102d103502c0c1c0300707144a0407840c1d48044090107a00708200c0c051040100c00b800141e2841f8a64610520081f01006081004000480022681e0200d2420800104c4035250143c000c2c10042114540203010488003542c1114200003820140d51403640580b010b02660355070600c040006005519500d085445c406406021074400c1c60340d174501a03028000000c0910b0045050a804140041c0a030003a10926a8987c840d18120980c5a003441105400ca60b41a02003202005000038811703021700c0108001d11095035540c3c194941010304918219260036004100301c407541c10003850b403859500381ca0540e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 149506681 1250 149505431 149505437
    0x306040c0e030a030504210807080c0304050d140d05030c0d050901061d0a0b0108040f02010c06151203022515030e0106091d0601080c010f0302070507030b0f0a1803 72
    0x4038248400c11101c8003401110582c140c85468407035418550080040c00898885a10b00340c03c144062403040d000307200044c0004c0400c0700502001002410450141c45010300d15070403a81003541d00e80c00103d50482400042e10881444410a201c04006104580c1061f849003882842c0d400c09174003130f2010b88582c4052200e110360744d0700032440341da8003034201c10014a0700d00c45108001c50094200d4144110580320691001d20704410081654000d800b80c1c0c1c40350f900004200c414242c00d4005580ba0240380804603205583c1d0341c1c1c10041c028060340404081d205c0750b442062040030341d00c0d02910380400d040d045462000c1c002a201d01080d84500a101035036020025102003030904181a800341011000c1008c01c0c0d400c04030701054a9205034403040019208545014101e2008031206840b0308080c02004595040030100348011b502580b800e0220f4075140c940103180001c1d685445003040d03a281c00459070344107807005002c0d080c60100703d06031b044082403208020344040c02d00307161a00b64403104000c040c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 149507931 1250 149506681 149506691
    0xb070c0204060f0602030301080601090c09060f170108100f140412110109150606230319110703031b081506040905100501140901140702030a021314150303030604 71
    0x8649450708450020180c980f4124800740e100c55000e52030350003d000c0c050087c0708480000802c10854003903080304007600e0702d8240c0841e0a140d0b0851719000011482c1060010307a442c2c2e05610060003070841e000306410000f40c80303065002e40c5058140c0303100c8240541c0301400c14105d0401129006d0b0000e41096106000004414644905403000e04283d64110250352810f490356060002d030f6154881d0715090b01c0000c0069030780720314042e00c600c400c2d204030068071030108001c1c0482041e86801550406c1075542c4410301040340d602103805030781004580402c0c1c144003090a0081641501820500c0f030017080d086000c014810308010700ba02c02c01040c503460036100b851070b191552242c004072000343c01d9041d014040ba113407500c1c2803400002c8034030800d400240988070411003295a041551325000c8142d4480c0c14035160459603035030581200e0700681c0d02d406441e2003000141d45480b4481200c103c6002e010440c03241c1c2c882c80c0440548010709a00042205482c1c0b210207590110031250b002408a8001079 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 149509181 1250 149507931 149507933
    0x51909051305120304030314010b121801020d0212070306150302090616111302031504050402060912150114010804060203250e090a0606020307030c08090402041706060d0b070c 77
    0xc88082000040c142d4010300c8040701010080800841c0f199000e910309200c0c440b440b0034000310307002c001d110701504002d09106a803501c0301280343c46600700d4141c26204850429500c1058220f92000b0f40b0701071015800240041c1d1088860040ca49c0b000140c10f0401c441c900c0e00340441c0385041c801945100300b40e03001500107550351f00ca00c1950320b40e400b00b2500b131003075415500d4074000c00c80802844030b100c1c912a185110500c01d150013220b100b08444102c035058501904144006000c001e0302c02c0f03030300140511920b403050301c440c62464111240c042c010b24483d42e40e111300602182c4180c0003c41001800c54a00c2a580d03000500140c00070740c4200c0c01139996071084211500615052548070806036501d000207001076002000d8080f0040844a42c10280c9808083d003049406520880700540c0050154001003805820010100d5004d0445145043d00c444001001c90340035800240740e40000c0d842c81c9150300d00c10002c05a005000396540c0e4803000e01c6480e040390410004021004000d42c1001740d01c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 149510431 1250 149509181 149509201
    0xc080703051c090302100509070603180203010e01060e09010615050304022d0f040513080a0207080d0309120c0203120903121902010510030809040218100306030c05190905 75
    0x902e20303040740da4450000400c00d18248010345030b201c01c280d00500c81c040c00404986414422140203444c1c000c01812000d103098019006010b03030241c0910741c03503002d0b902c82025880c2170140b8510021060000164541040507400c070280d40541034181682c9441001e0108812030201812000b41d5418082d49a80c4c0300d100160b440304118803c030703103d0389034a42d80300451070030f8400101c85048211980400052003a0501084840413280304140d229440d1020000c1000c0c1c00081c6581031444c819158155140c0b2641460800c21301039400c0041c1e0764503c414107209408651480b00032035803800480c030362038540019075071340614114411000c0e8005101c41c507039903041012003483d595070004207840380c003515194801c810b80300c4490405942014001201040980e042c141075035402502d180c107103122390003408029040704840800e03a6401808125107907440081c06190b40e140c980d40480c81600394905807078644001e030b00003030140c1401c3d1800614400082e03e081c0c143c800004000406644591680c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 149511681 1250 149510431 149510437
    0x30a02040315050609011d0109050603120c0d1803051e0f0708010b0906060304020604090207030512161101020a12091115121005180901112205100c08070305 69
    0x502c4096090030040411015401c00c40c07141d88120360324640e981c0da034503000c1040e04864411041a0006038014048440181d2286400c02c4014040307513a0454041c83d04140ea9114007500105a0b005e0301c0c02c0c015641d0301c040b001180e90a081500714050f0316650720969524100e03880201e03404080021020018020081e201410810788111200e4960302c01506008000008400303009140580004246080420849001d02c0d4003400c09403400345826504070084d0090384048007000750410464007a141e81c40a001d0041540b00c503001e441c00d044032005004001c3d40303d601c6115034014050061000c0c2c014107030032541c0c13050000102d030a1400342b5000d10f4012a503801c1a500507800030a105a004036100909140490300c240401240c8840520080d548414811307035610145c0724894000003400341071003076008085c810000c9a0804068039525154200465000c41d130311031070180380c4001c1035808800300105410f13206010701c5420b0300300040c402c000200b40076120200000e00581010312540803 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 149512931 1250 149511681 149511683
    0x130f1a0703081b0f0d051312080703020f070b010509100f0b07030210021305010f110601030f020616060e2b03051b0a0909050606270111010f151505070305030a020403 73
    0x24103550301d00380700b18070009170400e50795812030900e010b0010b5003070680701000300400f5400502c04103c105517480211b411b00c10003421b1000301034083c084403400b980820042d0001a21801d480c3d919981000180328003050020020321448001100800c004002d480402c02601c02004511740e6458041c10107900d060540f11307405170840d2001900540c0742c001085a401550001d036100308142c2e0702404101c40e1681000548402504040c00400004216a2840800ca8800f92049041100d0200817129000c2102e10a80c5c11544454020390170079021300c01101c450000c240c40c01d4012010203a400d0307080f00340f80425801c1c550341308c01103054121401e071104408940c0038122640e0f90150b450052000c8828821400b0080c10080400e80070300c1d06a05482030200800c4560041803140720070200011203d4511905020034100001580742c42070150b01c117003940540c8046001c803001c24402e40305400c0daa0100380c07030b21031a0240c0b0310b20355031000880301d000ba094a0003544035102c0d6144d00c80248500e500c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 149514181 1250 149512931 149512981
    0x20f0c0f01060608060102070b0306040b010c060e010501032307031b05090705120c040810150f121502040506070803150a1502061602030403060e0a08130f1a070308 72
    0xc282800c20a054004805a41150343c07081e07419224500103a91741d0fa464095114421421320001d8818280303a48503c45594051424081a03c040e03200d0200f01c8250700024401030351142d006100307002ca801c0400e000c101589640c6d4501c0b02800504c2038071801c2a004c000c0061400b030100c1c0c0407407102c2c003c00038007400000b003070700801d800d0907403003c0e00c00e40c07151805000700d0200070001810b00340400180d404842c00140a4607100001c058400014420f1480611030007500b0721340400c1c0c00c00080d4041d40030b440800d146002c054140d0815400405000d81a03c0c8c20f2401048248440c1d125141a10016a4409031054494580c1c0008194821944000da600140f54035400aa80c1e82d000d180054940d565800b0783c2c0141c1ca030352602c0303d003160500c891032000d40e000300410000204107030f112060072a2070380165050110310340e43d25816681b11144c0d000324005150030602c82e440c480101c0324000c04054482c0c0382180005070030032040c1d0090020250611103880006551071103104070102010701184 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 149515431 1250 149514181 149514193
    0x303120204030b0c07110109060e060313170903011802010c02090406020706050c09180106050405011206090903020c03060c041404090201030f1e0e060103020307091d0a0804060f050313020103020f0c 87
    0x1140c00213a641100f00196401c3e81c0d0811a1516075001c0c040d407609964250391056050018101445860790019007034488110410682c800031401b248034180301021010300da00d42c1c90049004143c00d407006203881085c100084111100140e07084040907808a0341aa00400709584a08000000740031300f5001412190904080144950040000b8190300200303c44d182020803c078541e40401102c24091500411000c00c010b02c4a0742c01603a984002184081011a141303444031411403da94890783d080b40940c0c086134010420345011720030382c2c0d0b01c010903960840c1018030b02080000210030090206024541e11003084043da480790b04480c0001c03410140910407480c44028041d002c2c032606802111031817510301055680c440204e0604e048940050081240500704145100105140c1c004665480718200e507042144405002007071545020710440d5440701d142c00030107444460a00072000410008000700070040081300034440c0d4140e0203103001a2660b4941003004840d1081541c0e12401d84285 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 149516681 1250 149515431 149515441
    0x402010507050d180b031014033c0f070501050d090501021c050105042c2b0207090504051c20010504050d0216030624140306070e0303040303120204030b 67
    0x8000130300c4040344000c0c50380c3c203200d0780d410098886000946040818240000040200e200780d6500d840003050000c00380e400100c40c0801c4a6210030522505001150441030300849003220101402e141d100e8500103024050318000e0308580f580740038010b050512901003006005040d0b5907010818880e8424000c560712300c00a01c4043e641510b1400b9220001e0800d000400e8a007000c0c0a4546443e0004003454840041080400b00310641c8150042c135910032500c24400301c030600d00b02081105c82c00c252084030b000541d08003e040110343d800c0080b9860030318003480700042d0002039041424064108111044018401c102c1c0c04071800800503412090b00c401030000c1c564198041c0d4000c92080b800c4404038403403114140d07192000c14150b22000030a400042000c65400d42040c02c2c440000c0b0a14070621881240d1095100e026402101e14451100100304203810100681c0780c011505003448030325801c507000000d60700d00c11030000034100030340c034012845000c0c50b40e015034001d1940a03412110030301d00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 149517931 1250 149516681 149516687
    0x130512030114030106060504080a0803060d0602040b0d060603060303050a110c060d06090f050f0f04030e060706020d150302090106030c020a02041a100e03030a0f0e03060718050402031006080402010507050d 90
    0x60b2030a07200e0f529004d80004d102c1e00940c121000c0f12811000b5121601c650745501000c0d8200401c00e54020310301048200011f403181c4024805800d4021809440345447c0803074504450598025801741490a2402d202194029058440581c0306260a44800740c0d04580b207400c1140c5a890785401c44000318075001030302c040f500110300740e0710219410005080c240745400c00b9100260707603a4005900c940089000440700c00d16140d801130090a11b003282c400c1c1a8007184980d44020810360f503085d40400c0544881380c860242103840c20780d8182c02c802d1507083d90001802c100040c81071200741a51a0201c0c8a03d600a000000d0f0700354004204001b081240c502d4009900c0041940034810b0a00c0b01c0e003040503c2c003c240004120401400460410442e0340303054840e802d15012101c240f01d41c080c1c481c0042d036030400080d031288589689800c46420b0000c80c00d05004010307041180705030300510810610170b0078894118103c0c0c0d081c2ca0a5640d80d11140016501c0c4d2141202c05411806034020500100750 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 149519181 1250 149517931 149517959
    0x150106080610030218040b010c08030f04020909010903020d2601091a010503011d0403032d050a090803041b0b07030503070906050403110d03031b030b03010e010605091305120301 78
    0x2520034522a00c02c0e004103c04174130030040710002c188014139501c80b850910f81d1044d0702d02c847c181802840102192250003c1c0d4000702da90740e0903144208200400c42c2010011680c000710381c0360090201c011590703400307074a6a01e41100581003126201c07140444c040300c4846000c19410091002040f56103e0000c0c401400c505542034071b00300700b06669500d1552251085074102c8003280030b40c5001101c05085c030586000050429000c15407a00b00c038280d803072007003007000c0306003030b180b404030a5484644002c2d07405a0f08020001042a454583c403c404525070f0720031241d01c11b51000c0492042c003603a0003e41d58444803500406c00703074217002c6041800c05420000860080321580c4601d80c000d81d0b2a10215140d20650000401c000b140c0d4050800d14140407884110203446410041651260035028032030100020781c50500203500c1e1141610f49040030b1141c00b070200000d0009202c96418034001ca400b00d02c0103450350f40010381e080800b1003402801d01c1903ca074441c0e1044038030750f00c1d40c1d550701c4484590 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 149520431 1250 149519181 149519191
    0x4060201050f011706042010030902040b0307050a171c0c0501051302150901020c1f080f060f24040e0601020607031406040c020f060408030118020903060c030915010608 74
    0x1c2d1900c80045181c6000400507800303a0b0203000108619601ca544441240702a051103c4901c80325001c441000c1d03072101c07803003c68200705541c0096403210398010081641c40c95502d00d030080d002200306124a44801d02144155400c400c80c80d6020b8800c00b400904d020503103020316025902c1c03a4070001070355070300030841008a4040c00080c0031030b40b10304917038030204c2c1c405a90095124003c0104402035040c250081d0850400500544801c0f00010b00855000803041c8070f00050501100701040059800c200b029401c8003079018140382740d140c8000071a201d2007140240520034401c40c2541400da180c0c0030103058a500c059074025864035503810020002e001c0944080d40580944800103007098428030a0500c504d200a51400036034440c0ca091200801040308124210300415208041d00441084030074040c1d07104440c1640c0d41c1d03140242c0d00100010445800c0e060030300400141034140ea0020321070b608038400403055982d0382c0718030611a1401d91841c24204000c0c082500004a440e0031554140c464 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 149521681 1250 149520431 149520451
    0x504050d0318060311120a140124090b0a03110d060b0712080403021b0a030b1602011b0504030b07090e0403030606020c011812020312040807080c091e15060406020105 73
    0x8607884080039010b599041d00c629440110500140384041c41c40d464040d0410440d1f1070004444c0c00480080c0e8400e03000341c0001c00c034881d485014542260210060303904078025071030021055030a11044400354800c0c0d20300300f0f003055183d2600c004104802800c483c40300d4120b003000c0029035070b141c107141c1460300010070070781d8902a5101d4501d5440c3c01801003601c140c4d8560301805510503801070362000c0c00c3c07828460541081458001000040900b09114010301d406204020400582e990003425520f5030414000c102107000743e06d860700b50304036098801341c1e58014030741d030741582c3c9400307081b03400419030f900c080d040354400401c0c0000c1c15016031111090712140e40c251150f5103c10001901e100d8411800c060016590140400050611440c00f013a91840201a510309400390f23201800c00c4e8000c0d41152003d9002a201000307201800c10100c0400c540665401e56185001540303038038a00012071051042c2d040e10300000e201c000142e034040f17080c80e60082400d40c40340e1710303810020300810080300c0181e05 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 149522931 1250 149521681 149521727
    0x909051009020d1b090207060b0406050607080a11012a1205010b070303020c010e03030403091514090d020d060609061d060f06070606030204181209081b010504050d03 73
    0x3911845014040c00340b030300030704000124826566042501d2041115540c2d00c0006020003040e0038485c1d000501310b050041b00041030a503a0130b8200012162103071f03c800c0c4074207810803070107002403107a4058407500b518a040c00c41c0003030750701060385015200e41c055188170401c480e0f4000b981c103149007000c1c0f0f10400c202c0c1d0301c2d05c80900f114480705044540030f00804450302020301200c80000e08c01d40040c2605606a800801c07200c040e0036890380f035608259801c07800705542560520130012002d0310420395000c18940b030030801c141044003800c58410f185c007035802021072500000a540324141da0340800e40d40008104681d95660100301f0080c0030034016610301800e0500101c20b8107210415040c060700004000d142c98507407480404c0303d5070344661011101140c440f20000007607596442000c035800c004000301034494519140010244c140c03004484140290080140310000000a00405904074000001c01102d0500700580307090103142d120030307030103105404194201a0700500e980c1070751614840c0a06 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 149524181 1250 149522931 149522953
    0x305010b0111070b070c0e0109050405060f0609042910090c020a0c06030504140f010203061815090c0732031c02030c04031a040c0906030308061005090a090905 70
    0x3202d41c2c107850b60901c964440340c010f016888401e4000c1c01c0c028842da58680d60180e03103900d00c1c55241c101347e12242e842c0da074030001c100070300205002c099804098100c8036003441c0381c000f000440b00329000e8006003c0e5901040300d8540640c04410b5000c610800d80002242460201c0e4400380b05240c60045420b07045c14089010080ca0000480d5025994041c1e0030f14900f50500c0c0d821001400010416500d40e160800c103150f9050007441400f4506c12603500160f941c2c903114050003800441190000344030020703042001040ca4003030548188200c800c40b1000800c0c2c41e038a484840900801401a002c0011086002e050a00b40304a0049007a189400c9007102000b84201541741d024282500c102c801660b02c00b000292400d900455014a05007000360900e80c5030b40303590100c0c4400342d800305a52450308043c00300b805020640c080040260820074020181580d400514404c0c0c00761071507004055140c0d1029180d80a00c065a180701800340400c402d080e954003128014203e928000c0e00c450059182900b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 149525431 1250 149524181 149524187
    0xf0809010905060d1a010e010507060b010306030c1203020c060f0904050417040f1505030108100905010f02030a02032a071407080105100e0c03010b0403020d14030f120c030f070804140d090305010b01 87
    0x1f914081611041c1c103203503040d03d407000a0603c3c9011181003594400b008400512000c940b1000351280b01500d024412641c070b03019142c0408a010944189010f10002a5403802581107900c4040c040d14080340720b03101d5192910001c40984180c4e00d6145c4041404a000c00440030840116028603100080700c809102040e10a84020301032600190046c0701401204e014582111181c07904c100e000082d01c180b40d1410800300d0304260761143c505078001007840401802c1ca5220301d0045075080c81c007144d1050001e00707602144540c4000401c40c05081480f24103441c000e12044000b45115402400545480140400080c000d80100c0d4000b030096004070714412a24030a03070303040c1e130340c140c611501d080e003190200b101081201600700c8142c440300074001195901400074100044a03240074070b483e581c02c1b191004074902e0042460706e0010040c800c210b802d84010008603001405420030030015141e50030040680340c0c0b0360907445400e00c0b60825041800b54800908012039000300003c02640d0300c600011 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 149526681 1250 149525431 149525447
    0xb09090a090c170a02090109050f090c13150b0d090b0c04030506010605090d120201020306010215060303030601030917040321030507020a1211060903040e0709030f0809010905060d1a01 81
    0x240c4506a402014092109849601c8984503890b81c11612400666800030b0b86d0700101760800748509403103406002102d90100083ca402c800d001001d00035a41c0e6040108005402030180343c40e105807214440c05444400c0448240a8506c1d200e145584a04110403400540000001218851b02c6800003038454210b036016a42901c0c3e2140140100d0303482d00000726a01c4e0440c46841e41c0c0000306003c488009040c03420106800300e83e980025803289443d8001904142080f00f4250300e5190800400c0716607a0b000c41200d03409002401c00181240340d908094000e051403540040c2c5641c0b00050100c01d100c600c0b01050344552403652926080c0380c0114080701540d00584481c00507034400c103110310004080b0b440e500e0098146191050500184800305c0d440c102c0143c5400169402c00039041c00152000c5080c60f40c0000c484c01c00000242c5152384405410039071010144c00da800100b01100640c0c402c00c886002013400a00310303238550b0b000c401b1003401401c813201c2c01080020b10380c0c600301d000d5000c0c0c128 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 149527931 1250 149526681 149526683
    0x60309030403230307030309020a0812041802070807050a150b03030904091103150a0e010605150703033305010e10030e0f0d02031210120212160b09090a09 68
    0x185051910b9a070780c4503810107001046516000c106008041c90700e504101400b291402990013003100300c064010300001c5400744d0003030607031604400f103100c5d46118680d007100c04940e5501401140100d00d8040c00c0c00030b009a200003050204001000da05010300058200d060034054407082242405102a8a041f1404c02ea00240c00d074005100303440c21842c103a40311032030f282d0094102110742c00c02c0e00002418101c2c030140f2000030102000c10b00c680013a140c89007040080c4480d0003000010304242c0028000f640e00c00300c2c00e003421000a140c00405100c0c2d00704022a0b06884a16409400d40003400c030700484804a0f0600146071005001611758803c43d0200c012107000352501c070100c075a9802c101d01505070b200c00500c9521546d020881d60001c00c2151140005c1c4aa001e50780b10080403d00c0f0903000009040e1980074804e40f41c0038090442003940042072141c0c1111131910340b10f20380700414200b00c03182510b40c000c2407101c50f002507400e01440040c002e4440441d03489015076a050030103800c50300c100320 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 149529181 1250 149527931 149527933
    0x903020a0b1303240b18040807061407030506041b05161406040503030907090b062a010905010b01030e010204030f1101050d0507030212090a050d140f0c011a060309 72
    0x380402440c012400207007407075030000e900b0048a03500d07030301c51001c03c1103600c01d94038031501d0911802d00140301512032080700c0c0d4070071141254000c06c44014201e51120151018141135000140e500400c0190b500c1078150102241510a00b40b402c004041c00a02c0101c40301c50086013010318180b80b1911300500842451a651203050400c03081c0e140c9480005452502242c40b82c540304044400040c080080d184607038880c0e401235540c0e00d0540002420f111850303102101c01030a0500385102e5643d40019685040d030200c181032041c456a00e8450707841048a4882c442c42d510381007024081c0101904a140700041c01e80f02844141d10421610b4204e10a40c440640072180002d0914001004144210703021003051424030305001800e4154400c40740143c40c00d4012030750002d0702100039501e1000305580640240040e00a1001c01e0b03c0e200d03101c080c1d003501c030b40030031083d61584044402e0010554206401714dc42183e05c52120764807030f9008015a089182c920707001221024898030b407503070440748200300b070030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 149530431 1250 149529181 149529199
    0x20112090b01061404030c0807050f0306010b090409030c02040e0705040c02120904110f04061716080609100f0b0414040e0703080c030d050406091527050705030604030f020d090302 79
    0x35011180440d50081c90f2074040c1017040000007068000400b18050071500020b0941e691034441001090010503010707501940201d00100040104281034801c4200103550108000708945022101c03002e401400030350092a1101c40600010000b0350303042170b21402d5904100029149905076910b951580d14001072010030003901a03941440c1d01711591212100f1030b61420300c000301e0f60b04070103900a0b070042000190750b86203058500c8494541d0030380200b60700d180b011441d8000138006004040080185010701003481c0171500c0143c1d0094400000c09103010503041460301c5842401050b0b100744543c8170000445d541c0c1da511443c141c81403e08000540000b81810fa1035a07a41c2c003401e070041d005569a500051142044203a00d40c0961803103288228000182c13801140b4000680d05291142211014039021401d8442044291441882454002e00f401d800d28a45003581c5464813640019816008000502c400c25421050350b04403210250242c074812858200112514045440301a40c0b0001c96 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 149531681 1250 149530431 149530439
    0x1203060a0612020c030c100f090209010509060d020603010902070201080610020319090521190b130c03080d0e0f030715020d0e0111040503120403120806060d0f0603020112090b01 78
    0x404030300100741041c0b03601605081d00001c03002c0c11900940388030201500100c9103002c2040d820b100d004c00c84081e0400070059041950049003214205004150190078404040742c010b955408400381803d9000700400d070780750384405010020f9044400704a01080210340481e4191502c2000d020801150758000c50400c07074004010442800d02c0c850020520046460209981d29001c034040c3c071000000c599840d5202121b075810f0310306580110f00484000c40d42765241c001601c10304d8500c0d042180d0800c01c0c41034083d03030f0038521041e45466000610120f000142c0100002943d080200c5d21a55401a030340700076602400c19440c0e00c98002e00911500300c0e81c0a1825100e4564054828005241130002e414480c50007800d007150890058469522000310f010041d9103000c102d50070380f0281c1800b400c0d0a0a2443d9143e01c0b0b241c020040d000c05100208001561944943e01178078070f4580300034810301c5a89400f4208800601031400147e000480c0380d080d04001081900406c0c11003503001c80211216860 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 149532931 1250 149531681 149531687
    0x60306011e020706260402012003031f080f0c09100302030a15150f09090f0b040b010303140306090a090302030f0d1d0106050a03030f03060906060f021203060a06 71
    0x524090512081d00c000103440c080c011090242607009400511219080000c00f50103580403c41c0c1d0306070303000000c2201c0b20403c0203c1d84039070800d5080c00c01c44a000c102d424507880c0024401640c5456106c04820484110000034002c1c00404226052038445500c030607a081d101c4e840d0080ca1600b80c0e0000311000a00c5c1014800d042c3d0140030903005428403a1039500081c2050700c2c048054036240c001141d448020f090a1007850301280140c940fa1801c5840c000700901a0203c0384504410f850fa103420706024400c090b50044400e41e070007111701740140750500d440b000d003007030030300003030700060fa0008482d56044940401c42703004000040c0260714607551819100302808450100301c04502050021603150991300000c0c1000200d014004030b40148800200301311143c000c0080b00950381011010811070b141d41400a09807074151800010342c40502000782c000c0c1203a9441040a02d03c2e00307200150960340007100c203440c0740b40341d130036101c0742198406080c456000030b13504103034481e4009404200c8540 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 149534181 1250 149532931 149532937
    0x50402042f0f070c06020610050a141302040b07120201060504090c0b030402010c1b0512030910050309030403080403140d030b132003010303091508090c01030506030316060b0f040204120206 83
    0x40740d81a9071400d003441d5140c0c04101c0c44c0b0341c0703c000917912550a02500f230844c2d000d540040c0006940c0300345105d2401d814503151483c50804c60b80500807424581c0c3c0000301940449010345100c1040c3d0ba40c035880c40c6859181c4000c2650b4800c0103510304a004602e03840d081c080d21641a4100c0e02220001e401c6c030765901216407014200301c1c1400810035a22000130080c0204550321a5609582d6030301c50710702024840960401c4258600f44d030410401c40340150b4504100441c01d41d00751a00a8981e41c0f01001c8134610300c600d03000a0f181d000c01050002c00c0010034032804bc2041c0c42401514520b00300404241d041d209662002540450300400e4580070045540c0280d440100042d5052005210300d81180141d070320a0704158006195601c00740090300804900b9179408006103080d070441d00d0000042c940341c0402c840c4040c109074a0310b000c03524503038040050b90b400110207034400214021601d05507000700070181d10f550040c0e400300300c0e41020740382c03038803d41d0200c0b040605130030310307028103a400c101b0301d64 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 149535431 1250 149534181 149534197
    0x606060d140c0c0c0a210f0b04050102070303061421070b0c150c0307050a18180e010b040b0d06051b0307090509060a06021c140d050402042f 62
    0x10340d941c507210340a8064500850b0140e40310b81d04050b51003e0007803035503007002d80200724140595074902c0100070301c0040e850420800c0300c04000e070303244628940c605240c651540c6400600003403000d00900c8280300c0194000c000041c401d4908210490381c905000e202c1f490983c88190b441080e945849607135462445040441e40c079400107559039140c5070344d02052640c109106480f142d07404500c0c1e00c0445940361721815000310304440d18908515000c00f00400c2e038400e204a190400402c0001b00ea032034820f80501001038150080c0f02c40509003903c00d540c004001c0400016036039800c000c204886800d06200301706010001800140c20540503840d00d001030700c0c000d010481c1c00584000c2d41074007281104089c0d80100101c0ea02e82803607030301c0c3c40104500c3c1d0101500842c03044002c1c10703080108075000078141096101e820140001404108000d607410031414002221a4500041482042c12980e10040c0701e03038800c85082100c13024020b6040c049520552003107081080150f11031080a0b40200503080c01 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 149536681 1250 149535431 149535457
    0xe0d030e0d080c0c0708030c010c03020f07080c0109080a02030306091f0b031005030304031b0b040e0a2a02070807090204031707060e0d05030712090b06041d0a080712030c02060606 79
    0x40d80300c070302e00d901c1e081e42a800010240c0001c188c10012050a00401070420800c4c0b07801e5040006c07010006003070707220303e92001304210000913403548210400c3d00000c0070580c122000da0703201e075044080a9240e510031900d480c4140215000151121380c040d00315240400c0709207120074441d0400f00c14134041d40c4054408410050407020004d015a0208000c2c0003461080c0c210800304101b055940e01400815004810b220105010601005140301c51a9501420003040442d02c0c1e013909140142c501409001c503003d0401941d02c00c0e115540000e0280219190300c421596100d980f480da95040340503500000b002e07506031140901d00e8070160307405800003138043d07600060f00c1c0f049211000c1c90304a43d90000e070003041c1c0200c01c00180503000310200d03003607030f01c5410280f005440070350700e59070384040051030366100b41c2e901c1c0c2d4041c811084112152080e40c0051088800c45820b42c10541e515410030380c0110f814280c1400c00340c00d5940b19029032070807038007260000c0580740c40d03400030440e85801c0080040c40c2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 149537931 1250 149536681 149536687
    0xf120b241315061e0f0f14070c0306060f05041104050411040f080c13020c10150f261513020402190e0111160b031003050604060e0d030e0d080c 63
    0x2070004035800007006040310f032221150600c1d910070380136600f1500c0c4018002e010810901401003a04039800325200e41040c60b00003c8014440e03000506401860800762101090907808420400c07071364030180a54010b40c924109841d076038000c01c02076620300c103441e00290a040c4001c0006090680280c10740d00725412826040540720f9a0b81c00e40c01314144c0c8a62080e80c4000c1c0e44501c1d81c10303c20010790124801ca10150f01e824400c04c20307682d5800e039040a40490719500d800c83c0300e9620070002050050150072140360342180e03841c54541c00c1d0004241420300c0c500c2030b211754041514000540043c40004000e014200d50350b8100c0440445202c00038160b800c55002c12804205840841c0c3c10303421400d90751100e100304125000011311612403d03c444015a1111f2220544d40400680d010126a0641201030f6030741c0d9000c03442503070311184d54001020341c4a02c0c414041084400c0e00900c1c001c60b0b044040301c0004407050802ca0a031949440100e81d90341141c0c0c1035242c0b130303441820241e40c01040810910f207 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 149539181 1250 149537931 149537951
    0x11090d02030c030f010507080c0306010c170c16030b010609080a031d06030403020115050105040f091a04050103150509070f061206030c060f080108010e03040611070f120b2413 77
    0x42441d2a14804c1e5403680d64139000c1040c6d00d50022101034100b6003d04209065103010030010f811800c40042c060520800c2c003580708000300d078410403607404442510917140300001038048096058040e001c00c07141001618008200f280c413800c21541100d10220040030f0351451924103941400c032002000480d4a503409500003030751248801140154400e500000701e091001c0c6e0b1034010004960411810050100000c014100401c8590002d0351603800c0f0000d910f40c80070220612010000403c0b5401c141480b0000051007448001c44241c240d1070721051041c1d07078030000780c40c0d00e40c0c3e00340c000c1c2415070441c80400d0000ca84105110a0300915500b4001005a1240c854803400000b81e0b0021000807154500100b5041d0b010800500410b08407000b40900c203500024152240980d000396000c014039411010344100c0704114060040c481c00b400c80f650b0b281c441e04407030103040c1035032420345120000c3e401203036001020031260300d003400103004d070b010035213002c4010014a08280c180d0400410f1301c0b13144041c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 149540431 1250 149539181 149539183
    0x702030d020415020d030b1f02030c061f120305030406021602030a060c02010e01060e010b09180106020d0e01020619020906070b1801150f1806090207050705040f11090d02030c03 78
    0x1c03015204080e0448810040300030028038203402180068101424151f5220f4581c48003200044a500412848904001e040ca001c078658000d09600444a126903001c1c8030113501c4441130170f0b000c550a0f81c041d165150300c43c12045202c01c034944c00100013032403c00000d00461040c0e80500480c020404503001c034210645c0001e4505001d089050f54031964400059080c03d40920500000c0002d000007489504d2901d1000c44101105220b88400c001e0006070080c81036581105d40c5191054043c040e441c25619401c00a6541c00907221400226000290312a030540c00016007a10a0581e02e5200400d56044006c040103508840c0000c2c0d00500e082c080751000401c4804002c1c032a10200b840c04040c030038560002425103080716030420713442d013200c2c2c0103004601006900c2400e0750080c910303040d07038000380e25650390040c1085d0388132040140c4042418000c000703000c03610100b110070444040c0405041e91300c646080f07950200545204960800c043c455a0500081905005000509841035480010042 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 149541681 1250 149540431 149540437
    0x80c0705010c030b03010b0a03020f0603070203090306070f0e3c0301060603021201050603040b0a0b060403020a081608030f2506110309100504030c0609020d0c080a06180206120702030d02 82
    0x40782c007294903070b082c011043c1401d20901c011800c08580410b0090302c0c6801117a00342868004a03805400c0010014034424020022120300f40f4000e401c9810b14a0507101c01031583d8851702d050b1000900b1b0032031240d141d2030048001042051050400340146c44100703c1074071446c800740240c0803440e02440c0c0d0000c66645c284200e20041c181c644015960305013040121500b074905800003440b410090040c4030200d03001e034650a030310840d290b41c0054803401032400138199024a60000798000c800000115047d5004580d9003524406007044056251b01d5a0303ca58803401002c4510344042d20600c05890030f146407207284550100c202c100c02c00c0280750b070b03100c41c0f00780c42070542c030691000782c00070610034145400c0140403195020130a0400c03090070555002003000100c0790f4040d02080d00d40c40c0d0300c01990b0324080c500d540c25601c09007a50001c2c0e83d60400070707200c21070550240d621034503094240c00f04403c0b50211041a540c003e00e80c510381b0020b070803640c4103400040e100004500c0180890301c0303442ea0324401 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 149542931 1250 149541681 149541701
    0x402060a0c0c030b09031c0606050702010c110301020f0406080f0106020d12090614100b04080309210a03081503070e060d0302100e010911010f1707051c090209060904030807080c070501 81
    0x83c66070b0304482c40c81c40100c7c030588081d01300074074035094040086c681d0000541e0802542460301801891440c10800a2a0201902c0f50751651000504140452005000300220b860a03151041a59030309042d070003000400f4800c940140c0c20490b0300c5400c4a1151480c0c00201080c0d080c001200036080c0c5030b100031142ca264801105407040c109201825030303072140072030062245000582c500cc1c01e02c0c0100e920b078003035607a00900174030317410a868078160080007a82090860304812686008131504005202c101c041c2c0c1d00e1103801c440d00410b80f05509000c9000c0c020307591280907280490b12054280116a110214244c086020307210060305040824052900000310100022410114606050201c036140c0104c240c14000141d9240100d1600180306a40140070503410820983c2d451a041d6514402e160000402c0104030702c00184210060b844089004c0c000d985602107a92848103005408509460140c085071000b40041c400602c2054503540c8003009171402803e01406548503400c1d6541401c07 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 149544181 1250 149542931 149542933
    0x60918040b1008030a0207140604080d0e19080303060d0317070203070c090b03100c09080304030602041e0e04080310030f06140601090f120809090c0a0909050402060a0c0c030b09 78
    0x140310b03004162040c2e880103030030184040c520380745d44400043e41c1ea0000c0d100311041100c207640e91001d9540c9100039038008100707a0007940c40c0c9a1100000828480d10081160310900c00300e102217120410300c11030b40c01901c8070400218030f503849500c1000180740c411181101004114000c403111500315428039405404075030008c44d120320840c64240701020240d0041741c101c038904007000341107940c00540c88001c0182e01000069060066400300c0301c40b02c81c2d0300000007911000030000f04100c1140e008100b1904030243c05c0076a50311055031480511128480c5460b00ba200c5030108000c10407490045400100781c2070a130750201ea807985c9074001d5a0845a007078a0140c1e91700880ca0614603a910304a0703101c4403d181c041011810f120010199114902070905034400660562040101060440c0c0e05a0001000f0071a6440c142d501000b19034008142440000d1000000282140c4140906e5009a600400c0e0508140399107004980300183c545003540c00f450b41c100b000010840c10481c560080303510340 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 149545431 1250 149544181 149544203
    0xb1b1603020f030307090501080603070b040f03110609030a030809030c0a0308090f15180c060c030405011403010308030a02030c1902060106030612051c020304030c1404230606091804 80
    0x2050180c1820002d2001148036001003080150890b4014400010344400342410222500c50b0004607103000f40d1900904a0600c0000e004580c00d941240603000300c91203407006e00c5071042d11409100d25801814a1640c240d4040640c07040003e0241e025203030300c0395150b02224113100f08007c1e10352604142c081c013070300401c0e08081071103415003081c0012400002c0703803030081000528404280801d40303401080c0c030042e081d0450311082102000c7c043c2d0000da0f94000c05082e20780040ca02d102c0c0c0c981d8010b1040703a012984008407402c1c400f90340804c1c0c07412250400c100b1403c42d40e401900070007070f5200421081d9561030410000024a081622054015000d50300400440d814080c0103400c50b1080c4e004003000303449038107103034002400001d81103400100c00240152040c00411052740303580102e40004204980807040442c00c508008158941c2d400c0c1110240240d81d65201030310010302440201c40d50280d034120018031241041002050028001b41250b9446140444174964070071f015101140d25003601 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 149546681 1250 149545431 149545433
    0xd080403030f090503060411090712050405030a180b030a18080d05060907050705060a02070f0c0e160e0f04150515040302130e030a1103070f150606020d0c0b1b16 71
    0x41c907268044c250a0b00104100d08194550540c50502c10000600c24014036001801c224802c01202818980512090043d82030a291841c1c4a030001c20301840080d00c0d8800c103440342800360306213800f00c1e10103050052854403895117401c00b404440c544a070740e4022400181c4001b841c003000502110001400024141c1041070411151a102429000401034180a81c00101d203020a03c2d6400940303202c0f005a848d801490100c62141191070080c01541030b0441c0082c4003a112004c4511030101031061110700e2820701401c0d0340188003c02c540ea0850300b0760b00000f0042c03c0a80c032180403010390b040c034080307204c0e80c0300002120302c48200085c0c201d60308046410411402e01200980800c103181d1000c7c849080d140c16501d03070f24002c50b00c6040c104240404490103600040c01181e104a07003111050b856268241090464201403030381c807402d0285465400111036101103100708003090903a440011b442e45c0c0f5104c4548805004d080b049a03400c004004507841c000e4880188403010000b21003004484003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 149547931 1250 149546681 149546687
    0x803060d230f0106050f06090f0406061706040c050901051b06130308010f050f0d0c030b0a1418030d0f0615021f05010e01030b0702010b030f16050402071a060d080403030f 75
    0x44005010590707070401c2c0092256070791b40000b041400c2c005a52240e11980701100080b030302401c100103a80c000b071801070082441548444400701010461090721036903250001130104a40d60310100b400060024800052550b10a40c000d0558055201070910000102c2c071449042600a80701ca81d4a403100d00020341c00c054100d29583d00411400c01229100c51800001c1880e400d20002001e08c18540012008100310380030a2410180d44c20002c00e9565240031920080180084280742003841e21640c009171003403810201180d844003d072400340d4207101141c40d0b6003010705804613003600c006880310b0021800071261171500c460810241d00401e44105003015404140c404400804100c0341000b00500c240d212840ba1141183e1344044842c031540e490f40e500720b00506489a4a80e8517015801d6280a2050000750141c01d148a00c00581c010340c0c0d07244100400c038400c030701000b003055029032007001d10210542d0010b603010740c020b098522035501ea642d40118950158200b10089511011804201c540c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 149549181 1250 149547931 149547943
    0x50d0626061303030e12070c050a080c0d02120f06040b010f1203050a0c1502070c06020c010c020102070e15060403080c241302150a030609180f0803060d23 68
    0x26000c406003410342401030040001030581000901855203500c3d903403508000402c00f414008034600c0e1041d4a0b846203260655940308603120302c80c498080a4404a550b007008542d40c450701c0002480c0d80e003501d884e81d0034403942445180c04001d2600452031035402c1c0030b009014151146206e00e20550240d03040c0f143c0c100c00d410f079642107440c1000301e224440d070000c1c0d0082e0485030b250101c5c0c1841445000c581c5460640e422044c80c11000b468004941da00400694201010648030700303800303488403500c500004466403240424060300503030001c1d50070800904500d00c3c140d04000403645110a0100c01400300e805030380954400c8410100000305000451818020b0750210b141020580a40b0501d09414948411005d00111203d00d114000401150307209070b48810000c0704021002e40f501214103015004083c0c610031408020304000040c6584040c40240e4140385030b000b450080b84007a540c540495a4200600c5541c210010300040d00c003158503010061030318052038a0328901c020f15510174905081e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 149550431 1250 149549181 149549249
    0xc03011107021008040203060a0f15080319032d090b070908060106090e07031e0f061412030307120902131a030706020d030c050d020a02060f09030c0c04050403050d06 73
    0x2c0f264505205c0181c0c0d012561580140401c2004a881014004000e000749a04540200c0280701d1050018001401002400200e030211800741100c8000308001c0d41561403144203004041000c8900034983c0000003120308405505450000703000b0065611460004002d45000c00030459181003002032810801c00705000d0f006c1403030901c040c54a00300c89109902c001409d03070310525884404d104049413111501c00051070358270360140000000700280d440241018040c03250583e040741500207071030038800200d2408506000c01541b9503560340004480300d08010b11241246512880504090b83c1d0300507100b81c003004590700002c0d19025100d85450b9410703030410014060342141e202000250f8010402070a001c020f4200413440c103d8105084416100301d0800020181c4080b4501400c207500082c01485010200e0191176240c550b0070045d5940d0049042480c0c1303d51190720110030320300301500043d030014800d050941c14600002030140564107650400c002c07030302d00000140544001480509005 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 149551681 1250 149550431 149550437
    0x608040b0109181e0b0403032c0a0204050c0d09150f0c020d0806030a050601080102030718121104020f07030e15090307030813030b0a0c02071401051204050c030111070210 75
    0x380d412283c140e20703101044102030702d050a00494100c0203540c41611210310b5501c03118101d0207181c40d01e03000c0c0081c00b412800107803510644254a004140c2c0000280f404500b100043c030f0082c40b40d07801c03c8041c0c00000c14010072410240414221490503001d0110441d00c601110700c2002c40300c003c01c0c1d0465848000800c46c0758145002c04450301d4011981400d034260601d888a480c2e074841012a240803944400200188550800002c00303900c10341c003450041c0301d0759440041401c0080207800c1c1c210841d00828a01e0b041a5000304001110380b641da0360b510001602c0503080c060301c20596501600243d03001d50100c1c1c0700349200002e07843c100b400c9039900a00c0d044020704000041c8003081e41c3d034040c0c1c0001440e0000c0003442c80364296a2409410066503c1401c104003490441241c4000d04001100c04000d0f20030070b81e006c80c0858507060a0507415074107070f6031503041c24000450344661401c0a0010b40e294040c80801d0702a40e00e0a0155401c40400501c546540711418414090b402c2c0c0800d101d4410 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 149552931 1250 149551681 149551691
    0x3030f040303030c14070f05330c0a090b09010318050a02010f050c0c06070501020d0c1d0904111306051e090612070b0a050904150e0901061503020705070f0608040b0109 74
    0x38116159046e030703811580050780424202501c3c90700c9854540c0400704800c0328480102100005880c00042411100001d0007607074440c0c40e046143c0b90380d8010302e041d01022031040c060621842c0b403c0342c0903240490b030502d0b02040c03090b42444901c000e10b00f08c100544907a04a035288005558228001c0002103016144c03040c078080b05030729410b4846409511080c4588000124641405025010b482902144102c2004200507090024056810003281c0d0b030720320040a800003100d0b1402c66046031090750001180034203a1048010002102c04080554240a503030b40c401148075151800c40e2030580048250950290030701100b0880580b400500306485203001c0c8010410482012131814112002e008078261204001d140a030361602401c414160032601d40fa0384d40702155100d0716101d08070b45280b1400c16081d2560003c6d182030f91401e00540c3d0112031040d2a03040024443d41c01032070312038028820303a9145500c40401c6680c8607071f103901c004005400c1c0028001030055101c050360051034103e8007080 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 149554181 1250 149552931 149552957
    0x260105131112010906050901050f15030c0f010c0c0611070b0c070501200a050307060b010c11090703020d06080d110303071407020d051005180a02030a060e01020903030f040303030c 79
    0x50004500300da5580122400c0c100700c0c620321000d40005804c1e41c0e020109002c2d0386402d2007011300810b0121001e4220802480c046491400301320441445118050003070002040d002e020f006404032400d6003141040009480400070402d11000b0202400643d41d502c102d6a09190240b45001c82075008024050400c000301c2858001c000b400c802292028241407580d003074030385405002d0142000035100c46010300010101080408002400384a100d0705003040816030807001140c141c00c1d4a24003d0107001340389013040391403524030000c82d407003521450090325100f1401c44000580f203090b800818240e1045102d8142d494002c0907001d4000071982c025400d510f03000d4030041811401e1340c00f00912100016580c0199120140c811200c250041c01310781050300c1312606200108400c80c2d001c80d60652582902107805004650140702d02e0f0001c005002030022a1503200050184072800d00c0250f50030441d41a43e500c0900c061701d82c0b0004400c142c2d850328614100501904d02c0b0300c2c40c0c00100304050007541 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 149555431 1250 149554181 149554193
    0x20a0203240a05060f03070b04050108070518010c11041a090c030c0a030902030304050a12020906060c0309040506030304090e0a0b150603040f020d050303100518060f0105070c26010513 81
    0x1a0301030540080030072144c64100105041482c07034510160540a03101011a0750b2020900800450710300703a84d40c18103980e91250444d801c0c0502811040d6002031030b0f0f520f0269601c84c49140440c9401184000ce48003401000079040301d00f0503000f24640841008001e807140b07041a441c95000f43c0c9076810364518500040f503a0001d200e91001d20080c10b507540d0303840c019034034104213407809084050900b281168650303d80c80402c8070364100c101c1c411040c460001382070341002d01c1503402c000d41c80750080d414000c2010801011b0b100041c1000d8243c0b006100c0050785100900800c030b0303c000700c00c002d0324203640c80b4142504026401400929841a04002e1520a45030101242e50154000c80c42d000303020050303c009140d082400320701a15030311021042c046981c903120140000c17503108868240c001d1030904182619180104d5900c2c2d40180741410800541d405540102001e0784540e1580d0081502c13080301c00c0c000440080140001045062090780d92403091192980208030030701a0509901c0c1942c40c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 149556681 1250 149555431 149555503
    0x40e0d08180d05030a0c0c2001110d03020a11010c0801031203090b010f050301061a0f1c02040308030a0621060c030209060301080a0308160c08070809060a020a0203 72
    0x14108001520300000c0e8103180c01c20700100c107180d1981c165000803864210040c41ca40003510707540d010310302e429442425540240302c803404180d0f20142e40b5035108003819025104064004d5241d0500c184800d180c80048401d0104480528080e01c006884a088460081020540d00d405003444d80c946008032001c250000c07521411207074845c0301000d45160440d0100c01816030300c0001002c0000810021800d04070035406a42075581c1070380208061541e411000b0844084000841d90100b01080141843c0c58004024413080c40b4000240300c84151080400b800c9a001d81d2003612018004000d004002600e4041c480c01001101c90824035511110a130103142ca80c48a0024a1340760344504c524000b034000e4059866044000f44029225a9554681d50303d5071800070f002c500091640000403031224000095800d402c099544035901c0d901c05654100c0c0d5540b129405a0b0300d1320060002100a03034856004202e407101c1c035800b50a0022080c0706161916040f094145c00088108403000300c81c0100d8042 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 149557931 1250 149556681 149556703
    0xf09010e070f0e240907051c0605011206031707030c080703031e0501050609040b04151839020307020405010b0d051b0702060706060e01030b0403090609050a0b07020310020c0f010605040e 82
    0x1440d006d0b180c0820541d1644110705a600300014400100c03550316169601210880307200383c031181002c000011880e82107442500004144401d02440556050b500c3c601900745a842400c20710900142504c0b541c1e400e8006210407070000740c5403003600301d0000c3d9803a50140111022807084c809941048002070301401141d65040c000d6030354a00c180071a03600e5422000c0c0c0c0f84681c0018040d40c40e00c07050540517460aa402c804030203401d10410965650300e00a00d5050040070b1042d040f00502c0d925203995240041d11880011440180300e03401c0582d582e0700c6814000c1c00d19a011640e91018006907000b0703598028090400b0b09a1005441100c0c5009030485403041da04540c0182e5030603070f5107051001441550405280401c41000101c00c10031540c081c180940d00035280d13820000d598031000c90b80303c502d40c000c0781d4010501c00700800110143d500075007242480282594403144050241d24101e800c145054141075206c2c4291100003082840348102a0000b0740c0c06100240c0c040c02959551400401c0d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 149559181 1250 149557931 149557939
    0x1020304031e11130e12070309030b0403050f0a09060210050417091809010b12070305100911120304050f01030902180c190c140c03060f09010e070f0e24 67
    0x20010000d80b0210f00c0981c0780e00070041000100d2100410b03005000c83c00c42060710b8440c6502e82681d1a00d154203845150303a0540c1c614880c0e80c1590345914450300c01400440a0140c107000c0b03810f46201d0540a44000307140369980040d841c0ca0321600902e801e103104401e011403032030a018440842c0c004000400301521100c00b0556914542001c1482e1603141342c402c0d65583c00030018080078001c190880301136201c0855107008140401807000303407212843c5c030000300720f50301a80d8900c4001d903076a04a2203100c1d002c2e1a00d003c0000c001c4010600341e42404a8411040e00001030501c820f00d407c0c1001c1e0710400f020320b4100f20b95003069011500c801d201c202c1d00e03503411404d1070004009200c000d00311010440003c040b2105903410a0016241a640c21000c0366143c100c09a0007510400002c0c000c41c1c00807004005080f503440b1040d0b180181e0302d000d00403e25a54940d6107030712001d40c081214400914002c245010350a15064412410280203041c03d000c0c4001036071108401c02c1012105442080111 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 149560431 1250 149559181 149559233
    0x60c0c060c0f010f15080d090509100504050f0709060e091825090b0f060d0c110a030c060b030307030504030b0a06030b1602070b130909020a090e030a0e0102030403 72
    0x1803401e520742110403020000660821003082d040f4030b2113800c0324101d83d05001c40000b02c203481c0c06e603407038840c00007a524400190000000300198500f40c01c001d0741109450056803105501ca50210342900c00440c2c090051003c0c4100788014240d01030556001803050b86401030014181d040007a6070540c0203400103801c480d03010099500c1090a00130550b10040d4070185000042206102c800d009200344500032082e89000d031b00303821030b00701100e42079050907000f40301914007a0311540b9180180b211905c00400c220802d1601000d1160400c11980054000c1d1200030300c0811600e0b00030140c070341c098007090094200707010503800a5040410344040c0c0f07501c104580034a6a82d40502d90060000c1c2d880a482c1c3c4841c10140302d034040c5900c3c6050592030f159425602e00c01d0711458400310522841e010750306801030b20841003010f80841e9104524543c8010041d0340b405039103100040503a4000151180d907a080042c1c0010351940085003500640000c2c00518101032840e19011521028031400221289001c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 149561681 1250 149560431 149560447
    0xd021804051303260702100f0605010509090a0b090a0e10090309030f1103060c0c0d080f0613060803030f06180906071b1b06090b180d050a140607080105060c0c06 71
    0x6000744c0d241d200c04444e400721441c07a20781c0e4000c0d0f0300c2001410403400c5070328000b02c10070100b805000d0702d000e07104103855040c82d04c01c0810510484110040242c602c0c25a140c0402110740c0d14140b505008a4060360b0108203142c00c400c0c0d8a0928004e07a165124242c504809800007075000a04982260703041704012400900b9030520740b141c1d100091100394940161810094071800e020043d00c50264031504669400084480c1511858000d43d1144001e89040d40052030300c1c41c2c50001c0800d00d4044060102d10b640d83c580c0d4007451074000366110b00d41195035004001c240e040040590400b048200070909841c24109261500c40c040038003040c04000a80042400c621041c680c000c1c40749610036030b501c0c110740c840b0044e0081100140242c03000500740c80c20004910300803009a5010302c02d030800c04641c0c0844d103001c018102200600403910380c011007030303400040744041000c1100c0080c14409006e01d031606000040800405801c6103104080c180048950204002460b00403500c09030340f040d5464042c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 149562931 1250 149561681 149561717
    0xa0909020d060e0321040309080c01091701020702040207060f0e0d081302010e270c040810090f0c080604020301050a140f1b0406020f07060f02030a0e0112020d021804051303 76
    0x3030f4454850f42281d0142600404005ca03e00c01845503001e81d88131003800742c03101d59842e125107050b070328140000c410071011300c4050b240380f1001000b916040001031410b1300b198045000c1e6004094150788050f500d814440303440c00f95009016844002c4c4024006010f405000648428409810b861410f4840c03a441401c40e40504850110741c0384c001c11021058100410308030348113581d4200b9003422021070000c02d061001c184292400e0350081009402220f400c12801c100801c103d62065418414510542d03020844840c2c1110151290102400c12481e050041c9400d50f48040c1004401d5440c202c0c02c5a40321810305516031700b0502c603031140c82203500c030702a81c007140d0a03c0160300309507220300140002d1801c0e000039140c07041440e2034094175000d1f642c404060340d4616a181146000d40c10030404c00c5240c611803000c030340d604001414010490310351400d07034104a800c517918404840364005038621020603000307044c0c01142e0342224103200d10b02d060740c8a203000e0380010301c5c01014010b46080c41c0f011a01 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 149564181 1250 149562931 149562937
    0x312090804030209041203140603030d021309020301060504060815090a0b03010608010507020a0501060806060a0b1b190201080a0b0a0603020714100504140a08041208190305060a0909020d060e03 85
    0x10f0002c10b805003a08003070030309003541c62a080c20b0f0b501080c1b6000d0030b0b0000c1c0c2c22045002d481044010051800d220104001c00c0103944640e00c03040d15412201004a84e0402d144051806000c4a6403495200c0e0304101015045810103828128048204000000c031541c40c041010b0b03115142d25404a488184000403c3c0980303443d030000c8003154280300030000034a0340018403410507130041c00240074950f43c41e0300e16a110f00d41030b01c0c00354000610107002d1080070000d4004000c1301d200400c5403c0c00000d44140f030340c1404072040003040509080300c0365006560b445000103801489010302000542401d9000501c4c0c550f40c1d00c917203014940c010034003c1c24004d100c944441324010040030303101c803403040d41071100003040b041310101d034000080ca8104d20301440000710070f008244c1c005034991600341410104480c00c44500c00c12900d00f1030411511040201c82c0c4000810340002d43c4000c90030341442420000c491050750014040d4074642004c3c107000d03035680b2200080d01b40c0c0241c000100c4441295106003188 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 149565431 1250 149564181 149564183
    0x406030b012616110307060522030306230310110702040516090b031608250e0306010603140c0307090305060405030304060c03060303080f091614040c0309031209080403 74
    0x1002e2881001490301c18000304074441e03003035030550500e0030b034100744107940280c003500c544849640f080c081500021034641c442a0131900c1074020440305100c4081c2100c001041080c2280065111141048150700111100640d901c80941d43d0120380040c00102c1e42d1412400c68034048151074040182103052a80d0855801d04e802900a121501e0702d00f09132010140840c0610700000c1811000207004410f03130050764042c1d642c20004030307140c0c80c03039440445018101502c9440b0b6540c20110807141d03240c10100d01d03041c01d1000d448205520813024100350610805038071440c280350800120307410715510510042d50100361007800c55100d490f002d40072204444039400081642c4249403e000501800001861140d03100d020300384100c0042d82e1044040d1052880000d0100c0e0700c010104141d0b18030120420390004001e021900030010040c2c1c4448000c5803540410030380c03420000300781300c90b0815003d407240c00020350400b40300c10b02069400400a4605a900310031807030317407504040d00f04042581294015 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 149566681 1250 149565431 149565467
    0x10e0303120a0b15040f0b030709120201031811100807200a1415010504090b0601050a0e0303040f290306100c02040911090a0c050301050d06140f010e0109110406030b01 74
    0x82c445104400482da0300070300850340d00600c6c2210010740303a03112000b2284200c80c207903511a40e051904903da006005040e40c00c03418181c54081c2c45030707040305180036458070601032142011030342d0b43d0030144000c400101c04180c0c10031456400304016640c00410070a2181c450b601111001001030001c01c0c144a16084000e00c1c1c4054a01011019040001c004010b1150340b0032000040c0da03a03108000407604143c1c0d00404a00101001a01c17035030044c006807290800606060756407200d21000242158031030b4000c101c0c2005403c1c0f042c0f1640c1c10b03c21403400003194851802d614030b0042150f0702407078040101407034481c05108802ea00d8483c855019209c5c0c1640c083d00c1071020b00d10926000c5042122640c120b400ba411400001c1c002c0100d40c040d440460780143c9825107140d00301070601c9030802d600d070b9080e182175403120194070484180301c1d541da1203900481d100020650600d2140b80810310113a10072030f040c03070800801c0c0e00c00000c0c820440c0c04564050400082401071000140c0da01e0687d150f0b04030388 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 149567931 1250 149566681 149566699
    0x120f250506070908030403050d050f0d090606062006060d0f060203071e02011401091a190303020f0f0601060c06060e09160f0f03080309030f0414030c010e0303120a0b 73
    0x82100015915000b41e406440e002405900c46044c544d99004521000d42a540500040320105014000a010300c0c58005002c0c0d15107502c444404069610300c1070201d42c8240c1d50343c0200103281c3e110710203c2c0414444042c048040e0202c490296803514040c280f140f0400c0c03070f4403c0108100b1901e00783c442940d44031205546902c1d090030301400a03007050020080d00b0505600c807415291061085140c26584003180b20301a07400c0800103001008581d85400c00340729411907403c00c1e6030b24140315590006500040340d400c181113280082c20101401d035000e02940c4400c8002c03902c0ca2011075102d06640d610300d0010100302c032504040000e80450b41c45504100464801d20400300000304200c0f01551221140950656540010b580310344018811040400c428035401d1001a413802c0045402c64070200c110703414507034001c0003141250b000303a000e446109021a0750310b40318101401510704481c42401c200c000b189407500826103a204076040c400440c1c25040010b00e10300c20076400418242c0f406845500 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 149569181 1250 149567931 149567933
    0x60c0705180709050f0d06050c04080a0b100621020304054b0712020402130b040608010807050a0e09100606021515150d06080109150b03120f25 63
    0x4030144060b105031000940105000c6941e082c002e901201400380034001d400b40066540390500105400740020041000810000803191000c00490034501c1c0200904405404c01407400310300c1c14069880b013401d203e10461030340103c1c000c12103070501d424203014001da40c0c0e42e1985007141c00c0607a0840010400f140c10390b007210780042c071516204504030005102e0700001c080100000f1041903102c1044045a01c50341007808806085000c1285041c8054005414025141c40d400c81002d15504242c00104000c50708000d1280d02460703803030040941c40050203200c3d0a00001c80c0702283c030f40c082c2282130b00940c004205a564104200031174890380f09020401d49440b248000c4d11351201c00496a1011100c13404282402504904580b02c031030002c091031a4038505180c0141d054204160010103e039890b0303000181c0301c40a024072283d0503c41c0d1000c8000d0dc1100e51300108544118540500a900c905140d059010f4900c0484c0c00000040302d0068959904001c40800f803040da4180003000c4c854000500 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 149570431 1250 149569181 149569219
    0x403030f0e13090308070c020a050103240b03090d0c020a0e071101050c0a0f1b120c060e0610080d0804140f0f060402040b01320c2b03060e06060c0705 66
    0x481e039113100c1c0e581c4113655101e11170225804203000300c0c040d50101c0e0001d0100110360080e4000c500030003040e02d90842000d00c40410a50040d215407202c10104030000c100801d059084c010000c00c401c280c1495001d03c01250040f481d81e510038022130300010252004a5040ca000e4840d161001c0c007010001d108a103043c1107501226004a5080e03808650061000304195000b800daa0065041c1d050b450088202292940c0e9161000d00040034180b10342d50003014045481c80c00b0b10038052280c0c0c80140903900f003282c0e100340c0c00d0155501002d0103810003c4a180310550040420390040c3d0411000b0710300a4800008504200048011b071480e4412814242c100060104405125a000721000c0104021043c010340b48502968402c0c01c01101d6440403e1159048c0c15076072003150384401c40f4501f402100c0a245182c01c01208140d80c02d98140325001c0c0b498480c0c03001030f00440c11589018048a490180818032a240c06001e4a118000108035000d8005040155000400d40140300103001c40f040a008 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 149571681 1250 149570431 149570441
    0x61515030605150903190303020702060c06010602071a0a031a0607050c27070309030e09190c020115170a0812041101021b061e03011502070f0b0403030f0e13 69
    0x10b01d0151102044002d0b1441c492410703103040b0000a00a060b4000c041d0703989846c1e804e0402d50490038103500380034000158540300050211101004020030b03155052103406886d106566110004460030340c0700840c0f0207058201584c440c42d58900740850301403280008030541e100c021007426000000480c10b0018400300080c03030301c94601e05071603600c0235450304643c505404c13515011509040c2525004140b40e80d1127603014001150091800c000f1030b040f00400030780c4541081e11102500c2c13000c962400c40f0f4010500c15460301d035240d80004c0082e2605804101030090a520a20445040e8800364052405040c0151b20109511a610b10358845c0151244444d8150940c0d00b07590103645440d5a9a50303500004507403110307240d045114413082910b8020001582d07c44801d5100c83c0d0b551341c00010020a101000e18040c20300042c00f4907148070200402860322890758400303928194030360010000706034540c003241c1c1626018901030001041d0b00c101510040f000d6140981c00860101100000e4a255400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 149572931 1250 149571681 149571689
    0x3020a02030d0504170325060f090803040b060a050307051314091e0d02060103020609030c0a08011a040501050a15110a11090c031e06030a05011418030403030c0615150306 75
    0x612408030180c4105140c0d41e000d020b038140c1c90310111b01340900d41e40760041c00e40740602c8e205003808981e000f00b51400c902a00c054400441d0083d03000b00034031003007010709048075621410035100122120b14140009558040501c03030a8010008000b64009813880c5401181405a81c0c0c0642d03815410500b0035a5903921102d03a88405906440c0300d10107810a001c42da10700b01401c6940104071036401e507000c00007154030004400342e01d031054100242d1643c4030301c129031005000b902c00015a0f040e803042d8100005140040c03c0b0300c00c2d0b1921005100640e03420071101c003501e502c0740c250300452003560015145802c0c29425208907200b4400300e0000c000700c1c1c1c0760340012140300b5180001c0c0d54035060030000d960301065035074003602c01100700c45a5560341c41c90125a80414000c0440340c0000c4030707444236400c4a1400b4507640304600310f80c003040000054401801070510a110041d8035040c42e58800400d2801003a2000745001d4451141a1440d08843c4440000c3d042880c8031180e0441d0245000c2d00502c240e2003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 149574181 1250 149572931 149572949
    0x302030a141e0f0c180a0302031c0806040b0105030c07080412110a0e0919020109091103090f0d0f030c03151d1605090f041104030503030403020c030a0305090103050403020a02030d0504 81
    0x30000708280700d4a000b29000f04400803c09080030700142003607440c402980205c03904110044000001340e901080b07026414070f00b00060024041e14068000c14404000b0a141d004900f07000000003240d901100b1a5440920b80076115140c16003841d00d4111485031790300c84034070040c0c0103030107a0902a4a00b00503118850448031282c0b22640c47c20745681074030301162620600d41000d1100f5240080080d42d01d16001d00c140f401082040d00d039120241120402c010b02d068282003c001c000301c1200401010fa451060240184803002e40010000c08001460030324504140e01c40a60341002c502907040041c0e1000000c403040c00d0952191982082c101d0002c01080b640350008000c690000702ea030b0072451300110b803595a01c2c41c14880c0000d10000c2180f018129800c6603540c507049102c021003501500156110354040c3d0358906090800a103007694041c111031194112100c00350000f900b1804440b6a00020700700800c49603114101a4100514500d02940501605036404500d6502c880180103070303a0488 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 149575431 1250 149574181 149574241
    0x1020715051012080a0306170307060605040b03030f0d0b0916021009030e01050a09050603160909020a0c060902040e1f1109300a050709060b0304050606010302030a14 73
    0xb000d2542034855110700d89a02c4a1140702c0004504900000d00400880b402d01080d0300395255518010003145200d11000f541003c0740d001c003000964020403008140c1120103000544d986400641c030392007080c203c0c25104000098040185c3c0c0780e5003099043c8207000700011810320700b401c039101c035100020b03d030100140280030716004100000d1054103a03032a015580d07040e020448000544450f802001c1d90004d1184a00e800101c81e942d840c0210311820803041541246980404080c04044170b5408c8048214010320004600e183e024650031141500729401160302082c42c00403500070300074642a1400c50060b150580c0b040c20720604115500d04412008124806150b1405016030060030280c96012080500d06450b00f0726540c603841804070f841000c080030644054095180c121315280844954000e040c040244c141548506001403000c3c048040c070307608e810340c0c6440e107900d001064581411b501202152403c4d000780d00800086d9586900c010907801c1134a100b1038180d03a8001d442c00c9020701d01c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 149576681 1250 149575431 149575441
    0x180f0615090f01030b0c0c011a091810020f0403080a030b03060c09180702160e01080d0801060c060c0224010906090e0d030c050f0f0309010c020c0105070f060603050102071505 77
    0x2110031075204140e0b003a9041e595900f036a0302c16a040038041d0642c0c0100d4420f004d1910518000c0c0308140341c00c01d03400408800c11700d0b18000d203d40b07520300402c2c041c5c441802c00008404960301081158400407110030044e03031100d0019a80241c0e00464101801940c800b00d40c021809825a00101008104908031003440d660849109090300c52010f003190002e0f600054500030089060001e500980302e0700543e18080314810381c990942e5001d030300001480f418100100008030b018003042610103868581411198104040681103000b1503100410555580d800201c0440c400d10200c5408101c07220301c000c1041007400c0354116503c0c2070140610080c5001e90001c0c3c00070091098003041c084400207070000444101c8103600038003801c981034080c020100f103503131040c21a04000b03080c1003d1026505880703080c883d0b10b460842c2c60031071084c020741d8040c0ba00d0300c1a9a8018050360b41c0c25602410007100c0500078070340400901f000303510007401507001262820803c06010117100f501a9000e4080100b5564 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 149577931 1250 149576681 149576689
    0x3091207080a030507020402040b03090d08060907170709050a061706030c010e060307050403020d0f050c09070210020c010612030201050f150a030807020d0c0906050f0306011508180f0615 82
    0x30511981559500200c1c02c000000c0c0640003030302e01700e800248014101580d0380e602c150140e0044947e407106412507076008600342c1d0040c07034043d00481c0c16612034005181599010b0843c1003241481c4541d8100500050f5401c3d1143d007210015280c060074500120b603031000003070b00f01d0309442c0d07010080c00708150000302c0a0500040035243c110050751820000340c0644c013400743d594805450b600030450100070110258945000850740a8415000d800520500d824058204011990654441c0b640348003802100b80c0d0003e008284504212401a9211900744480340148103541c0094007030b014000b0b40d0000e0640650010344690a002c0d02901d8035507038818010203401c550700400740d0245086000b8004135603c40090b0440c20f2014120611040c102d03200c81414500a82c050b2003c6d649031f25081c80075082416100a000e48150000c020b0741d4105090708454000d540010b0080050700340000d40780045443c2180003064201081e07038520ba1781d005480b911003201316003030341d0341000005050b1500c0c24 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 149579181 1250 149577931 149577943
    0xc031009021b0724031505011107030f030c06050108030a080f061903200123030a020706020c0a021002010c0e09090a02060d06061d030604060c03150b0d0b030604020a0e040320030912 80
    0x180b499140f60400c0c7c103210041d111821008102580742c07142d1000400024502032038429011300a4481e0450340b40c1300e140c031303006949050f0450f07400ca80013441031081007504018080e070080060079040d41c039507858001044101107040a0072421000d15103000050003483e441c1c0c030a1024020f0b0103040308000400c0103403149100c40d000e60101035151031340308810f00504000ba540140301c050026245c90025200c11013a80c0142590120a4001703140560851a2080320300f52191141d0000b84416004400c0c00781500f03104101060190348480000f43d41c4400600a0081d82603000b4019600c03500c410b0200c2d0000c00c40c0f4040c00000c5050005100300c007076051000800e140e540200144030569031541d80901401c41c81e2504801c0c075441d034058604940300c0c4c003001005040c00b690900d46623140384100c0015100503543c82c03806a0800824407000d43ca07203451000c1540c0700d002024000392202d00c1c04030340020001d101108020307034260166110300e030040010010f108003280c804441c0404e08090f035407548 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 149580431 1250 149579181 149579201
    0x30c0506150108040f03030b0d060c08010e070c0b0606070605100602010e150703021c0f1a0402040308030714160c0302011710090c030b0901090b090c031009021b072403 74
    0x140c0700c0f2000900080203000040c00b62842440c000ca000301402c2c0c04210303074441c0c03040112525a12052816980b80d4000000ca0041400003844002824424800b13406219140c001a000754203090010b45c941d1928070440300143c0c0e00580402691502442075059090b041c041da0005500b06042401c8084c0c0000d04038410b41109000406551100002600254840807124981b101208122074100c0c141d44140e02004070200004030301341d80e60500798001c10002d40c072003d00c01c3d441400184041080700055a911a49038100351172500c0c22050740c0c111030300611441c041100c503421020001c100c03842c410282228800c0c0ca030341804a003c0c80002480d050100c54806032191180e0040000080607000101c1c00103040c18001031090a4401240c20420309801c0b072031030b00b500c41066640c28201007040c641d04c88c203e40c205a045042810f01c40d04c0d07003030680c03013134014182e00480e03405001800c66480300300a40081c1e0850340c08564400464010142039968500220a40c00440000780c0c040d000f071120302 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 149581681 1250 149580431 149580437
    0x120403120c050c09040b011404200901090308030108071a0a02060718030503121005031b0d03031e090203100e190624050415260f010207030c05061501 66
    0x524000d00100c03003000d09030605442e68480c01c40e0540031529080c054a0083c2c0c090f45602c9a5581004440c410813612864007034004c3c0e1421031011952500e01c06007071401c2070340c8940700d55150544d00c0100c070000340c1341e000a072106400200003d104100002d5420884024500034004442007083d00e0015029292208001d41c1281d00060708540c400c080325200d00080c0440101096103a03200d207403441c1c1111b8190450003886000b070040e0540601407910081004070000c1241c260907059103400008001a00b90041100c50941802c040c0203800c600940e00e120f1207107141c100c5d01c0340c07001d4007d03100c8100d0036800703401340042c403245c0301405025400150407040010181e961500300400d40741968640c0a480c3c00d5a20a2070b1201280c600038120380755000213203020b042a04007820403003110707111503031040d1694401408010001c0103240d1440000c850001c80400b01e000c2ca03c1c00f40c01c004064007414400c0d44000b03482030425810814021055004030304494a95480140c0300030310200b00e10045002c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 149582931 1250 149581681 149581703
    0xf03060904060e01020a0201050f010e130b060a09020a050a03060b090a2310020714010c031e0905190f0b0906030402090c0d050c04090c080c0f09030a02090f010305120403 75
    0x2410300e000480c0e0400d1094100180f00703a0f03140a240d0898111801460041c3d4407801404003131800d00550f9409001e88510071301160825000b04010025107c100510301484400002d2080d07035016010001003500403825561400010740042450744440182004a468a00e000c034249515005907051800c01601d901ca0f5182006494601d00e0f40d855040c200d0408805488115030300c604881905004950b0010702c20326003410919281400d580d5006810400801100d4020035401503880c80d910301414000d48c00b806101c81d04481e0180707180c000a8121990f0200700307050401c0540680102c0f0031000c40a80e10ba61074040b0040b85200d030b00303010740e800345050000c0b9000d8030307010402c141c01100030504c81d80b0b0521412401c000341c0700101d541882024020500b0050304c40e150188442d0540d142c40d200d05586003454880b20240103003000c182240c80c01040070084c1e81c81c10400c107542960024002c00e007501e000d240d00140d07500c09000c1100d40d8000c03002040c50307156801b02070385c00352030f4030900c1c00300 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 149584181 1250 149582931 149582941
    0x1802010905010e040b1302090a0b090604030b04080702040e100b0a080303010b2a0105010e06030102070b010b0f070b1915060507151805010b0324010b3406050c0f03 72
    0x30080e12009040c2c0d441503032540368600951b10380c92120600c0c020900e025880d40ca6a004101c40d821840e840704d05505010800441f455546c5c0c0c0448064036800021003666866a04008090f40520f02009401510703209082000601c00224002c0c41300e40ca403000c1c402c00f12580d05011a5100501c1140d880354070500c01031000b0310315040504000c0240e4174071240c0002c0b40380710210212089040044807170f5520001031018a03002800180e118109400940c41c00460790f0710108010307030521034a440e210f400318500101040c5041102c04003904000032401c0350030a060612140c0000c2c81040c182541741803180f007030003041c4102000072036103141c0341c40d03003401110340303584a807940e074203017400707420303990307400883d084c0c3c0e4603070a0164101c0e00550000440c0c0d4251410300d40b402980c0c0c0c0f0250003003c070001882113800c2000e5141d40c155803143d6202d5071940c0d10795580b8080c030f480200c0d83c549001e02c5000e101c0c041d611444484c0c81002c1c0220700500c603545038480410814800e90040c81c0c040f200c20400a0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 149585431 1250 149584181 149584187
    0x13030c080901030b0a0e04060c03090206160203030d020a08090706020f0709020d150b0706110906180d020907170106050a08010618081603020301110a020309120c06040306060801180201090501 84
    0x1a0703201040c100450054035860014034403030b140741c11003800b041c80c0f0340c20300060000510a10b0402c1d13030b09041c00c010030340c070540001d403142c002d07603207140e07070380c5411607580000c40d00e0500960310320f0781c6c0000e015901e50201000140003800116016039403032054010004580d840052003810682c0c180b00903100ba00e0529414502030b5003c02c4006c0030544d00e074507604040d252010007200003000011001a00c070015442c002081d60141d12842a0003d410321014050383e88810485262800049920038041024404030300780041e40400650321150140800914941009264000c0449030002c20241c3e03884000a42c5d00d802a90f0070760001a41a01c01488180d001d00200408c076003c0f032680400312035503a0007403840c0045d92602180d002c01112010011804c0034082c24500400356914103040a8550300001e40c3ca00441b4082231103050000c24041804d54140300b141c10301c2001500080c1e03181c1d20ba007410b070050050b0f071144960035843e0403075014020218004422000340c2c141d40304009076103808011 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 149586681 1250 149585431 149585437
    0x70b09060f011e0f030804050f0d021e011b030201060e0c030103030f0f031515030b0406181812020303070f02010506130f14180d0804111302090603091513030c08 71
    0x1078200e407810b16008102c50055609071300080d0f03c503800042c0c0d03d604040601070360300c911021080c042ca0702c2400b031000503070725130302425010501008018481d02c0d1503070048481c0c1030130140c02980405441c0c0c1000a065043d0001310036615241c190040c40e88402c4001a180c0c4800d06c0040c002076444018210454801e004031810b500b103600e00840c40c01c96140150070f091040754442070742c4914649201c0c481d9500750017a980001422034040003c02d2400510b0f01c81c4801c145c2205001d02c0e2b90300078402403004142d003c3c100054011440b002a0003400c20003941d2607206035102c401107a03400c541a80c11a2050145038070684010785105a8090900b81042c007401c1540ca0700c00c02e46441c0c044200e41d0340c03040f01456103d000d0f2200008404441c0545690030900c10b480b007042001b20400400c00441c0300607401d03004a8074203451400c012503140812078002c0c011402860350000c800000c2c420000703000074074802c0341400380b00b00c001a51580c0c1c0e4214010342141c0d80c010041800c0a941c03c02049030100a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 149587931 1250 149586681 149586719
    0x606090c04140f04050f0103020916140703020f030307030603031715040b01091d0a060608010b03040807050309040f140a1a0d020a030b010815060d08040302120106030b0c070b09060f01 81
    0x115143e0382541d40014058130000c81d29816130400c528010415450b0546850707070015400d1040b18407145c00a4401040c004100481180500d0001150f008140c8200103420040c41281c060b0380e203d0508040040141880b0f120036800200800904801800e0302d402d414000e680c402400c0f4680c82001d404d000140c0000003407141441807103d40052010124403000c4c0c22205203241c0c901003072a0405031801210301a4000808001132034006014040000003101d0f0080c0d00b016100e500c0c1c040710b291079880d5110385c46030160058204a0390b441004480d42242d24094240005043d13160f8070036030050112580041e04510f6440c0595070b0004606012207100e00381c9001810708180d99849484003400c80301d017a23010306840d901400c0550f08041c10130b411035030480e0b8115809038a00045444008440c003a81c000a845811888809050740c41d095011800442e407102038501d2520b00600d040719541c011000603203440d0200d90004040c0880800c1c124444c6d044030300d04081903424404610300322084509 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 149589181 1250 149587931 149587939
    0x1203040b150909250317070c0803040b03040515060f010e030106090509030c210901030507050c0f03041a0f0414120a06050109060b0903060103080d020d0f0903020606090c0414 77
    0x110241c80e0a0215403040c080c042c010540c1c1001c0300b20092850429103500340c0c4c1140d2040050000a08420a0f050401c0e5241151501d072840d40c20010180e004640c4100518440001d0006a108440d00510b20850190081d28010784008041c0040e00004480c0d03158400fa181040c0d910641c012000300560100140c00052065200e0421500b250310584068056920100b81c803180e035503041006000c40c06000915030800d141e5100c507540980030700e1300a9410b142d02e513000955000d01c0390096a6450810030704807050f8540c40c0f0080c0b6100e03030180c001c1c03949006894a02d010200c2400c004c0750703030090000084034680b5140c4541020100d400892080c0d101c040000c0141e045441007000c0e0004600640c0700250f01c0d49465010811903440d640106940b14080c85404da05642c04601581100c1d0010944c65a562030030b80008028415024200065442c1c059043d0020109600407414036110b6003c071203c5441d85010008243d104460300e480311101003100307006981040c5054196001d001e0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 149590431 1250 149589181 149589211
    0x50901020c1009140a0309050d1a0f01090606090b070602090402041a090301050f160c391a04030f060b060c030c010b01050f09041e0e0f0f1203040b 65
    0xc451504101c800d14110070115150384403681441a180303000701e0340800780801080f1700c3c0134640c0c0250216a25224540c46403500c200d0b00c4080c440d0015908149a10046a03d070720340c600000b1168800b0f4081c0904a00f4520307125000c1030070b6000c0d060b400181d90403040181d04111040e030311794000e0740c40483d03c1500190280030000b120681c0802d80040f8146041038aa2200c8401d403d2500b110b0000b0030b6007104c94a62003e000707a881400c9280c022030034040c644949252058103203030381c1d04043e50700300b45455008210541c817001c4119000c020703a40080d01070205071540d14500c80198403820740e417a0b01d2003007042000708000b400e010210740b14248124004981082910001205600058200b900c1c81d0400100d4103030340c540031700c01c84002107402d0034000d04008204648001c0c601074004904c0c09955504200000d01002c2c079250560000380038800d000c0941c810a80c135071288156290351055125050600006000109803041c1e041080400e1600756626500d0b0300070740c0a8080d0500700050050 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 149591681 1250 149590431 149590447
    0x12070902040f0303031107020109090b040e0d03020705250b0c01111801020c0406030c18090203010f0c02070e131106130b18010507230322050a0801020a0206010905090102 75
    0x180058002480e450b0000703501c40b80341d03090180907100106940c810580c810888200141e80000c40c14082d6840f00e90005a580746010205000346a0415601c41c58403401c13043c401d00302d034140c00600ba118422400c0c1c407012039501080c40d680720f10380d0a030768841c1008a40d041c40b800c92440c01070041820b5102c0013081a206a024001d01d80c0d01c2a80011740e4281448200b000c1540c04215100305a04190b070b042007403070318549500d40380003118010389650000c001d0340c6082480698000008a580090003005240038440001005041039000c0601600448400181280c0f021802a02c14484c8a000e00e80c2446a6a100420700e4448170845500c0801030028810f4000f1542c00e102c0507150150700969079008180e954000c150340504002c0c1004000c03c070344c03c0007030042d808002200c1214001c48680042050603207003140070302d140b10002c4071aa404144c2c208103d4498500403a41c0c20741f41803102648802c00c0740d090f13204c2c3c41500005a030020004000c8016a45c1c03082da400284030300010301304000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 149592931 1250 149591681 149591699
    0xc0304090501080c10050c0a060c1103120f0f04050c131b08040309050301020405060706050601021f0b1c0b0708090715030b090a0c081f050603070201092f1207 70
    0x820703008000c03d40c2c4400b081600c03a0510b0400340100c2c1146060081c1843c240c00012a900c200e400c0c1d008185680b41e00300341e0225070041904000f80718480080e6902c404000c02c00003038010040320320804040c00301011032100d0103480c0c1c10f00d0003560004054041001710302c091101c800001c941a803440c90b60703045244204d0440040c40f5040d06119031341c0390610300f42410024a001d00e0b80c0c22a5100ba441003104025550303130003085810066004002094554501c40140e0800300c103c81d1001601901a00c5001d8140c01a0f008040c0070f0b400b1a501d40c540e1400b0307000359076140506840101100042008126024091288103510103400b1003100c0175a5182c10102d45a40116681e44000c41e40326002da40d0b03030b8a4205649540103030031500411000d02920300003004007101030b21030b140038440620384040703012590702d151000c0d00c80502025502e0914240090003041650300550b90111091106520b001645040c03811206c980410114803030224030400a105008900c2521a0b1049220010341c6100c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 149594181 1250 149592931 149592941
    0x1b03120702010506040e01061503050c1e040608070804080706050402030a14010b09061005041809020604060509040c03050103020a0b09030c040c020a020907030207050712031107080d0306120203060c0c030409 91
    0x1240e070001ca081d003081c0c014401515174904110f01c007079040c481c00b0300501200c0c2848545007840c0b40317404900e90b1500001042e0910070340740915403420144c00c0c05110980b0207002441100c2042e40d4656980c3d131954400c031100c03242a20f00030301004007000070f08081152900504d41281c001000d07160401101e503121461258103410020050f51114010043c41c640703104001d80c049007d41d1043c4520400010003000b034491409503004046980401500001140d4400c4445a80c0501001e988a4850101400a8001118007032140d42401140003d0034481d018003412a0b60240c403a080e5503090000511043d0002c41c091501840744040d47e03205a51a17002d072008004854024002001c203500511000e00c80050040c81414010041c241c001400007410000700c03500c2c04c8201582200a2404807540084200480b0301e6118220f0041058100407030828050b49c0b540c0c03030070081d0782d686020030504503944100180d170640001d0002803200010320300404070843d2000c15685015240c0400c1006c480b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 149595431 1250 149594181 149594191
    0x414060c1501090e01050405030f03090a0c0b04090c0c021809030d060e04020306010b1602010320191b0b01051306050d0305040305060f0906070e12010f052401051b0312 74
    0x181d524401009003022904c0b40c00c151254400c000e01c010314054507800d5691195408020044000100040100360103021500400c0c0e40144504050399981c0028416500702c3d00401030610315151840a0003030180241d08405a405400203040342c000c10034100c12084000c0c0000c286000421807400c400e6214403a01000d00340c0c0103010802428240141440d0802c160409003003240304200c040e206008031003880c2211a030900e0301146140d408421a10800c190420281b41d1050220f110000c0d10303031814803600020855079030410084030b59000310b01c480f20420000381c00212040018461410141c600d40d005541c07240000c543c850307541d000720b00c03480540c0310103900141011800388200f08050155603009405102c40c2c4010342443c4143d25200c9002400da171080c00303110290843c154544038030419503220742c0d8008100da07849413107820003c0c2908550b404a03040c0100c41c40314140b4540d641c01144c007207040c1e54003070616401402c5030200010100402001e40300600c44981d6a2002d100c5046c411 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 149596681 1250 149595431 149595463
    0x19050a0f0e1b040b09010e070302070602071214090d1e0203070b0307080114130207060b040501170c04020307092120010305060a0513020a030e0105040804030507080c060414060c 78
    0x640c1c620b1075031035280c02000000b4412418240c0040b21030740d6011400d030549110f00c482c042c040c1c80e040020b800174400c040c4002c0c05680045103860902403280c0311540403820585a1982c130641100c2040700620603c505142c0c040d014201c43c40c04200401c01c40b132030041d4402c403040c2c48400d1a80010349408200c0e0b0260f045041700008000245600a5101d0f0040c4107203c2400c00034078000c000220010f000018142c103695003c50000c0500207184c0101c00c404801030410006540c503042c00c68101d0042c1500c94000b0b1060711040c202509041c800c40e849021a075803040d4265081130300700c203078034000d0460070654021560410008501580341016540e6014204c0710307522061600050203a5400a0603039110302030240c0104910b8071013403d2490f41268002c33006a0380c0184107019070017440000d9450315030b0340c80c1404110410002e00e00500a5074016000c8a01c595543c1d40e41c0c9907651001c0700c0091304101d09010820284425280c01e00c1c610600a00d65410164044101c5140c8105003c25200d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 149597931 1250 149596681 149596693
    0x903020f0f0a12020a0206070803060f0d06020a02010606021207020907020f12031015020c0613030503040905010515030103110907030f0c1e050403020603040b041103030c010b1819050a0f0e 83
    0x4102d15000200b680c0d0750f650003d0400c0c455207400040d035074014404d01610710301000000984a50b070344d0122004015000304424800c041c0d40c18040029040520010701542c42c0c82404507040b400002d4070300407100c00901c1503107801c2c210f6003032041094025080348294070490001810340f0106000d001101d0002c060381c191245440800304203002c00c035921980d0406003455013110080c1c0d000c100040315250035150140d4440103846a110b644a413544060560b0002140c04120f44810f80c108074101d4200b124100950407a01c14070010701c0c0302c2840000c0408508400c14030b403900f404a90140e000e82c99050000e072500083c0171810a072000e0030500000524172540c07460591843d07200074040d20240346403150809003194040340c420311000d00b01402d0450588000744c10810070841d4000624005010f503621500003401043c00303814040d040500ca01c0c3c001111200410480300d40d10700c1503000900440000014805550051601034040240d103925494030104c410910300401d45590030080050003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 149599181 1250 149597931 149597933
    0xf05030a030b060a0824030a06050f1f060e010c0605040b040209010b04060e060c01020f04120303110a210f05091f0516180f06080105040c02070305100903020f0f0a 72
    0x1c1101c00c40812180f1408051000400341e035403010b40603920071178100701d2229060191711042c4c5001762518016601d881000300c0c6c041046081e030062402003442040005864649014400c0141403800509841042c210740c10401c0324030420b52022000c0040c1007141d001e0000da110384013628000c07642030310304141d10000d0000b18100741c1141c0b0300500507404542c2c1054244540108840c07405200c56100d00b01c0803481e186000029070441e02000d0240c0f08059440d50b840100d80e000320007501e000d502003890100c0450351407204c00102c99442c01d40f0398819880c2c402404840e110010614620f21300d2542d00c0c1d405c4080c0581c0c52040e24001d607600c4000303114505a07444609800c2d007600c200a03a185041900380100d41c001007070300c22005401c50800c2c13060202d91000c040d1200c8070310b82c0402d00d00300701403200040003074111107040e058400560b0103104005c04070809a0365070000b0b2000170210707440a9030800700900d05500c1400d200e4441d10650303805446c0001185e01c0e20089109079011034120305507040c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 149600431 1250 149599181 149599187
    0xb04151b020d020d020c040902120a112701050108040311062e050d030507031710050a120c030305090402040f090f181113060806041a0a02040e010b0a03090f05030a 72
    0x15030300480364401007450000800000391506c1032800c950340240d40360b43c40c01c0c045664804101640c041600e08440841d880c1e410001402c42d00c030480c09004c2d1109510340e08a01100151500071000c04441b80748447c0d10b44001101d0b42d800c02030060f0208008003200170064941400340c00d004007103031404040165824544540c0c50035100c1c2c20090341143c214010000c50316131845101c0556058140580c03a108181800d80c1c1044010161100c401c101c1000c0210229a051101c015503000f903906160701c03515a50809850180309602a1400325402d50400c0024031610041141410107040581015615661405a40d5003a042010090340312810803c3e0460305115415410403c01c5120002c05211385480d81c10f0585260928002c1000c0f03e4554000c24080c1c10100c020b0812404030790180c0340074182940481c0080708800905c2c40c29402184c1c015000c1c0c000c2d00c060720a114000390031a4a4035110440c0790303010034074450515440d10060404140c0c0000341d08002070181000c0d5940c0d02a00f1401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 149601681 1250 149600431 149600443
    0x203010b010903050613050c09010f0e07031a0f03070b13140a03020907050d060f2c1902090a0504060b2d03040807050c03061801060b07050a0b04151b02 67
    0x2090410076240b9040010443c0096810380107202910170b85a861818203010341003c008044140d08250310b0000091a444403a06041c1252480080d0001e192215881102038400a4076201d11400600404108500d4816001c240c1d0810050880b8441c1c0c0d0b0341c045180f044c0d00b00c041d0800a2504000c410404166080c1d80d03154000011184508030500351381c0000c0360560007910b0101004030110342061030600940c061805408000311402c0e40303e5460307441c00e803030741a100e041d4490b0441d80d1a240001407601e401a03401780c0c0c0d80c24102803003c06581d403030034000d41002d108264440454030001466854a110710805002c0c501803a5a40742a61050b15802e00320070641201030290000f100384e00f601f0f0003810380f500a40e2156001d030303480c062400c240e443c100241c40381c15418001d04041c000042000e410030103131101601c00074402d2a41c0e4880140040c000c00e40d003e045070b0010200e4500054504030040d502034464941205810003000f51403044a04440480185c44210414190402c0c1c0420007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 149602931 1250 149601681 149601701
    0x1030e0703200a1e030b130501052805010501090605070206070b011e0e06010c06180b0703150812040306021e070609202b0203060a020901030513030507120e040e010603020301 77
    0x540d0624a02c0d0608140010040c2e00c0042c00c10511b440100e401101aa0b291801032a006002802242010207082c070f24200307000c0200407581400d09010045040034003419040303500c16100c0c20081868140d00303032519440008101d9005404000502c002000c00b00386601a08061000d21141200c100c0c0d11f1030800c0168000790094120a000c002c041c3c0e9010341c220103040d42c01240810f440304d0b0031017200000c00407040000c24440000d03040210741ca5141d031180050120382c10307850a2041e038030000e82d0741b102401194907034100b2080105002042141c5c000342071360001684ca50046448200400a81d6004288222070154490f40d40909000411800c01c54940a6080c0d000c0900d480c040001ca660101da0305801d401c1d41e50b4101d4500011481000c19025600a070640385030345403681d80c61001350300104c50396022902e0080403a542d03c000c51000184258583c540b1072601c4980d817100048000b281c00b4640030010ba5503459080742d00c560141034807044c1e0b44000403c9040c1144105425a80c485817 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 149604181 1250 149602931 149602949
    0xd150c031e1d03180d0c0504090b04020f0415030b10030b0405060402130501060206061003020f1309050a0b1005090a17010f0c0519050702040b09091c0c080901030e0703200a 76
    0x3400d03400c03046504c400d4542030300b20b440301c40c1e00e01c403458501d4100c2181d0340f00a0b8043e25200b2000309104008203c5071055100701d83c508032030300d00001000b0032200451a11088254880c00c02d03c00600d00644454102c00400c108070800c40d0740b0340d1100c1d1b48000407241107540d80c0000007030104504200390b0724213071254104c41c03d0081d51b040c40c3c0000d6480705d000b4540c3d84a4107248611800320342c025811680340796070000c016070340c07444190b00c04c041441c4d2512818400034039110008404800c644540c409207070340104892081c0c40307003040480307140e0000e1540302d500c0680300303000203a40941695814407540c107400c00404c0c5d050041c41c01c20100e42d0040c2903071044c480100b101c1001e40001000d01c11301c881460400da0348030300c420300204004020301541c85800c95808428041c40c40c00009515001803001e03248465810380410085440c0381001c840140210810b10034618658000c1d0846003034080c40000300c403560341e9651650349070401030480c0b1403401c0c212101131411038104686c2080c040c20301c01c8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 149605431 1250 149604181 149604187
    0x5060307060e0f06071b1d062b080c0714040c080105060f090a0e070809070e01050427030513060f050318010f090c0617010f030308070c060603030206150d150c031e1d03 74
    0x84042502201c9c0100c0c0913545c03403900b840042c00c4150400700180d051f03030404400e80d1901d401c0c2490300e60302c8000e40a00d101030304140440c010149064080e4681c00c0032250b0742e02565919200a2110303a41141c5025003c11609002444641d194544610011f01390000125024100b0080182c1030b40c0000e41800c40c550007000007440008905024141100d2003541d00049403800091103c900b800c1c084006074401140c003101c84141540304001e0810f00e100c19002c4202684d40c5c420a440c1c5e08a02c5820801060040c40080e00c440380b030740080f6000b01c002e0000030400303401c564507950841d143d1540441c1d540c13041403024445140c0c0b00440c9118200e16010300c0c1401d504211010060000e284001003c01080c0c00c00640b1241c0b10360075004180b90304c6041400007613264940130f5212081246c0c072a02000c00290f81500c00d141820400b40c4413500011008e011645106880e03025140440070b10b424185c80b0501c3c000601402c516040c000c1c05034550000d19000c002c088401c4451009406001652041c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 149606681 1250 149605431 149605441
    0x50717150f040c05090603070515070204060611060a0906020c0d1d0f0105031305010603050d0207090507050f0a030b0301060b1b0601143708030d05060307060e0f06071b1d 75
    0x22921030250b40088401001c80c0d901c0500084c03400348da0f600600d800c403070464141d922400c2d060002d490083d108030343c18442152540f1007112003070b00800c81208158090008203101882c158061390105018000c054070385a11f84074128500a8180d4003400021905071120a180c908400d003901034050884000b00f4009071000001c10b81e0001404008000307420001c100100102540000011980041905c2e030b04040088042e449251902c105881c840c10000018881ca229a0498550701041d912907401d04802c0c9004400521440501d40c0e01590303540e401040c01a204409000f103c0d103401680d03801040781031802d9041c1841031340540e52108205005c1a040c0c0d41d07070808900060a1140d040c2c042250781c130b808640c1c120300142410310301030080102207003e55000c40140125640000b0901c090388480b818180e0303030f251622861001a861100318030851601000d51160745000400c0c0d02d00348965620785c4480c02285a903a0100b041d0319800801000080c1c80b4170b0803011824504201c102e10b04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 149607931 1250 149606681 149606693
    0x9060b220501120b031c2a080712030b0402180f040c0504151b0c03050f0a150e072103021e031209010e07030b180109120c050717150f04 60
    0x901c02201c82a1211504c1c004c0352410800350b2110700d800039035485140b40e5640d01502e02c50b0314107180924074030241c041041075010450380d406690b50007150030b458041187c131450200303004405400d0030580c54560616449c0e8442c0040c040b1064003411181501d0743c242d007040301405c0300011090049040c4041d001c4960f80000c02e640480300094a00e850f48803544108a803809030280b0112404131051a42500340200c1e0700c00001564441c104448e007038481e4804071951403010300001080c064428104840311165604469407245540c82200c41030b60719a0320014044240c510303402c844480101e161000e0660401107612045842c80e800a207a9409a210f641c8070700c1000007189244000b07a0208001a009510540c0c00000d044103580740d994030380c981490002d009589109080c0030980301803030b0440f07062141811903a4440c540d003000d00034840090714080302d904030075280c600405400040c3c0e03449015141600b8208040a840381240d258046982047e0180050461012074400c01000401d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 149609181 1250 149607931 149607947
    0x606030d0813060903050f0a0c0c120f02040b01090503070b0d2403111309110108221704030b0f01050301050703090f06200c0303180a050a11040609060b220501 70
    0x142100300410455910f06041e240c43c4117541d0320507c48400020080720859000e503913508103510030710303c4442c415580d8165244801c255040500ba40c40642681801864143e12941092806041c0448500e0307031100040d080121907800080703656000180001010801c3c854014820710f48402c00c20f1062a100b28031064080c00d0000a04080c2d4001821005d50b890040303000d0300d5074071110300707018075015454040120b4011841b0180800d005801003040341515034842a050440301d425051403400b40c0d191480c1240581c0c20105407000100000b20204013042d8006204051000b510301065152000341800c540000349900f04042c5010101c0c40083c04548000c40d01641040c0c010910140080030030242c440d03110828020714030000303043c0160800200146204079450b41d080c481100026a90070f427105c0c10031070001d0640c2c00c41584040041d85400107070700d440d4400740c00024016150007400040721b80d00e0700b0500300c0701e0700840e0600209104510706665100d40f4480d40444038600000a04040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 149610431 1250 149609181 149609183
    0x5092b030b0a0b0d06080d12050c0c060403020f0d050702060706020309070803040f0602070f0b0f0c0319030515011e050706020d020d021e03060a0b03070e030607020606030d0813 78
    0x4021241154980d2103500322118510004080d00d5109640304199282c1d40c1c007905582c582d050800f60002000c240204010040185544800200001d4030068100402005004400c000d1040c000300000c0c0301e0400c80c040c4124400e8004201e4030040b00049407609c0c40e54508141040000c1009900603103400c819220351a43c0a0000350f100d07103411580c46d04000403a0064a128030011400103403804050311071400301d400d50b070251407072251070720303034002d000300c100d0051270040203040140011b0400c04100401c82c4034180e0303041d00e0800240030202c1050b9820842010000703a00c41c0300f4440103074003450040340340845c04d00b000121000a06070a030300e0b01403a541d811042c45008203e04080c0b12a9804484004030b095801b1955a1401c100c600001e4011442d6102000c08a0540e8015080c0d11011030340110300040204827071a150083da00c02e07a9000904c0a020402c08450a14064408201d49800f410b2540c000c0d01aa1034407106261810f1741002010b0100300f40c041c00d20034001c13208040d1000003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 149611681 1250 149610431 149610493
    0x20301050a081207020628180b09030705150f030108070e010e070c02010e0109050409061401080f061909061b1e0e10031506090807060c0308190f020c0309040509 71
    0x240d6002c510b80311f00b40d055022207603000407140041c2c40c00140d000c480200921f07080d0304040d5403a13441c1c0e4500d01085c09040d10468056004100074042e034903056101101780c0e25070794001c07840c0c0f012007414030000c0c1d00300303900c020700c81d80c069107040c030400300142e080d28090700381140084a1442d01400080070415110340181c148844280410b503903911442480005d090042c2090004031140c0c41d10100803c010390a00a859070075900204107032201040d0400c207071040d50010951070f06c807000001c11006421800b0000a03590ba01060005281e80c001d0310318181100035481c00400c00d00001500d45540b0003044a40480c48500201103143c00c628414160071007030320070b601c0307101c0c2950f0b0607401000700f401c1d0403044a02031940001d050798000d201c101030314450820b07a15403d40d259015903440104000c01070200d0320f07210014981c175890002000141000707950105101c04d00b982100c1c00c1361f009500c000750913080011441d40d607007818004c0342d070401e6041c0c0c000d05070f441307440e00c0000e6003e03c6104c1c2e031281 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 149612931 1250 149611681 149611687
    0x1202060c0a1b0501020405030318040e160603020a02100c0806040f050105061b0109050a1b06091d060a15050a080c07020127030209010f0501030e0c030706030b01020307050a06020301050a0812070206 87
    0x14494254180c0303000c7c00c8054101d9941d002a440300c11542c02d14208010710560130031038900041d00000c1040000034000b4100b20005908004042e400303500300c440e02e0001c505c2400002e00c40105103004006101c400d98881c40c07010b081c18810f020a544044c440404a203007000010002378440404a80c80d61040d0105804440c182c55805409843d490502500601c0b4590b03840301480490004d07550305242994850701290b540f210141c4910070b280c410500e0010806040d030320740c0c0011560032039000707400402d8440030985980030b07803004414903400000012008180e9111040d0000103c0d500007a80d11f00003400d1500f1980020011908000140e0b44400c03800000f07107000b2a0130852a01556000308105010742e118900c03400707180c159119241c002030505051130310f1014041101844420040e000d00442070405038285c000c2d1400c2007000341148000c001c8500031400603c110b2000c14401c0b1009a0381c0c0d4900010414422060b801004894103c3c44100d540c4041182c11111520303810764000391 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 149614181 1250 149612931 149612933
    0x308070e09011512150f060f17060d11030105270106030f060902010c0b070309060b1e0909100f020723071a070b0712050a0c08060607050102090303071202060c0a1b 72
    0x40500340402c17109401d50082000802d07166000100394060300e0b07840c3d0322075034140e0b0110340c2229107502c05e40d1805000444900860902d01349034040c3c68042d40620b44400315900102c0100342141c070205e8090b0f4080340746141c104045c600c45500d0440120300c0100030710049003181c07504020401550001042c07641d44900700301c11a405030a0310444640c0010703000300c0500d0001c402034041d080304103044805074035101c0000d4003803030000e004001d4054408400600720140300706000b030488015140082ca8407404001d1a0120302a000da40800c8070112000340c0c554419103072040b000c2c130b21215981e809924980d480443c00c0000621a42140d0840f40b000a07030520b036100c9181170784100f0344042d01880c440d004104482d41c024444e00f03c40c940c011030410556540d1031203d012250040901c1001549034004100603142c148003800c41c03030f0b011740c0c001403a2650180000b46181d12800f01201e902d04076040c00c6850607018000740394031641041d4403901e06042408010500500000d6600b0300003c4207510320 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 149615431 1250 149614181 149614217
    0x201080f18030406030903020601170d080405030c03070c030c050103020f0a050319050705120f010506040e0a0b0a060c0302070603051b070c0503060703060504060902040b0a0f1103070308070e090115 87
    0x4200c00d983e5500d844e40401006001440c00503400340c81036a00003d10306200078116180700d0b81100240007440d0f42e10300100c600000290007510b9a11080c060790501d10307000c3c030040c41264441c0201283c0149035203003559148009900c158145032043c40140d07840344c070010854040350324514006540355030340d021617000d1412648501e1246407500f000c20541b550000d00611206400d8041c5900c19601d0440d2022512024080e80e42c0204007400100310401c80103500300c0e04050280004609a070303000d0040380310496035611020014403002d0344002030503010f003c0d00015200a14091119181c1114011103840300c1d401c180140d407000140400034041d96181c26070150070002c064800605200b9002006059140201441907192440c0060340a060707100311030444584403085400e0894061003620308284011a04040c8170b00f01c081e80100354070620007802480c1c4241c6803080300341025000203007a0661000260f009c1c038401c1d001031000014241e805c00c040c1049140c46150701c9210728210b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 149616681 1250 149615431 149615461
    0x60108160c05011103060103050a0603050c01050d020f07030e090702031314060d0c0518030c09070e0d050102071a090f120f040801050405030a0206060312040b0906091c030f0c0201080f 81
    0x50115481c1c43c1c2d8440134183e80c0002140241e10981e4180402d440d20402c4a0840e5114840102181e00900c0304801650040c80a0200c04940e41c40050906451101502c0c103980324804c101d001480a410b12842032900c80b00b41c50700800a07100460405920b403200103080480ea000d2a04500080c114100180c0d540400701d13105160141c0e4103000031107051401520303980042c95100024400c5142c84009800c000a00c0711003058010400c1c0c0180d2600e0609030769070326108032410341014024454002060b030900017400d10a11410043c0c101000711401100114406403640560760081c0395a01e0030040c0000c0c03c0701e40031019003609951036070103466680c039a10031648043c0281d42880100300c18050f011018140c89c1c00c882e0261407640e550303d0101621040401880362001c00c06100500115218801800040901509092605480030001004407400c6030058080300e60000f10303141056403284031880300b5111414003101c4902d0980c006000d492005001c188001030400c000303840041e1a500f1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 149617931 1250 149616681 149616683
    0x118051f020910090302010908010c1d0a0e090606010e1f0e1216080d0201050601120f0906090b060f0f101107031e03080106140d0c030603080301081e06060108160c 72
    0x943e407090072000e071000d009101e0703620041c1c0c0401d0030503200141d4808103004d50301e030300300403981d0f4980d5000c10508680f03040d01d440c3c00d4030742e08003d010310082124541c400e68203003d561440d00504041c5890f2000404100010940c140100f80c0c00448621402120034040d942e8032a5080400402c2c0d4524040795025036000c5a1200e0352040c0040c240810f5082186030b410341d4070341c501b40c90b00384c58a40000c3e42601d40c241c4e989070010b900310b80440c011101c29480326440101191002c40c40c2d0403180c54980646545140550f030030701940043c0201880c01d40d20000d00004d0a680301c50b0440d0032140010100f040c40c0a40e1000d000310800b0320b0300080014422800616070090384607203040300010341e1504e246101e00c400c0b17003c94040400812514000c0007403502c1c20000701d4000303160406455150300508a001a241e0134075454640100000356510003031030203080500f0050400090140e540512400301703440900300c5401120500107a0b980c0036040582c8040d0303001b100b80e9000c0341a40211409080044 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 149619181 1250 149617931 149617939
    0x1b0c0112091104061203030f020c06071202040801050f19090209070e0d050118152705030c0601080d1d210a06050c0a080702190b0a0b0604030b0402030118051f0209 72
    0x5401708803107060b001080940340c000c2d41c041000090000391a000ca210301640c0400d540d0214000900c064480c800c0c581d80c000080101505095a40f41c1c040d082d100d0a850a42d442e00203202007020740d8821800841d40142010303003e028401281c0c000c550240c0000c1e00c1d6500300b29840381030203503c0d00c410f040b038025142e028000301701005074104203102c6e54001c00402c8441482c002507654102c0098010100001881905851a08400c503a95554446c080800710b800d0302041c002c20300b802c2c40c03c1c4119030090611001604800602d070000400a010140b03580101c0403085206207503030b40f1200100e1f074885205890704480400304800d5949014441c5a00419079030030070f010041680d0540024120028071921050b281383c40340300c3e081e41c4030421107001c0b0300441c03006000003001c240b500039810742055426400140c0740c000940898880d500682060310032442c0303c0d0900c41142024442c038003032102040030404d06a51150b881036110104600001542030403595000501d0f40594110740c1c518500038 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 149620431 1250 149619181 149619191
    0x1c020a1b0c05010801050d03080114010c051507020105090f1902010201020906030a09020307051c030804020f0607050a15050103031e05040f030f030905190302091005040504081b0c0112091104 84
    0x480c00e012050780a0281e1800075804800004003800c5c0305481c2d0107441e5040d2240308a584c00c25451003030200042e000d0904201c0720401c0100490814004421940445080c0c002c1a00d0000310190035100050410411369000101384030185d42e02090b110101a5152041a46039585d800100c1c064040c0902e50750340500000f0502c0602c280302e903c01c008540c800d90aa0f1482a6200700300f08908100b01c0c00c2901014100749018006441183d03001e511500c010078a03010f400f089004a1810b07044000103d40c21717848411460103000f0414880d0b0109480c01c1c0041c013007513042d03a500610018901c2500c6160340c81e000c40d4900c120340078000380d030040c0000c0d410341d5030500d03500c1c05c122085c014880780a0340451210f40001c02e06041c240c9002e00c124828102402410707207940d085c0400c02c14000c0c0502e6403868a00d802107015600d03401601d01a03030041600341e4039008030a2484081c90495190350705a0392104601c0021a41c100140714040c58000b40b000940c0007542c01c1801c040c2d8006001c55500503e04 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 149621681 1250 149620431 149620433
    0x1203040f080a08152407210c0506060306060d120201020409050a1b090e0c090a05060a02010212150a03120e130606020709050c0d0b180901060302090a021c020a1b 71
    0x111104d210310700c5040c03c100308224240c1840f94142d100e640700707110022122400714002c0103507030040c6050391050b1a2044100c044885808986a410b0500d00c00260229030690034070000300545a0411002c0b409008681464000103412035419030000707003070f0550024024a124001e5050f203008090300c0d20144860315168603044020900080d1032900b640c00c0402c0d203071100c0d1289031500d0944180702c0c2000342a85079005101900c0e00250074542d440b28a024010900361613180c00341c80304158940015844804a50748051a01d00040c0f400c040052840c1200b0304540c1d40310038040440390012112400494a508100c0b40e400364024600d4100689004c5005a0600b690040c0c0440301d50360709a42940d0b407075418039015214181e03030900240d00140081460183c0316881b2500607c00207020602550b5141c182c010306982c111b9116102c0e0f591544104198100b10319201ea121445040443c50500003001944549c244001c0c0c0c0e429031540410400e030b00300c0c094490a0346422140d51000c1c521441 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 149622931 1250 149621681 149621687
    0x10f02070f0605190302030f010911040f030b090c011d06030612030a0c1101020703030905090a0207020909010203101a030f070504050307241106070f170a0504030e121203040f080a 79
    0x1089401c10781c9a601d42410b19490b80c070031b1090300d010350403010360b81c0c804e64070b0011030fa80600034414007070900480c2044001401c1100660310070003184a188040c4152a000051a05085c0c040070943d0501c0241e403007540348a00ca1401c60518400d003260f09503141c0c2c0300d83d804122414107070010032050f44000190144040d030400200950310740300b03410140c640c40c604001282c5800c4a440001e0119a81c032400740249d10303200d40790603400380a2000060610b0140d40000341644c606403104d0149035030000038868103101840c0c142d07001c0c1c4000388c0701483d040d4800556010a101c001c0000b0f00b50890000806c0b4120b01c1101160000e00c001821280c0103615a20840805102c03000026a4118a5816400d103e401065641c04c24030800c07000c3c202c0e5944003401581c0400303841e8000c0040001000c111030140000b801514001c0202e4000001c0e07a00d05450058071240e880d0001c513108101c211120001d800c400078140041914420101f902d81c1c503117181000d118846003000409840010644150181d8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 149624181 1250 149622931 149622937
    0xa110705010b0307060f0f08150d0317090a080313050f030a03020405010905090601230903070909121706010302070204020f0307020124031502070203030705073b06010f02070f0605 79
    0x8101c0549081301d03178400c426245160804085000b055171502442401070141c0000ba5205044400036461034024000081e01c4404100c42103000c5091201c2c5031780c501c0300600c5142c1e8840600da000b4180c840701034445211034007009080d4074140e00200390500400600344440050b013039004080780d880780e81641c5c02030085c1d000b501855000030500318000460b454030259290254206031600100590a0308000a02200140f00c20501e40300800504005031410401d040042010b080c00050b0440c81e443c2217208444c0c2d01c0d40800800001d005421600c00c030101c100d640082090074016500d07001840860040c0c01140d5101440303c9004c4108560280c06401c443c404e18140b1403a071015440d03081648542507c80e01000d00395019910210b1885c034250381c01001d80d140000d0489080c001c041c0d451034940070b40ca070007080c0001c405c0d0203076000d0202c1744100310760503006e5190190740420440791080c40a8000a1200c6c5c10411a01210f504c014001d110100c050080d1101d00b265094a03100e0140041e4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 149625431 1250 149624181 149624201
    0x60a0c0b0403110d030504150c0c050d1d040905070512070308040803040306050903030412030c0c06020d0f0605100509040b120f0307050d030203090a0b040203010e01020a0c02041104081002030a11070501 89
    0x80a4155002c104c24800c1c0301d00c9100d29031041c0c9a040312140d050f45180148461400e0a003840206c0a0800110360201b10302403152030255a0300042416040c142240380d20302020140c01070f800c0c2031101000070804151310003510019101900303c07160b400c0d1511300e880358980c000340ca030081c006000301d0700090200003001501c1c002c02c41802952920001182e82c1d100c2103030050184100c403a41c00121900c203401c4164846150b252441c2c0c9104562a0801207900c81c07548042c020f9030b52034001c0001000e502481c0c008110880f50701300d249504880c094000c1c03040c1c00c030103031080d03a81d440f540320b45617620700031400072425820454840e841d00c991031035941c0e4070550068415220703141d01c41200ca0b05c04d0007164401c0c0f00a40c050401034000f0390701c0050803040039008a030b00d9502d5a50040081109202624a548040e502c540e03000055005210440e00b41b20080140600c0030032041c403014100058082000c842c040b80169242d407145108002852080580701100d040000d02d0000e1260540041143c8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 149626681 1250 149625431 149625433
    0x50a02030606030a0b0a05040c15020a0605100815090313030305030a24180e030c0109031106010b03010509040c0302060d0b1c02031b03070f0e0f010603020414060a0c0b040311 77
    0x42d46441c000c060351036960050040c10803400000040d140d000d07503000710303401c130b44030751090b9561940b41d151451096038003010000045e48111400d509211300ea008040e040982600d5604101c1d0400c18440c5d190940408130254454041e000300d888140304004450804441c01c03510703411207480c0d10700107005900035104000c01900300b4105075460080046005116485c0d1481401e2151038031010500340606000795440c4203541d11080494000c050000304030030484040001385050f03007071802520464424280b0110783d441301c00140208603c40c8100d80c150750b011618a8525a110315040d02c00d50301640000b9006600030407110360780c490707981040c035100c10111982e865018040c0c132018030500000c480603605601080d43d159031a1200301e018404a400501035070b0340140c9034000d50039130750055481446a03071280704c10403034592421000b8901400301450194501860032140c4507580509107082e6100e08000034a8211880c00f1300f20364041c40354042c50502442c81c060401803d6001c9040400300c013 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 149627931 1250 149626681 149626693
    0x30512010807050a06030902061308010c2d030b0a0b0a02060a05070509030a0b060402070501060f05030609030408070e0a0221010602070605040828050708010902040f1413030201020d09050a0203 85
    0x6210218110090710005031601280b45d03c0c01a08034041d290081c020ba81100b03007003000030100b00c040b1000d10064141c100005c51300c4480790f00020310722a09402400c00c40c1010b001030016490205080b908170040034900800c110b041d150005003903690741d9002c01001e40c000258088480e4010640c0340c800e144c5190100582e5650707600565a51041c942c542e98590000541c02002885110302c031317a0403e50113000182480104e41d00e49086038070540002078031413800e40082101d41380030400302d5400b1164001850800d0b1502020319030302e103070741d0155001c000c00d80c00000300ca40344160b041c3d441c440516038180c2081c0489695580b0040c0d020300030100107014004000c14010301410032681240d401d82c0080041d101c1020214500382d0030342070b0310141d1189031809100032400820042010704a24400001c0084462040000300d403c004c0c1641405401e001c1702d07024241d6050310486d4807034000021600440701c28641240213200b02e00172046414580807001c2d0a0010010300106194070070703022030390 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 149629181 1250 149627931 149627939
    0x10201021b100c080105090f10050409060e0105061512070e0a03140d140901030e0a06090302061e040206030403110a0c0f30080703030204091d1009200111030703051201 74
    0x21301a0090203995001410b040100e0f0b107810720998495840401e40000c2a4520b03191000102660b03129002071b00d0403511407a11b460b400200f88181034002c241240c983d00890691014a5564000e11060400d400c0280000a05041c05a4605554030314000c1c242d602c015100e1500b01d00c41201000c245c02580315500d4940c808c0e45c01203214242e1901e6404070a820507400000440240010341c0d444405c41c062101d40d100060014003441c85074510a402510040c90101100030740152054032801c09040c108040c0805038503240e00b280d03042034141c90000b0903281d6a0701320700d250185040740204040664900058a01c50054040301540c1548210340c980031001c05c845225060030011400705070300c0c0750843c81c0c000b0300000c0c0100344183c40f1342805401c1950700c1031071400303d0300402c24010700c00c403e1201c0030f50781600901c941c0046c150040b40130842030700305488010742d0b86408002c0700c1448400c443d994002d03a001700d2983c002c0c0142c0f60704885d603031415841c00408540020005965a003101c0300041 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 149630431 1250 149629181 149629187
    0x41706130c170a02100201021c0c0e0108180f010b040c0306210c03080f071e0b1f09020301031a0612031c14070201091104150b09010201021b100c 64
    0x121038111a04001031410520100b0094032041c1c905800c0d80b149501c4100140c0f2050442450000b258000680304c03810030030298560360745000002d60052a0000d6003951941041100d64200e20070701c1c24103144d58420f40c1c5904442c2000c0780d0340b03840d482005001c42d10000150001007140c80d0590341480039540f1b665066007600c0307050040020040c40510302c00145c1d50040b00d804203960044002402d03a581d41c4d12042d509a01000400040d400c00080c544184608046040c41d106641c0da0380703440303811168541c5d4080d1500603042f201003407400c205044030382c0c204007c5640a0104d15604540d0b030350303403480c001d42d211686a9800245896400008a40d4a818020b50441c80500b4004e10f01c2d00c0d0451310f10044c44071481d006a40159511701c0c0b820145104c2003503a0303200d04826000014445018104007800f54112500c941c0b103036040c80d04400e110b1202d68140d5080f034003010308094440c455a00144c3c00790003030b0320200048440094400c810301c2c0c4005151400a60711020130401c00004610807 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 149631681 1250 149630431 149630461
    0x8010b0612010909030203190206010e0f16030507030e01060902130906080303071202040f15020105010803092d15180d0f0b04240e0c03030915070f0206041706 70
    0x20300356100c01c8010428032140d0380120382a40d01c20320683e841d00200200242080700024090b60041c0d20510041c41108804034280e500700190400900d1145840340791589118001141c0400705a1940c000c6400300380a9040701e0079481d075510090004070780740e25040c03009400c02184211030301d4044400040701c40e40351203100280c542800c0074503d113542c0d400303095032460021901d09085030303405c0000142940301a00c00340090300c5124010450107450403002429108103801506594000b04040a0705583c2c6c00c1021382034085900380403010f0130303195000c90790b9200000c20094018040c440d51800602510004108200010480c1c00e07020f0440c00c00e00c090581c01c003130014a01440422000b01145500c039000b81c3c010312038940d04401d4841c0342d824800e8846510540168603441c5e40030f60030083c5061049200e088010b80055040186002c001010305412610701088035070000303000300610640030f82c0c01c50030a03005048a55501c4d5202c440c0c0914160a0224104501480300890280500d00080c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 149632931 1250 149631681 149631697
    0x5060a02070e15090a0204060225060e0d080a020a020112050702102f09040e0c090c0f0c0a0507050f041a1314040b06090705040e04030f121508010b06 66
    0x8100103410511926210310b40504851420345050911515941d0f6043c0301e107118010032200940c946150140203850440a2010030011000e420340d00c1c064500794545070011a10689050120101032502003003100014480141201030b0000b541d8034056000982481158402c0c1e031103038003102ea0304003810203e603401c0d00c1d0140142c00c908085000d00e045604034900c680300580700340c4081860076268051680d4800551402141c0202d10040545844d00c11034007081487c902070300c600c920020010307440c4c00004140343e1401802040c20303403c901c100400d48030b0301c00c80c06003162500b012504120303580d540350707105e814404d106542448078031381498041c800d404035400035032540c45070041b020810780910600704101c01c9035031144541801b81c2a491114011380c05807908a00c00e040020a201041100405084c24050200320802030204245c0701203600503054074110284000003d0115110b00740c2c09400003845045c440303180d00c0454010340620449898038000c10410810f1801c3c06258060506 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 149634181 1250 149632931 149632933
    0xe061b07030f03020d0e100501050f1c02040504030306051c020a0f080a032d03020c060601140f03060409080d0203311b0905090607020613152408011505060a02 70
    0x14800602c0d00a8010300f24150603890040303600429004090315003a00903108110694403000100101c4c14101d010002040003594001504443c54180c450381c4071030540000d000d1955503000409051080d40007001a210080642e061013104c20100250107901c200240c1c811000860001307404007401a95000b11140c3d40c01402034030b00c00d910142d8410003444c00c0940e81800b00301c0030380400002600d025000303030340c28ac50040c0c5407000001c101c3c3c40c144000b0102030600055921100e04000300d1020341303006170200c00324650360341e680d8804100a0510404000c1c034004000c101441244040e070063b51150b01900b90b1040240c04401c10071882c483c0001d801000300303111028080c0031502c210f03202c030200c0c201480c6890641d640c415803e003c50b00c0c1221440480e401c00c6003400034140c0d05100031504000b2944000900000944a0b10701a0008944441d00c280d614041b40c0c400c099070101c04200200f12966801c6560b50fa814594042c00e0407106e040b8100c0c400b4900400c00d03150134400d9800d04200c6038 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 149635431 1250 149634181 149634197
    0xc03240906010c031206170111030402010806091819031101060308041511060703090c060f050d02030405252c01061119060b1c120305060f03010e061b0703 68
    0x10740f920400c07040705404110100b42900301e918000e0240d0f03c000d100c00240240164018042c2908460343e4000c0803241d038804000348005030380d00c081c22540254007151000142d84986032014180128841090411300413034484810901100d140385908602070784688038200b141d24800c9080322480d01008100e03071820300050050048184649242c413609052030003144851540442c0340010458811000a8840317110804000d0300e691402d00411040c01c1c5400303424920540078126008d4049480300d466400300015051010801c0803603020034046418413081d4201707207402080114640620b41d669032140401d0314102c0b8002102e04808418005040616420448111000b265008998180307104092122039066072120440c901e080c4240000110110548140005d50724500181e0310101c01810100001c28410003e8003160142c80c130b00012155240000101c0e00c0c00c904000303542540c82d00b03034914141000081e4107801180c0b812148c01042c0c5481c3c0340c1d40143d01c070700b03200100056491 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 149636681 1250 149635431 149635441
    0x60306010303030e0705150316110a02100c080a0e0a0f0503120922021306110c090a061d0402030106090207021f090905040302030a0305090c151b03030c032409 70
    0xa031312100707002c079001c401d69410556a100140381200c0684040da4120f80020601036214110328101e8424881030508405480b40303500d0f003030b0300c5014207000a80906113250340100c10340e03ca10340420020b648803080d15120710002400404100f16021035074002c200c0c5800c08140800054030780e0046490084c02884002a1070040c039405410140c200d44d00116440d0251400c00031403403640c180c145500780700517201d10941d0084560700c0e80c15440b51040c8281982068151032004c1180c03c00302006aa03070125a882da00c4a440c014685c50344441466070b0064182038561076040191030007140220002d106160311215500124880c3d840000d500c1030340d4030300381d0074401030700c0c164402c51b2021030400e140d00c1965080002c05640080714120010f030800030318105019007500c500c41d0400b1184000300030040500c400300b90800c0f035580802c10b082c100401d004080160281c545026414072100313403030300c1c0e007040c1003000d107182c00c15900b64040c0c42d0319404182000d2044143d640503034200511000030b546031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 149637931 1250 149636681 149636687
    0x102061b090301140702030a031505090402121f0f051f12060f0f0b190305070603020c0a060c0c05060a0e03030402010c08130e0115090e161715010e09060306010303 72
    0xc41c0044075050354803860346441907000f01111610412054000d580d85000030070340201140e100c42185451142e003c10b09200f03a454101c0b02c6640715506035001305a03c3c10345d002c460b103060701e00840b003401c581081c600301441c0300c4181c202500c420303840325041c04151510f05114401d042074030982003035600d054108000c80c181042800c00080d006000003d001d082c2018800c05480c1c0510450080a8543e0006841800c6c0700901c420a400c0c4840f525048504582d82d094030340b001403080c0400c140c1c0103d03000001e5070f03040c03108408442e07010a041012240500c00070300402c031440800d940c2801a00e0019200c510240210000c0c001c00300055842c565443c1d0054a940c1c1c161701c02540c40040a2006d413000035500b0310a0700242c000c0d444032081d0ba6140c84080041c1c410241c2103c000c10041d1001084071600c2c4840e9203801c229045030070940000038000032510340807581160b88981c0c980d10240606010300c600b03280c40001e001c0c0c3c1c0c1c8240307002218043c0540c42800b5600d294050380108010004688 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 149639181 1250 149637931 149637937
    0x105042c0706171b3f0601050a12020a09080708100e03070f17090603040b0f0109090b01090e0a0b0109020c060c121302061603020601090f050412081f0608040203010b0102061b 77
    0x17482e003074402d90071005c01e400c55000c5003c8440708484d00c07500118808210400758404c0394000d1b02440c12a103440361440c4002d101411100303d403c0415004108210094028090b0317601400541d01105c000b555502123507070340c82d80c05008941442d40345c1103200804050200480c0e0103150801c007600004102ca66600c00c800c526012141042c18040c0800c001c10781d2000002c501540c0148252000da0a20b83d0030b122603107806a02260385140382a08003000280c0301070343d1070b04507206880d001826030b407004003550500d2103a0a0061040000000114413559981d000e0f00084800004640b00c0d60f469000c101c0c91b07032042c84600c1854802080004200000190140c061070384050107444c1044003040e00600d401101803821405a04050010704c06940d00c1e104651090801e40424051400e040e2900701e03100906400e00802c004401e030010394407146144c00e01c6090b051140018100d5544c0340c00c01406094191000c030311035401d201c8103180e15072000482502801c50190007125030b105e01d062026040d4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 149640287 1106 149639181 149639197
    0x6030712110309151f18020405150421031e021002040b040810050c071e0203060a050906130804050f040b030304031b090903080105042c0706171b 64
    0x10201c1c4164000c4441115a2466403044046c4450192041d90801a0090001034607044003000c0b00c002401214000d500c0c48002101103044030400c80c400d0b0001800140d201c40485d030361034081c10016040042d5500440b800c402e0301600800603030700240c0c009207130f11602080030070101070240100401100310042c02c00c09481c1c21003042c010303400343c0d41020780070304c81042d00ba0013560a040c400b0010680c00400b01d480f10318104941708090841210885680c3c0980e130301103828801c49005031115550f11600c2c16081c2401c12003403140c2e5500981102e540151180160229034030103000400c00b85005045c2c0101000315881000385141e03960b841240d140349000f5010010a40c4492500c2c15280d040720003040b85429034604d00c6803c0401105001103215810100b08586c400107040411641d0302d032180183d00012284c80548205c0c01c8907086c4181f0340c602495400030f003440b00241009 = true := by decide +kernel

theorem cover : BRFrame.Cov 149460431 149640287 := by
  have h0 := BRFrame.cov_init 149460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 149460431 ≤ n) (h2 : n < 149640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
