-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0050
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:33:55.841588+00:00
-- url     : https://prove2.me/submissions/9b2d4bd3-b45a-4a4a-af9c-d1490d7a56b9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 8812956 ≤ n < 8992813 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 8814206 1250 8812956 8812961
    0x20a03080601050d0c02060108060a061d070c050601030f05010c090303171008010c02030705070503060907061d0607050307050106090c140c0f1f05010602010203010b0319090203120d060503060105090106080703 92
    0x700c01080c0c07a017848254002c00784d01003a060b040724007032003c8411a8440d01e1000c81030310100c0c060a500440d44940da14070391056086881d800084ca41080d6080075255114130b400d04009130011342c1d5280501b1100ba0801c682441071001c03c0644e8944801c0031400c50364010030085100c407208145050356800308681848092a07a001011070f60020170a600b5000d101039142d420440d4151450300984070300140b24213000c030301d99104411610140510706d0420070207590720000e0840b114000c03220808c08030043c2c2c40f40301c003e0001d240101d0003103031541110f1a0450a4403059000220210b060400080350540c2000b01204450342410f090741d140c000144000e45400c840703d86410892180140d01d2108600343e1160741000e1148201c02d00c034981e02c40c0e900360700b070344400e10800b660300300100700088060700c69401c0d0021841400384080b51030309407070300041c0c5810090240e400f151440060031200c040c078a849074034000c000542c00b0b00610b41c50840000c1c2d850750140726880900040340002505548290f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 8815456 1250 8814206 8814217
    0x30801050105091e1f0309030908070303080601080403050f0d02030402130c0503071115070c1505010503060414010906060605040f05030f0309040203070212040308040303090509090705060c07030204020c060901050f07020a0308060105 102
    0x4001701814481c03411710040144c004900c0035008155440c5012802000209100058175096110035416480355001140d40400040003607041000500030118407160010091001c000e490401684a041c9801045400c5081e4400018210700d08200029402e800c042500d5121400e42800344d01d4150000c560740c109000e5109020054031074004102c2041d400003050581d0a00900034022881301074003a0204548080c090103034594403800c0000c0c001040314804a0304210182e0020031b17a2034080d0f964030203547c00c50300700740041200440d0070300807000455000c030020002200200044024142c165442e4492800e031390340076a0700000004c440900030410706100c2e0034810280e0342e441da92410441c6603138100e0b0100310001107035000c001070b181c90000c402600410780368001e4a0f40c1c0340340c141045501d50022421a28902510302e00201507900c61015220007141c40c405801e0030300c0e0040c260b82c01c5940c024a11070304101c4a1051000450340065080304c26580750406060030346500006039201e003d41c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 8816706 1250 8815456 8815489
    0x801090b010c06050f09010506030610030f030306090e0606012c04020f04030b0403020a030305010603052203110a05280b01140604120f0209010501050405300d0804030801050105091e 80
    0xc0106102021703111040305403061002500800040d29404201a1038070003e0f680011521418082880130a20640400d201203109044c00544035030384d08000c405440322100154120341181d810810b45580081b2841d0031035101400302c1440c003030310800c64100300c4070414040c0c1c01907074081030b004055001101154043c1d500103003a00801c1c0792034a402595009403030402c4000a00703040000400303502034015140501440c0c220000024031020b18011583e19401041e81003080018620b48001014040c09d000d10b0300940c00b030f080340903040381030b50080343c40e14107801c40110740040f0748030128000c00d43c030324107550403001134001502c1c401d03001800c50302558020004500c0450400010800341d410900e00d1a4401d0705c8040c49030782d03140d0040d13a60740140d1080a40114800441c0c2290303401041c680380c0007142e00d85a6800840ca001c611500e031140035091100801c03428000e00c0141500070703407000e0042030f0907e0446c3c9800703134000201d40c05c84041c1c8074420a401d58860b4240b2691342d50b101c1000d042c0070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 8817956 1250 8816706 8816711
    0x5070212070e041a04080409020d06090519060e060a0506070f0203060f0906060a0302010e0d0303090b01030503030403020f0105070207090e1e0706030b010804120e0a0308030a0b040c0509010801090b010c06 90
    0x2c075241c05248115040c0d80c125503203d55500710707071a42d81c902c0c2400d40c80341d50044041401e00f80703815200c2020b9400b005403014183c6e603071000461a451301d440745501076848095020b02c840c109071801400c54026800c0810201e80041c02c016490703482083c88415180f0588032a84c86024a20b0a010b20940c2d140009615000d480c0401c0300e40100700d00b1040c40340c4040070440d466501d881d13052000105040c000a4000360a8000c6401b06007800081e00c20064802d1800040400041c0c07100002c07440c080e04119420380001090005060f81007111914440c2110000c2019060031440a1355943c1203100d400d03801e946901c0e42c5040c082040c0002c9201d0b00c040c400b610003101110300d03c41d07282d8109004120200c0d16080380e043c019442040d28920855001c2c031003201050101c0030a58071300c641702c40e0403680484a01008000240008059809510441000714410300701130300304003c0d104410300c00c004118050006880581e40140c10074115102c020700081c200d040341004882e411040c46000d0000790 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 8819206 1250 8817956 8817959
    0xd0f02150a0305041106030601020c01200604060b040e1203061e041802100c0b04020928060504050c121803040f03080c0c010504030507030b0a021605010504120f02030a0507021207 79
    0x81e00b60704183d1146110b150311141003280781c002c005113030105485003801031f4001d2003004c900354000c19841c54503005070292488040b43c000030480c64000110f90417a480ba40b40c420030360050138640140603910340e546000c0d201d1596001e40a032150f0000900c0d10380328954041c000c1007001100da18003001003201034001c0c8501002c40e0003244c6e0b4403090101c01c0340150a450000b40e21240300c0c000e55116a0ba02c5000e1400940b2682c00300089400b01410150040c51414100c10303d80411086025010318141c0d008240306140008200860f0310061020386501c904000707946540340403410141c3e100da540003201484903003100b029072446c040c40e00001000081028003105100d2010007030152075000341c04880c0000c100c10300454039401984801000e80e070110206000040f0503a0707c1660010a0707001c01030501407811100300a004003450700307840c203944d0b42c4284000d0080d8450200e0071820b039410003c0031f010304010000d60301c3c03050b10802010420041703035400440d500c0703140f810706244000e01103503400ca = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 8820456 1250 8819206 8819227
    0x7110a050901030b0f0c0a02030a1808070611010e0303060d020108130510060806010b09150307020c0d060b090f0c0423060d05011809020303070303050a0207020d1103010f0b0d0f0215 80
    0x700d030705545005c404075402c0d0000e01c61400070310803541d880c0c09a60146080082c001e01c20f5803050801c1215041809002d600803d21103000c124800060601c4d6a40900f00c00c5030341a41402c644c5a0712800701c1503041041040029150039030180c041c0d550a1034051440c1d9528110014596151540108203000b031a100312915001a0003450a41c3d10241c207448c480c4e61789003c0030070203100ba4101a81c114183c140544000001200650f0b8445c03420b00550340108a03040000b41c4000407450b00700c50f10396451804000320f0034044d05641e88000903010184035410301c0400c0c0746090280e0700c2007801d24240400c0e031104200d500c0b906001d05d000050050740d04c0340320124003200640400d008914000900950003070b5602c88900a0038140f0350094043c61506180352012800b8020003440c0703086a6408020800040e282c0420141d011030103403095000509841042502752218000401006814910440039940c0d45407091a0b00316844000c4d402da0250603c080784404034040001240d40802040303c0c01c0a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 8821706 1250 8820456 8820473
    0x316030818010e19050f0a030302190f0e060a020106030807050303180303040b041506050d05010c091202031005070c02060a03060501020705040504050d03090512180f0904020607110a05090103 84
    0x4505040c0390a544884000c5681c2c2280da0140c6480100c0d8005181c0300980a4000c07030001d4103e0080b01034610842c1001d05580c90612003580460002e50700150300c1a841003040ca4a08587c40e1a180c411700b144815100203040304040e1002600c510b10000300503590178000d5009000460340b181c103041e1204036605040c0d4803500101d070b03036800b07101180c10b91154048010007180d203d0765112480c40000e844a80712580100c0b0000c50704080e450703607000301003000d99520f41021240b074480c01c0040b4000d0300800c0014910241da40c0038145202c080031442e4016035001c513900c5011a20039000003815070b1291401c8854a04041001c0d40100c000128486c0c0070394941c00c24000e41d4401e03002c41d18510303038940511088540441c0c02502e29044480c50301b0b6568031980003500590300074800c0380c201e092200621880d540c050b0302c5c4010b03031101a1554007254240759840000503103084038905400e1400d9000b003446072040c200c0080c0400054011010669208070080c0007400d0090400c0100350f8407460602c02 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 8822956 1250 8821706 8821711
    0x504080106080604050d08040203120f0c0d1e050702030102090402030f0702250e0405120f180406080c010513030605010f09050f0103030e01050904060306050c040f06051801050c03160308 82
    0x110350a1800200301900d0002d10a402140e2001c020302d41515406d108a4011001401c100d915014900d02c4800700c3c4032000162100d0540d402d459070344d466645244502d4941c0c40b42204042c01b078100c0f245460800310305179001e0b1161070f900342580e82d08106e02c000780c0203125418402da4810301c00310a1141840c0c20007100c6128681c01d400302c60b0512000001d419036000b4014159485807a800d03814401c00c5203046d03d13140c20074032510484030107040c07425030100103410040d07106150410229407800c9409046551582e80e00044d1001c100031410198256100c070036262a80d0f040c00390008081c15981884020080150b800078010826940c48030150b1144018a1060f190070504140105151480c1e81c03907075504032980360b115680320180140c01907c0c540c01c00809a84d01a544000010108000d4000c05105204403013282d941c4605251074105007608a40102c410424240401140042450f10b09007401e034090170072a840300c0c0303480e010078654802c910941c0c003803545480d0300004144e00800304030b0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 8824206 1250 8822956 8822969
    0x30305040509100b070f1a0408190e130e0f0106080a060b09100302010813080c0105040b090304080316080403020d03030606080105030d0503040b07020a1a070305070f051b0c030a030504 81
    0x41191903d80c0c0d290064055401142c40500040186200061280740343d0f07002d5903c40c1c1c00408100c0381003081200d26034001c139426247e0410004061000800604400031150264281000400a004042603600b00b0a2045940741039407025016031a038010401011072188400c002e02829460380481d54861041e100c007210840d060611041440c0340022740c0c54070032a15240004401803441d0011140000064006101901d04580c41c038046400d00c0002d004030380c506000481c15081a1030103d250840040602c100e541042c0011b20890f40c010040301d611100400d00e610100400c0d04102c1020b21550384000d60201420003a10300300354254000c003049800d40c0d29400d440d80e80ea00c1c00c0c90344030040c00c2500340c0002c4080002900007140c1e503215680000c0e20344101c1d10350505c9691010440220b00902c250305800d6082048031007030781400307100d600425901d0840000c2c185428060503070300a1b008124540f1040c10f1350781c80070140401401d503880300018102d8905102504024105600a000d041c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 8825456 1250 8824206 8824219
    0x1060603050106050f2b0e030306030c0301090305070609020f060d0506040507030b010905061c050403090801050703091205030403120501060e03070801090308060d060b04060603050702010e0f03030c0d0b03070303050405 96
    0x43c028041d0041d661344500380051140b50502000510010000c4a01000d0b440d00419a003a1040ca10511891040451000095950303082040815240c8170407081c0e013500ca0380c1000041c0c1c0010f58003070305071030100c0da100c01c011880b2045840014860740f04201419000bd00c003061140001c14585c101d14014031003940c007001a600d41000c21030642c1d440580c007a003ca1a03480c42081281000c0d8000d00441088100343e0411031101890f003420340300309403026800140c9a030028405540c0130f11800390490420306041160080315a103e00c0402d0034140c451080c442d0100000e0300b03150007480582d044ca05400800c1040e90303110340020301041c0c0d400c90744601034450088081407000051040714022909a21928455030b45d08040100508003c0400c660302500c440c0d03d5901034071030780140f8001d400542c5003c9024602120002c1c21104050001c03402980b06008031030400001008481e00480280c84031959051505150b80c0a40b242c8905140c00d40318440380041070581c05030107071054400031100c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 8826706 1250 8825456 8825459
    0x50316030305090607050f0a050702040f020301050306070903050a03050307030f14180307050c04020a050c01020c010c0e03010203070c02040f06031a01030302010507050307080114010c0203100b0f03010e030d0506030106030212010606030501 105
    0x59070f520800c903001c5000c504100402c1f055034000b4400360130098003515001c0e01e41221039001c41c0a40d40d6041c8000030042d00413005224510702400455071054152510400251460301c031165110480301010301846400404680300510982214010100c64101801002480481c1000342c00d011a6900b070900c0f5203000ca0364a096012007264070b042d80000c002d2440c0d0000001b040020b600c41b044860a00004012000301d03c2c02c207001801410154600000b582100800c000d8500e040c0d41c10b4091003079104008210200380c00009030110160191800548401d40d51148802818240c10140680007000040d0b45c1e844003d2014605882c4250300900280d00e82c103001751a41d010030746550010441110044c0b01c01505106074001000341450858600761450b00807038281a0f40c0d0780112002525042c8a0560f030030100040b801d003480030340081107503000c0090941d03103a01032544507600c030a484030b0104004e580c003504035034041e40d001400c051a642c0c0003202a03008100c64824600840d080000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 8827956 1250 8826706 8826721
    0x10030c05010e010e0907110a080c01060f0501080a0c0912050c0f0102010c0f0e0d08030a020a020d05041404050405032b060801050402090109020307030e0d09030201020c0a0506070f05010603050316030305 89
    0x89140700d42d8044e181d034041c074100c41c01040360001004009604212032510985d1481d101000b6102e0000d006100003a52161103402440c00c0da000c40e0086a94136510307620401450b41e0101c0003c0d4021480480081da02c036141b18103d4504449511003038120719048007080a00502043c51a00840b0440368249801030380c8005a090790751710212100819000010001101c1c0585003200789508002c10036200c000740d50b0f445510075081900c5484a440d03000c540d0032451501084000224203440c10000d08040c60402c410001c0741004006500881d100d40214003008420415203180c4e0a0520141c50303403101464841c5000503070300003003080031400e2103000034051006105072405250003600400c00c903070a010042e0007a5002500c004105a52908000304009050151100303810865541c2c280484c41c60000915103035041d1100346c07181584c00e00c100070035a1100d08440034a035025220007088441810018010300d142d40c00034106010016076403070500c00500c2c50400041c8251010880ca860b00d50 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 8829206 1250 8827956 8827967
    0xd0e0108061504050603040f060c030b0108060d05060a0b0102031309021c0c0c030309020f0307030b01050a170703020d020102030c01020a0806040c03050610050d0605150c060c16021507020910030c0501 88
    0x641000000c00c21050105041003401981d20038010a05403001503231503a10203040390003080d0700c4000682c1d545012011581e02849081d0460f0003200c294111820980b01c0d5500d681001d007981000c0d43ea00c4076409242e034002d000360340101d041c0c42c641910140d131340d0304004c0c080c1d40900e03103011040c0400803006540502d24442d004046046a03903500c42d40029903802d0700142500c43c0107130b90007024600c03008410f5400300502809180301da02100180d525103814452910044d800c49994408043c0b442000140e0000e00b010407213804035031100d010056400183c0c114440c039440c022182d4000540f007984550400fa6003401070405560030061620b10b51411001c661003030b1484c1d54030079013251000f4009842403014000328290704030b00203002592500020070b0441c0c01e4103042d5800201040d48420314805100b05503000c01405000c0b40b8014421200707115020807440001c0c40380110300c125440c030f084000162000613a020304000542d08013a440e440c218050b078402150400c0240c0e4011409502c1803 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 8830456 1250 8829206 8829229
    0x80a0f051216030603020621060301020a021b0d0816110907021504050118031701060801060c0b07050d0504140c0a0609090506041808040f060c0807060b0a080d0e010806 74
    0x74104511502c900380585a459044200c42d0200743c0c50341c43c08400359840b00000d0580c1d00400304e4410b400d0480c009038003080c0b40b0080480388240d106001101d102900800c0051450071440719000b04100003900107002e48030000c1019100319000300d070100c080540b20318030851080c0510702803603404166100308200c100381200c100340180c2000b0403100034454030001050308103105a001040007800002c0e01c0014490007a410380024558000304c0e41c1c0c4c1c074821007040b80903128519200d43e40d58103114015007002d0f980280104101c440d4400542440c0c45a0f06841240000d2403083c0154146801d20507a58030483c4072642c000d02070400d004807c3d02c1c00b01010021903040d80c580d031030a18900f0a41200600000303140030b030490b45404103602503000350201000b03d2840351010035243d50603c0440d9001c9095030300140103000c480c010000200340c41800b81ea140baa440600480c940c080d03480031070300d039800c03d034070203c1148507440e010100f154108004424140003aa6030440d560355010030000f51440f41e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 8831706 1250 8830456 8830477
    0x50f04050c0a0609120f1403091507020f19080604030906020115050906040b01020a02040501030b190204050f06070303090213020a030c0503060a1205240105040501060206090606011b060603080a0f05 87
    0x4004007000103824070005c3d40403541c0503c5e01e0640030a4a0344910601003e080084005500001031800292402c80e051000114040300302d43e080c00c40e150301103032800b9018080d880c4150030740c1c80b0049002c182e103612440a09001019a00c903400d10345406040815a80100805035003410300000c40b441020f2060300440700300030201c0d86c540d201c0c082400000c20002d46aa411030141c1458100541c940e0301615008500c10b840892251519811000c0592a40308036a540b01d0f004000410440c0d513141c071b2000b210708049030704555074040b92034141c0040c402031100a4000c4101402c89019081d190302034207003c2602c0c0c03805e100c50107a003107007140c1c107100c2107482d0f1f54002c01c0b4500a00c013899201c403030607410301d01c40d108a40c403a488031007c2e0500303a9030800d03031102800c24400040c025403c260040c140101814001404c143c10b0203850261a58001401c0d1810448000003038100068540300c0080d201d1b401030020800c0035128101502e550b40000203150100e10f1002c6606071140c462012944030000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 8832956 1250 8831706 8831717
    0x1050117150114030a050111041707030c0b03060a03020904030201050414010c02060a020a020102040e0a0c020706140d0b1f0207030b1006051e07020a0e06010201050106030b030706080a0e01050f04050c0a06 90
    0x34450b42c0000c4a09559210341c045c4a20700c1800e0008009110320200d60ba80301880341c1d02d0741c9c40c00741d50308800c01958010b05080c4d041031000300002070060104205440b92901405d85940d43e06006c1041a200350340041d520514040034032050580641c0454000c034003a10240142d00b07202c6880c00e09850020101800513445540000c00e640c02c03a5000d000c50341514400940340542c2c46058102c507110507551a904c0e03a96401088440d903404001c2e01d00209281d00300b11010301c0081c00108407502544841e0a980d603151000000c19a5a03d08888908480b500c01680036807000c520003940e038115804100d41e1612903101080342d1089040105007151035581d580c1e4036164286d0305003183c4401e000e000d040302c83c1045c404800160b4031084998080c021200d550351081c03070401c0009080d0b13071040e80014281468503005c8411500d0104220003503403094104036003d0b8496414803c000e00c03880c81103d034603520b018203000c420004448040e0140307000714211004000d1100400515410500c074100c0401c8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 8834206 1250 8832956 8832959
    0x6050603070f030209060d0209070f17061c02040e16090b0d0f021002011104030b0405100b060d020a0905060304050313060e030715180608060102010609090c05150d0e010501171501 79
    0x3405da0001540314002a040c0c0c0c03100a5282d0224007652001c0d910a80856240c010f4807140562250742c0d242c428803070921a612508088001c106040c0d20210a0001245181c650f02d0554841740c004a000000003400ca030300c4501030640c1422140b5050007441c1d50030b41400c2000e203203881c00c1049645450341150650646610503802c220401d40342107040d106654032001106090907c030400b8100030350040d502001c142c0341900c1c289007882c0d034052072020001c0c5400403050254031154140e85d0660021400103075500c2004100b51040f500c00c0e0301940e80448004204002c010010000d050710b04010a43e4401044e103400007a6128402c540d0b4464059214000401514005207000d207044105410846540301400000216104058114902058924050000550f0309101d41c10081558503000c004418003582e400c11010840d02c2114410b1060107111000c000011040342e6484414120401c10018610101400382900b4030400a000b44003d154035460100030880340340c18081441c01120380ea = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 8835456 1250 8834206 8834209
    0x3030307180b0c0102070b010501020a0308010e0a1d0307030e030d1b080405030a030903030806030a0b0406020f04050a090c030605091501140d060609030c06111b030a150906050603070f0302 83
    0x100c00182100300c5418800002e104040e41008240809070f800c0090390354121420481401036060341320604544c0125503240119a02542d40780c1921011012203107140c9030000c1daa40a0300d800c0846541100b41c05c0040e60a07000300100a0040074400d072190345c10b1069850416850341441c02c5030344041405d1407809038038228440e1004410307034400c0240604254032040802d03d40b444c074400072404241e0244090050607005020940c1c0524210000c0501202c140e4a800c103051028000900e1140c01082c50740c1401010310a4071b001d01005400144003564502d1340d00050100003100c1c2c0003091900c100450075091000840e4071076810005503120301404d40d001150005850310b90302414080c14400c03201046014003540c07009281d1540e402c0003280c1181025042d04240e0341c00707107003800750801c00305200301c0f0045400c001441d40c020500c80031a1034200803909110341618001e140d84132a00076880d0408090703003c89442402400300304040d5840d0301c01d0560318289030040e40f21020030300d441000103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 8836706 1250 8835456 8835467
    0xe0c010807140d021206120118080c0c03060403050703030c0503070509010c1113020c060a0b030a1407030606030b01080c01170604090f0506070c050615010905211501050307080a0203030307 83
    0x1c40702e418450382c0c039044510440c0401c80e00401d03141d40304041285c082c44110700c5c0a0003e02c0410740070308000c004541c00e012003d0549241117000501441001c101210140700c00d002c090800107000d019250140b07414500100980e01c01d44044021a1404e078490080a1103101603d10841050300c40f03c0c500342c440b40064420560111044816030001413040706e640c1c07284e010060301095032701000350f01d40181900e890f05050300289554071366071030002990841d60307001030182c0340e00d500300c0c1429000c000c28144440c1003000f250005440c290401400104000a281d480c6040700c08444c25203150341920b20045414101043c070200c440080c0401060040c5070661008003140e1180365034408102d050398400342840b108480490105041d810040144401400340540c84400340700340c002c10403840340c00a00900a18050980540c0207080c29208600040d5100b210440c8150104c0702c1000d030007006282413200900400d8081e00034018000741e641e000162104215030300801650a43da20b02804460 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 8837956 1250 8836706 8836727
    0x10207030201120b040c02030d1107150908040b0c030901110d020d05090301060315050702070501080c0a0302030601030905031201030c050a030c0506070203010b10020d080609010e041202030904061403010e0c010807 94
    0x1012a5148003048085d5603034420b4070b07250b44094000d10b031151004103010044402c840440c07840141c08000000001e220044110242003c00d107001640001c83d06100790f007030140740c1000c0000607000800c0008548004050803101d0700c00d0303880800710031102c0d403001e81312560f11441d04050f83c040b82e4000245400360015003031032140600001503099403920b4960344154510103080f405581c40d41440003482e410b01c12003003c1e040a0901098900305490b140c01140b00714114041016800b10214090340c0c8a40c003c030503140d0704402100d442e00400708a221402d1402e00c811509844000b80002d25130030220740400440750841c2090401a1600c402c1c04203541c020395040ba8107540c1c1d110380c100141e0314020744030000842d90b4010080c0601d1182e000d450800050020303881888a140108071160301a150590f0090703106092810100340e884041c0c4c03450140400720342d03205c0e00f0804003148a4100300c43c12081d445084000388888240c800049464100703d0440c18005480000000c1069014886216 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 8839206 1250 8837956 8837987
    0x2030702130e0312010e0907050a0308030709050a031208090c030a0f11040e03190c080a180905011d0c0304050a030804080705031305101409130e0708010c110c010207030201 76
    0x607940c0d0001c00010f0071548100b8040614114410050003842006c01403294050b0b81c003c001d142d90350030000001c442911600c4000c0a1880010001d09054401c03400d4800804008e020405100e480e85451074040545282c0f0070002013801001400d05040080c5c2c42605000c0a0050581c50360103844602c4a070790442c00c191000e023142d5025480340e440358420f48280000003009561642d908580341e4030030520000c105020000180102c0000c60107260450b080c10000703003404400d180d00da0050340c0c599402640501c1410345801c5c0006200011000101c0d00302d0310000c90804565200034452046001c195405001a4801008040028021040140c015010703c9d560b5040020301d079203e614507400182e030b84e4441003407640308001d10708001000080025650404070364501640400c0c108501904031800e00c48e44140c64a2201003940d540801c056200780d2013030b280c500d62a04105c42c082c00302c8000400001c1d45002103840c001d10082284490b0540581c00781085a2550300115103070654447d904 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 8840456 1250 8839206 8839211
    0x15060a050c030307030203040c0e0408040b1606090303050901060902030103050a122d080901020a02060a0f02040509010806040309050d0809010f030f1d0601170c13060b07030306030203010c030209010203070213 92
    0x62075007910800c040c51092850360340140e0b580c94289001c50004140342d0050300e800c807038101880000f80b543c1c0c003542c051302c80c40c040140e29008960020300800891441c05003c0a11f0610050181039040d08410312400d131400c000e11180e5911a100c5040f84001d1102500f5500250300b5840041c002c0d252036040b0188500c2c1c40320b1303140101f0081c01c0107941d00c1a05030111558a94240740400e400c0b0035011750224880000b1070502c0307441c1a000c0c5d20340b0381c018054172409607500006c80340a80c03141c0c1620040c0c80042c00c65816980c40317510f1240d076060103540136400b1681e0311000203500e00e03100010050141e407040c001c42c20100590010360320100c1007007041080c5611141c07070b0074022130715106500c0b40425104007204034101d0800700e1420103006070000082088095a00b07070142000040701d0803113150654403000c004100b440c0c4100203103010340005000f000700140100130726a06d070b0060700a80303000300c0003001a803000c984260304a00c103081d8400c0c0075030410b10241c40545010b40e16009241e1044201 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 8841706 1250 8840456 8840467
    0xf0f0702030705060c0601030507320a08030703020601091503080f0322080a030c030501062307050f060709060507020a06050c070503032703060103021807020c060a09050405060915060a05 82
    0x40c0f01d0703405c01c041d60340403a401640100103100041141e240101986000000a40102c49100c0444500d2187e02d440014100c0c0a003040b0352180c100302001400c0a40c140ea845482d41d150080d04c07000c003840740c500d105060614010300958040c40850403654084a803a2038050450031580164100810f2128584051284103480d01140201c00d442e0b0752042410310354400c0140005402c54442e00e003558201841c240c01480400c1c3c10400c2022480c91180d070300da21103404c05883c13510340c0c814503000511a0044e104d4403c2d0044000036424041c541c0d6841e0710703203c940c031081c0840e240c0c0078812020b54008600392003048142d02070030003011147c40800555004030703241e4000c40d156510282046034244400901c2c01e44d0314800002d8906000411406041c055140d84c00040302c41c51005289248030940e0781c0407540241c0208003a111203000a0500d0b41c44101c550800741c40d512080c03140718051810480010103920f441002c280c8550b0071910903001f58605001400110340001c407045c818003604109 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 8842956 1250 8841706 8841709
    0x3031213020604060302041503140c07050f031801120903020c0108061309110111190206130f030308060a08060702070b0d0e07030c050f03030a05030408070201031e051602030f0f0702030705 83
    0x9101800782601c0141c2c0e1507103800c6541d010223800c000c40604240c03806a115030f0345d10101c0e0400342c120840a08850311404182000c03401e0065541d5046440d1000048030382e2407241084c40f83e40003a5098864010800d03860717a51038140c401c2180300070016081051403000c8c1e503000308880f6410682c040c1000f0104000030101c40d0454101001c20f40d020512210700701140d40c2c1c80b04005820008500140001420170001710030b02c41e0034208024410380340482e440c412098021148001800c5c00280c500c0311581c3da041c0030748065000d07100e0b503001e407a450174003241170350300040c08502541455005140712880e111003905c03150009407103071130010b45841e14050044000c100800265018111498242d8903050070401c99215828105009800501c9540d101681002c01d49a01503004441340356140882c1c40120001c0407040c04510b8000c0c1c00e000d0b40304900340d05602c1a4441c1502804142c650151444180d03640d0040200703a038003c100400c0082d0907841c030761000e082d42c82d101800302e5502646490 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 8844206 1250 8842956 8842969
    0x40c050310051803070302060109090201110303042604030b07141309150806010b03010b03090a060905010203061002011b030f060504020301170706030207022b15140609060303121302 80
    0x2004820407a202c100f0321000e91038048807100607181c240001c52911140e0b540103500d59005110324064699519101d0b400d41e40202c6028281c500100250784d601d00e001d2810210b00ea0382d0f50a16645003420902d1a23008014000c21102640d811481c184006d6507a900c04a80840812140450a12040c00f505d1948501407412102030819598080b03404d01c00350000c254020f0706d6a10141d020b5024800400c10b100c840c0c400c40781911480061650f0381c1e603c0c121124035001d0701040080c40c144c03400928a00b07008065024501441088604200c44140040308a00f0390f241e0303030741c909038030141c14440c8080c0314001d9001000c81d03902104003284041d61440018100c0c0c100364002e8400c03400c403140c071030385c952024001c60004d08450309045040004980214484011861101d056052b1260070b0062a00340f10702c90135425a8040c3c4a46001c400c914103401c05070005a5601200c41c0c0140c000c550305142c16094a0710604000d0000c508244070008018210000130702184100c0d805e50300c4000168403800d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 8845456 1250 8844206 8844223
    0xb120601140c011a04020708040b0a02030f0a05030a0506040504030503060f0a0302030f03030906180601090f0207020325050111060a02030709030c080a0b060618010f0203120a06050102010506010c05030909040c0503 94
    0x2100010300d0101e078030344c0d0780b00441580310710b1482103104112035800a06040c09540507034054036000303501d451880800380c1c6103202d0420b07001200c14001c14004c02e4030750302400540c810340c174861062256841c3d0400b80415101c0c00d980007404070724144000754090402490491070004018001d80c0c0c1141e60f8ac001c0307401c201103c0216481500b00008000e4040320800030190070131106d8556a14040c0c503100306c43d4071903e041c0290000143c54000e5840c0d10026501580c000341e4009094580f841d07050f81041e00d004010031940c294860300c0310000101036001e01086902c01c82044003034240399561190100c0254030042c025010322003170a9000c00401c40100380312000c0c0c00303464012720312920541040c0e103101c0c000511491050f8010407682c200480d00c00c29100821750300382025045101c207010180e085016040a8103140d0007a5800c1006119043e000b01013110000e8000308a140c460a004403810000460041c00507401001040b4050400d09600c90384540244455a117440c0c603800042e00b000c004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 8846706 1250 8845456 8845477
    0x501080f0c09070e090c070803070c0606050604030507030b090f0304090e060a05060120010f090302010912022407120212040c06020c210a02040207080a09060302040b12060114 77
    0x86680803080d10001c1140c0800d0241c1110300c0816442d102d000208151400c03c201c80c00340c120b135404a04c0000ba0710b420b8800c2558400d41c421380f28544258028019900c41e0800d40301142451400555400d0400444064036044000341c50303400d00303503240c2e000204d00240240c0c0180c4183d88085090174410700190025180c0360f0004181c070102e40b40094603100000d4103a4220628180520a041c0e810031044003980d80411030300800c5525188a06004020610030504941e0901012008042e810340c44001c0c41485a246e010f544c5000d801d0890f82c0d0440c40082c0e04401140d01800f60b040404580b9050b131003d201c0c41c2072408840518040d02c141d030003412110584a01c64400c0c441080840b107a50000341400d0f20080041007120301c0081d001a1080100103007007045513031903610780704c001d1000004454001e0415035070f03010140741450080d0310042d10540010f00c1024007040d0540300740216011a40b6000d0301900300401107001000020000d4450340c1808030103d00070801010880140248444 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 8847956 1250 8846706 8846713
    0x20f0f030c0d0b0301020405010504051e0306130501060e010f0303110307020604030305040302090a0504020603060607020a030507031a07030203090309120c04090503190302030906010314030714070609090b030606010e0a0306050108 101
    0x4001c10b094003643c603900c4207640309900600040c08035913448010356088660468000c203244080540081c86603441d03901841e0140148403c2180d0140504da404100d1489078000b040403580d55298001144d100307000b03054078007000700d0007000441e02c01e1100d000d02c91000400e40c1d1919650394006055640b03d94800c40104d04046410003e600e86140d01a40c009061003060080b031610f41c0c000340c001e10008100318070441010811030b09544403002000040c680c008100c4800e61380300d0400b014151510402206082c60a90015400c1c902c24001d036070240480d42c00550404000604111031a4107660721141e0510600ca02e8424664450180c2c030085400f6001030b40d0780b00c2004e04a1051030095101280505004105000d01c90000084c0141140d410140b0381e401b10350612242070031441003d002804040782420018410310001c00c3c41411511107031125400940d50b94135120507288500d01982e4141c0001300080d4680d40212000c04210381d0040100bc1040c1d1281d441030200c403c20b0f00030016960 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 8849206 1250 8847956 8847967
    0x3050d02040609090606021506040e010207080d1a0a0612020a03110a030e0601050a0b04031211060403090603150e04030e030c1306030b010605090d060c1701030302010902090106030c0210020f0f030c 87
    0x8440c0700d000d018004510207030441c030040005070a82100c8c094026409940d4a41c5c200520102c02c0d0705540724154006035196480c1a15865500984100d1600d02c00440c8040030980f414546034103440100da040c0c4e180c4031502182c446010000790801e56516050540b0748640303042e0580100020000c011154800040c01c0c13218241480c40d10f04140c101c50f00500c680c0d4001e0200400503c02d540031258000d4401a000890321411910283d002506100703521882d0240410582c0240880c02901c01e5660f04100c80c1000d1b075034808950000c0d115400c5040603d80109000c03034440e00005035480c0c0c1c080e085524060034640841d40e442c04100319000d415684035818400c10588010250041000303280003030401d02000700140910000744002008280d4440410104500400540c19110f90b4610303c203a8942e034a0074083d020f8800c0001c102e1080001e2400411344602030b120350510210141d00900f510f90811010400075407295000000b4032000344681103401a24400031807048807804010354070350 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 8850456 1250 8849206 8849219
    0x60606050c010e07080c0f0307120b041a010303050a050310030c081506040203010605041809020a09020307020f0604080a21050c0a0f030606120513050607030606020c010305041e03050d02040609 85
    0x1654480c83d111903503040b49204001c09400051010b2121000721030017500702181c5c07000240341903086c0e804a43c21900750900ba90500045d200450710503402104c0704a4004030408600d8241842400014003003035043c07007030b40700543c420005540c2c0b186500d0301c1503111585a840d80c040102c4d07154481c0f01c280c0d2000003181117982c0c03001d1001e50862002d440035030030b550404a0291076401140503030352a00316a6900381076121241e40000060f02e801821403510f0700e03101c1c03042c0c10196000b04d4119000d0305c07466514815019001410038030482c0c01c45040c5050000401045501d01d0a414002412161003452941c0490b640d204950145125404240c0c0ea25005074020b0700b81400c60440e941414640003041080c1e0350040500403030703520ba41500150503a205c1039070f00c801401ca00c401914610844042106d00c540680c031081c140c0d6186c0e0200d543c5038000c10011000c1e581c04640041c03035003480076008821541c4021620441601c203060660a1810048403601260810342c04003000800b040d204002c1e0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 8851706 1250 8850456 8850461
    0xf060c02010c030b06090103020c030f070c060e0108070905120304080f01060302011407050703060c1b050607030b06071110020c0622050105040e070c33050a0e060705090d060606050c01 81
    0x40112900742449900400e800144450051286c01c138141034001031405180141070003166100380511042a4882c192400d042c0c03031100b094000c020204034050458a000e6001f000b209209054540d1201c0c61103040400380442c10300c41d5410050182320500020071907420500c000d02c0d038411100c000040907441d50000400081c069034512001d480704202030408203102049840943e5003008010070104c2c0804011140c0700c40e1981e040324642085900c1070100800428814082c0c0802d540c00d106c8010f403142000000d100315140104412321111240a15040105042402e482227006840c15101e030040031406a40c89480010490041d0403072451000d0040080040501020702e001030500b400c10025110040f4041c06100612402061080811040b02445410301074105080030f80c0c180c594842020402070221640c01c0c00d800c0000107950a007a0384205ca18181c0c0183c010322a544509205035a6903002c20701041c0c20064110f14440400c00b54065034000384066510550340b07400341003800e800c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 8852956 1250 8851706 8851721
    0xf1f0806040f020301081507140703081b0405060a03090807020603090d1b1101030b03070801110a0207080f0a0b0406020c01020a0801030303180b01050118170106050a0b04050108070302030903070f060c0201 90
    0x40b40c4140010b00c0a5a07000504400080103039950240544a001d42074980d0584800c5100d141c000c005005c0e0109035002d07006601900c0600b105034020300108200b000c26014a001e00d54011105120b00503010740f094000c45900e0b8002d440b5540342400507008104140d0080301c209c03106510100104807400d40c0220340b651040c07100c0d14140f0150300c065488216000b407101d9401c0c101502d40310304c00d01c1503038140080c3c80104030080007008003000d80303040c02103141c0140d04031002500402c400040d481501003021410401030102616045030580e0b10304841400c0500160b4001d6401d21007106085024401020407120715140c0b13030348079859403130300400b61410151034140081010741c4810006a02058007410340360700b4205419403045088146a071601298404402d1203408003e15030100810740c0001c05841c810b0b94810400c40e114145401d6610441c0702c1d035030010308400c00140d56503100394055a000401715090b41d01c1c02109842c0c90007412400903041c1c4603542e6441d05d80a109409118000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 8854206 1250 8852956 8852981
    0x702090705040b0403060b0301140703060501030c110d050a0c0f060218011107050103110705060a1a01050c0303060405130203030705060105010305010906060504140a030b010305030c0105070503060f0f1f080604 92
    0x900e468100b0064003240e001313134403000b40101e86a010262880d517080d00115100d8800000c4400207250841004019120501c51740740403926140c1e03000f8880f8071566414080c1300001c2c0051050300b4001104503200c2c0d110411202c1000401c410080024008202e15400c440c01400d02607180c0b030050300407501030000d104029041c0070380c0e91208510204042445011985d090078000b60080903817203400345a20401100400501a010400050414983c0124900304101c0714800803034051303000541e947e11520185010a030700070f00c00100a441d00d03400482d402805034220f01e40000c100da011a00d960803c181c201c5a03604810700600030703960315120340380c0100807848060120a14000f0064154070480c025081e1544007000a04156282c0880c60401994442101501581d4908010381c0300c1d0810101c124880d42080c6c04101e12600c0780c0b081da03008840080c9032440300e20040c4200701e18840300c00442600503005003008113032a40444240024054240c64150321840e12208000480d101d00c003480 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 8855456 1250 8854206 8854217
    0x30d020d020c0108070c0b060f2701060302091c08090607060506010e030304060903030302030a060b0412110303040f050609010309050d0201020405010e040504030e0d1e030c050f06010b030610110f0307020907 91
    0x105c900390b440040e40036690303000069804152200d10104e6010b0302d205960740c1c3c001036940078020076142402c030201e02e0300454400202c990303600c40b64100d00340d00ca000f00c0a07034090440001071258001c40244038a01a100341c20b001e1170070110b000403038280e80000d50143c0309031359a04100041940c0103203000c01e4045040b805903241c54204140900b0086d0300e4000076040507400700000e04a10f00a0740118083e02c20343c401c40703403100d5448011450890321803c040f2230229100b894400c00307090000a039410b840211b00618600d50514003801419045003400504143d1038100a20100340280049448038100e0760015a4031801e0000160483c040a030319180070318541010040425840030300d5a1b0800710840e138170b41c4030143d42d00b401c544451020455100c03480b10004c03100201904041046030341e030b1145040d81d1004107030855403503c4072002d224522030450200001103080c0b4011441c120403101605011001070008a000fa203040d444407100c1c41950300002d801000c2d032400d1010703079500214500c1c01 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 8856706 1250 8855456 8855461
    0x2010e0604050714060c0a0c05011b080f0703051908100605071104050403140301180509010b030a08091314010603050c0a052703010c0e0f010924020a02030d020d020c0108 75
    0x201030b5030350b41900c00d41c02e441d40501c0803181c50750740d4a030468000786d071a20200c2c1c400381c0e007a0a10342c4120b6240c0c442c580c01700321100d600c4950840035103c03010510303800c003000c642043c000d04083c000980c4103000c102d080202c104034811350300854000f04d03141d081c003d0303866452910301700341140550540741d08140144a02841080001580c005035207844d000107840103e200e1300c40d0324080d00c0c501c000f0000d4401020000c0004110381c07503000149a41d96a82400500045d201c402015007204c524588507034041e000784050201044031390005054038030001c2c214031000e40301801c00c901107408010104a441c4202401005001d6140c01040e81107544020100d2401507806405002d40c81502c0301d00d142106511210b00c10481c00c08010101884054020300286212010042c0052510300c0a903205068001101285510a030210750564551204041d580c44440301020240303100b00300c410007184183c81e4a107006072018001c01840b6a89600140303c65001d540000e410003881c01c0c0303034a04000b003c908 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 8857956 1250 8856706 8856713
    0x1020c0d1e030c02030a0605070f050901020a030311090a030308270601030b06010210020d05060a06210905070312120b010c03080a0c02070504020c030d060f0e0c1602150a02010e0604 80
    0x120458109100060840d20764441d103030690750402661070180d814021500719105200094204500c030b60782c1c5a40e899801045484151602d000b220081801a800b895100340001c0c0a5844419070400c1100e4280c24554203100003900e020540c3c02c1100040d07054804d02c01c002041080c00300e130f8401000b089006040b41a017000e9541c80f070501c1b02500380740c44d000125203980d000740329184000051201c203543d180c07028456580540703010303100903010b01028103000504038480c0400d4003c081907105002e46517000c0f141350780090507206400361002d00803280000000740c0c80162541070001207840c0d2155000c141e00f40402100d4511106905002d01030f0300c4d0f000000d03406641160f00c0001031034009030800d00b41c20124904103182c0c00003a0040c1c40000e0304a22000e00201508285c51995424406161126074070301c0c4c2a415071003400000750201c8085004842d400026180d520540741103280388441680020385616680d40115054030750000d4999803040e820700440d07401d035080100802c01410584d6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 8859206 1250 8857956 8857973
    0x1302030a031b06020d060311040501150f02010e151e040807020607050a05011119030e03070215130306050402040525050901020a020303070804080f19020411072001020c0d 75
    0x80810041a2207103000c1d402c000c840034089a00460115100c0009003c2c02006000e50301051720700ca014011807031024940360145038140c403400e00f1600713112840c02c0300540382290042c11480030341d5260380042324007850410200311001c94142190b00709007050440048e00045603c20030700010211005c02010600c00d40440d65a1581039520759510f80f8941006c504101d0440f41c01070441d420904030b15022890000640500d0692210400741c4500c1407409074110348002c1c00c01160354205200740005031620042c40c407038541050200034a80f10550150130007030b0310141c008a504580d100d0a02095040030b1180c05d0b40a209490448007004101c41d80158900c241c5001c44200034000035000c0d05070b4030031303c00c5604082d40079003103035120060703071034400c10a40180c007401e10140329072102070714140400240c0190b010a03078541d1484a042c0c4c1d4080c003000d840001071000c4450410400c020004031084044115042c5e030900850b0580d00782e00c0028241113080c0c00d610b12035a40000304e80040f44201 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 8860456 1250 8859206 8859223
    0xd020a230304111f02010504110103020c06010e061203030703060602010c080402130e0304080307050c03010b010c030807050309031303050c090901060b0f09040b04050f07080106020d08182104050306130203 90
    0x1000c901040c1000e40080c02e038100d0301404c1400703d0450340b460a049501504418091442100ca4141444051004504a000311355003c2019400b0400400c600d2003804200ca401c98130140c58001c0340b0030782c01b14403803071640b040c2c50300310019544200400c5419030a20426481424504e0700701901e007010340001b503d42e8030b001c07425092207a540d59003002c05001001141c004000101c03d4035102c0119041280c5c440052105a41c029400e108890140390f10030355000400560640320318146440d1010100da0030b41004004070003502c420081c61180203031141c4070b603000314880e500610755080f1103404e200200e84082d111414a0381482001d10055a00c1e5003070381c0c2c1580c8800e2000351100c075440b00080140c42c024015541041ca851b0600618082c071000b440c0c40341e84540c98458440c0d9a91004a96801690700c0d401c00280d90b10f400700e0000c103004559100603150600131511440043c510703158000c0320302000c5440d0b01c0f034002001c0200303040c2441401d500001061038081c2e82c9240341c0100f5100d0100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 8861706 1250 8860456 8860463
    0x90501030203090a021009061101020c0703080309190b0405250909050106030602070b09070602030901020c0f210f0705030109020a03080306060d02070b10120f06050606040801020d020a230304 84
    0x840003038603109042100d01320094000f40140703a201008040074000780ca2901030000042e100c010340e015540d50500841e201c55007041c008050142c03560310380c80c200c0c3e00060804c00b002c0c0100c0e14940742c1001030000c9200110300803403401500741000c0c07400e02d01d880c0080e0100308103a0403142c1c490709840742540071142115030782c81c404500d0b20894604540140320a4100804103840811202c00380890303031124030311079800601112030309a21004181e0742e03402031085585c0180c0c0b1082d042c0031a42009881d261220b00c2c05020501902d080342c1d031219200d8002c480d000415402800c00c01e000500400c419401046c0a4000708a181110b401180310b0a542c1c1c04083e1840c032001000c642980c890700100c40001403071200464480c521b07441c0c103c00003141a61500414425060040764000c42001100c2a142d4003140c03104070361003a81e980c000034003401400191300c01e50601c00000c80c40000c2c001011241c0c8210001640c0316a041e401034051a0b14650321080110303001c2c05251030307030800d00c1103d0f00680c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 8862956 1250 8861706 8861711
    0xc030804031b08030901021e040b0306061e030702100506040e03030408030705040e01060c0605060603150d260301030204140403020d14090d0605090c011d010305040501020702040203070c030e03030a09050103 91
    0x1640b01151005441071500140030807400002c10881080640c05844a0300c1c1441481142c0103c501000c00c06001d9405500c09950040020861910786000205614000f11908104511104260a400c6d0f0030803903030780d03001d6000602c84a00704d454500c01d02c0d51115003201d0802101c1c40e280d00440d981d0000400042c00c0810000119500d0fa00903400d660041141104c000c0c85503840e07100c000c00007815207108640705c41c100070111f40d0a15180090b01c0c49240e8076103c1e0080c10501d2000c01100d40700c9031501307582840408458950180221000d6846040400081c40c2d407940365105201c2180d5043c40740408058901062200096011403809081d5204d03240c4100207807031052220b0504c2c8120146213904c450122100c0c1c04000098211300d201c3d031000d506403402c032041d00c0015914503443d250700360a040c2d04189054186d41c043d500003500a40201c0005003003012a5020030120703401981c80c0004200059108000c1540c0043c82607490042034014504001c5107003406804034000e8085c0606054 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 8864206 1250 8862956 8862977
    0x50a09020f040c09030204150509070f090914060d02010c0203070b09240f0307032703030e010504020a1502030f04080601030b0108030702030c0d0f0501061e0506090603011208070c1d070c03080403 86
    0x8d9400a060b005100c1c1429080030807019100e4020208100080340c80d500300007803c4120791282815009000303140b0382059640404006960312891400c9052007520b04940c00981c604010810161a013510441d54034864541000104e5400c803070a00c101d038482c1e0781420791001080307090712101001240803540b00e884021047e0054240e00c0303141d003601d08048045016010350141c171045958060340b81001059185004142641c0003141e003c8d402611300441008000001300b85040c01c6003451050380d013450b480000591032584168484421980140b00501c14814252551801005400f006510f80903980c0e020a49031a8900c10151180c941c01d2081c0c1c0c01d0001c070b0b4191502c0c07e03a000d0020400f4988510858140704205a00140c3c40650700d40f0101c0c1e18100740b0103c034420b840007801c89046030b183c948a40c1414044110440c1d05110a006040001784400c04136006005003160400300030109400c0d48541c140014400b004000c0780d4000c4c40302207500b02c4100d503040380d010b182220201 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 8865456 1250 8864206 8864231
    0x2306090129010516060203040501020307030609050709030228030c060905010c0f0813050301090309080c0607020306010e13080409020301060305220b1b0d060e060306070816030609050a09020f040c09030204 90
    0x84c20480406020107000000300700420406500039441401c41e0780b001c21446850305030650446030202c440300f000c501c2d003070303400d00162814810354000d001444a070281c24402038610300e2001c1c14103900441e0001d0340c40307400b84841031f008031200707000d05000e1801c90060700b010b0f1280072545c0031188000d0013802000603040f55170002e40340c20701c001d0800600288814941c51500410850251113102d0031805040ca100c1030b54030b030801c200c81181d5001001402c069003804030401c1c426201030410700007106907001000001e071a10004e4801011803280040e16507240040140c2a103100400d03980c0c0908240d5002242c1640503000c03c0201034100042c002203595840c20803003d0104501c40614600d80440e54a00020854100c0c606031911103060150070b44800d800d050b900c0405035103a10115000c0000105c030700b14510910b0481c044146008908555140701500807a1030941d150320f040d82e164548c01c13003542005038103d00d0703d01060340c1c1040b0503111000014039480050000a101d5a150941d03844803 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 8866706 1250 8865456 8865487
    0x6030519090c0f06050c06060301050702031b190302060103030e01031b0c050a0c2309060105040e0705040b13060206090a0c05041109060a0306030311070609060c23060901290105 78
    0x1620500c0721801c1201e45030b0f80040d1464000c400d1501c042c3c032554000400b227041c1070060302e0150349a0340056090070b00502032100a0042c00e00703e4170380340c442d10a00c1e41551480090f42314546000760090541c03541141002000380707185580c014180b41c140005040441c540000c10181040c81d480c08030300c810719a1814904202c040c00c000fa00d0003c41040208040c1c1d00d1240d105c00c003030407200018141c140f01c1000d20010030822103005000c104c003400200110300088101a90216040c60900d00e441d8440f003c02c0d840d40c1194910341d4000788880d10900146d42c04104450b0040c940310001e002c904107690382c1c1280101c413401280d02640c0c070b9078a1b41c0d010080410550781900c0e8001e00b015260364511074020003c0400c0c0c4010307000540d045405800c1301c0408162503003518981c3d552514898140981603480a0402608952400340c1ca80ea00150401d42c00c882c050380304074000600040d040c04000705c0e09564000d400700711504260100811034201c04036000c03415480a00b0060740b91442c600d009000c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 8867956 1250 8866706 8866709
    0x3090809120304080c0409170306030f060a05100605070c06050c0705060d0b03070f030c03061d010504050106030212010c0801050d17040e041e050d0804060605030f061006030519090c 80
    0x104890300000700000210084050403c3e900a030781143d4401c80d0010400003943d084020113400004420120b20f50913118a00840e40808058225040521000404d601c0c10100b20b40e04002e855591061001900b2800008002464139251179400c0a48030380b20001c80c01c8207032282d0400c0c40000541c0c0c441c00b51080c00300030004e01000b056503469985100c08103003d40f404d60304003072080c080c181b40410f032201c0d061058000c0d660001d00d000704040c10340d51150010715811400501c400c0c9143c030100322081c401d02034588641e00c1107001040e110301c2c2d0700c10320882d200444400201c90341840700107103036980d11a13080e60440d0011600a00d1020050900c241000e80c4058051400d100000700424045052a50301d8000c074410501c1d841c0540070780c4c11040240000642c0203025822000894030714602c85c1001c2a0000d005082c009202992040002e203408942c00c8400b107160840b004000c1c0142d4840011002801a82814021441d00c1c0c000c80030381c03c2d18000b610402d01e540c0c480e13050034000001c0c40c0d41d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 8869206 1250 8867956 8867959
    0xe15010c03030e0d0503010806060109180902010e130b0306060609010e0913120f020601090612030810090e0a0201020115030203060415060b03010b04030221030f16060501060e010801090c0f03090809 87
    0x1008000c50100c010017581c005d0017080002e206041c041100b0f54421204031046441144043c1800c28842c0a44c60151040f040103034100314102050400d9070b552919041c0301d10410410024400f541c41c01403509101c4014a000c0c82203006200800036030340c0181c901005514100c0e602c918660b10a8034000c0103201c15074000d002d000d02182501c058540080303507540359144c96001c485240c0c1e600c0c40e01c00255099405240c030141400703403b540000340942e040a410a00664549140300d40b01d440312002c41c2c04540080d00103030302c903809200c25940c080c0303d00e00e519015040785000c2541140c011950782c50024100814001c21031200c2802462594022009032540003e5607a40396594011240d01d500207010a0384130700744010368003061541c8125289200c0603900041c50070800c2c03041074044541c210240d014141480d50040e807000030040e120f681e010307045030b86880c1100b8190900040000105030070000269107407181d1010800d81050102c2c2c5094080d240100e04040705181080141c09100c020f103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 8870456 1250 8869206 8869213
    0x306020c0601030b01080304080a170706290607020a2610060317031005040e0304080313090506060307050304080304020a080d0806010f14040b09030c030d050702030105010e15010c03030e 82
    0xc1099140c003240c014100da001d00c07421001030f622081e40c1510703481140306142003540044500b00000340da800c03500d005140003004079420017845031602000d48001040c03100ca42c400701c2d0702896000c008041c10003a03e050694140303083c07142650100c2c40c0710307520780251181c81080c2500e03000700ba07000301d0070b0a004003051001c1c0d403050602034010304007518050004440c174122103101c980c94031200ca01901d02c240c1d802c401c0c07407901c9031030308003484018400c0c80d01040e031600007044080f542c0d1100f04001c008003000118800620751521412004807140034080520a00081090018003030f400f0b0290380e00f09070040d4009590b61200e00c00103541400c02d03440070055006945807104210380100a661082c0402c1e261000250307001c200c1112150407032142000000b00920060268036401400341c07406400150844000f421034500003131916a42201e20f078005903001840c0000c45c1420701a49006083e00c00711080581003aa5503024001440c004690400000384000070501d8446d80140c510a00b81c0d0054 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 8871706 1250 8870456 8870467
    0x90604021309020703080a0908090108090313031b0b090a090b04021e09010305090304050d030804020d0501020301180b0a03030e040213050901080d020712020906060d0b03060c0703110a03081501020304030602 91
    0x41c8006500140c8085d0085101d00c070000b000724090f8026000c0b50307039006418074681185d000065590400280000010b88004e228003955101000b000c40083c41c0030300003140700b403606407090121044040c0c10100341c03103105100054407074454004450a80d0145003011444214132030105009004411300c10490000d4052001f00c0e01e07172400001c0c4000f440c02eaa06101d42e58560103c6d543d28800c0d849840e030050307220101d00010030303c900c6019401c644000c1026440c103065403129400e9030001e0300114003081d440c0800300d41110701c40c8145000030a003591010819840c50300c0c0034181c0d200b400e04281c040d503000159480f04070100003074000604401002800d040d44c4628500355030f4525500c42e8400344c4541c00700840c0c43c0350380890240d14541c1c01402c00c0c7c810f54032402404060780105031448000ad85034000452160303014041e107449040140d0040e0388a00813418014aa00c5442c030740c56034150007500125020a501589099000900c903e00714a01015080100d16611559201034040c91000c1907 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 8872956 1250 8871706 8871719
    0x603030509010e01030515060913050a0501080d0207030c09051305070b1b01020306060912030c07030305070204050a05130201030b060c0703060902040c0206070e04051e1003030801080307110906040213 88
    0x64149007900303070303681081e4103441c400550844d801664100c0305619003800804403444d2900c0201194400948a03641106882e14600203580003a24001611601e41c00103000000c010801041d000546e8401030060f00d1958a500c1c0310081107001c2da031052926540000d20042014909007203103540441210300e955a500908a000e41003034100804418100101108079031050080d42e005e00300040c40c1078500b104d5001000070160f060081114240000e2010505461091201390011030003a11480d555030000e00c10003085842c02800f4003142851300052003d903d6220039070403403c69080c28009900b5580000284550182080d100703803a00c1003c80c04410000030303800854a0603c00d81d02400b0140000b0b60a80c1c8a5208440600004198034485840d034030f020341011f50004036041d501c4405c41240100362400d07030300440e83c4003140c1900c4c450030400c01da4007440c07072801400d00101840c00c100060340c0d010f1182e00d10148141c400d112000c00b1514655640e81100c02042500c0206000b840d628403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 8874206 1250 8872956 8872967
    0x4030e090601050702010203090f0d02060d0b130603030c030e0a0b0408010905010b030a050303070c0c05090703090507050103060b040608040c090203071d01030204050d080309070e150a05060901080c030703020c01060303 96
    0x5a0340a40258408929594000c00a448420394140c000e075040030380000501c00851281000c142d4010504030001015882e081c000b8007040b860120302003000c0e0428020f04c107000031091405440d161902e0340030030100385d11803001d200540c1e152504c0c60490010344001140c411a54020b9017003140000b500091208056103c08031161140000b070250220315020151181620100509180c208000141c2c115100b0780380005061306c50800c4100c1642ca8802140c3c10a0f401c894910100380d80302000002d10000b0400d500041c0400d107030030f00c002410f0040c00c10b51400399101da0001d020141c0082401c0203d2036504201601e48920308540324940344500911810f9159005800c0150340e1204100e154868000c0303400350307031002e002060152559540c104c40c2d903000803d880d50740c0c000d501020a4019803403607114011201c442e50788030040c140c0c10401603603440761340c0031500ca6002000140c000c1c0e40c100d004c85504c188241403003034581c1d554840540c081e2240b443d44d0340b1035501c0c0180101c109504131 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 8875456 1250 8874206 8874227
    0xf060603060302010212040f05091003050307030c02090a0e0c0f01020f15061306060c02060a02010e0a081309060806040f05070806010602030310090902010c11011215210b07080403090305060403 85
    0x2d0382200d818404964031001d581c0b00388d000b0900c01e81866542840329041a50005030011209070441c03031550f0f5252101402c3d40c114040460010354401c0c000d406618180f032507950807103180e0808101e0503010450080e50b4010713a410b44c80c0503106480070080d5680c020720410b00000b56100c140c7d8403c0c1d20700702001c03048070001c131011403040152580164141249110b000255007482d11084804200c070f40800c01039030010f201000c1159200c981c09020300f5024021000f41034800c2c642d1079100c0380340c2049541908043e810002240d450018100098074000035240e8116401c03460b00b402c1c0c0243e0382000c504102c0741da08480480d00c21a800022281d50000c021807085040303907030310101d0039107400c4003c1c2900d01041c006400640043d4181e00454191000042889c3c81410320345a84406107401000b030300e002c41080680084114010014013140000b41440c8e080d60b502c9003402e0440030ba0701d0207080f4a01401c10301c108040c8000240c03c01d400303108108080c640190480c3e01c039150500c1d0003040349405 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 8876706 1250 8875456 8875459
    0x10807020a03020d08040c08030d0e010b03010b030a020d050f0303070e010f0e2d15040503010e0106030f0f020f180a060f060f050c0304240305100509190f060603060302 74
    0x4001411151010540052059055025042c1c0068416007101c02400c094002e036290001c0c060000b550080400003861a07036220781011580b1140300341801d0071101d020300c00d9806a4100190032807a5900400c4c07407031002e64111020f4250f14882e00300246001e56180e0441c0b800d10000050010391900001c1c1205002001d0740c940011080b40300048600c1404175a000e50401c4103410404869034011030f051095011500003c41c0000c06400003c0c124100100102c0c000c6400240511060400f8099031701103a020800a100303162a580d20500d150f0255640501184030440b410b804542e43c0120091140740018602c000c40c0d6164801c074100c00300140c80d10300300307645028000901c0c13840d01e00c00801125603942310040d5005482c00e0a584c039a00403035089025002c1003101055000412449003e03c1980340c0c08805c009003980720150841c0c402400c1030000200d09402000a6603440345143e621070a0040c130740c080c070f071501003000011308030135030480c0b403480d04101010401e01d03032552000003200d00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 8877956 1250 8876706 8876717
    0x7060207170307020a05040f090204060b0a11030406020303060105070305040306050103061b080601080a1503021f080112050c010c0201020312090d02010605060304050604140708160603050603030a02100f020c070f0501 95
    0x6445480c25660303c1202d800941042da020410001450254000318000007000c0001c40c1304d10341e65001a0444005800010411401146904105500c41548520a05c1c80c500440c03509040010185d035038040207001074104280040d003030080504c20815280110b070710090a01032541c580c50a000038000e01c0c0201e00e40411010000510280b0a01c0040c1c024441a1100f0906484003d03008001c3c00a41c5044071203070b403503401d0020060f211445100e10512004145001070802014000d00c50078040e0b118040d4110254880b2022810200b080102c500302400d000188014a10044c0e046004010604455104410401805603004602d50900241c03d60081210a454008001c202d00050710040c0c041c1c0e11490005000440500c0002d64502840c0700710b030100e03680c9001991502d8030003000b00c00d04160800082002a405000d02d98000d0000c40284d414030451401c000e50b244d10503c0000847c42e16152128030310643d030ba04130740b0b1503c0400180d4200a0700e594001569041503c10180001d1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 8879206 1250 8877956 8877989
    0x9060c050702010801030b06041104180b01090305070e180303070c0c05270901020c030a020309030114060303030714160501020309061003080412020102010b0406030506160201200d0204030507060207 87
    0x28810030481d66210760503180c0d802940d00350b88800420040007040d40d03802c01d54501c0362540283e0600054001040850604103858010080100541d000d92074014188001c000040c00002c001141450503034045050042440e51031447e01410b50380e4810200309140070000602224070341c0002c1400840c0d0080035000b401076a103405120510701d0a0105960361400c0d40004140032000600c1560080b403040005030810f05003030001070550344102c024401680c0b0010781c81c1e80600b402e001d20321001290850303181e07143c500000400e8503480024428407c00078a07070307551030340d01c49000f040d5090101503945400c2101310600d031080c007e41c030596400405204170000a01c040c0008880107080c0e0f41c1c02010036040514194401e0389484102400724195501c580c01668103480e284a10002140110010400c07407d051120042010500c0402030071641070000000060011b03000d010680345400203141d071b0b15140380c81404024050380d0001041030040800c0000c48640c0021050240d4a0100c84040d050 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 8880456 1250 8879206 8879231
    0x9040608030306030a1104111b0105010e040b0a020706091203060816030804030201080717150418020108070c0201020a020907030b0909150f071107150f08040c05091801050106030906 80
    0xe0100f2034402d41e069000c4451040040c0910004c01c4207018050408140f00741c0721040285960881071003150408014000014041c05c01d020311030041590b121210070a007069124a040d41c50002c001e5242e0a40000708801086401d90102c1ca4180d0088e80c000f541d1018080002c1c043c0c0700314400d91065101e44251141c02d200303112400d01c1165803020506140515690042d00c030320304010026410310502c40b404c0358000050008035071003240b84081e001140b03d509010002280caa0309003450202d0041c8140d40e0050360040462038109400d070034510320b560640d04c0106d140c0089100c1c02504603039204140440036425421116804c141100c0101155480d25101691035800c1d08440c0402000c00b404968951414500c041e002410347ca82060b045a00ca0103852804070150311058100c0847d07455030040f1640503035401c1080810340303019a6942003a0301d444190302074030300640b8070907020440421745c180c00c0745a15441d8500c80300000d0000d90f81d1110003500170900050142d66842c00c000c0103011740c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 8881706 1250 8880456 8880463
    0x60302030901140f0f100906030f0201090803033105010e03210702100506010504031a0604050606090609062217060606030915060112090c03020a0902070503070f030504090504030509040608 83
    0x80ca813207051610550f515001150203690f400380c07400c2400944130b80e0100f0800c40600900340a0742c010030404079802e0b018800100036015036485120350360814000c0c800c043c0c900980d180e2202c1150740380d00341c03543d600e0035441a1001401c2001809507180ca280e0320354010000c0060f15520700513000b079610948000c4a40c9500f00d000300c802000580004903403490844c0164002034101c50180351060400c1e440b030362429510702c155441500e03084a07400401420340703014019154860b5044c0c2c2c0060401c440b490201c0c0207409240003403880350501081c001c42852403030001548110340c1c0b2070f029010940d281c070305072140540b0510315081c1c1d000e0000002e42a041c86002c0b0390240d90164003c11190424040209907101d0150000d410020180600300081d0118082c07181224050751088110f54a180304002c600074031648428165801840030f40040358011041d0340d1380725000754501c00c0c880d25501d01100e0700e01c2a40c2100380424078005c24041813550080c0600b200344819201001802e807510b100c16034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 8882956 1250 8881706 8881711
    0x3061505010503040b0a050907030b0406020304050c010e13090203030d14040c09180b090a06020a050c07080d05030403120e06010b030906070305061f03020d020406030b18060f090411040606030203090114 89
    0x140c2c0c04400450030005691f40050340c8031030705030f05445050752a541e0316044000261001c0da400394000c0144000e00c00c00740303c44180c00302c0074280b54091280c514041501070044180d040e00407980c038030404080d5141401220380410070103804024020110030105110340d400d99007514802c17900680443e1180b150300c60f42c0d0441e44030304c145840000c05a690306194107401454038100d0300460700008001401c1d8006080c6c44a5107449541c0c80c1d246a042051601c0707104e61110703039942e009004c00410950070400b180e8005800d40703000301f80720355150700d0310000e0700440b010f292840c4540b10000407006400d401841c014000541034840355150700100b101950003d442d0f10b98040300075151a80c05000f00d001b07001010f44181005418143d401103002c0407a005940141c0108c0c2e103030445802c0c01d1600d000c030503c02803285550403134a0b040001c0800c903c844c0c1c9004442c02012858045424446010040c0308102c1004105002c9035499000040294100341d1b5010701c15030034121303524803003e161311a507403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 8884206 1250 8882956 8882963
    0x12030703112107060209031006060f080606030703111b1f020705070608180604110907050a09060f11030711010801050303040509060f1206040309050a0e0c0a030c020c06040306150501050304 83
    0x101a1907510b40c4100240e10506040f01c0b22582007000c10580d1320140400000c0c08860707a8000b942d00d151410290a4a0190b04003a0400c07034114100030040d0340e80026030340c0044141c600000d69044482103009540714a0305000d2049022103401c2c0030541c400180449448003001c1c40c0b030301c003140c2c001c03030340741680940503000348a50091f21040c80a503214140a59009040f8075036801c140c004e8494503400c1080658058400c4900790f0a90021803c1407a2113a42000035440c00e28a44030b00c00c1e1000f084a15140075110800400c1d62441700c4051040381321b01001120034041d00d90b07442c03a80c03034240002a0424a81400304000c2000002c4030320700402030f034040364005449581c0940d5044208002440a03800b40b685c003225003a8981c03030000040201c1842035120b612455109400e0200300041242d16900101e00740e58a5030400039444000c01c141c86400b240341c28041040a0400340076814503a540d05890342100780454004144603181e0400e807500d0000242c40410241c841004690318402180d015 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 8885456 1250 8884206 8884243
    0x6050f09010c05010b060f07050601050609010207030605070507060203011401020d020c0a0506130f031211010605150c071a130e010b030106210f0e0f07030309090f0204051203070311 80
    0x190003a501951a00c0070b01803140f40001140201c1e02e000810325040041103000d0345102240c004100802080503502402c011a01c05083c0041000004d40ea82400c0c040142500c0d00c410100711f25500500039100055445041951030f90b8582c454048040c0344c054085005226072180091000e0000c039621007007203030160040150074180303402d0004690100442d0f08002c501a40c000a0008980c0c5592004d14031a610519501800301d40c02030401d108007900940607403502d10704220300e596000364246000070301e00d0351039141c24458071402d060030581d074051503008100c0c690041d0b40c400780304001d140d5081020b81009000707840c4c040d000d19610007400f0740558220200014480c4602490210000c12454030703101c151500150411010f56500301892800180c490000070100c003414004d1004408680008200ea5450368500030240b003058820b250310b040d5290b0801d5164031150f01160081c01014003182c010f050128056640d03503002d40750a80019090040e80200e016000c40d240030b20560b1103508 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 8886706 1250 8885456 8885467
    0x3061e0703110702060406030203010f090608030304030806010e090708010510080108030307140417030702040e0a0201090605030a0905011a09091b060901030f09030305090c0109050d0803130f080309010606050f 92
    0x6074010300d101d103140c5030500802e10a002c0103a1301d040040c0081c02140c0e80150716549810346886070305299802c0aa0080d09206080c04403000000030fa0f90f020780c26160040281c4c99010062b1104100801c5042d084045902040b042a40142032141200e006036100700c40c564003e41c1c101e45041081c05101680c7d0010404518011300c514045852080c002c0509031030b091361900603240190040311022034680010406405500c0d041c0b14103d500d89611000d000e410109600007060400780e0f000b0300301400004008200d400c85581d002000c0264008020095003070882644031400080c064010301c9010343d100020154440440c25826410644801d0000550f0300410081941c01110205040680d511106605001035004039500640251000a031504100b581d46003010205080d550500404020410180d11030100c82c11007241c03c0b4101030303180c0d125001e210301d00302e000c0342c2c01402c1e500e8001d9600d0248481080118000c80e0084000c110095450100307580c18007803816000000c000910a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 8887956 1250 8886706 8886721
    0x40c060203070b0a1508030c010506101409010f030b0406060201020c010506061603050702030a1a090c010203030712050a0f0204060f021603020a0302010c1401050a09060e0303010509011703090904030302030603061e 94
    0x1888a400100000d14170041c3c4444690b451038001c03016a452030b13912207092180b41c1c1401f01200c40fa22403540b51141d00e0000e00300c1c1003180c5110700741c9840c0c1007040030030316807490511070307031111180300c04c020001d106082d92040000e001c0d401981d1b80d01c9455103050045001840d051003140d9200c1407900c40c04c802013200c0d40b81a00c098000c2c0c00c003641c15006403128980001d450b06201102105409041030f07140c1001c050042c90b04100b0350303c00707066500c2003081c8820250000d03544000405842c0c13020032642d0390440c002000c0c0c00303c282540d400d14008500460391030780240c9884015600d0b64200c51406900f60700a0400c43d60710b04c0060741003020702c0000d1002d5481500d02c2c4105038040c294140c0c0c1a940184107500311001111a1010969240c407440b0400c00745006088a405040740154119414040001c0c40321304c061042400030080f41420400009040c0203480c4c00307040c02412a2078034139144c2400b8010798001c5410602c00e00401c0002111240703d500d80c100920001800446941d59001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 8889206 1250 8887956 8887961
    0xf020d0503120103380606090f03010204030321050105090406050a020702090f10060305060a17070905070503010509010504020a0e040b0109050307081e0a0807080a050405060c06040c060203070b0a 86
    0x340d510740010042c110440c00e460040034000c40c81203940e48201501810003054088403034025030110b00503078401043c03071542000c18a82040d070444c2c000782d64000c0300c03000500011039040d03080c1d01940003003400030900d500003542010b103000c00d01d0850200355005031000210340e424020a58012001800301c0e002c20340d0341e0300142d1720000f00c05006180c640c40b500001c0d1455400c032803288400140008005075180602d00150080c501d50400740880d051803400594801d06502841000c130001e1001501c0f5442c0c100001002001c121808004a00340404001c12503031090207418099010030b070000a00c1d041030301c201e4894100640d581e0484420040230403000d40b21881c035160410040510100f00d0b07035014030003400140204c000402d2034003220040b0320000010354414104981003005540089180c507000c41c0c000701d42c40b503e00746c0c2c0c4451584055800b8026a0042d0b03401032000315800c10038250005201e40140d01607208480040e50b1001c0403a56031103050340090840c0c1401c0e0214180c810140c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 8890456 1250 8889206 8889229
    0x6170708190305090405040f05011b0804080a02010603121d060403050a0209061f02010f18020303030a090614010b13140a1a0d05040309060e0a1a0a02012004030b130f02 74
    0x915003e4a8030b08403000040035180b0943d81030720070700c69500c1101c2c108802442840190140f401c400c00819144920180140c040144007610744500010a00c0e4014803c2d40b042c000703158031986032640031022020040400c0c0329002855000b12201e0540e0280b0b140c075000f078078200c0380c1c04001084840044da00780116074402034407258005907210128811516107140101c44403d40d036000160a6003011400c2040e0b44003901841140b032812515400943c40200c103c1ea0302444514001c01c1003200f6281140090038a15010040c6503071410001c109102c0c0d0000600d02c400ca00060300040d5900c4007405103540351010762241e4894504082000b601c1d0662403581a404951006a81401c2030b180e41c1d0801c0c0c500440d4110300082c0b03240014402c0ea50050405910401c06940000a603401c04e8920084420980152000ca20010440c00c2d507261007500882200206000e030b0a42d200c080b81e50400944d04207020454200c5098030000703c5c0c10b01c2e00c003d804c90164014001160409050302132280301c4405 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 8891706 1250 8890456 8890463
    0x712031802100c0303050a060b0301051e04050f06010f140301120501060906030303140a0209011b050c030a0c060e030c0a2904030b0103060b0105031014010509030609010617070819 79
    0x408808050b0b603890a0600c0e1014a03501e500701d039000c6900d4018200c80000700400c0d4150320700310003441407100310000e0b01d05452040d9001d0340352040c03401c0d002c206440302c0d20506500a04000400001060605989009000a8840083d07002c07549030180c500d130f9010415642d4001040c00100415018029071031481800b0300d000040f41900c501034039080e6901d82e001500402c0d03d07170703082c400c074203a00c80a00c40d406010303030904605010080d4002002c0c2a00b46118120b0701303e13542d002c1c43c00c0c4401882411151540202224404011850b00c5d000b0494148107100100b282103040c0d50b41810041030404020200800300c4101c10304116031847d68003264a90100c2400d040ca03100c060b0711680c40e00500145001303407090820f80d0303d18070b0301c00107480c200b86001c0d0401c0020301c203001300c10300c0d0105041d05a866a0180740ad010605400403503c6000703c0c0e03c0300394580301c0d0302c0902c1041d006c1980304805403000d11142c143c415135031501c1582d551109105204280d80540c1e4481c00c0d8085045942040070312 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 8892956 1250 8891706 8891741
    0x203060402092a09030d050a0e09040c080303160305130803010b0a021204060201020d0506040209090610051e0714030a0203040b0a0302040504020a020c0406090501081b03010b0405010e04030e06071203 88
    0x900141491240c01e50300c400741064040051801381c10b1408020b1000d4040040c98210711f0a0f08002c8000c102414001c2403e01030044880450b040002402484002e00011000c9a4070707841c02c002c030105100c40031031942021901c1d0201040b2100941c25920300015040b6407814656480c00710000416480801018110701600102056807800b41d00240001c00596001503200c42c01c5d40300920840d040505014401d40c410407000c1125100c00e00324603070107001216000c60784190118145c07124030446051052018001d05621040d406010140c00c0b198043da080b0144ea403a402e080e40d45d40d00c03070b00201b240540d009000401ca40700400c0010b01800e10380d440d0160415941e5000316050341c0100014030050f07001410380b400c41e8106440307041c00506c0d050720700b4845549003d07950303a110382200350404034100710342c2500350b860740b403d4228100428010b0002c002e01e682d11000c203000381c1c6003520205c0018101d2900d465403840c10009031000c040e0014141d01c070203050054180c009100d803a02c801c89054 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 8894206 1250 8892956 8892991
    0x50c04050108040c05040608030d1116020f040908040603090b0a0204030206070b040309030203101b180b0702010207120609120503070f03090203100f020301050a050406030503040302040b060c0712020f0904020306040209 96
    0x11224012000204200c0c00292b840c1c0c03034498211015035500400046032400c4c06d000942d071407c80c04071080003072901500e00803034a0145c1e03c00308024000c0d074140902400d0001800054050b41684040c0c0c1282c021840c0e1812a20b41c42404070036881a0b12011354420810300194011600340008650024443d080003a403182c0d80345e0109040c0390200b04000c0b210fa81c3d8a0203200540d071343d104034021a19032803a140c00708620103005080c6880e018007801e80d00c0440401c6e0402164020001030000c0c00c20224444114010b6281010280070841012102c101049000d101c06a0007141a240120241e8644c1184011032140850081600754426685031107610f03174120144007680704d100044880c0c2000540d996040000f80171042d01c0562040780a5032500c8010400b140011050f902035946c111000315a440c5418002685070050120001e1540240140000e081d20710100340b920032882501c43d503500742041c004010b00000d080798041e4054001c00300050040c074202250b96480700103200e0850044 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 8895456 1250 8894206 8894209
    0x309150c0304030e0d020112020f0d060801060609050d0f0b0a0209060c010906110403170f07020a0609030302060a060803030a0b01050c030a0c050f120a080702070302090a020a03060801050c04050108040c05 90
    0x1a425100a4600c890020911042c1507001c0f212815443c019100441d03449800e034002052034080001500701a50b011450100c40c071050342c220781040f0000042031000e9600c80314403500900740b500c10000802c050080c00511414814900e1201c0b60700103001c008180550b031206007001d040240240c100700c0e03080000c0c0950740d503400040c00300100c45c1000044c1b1741c8407078030700a800c81d03503650a03015a0341024082080003600b181c4107003c6040c1807140071611201140c00380e40791130069810096000021b1840800c0065210072107a085900035401c880f09520360b0760030401100e09500072010311f074204000061200c1c0d00d6401c0504884410301d0901e161240c214042411500076229910000b0000400b000501900300200302c0e002c1503074000f52246d0b0004c014070f1440c2d0f1158582d00000d00440d88002001e480c024400f0078011074001e062030b501460000300301c800a602c120051804a0301d055000f080100781481002e00c10444045118a81400c1100540301c08500500c102c642c0d49400c100170606 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 8896706 1250 8895456 8895493
    0x4060b0612010905040b0f01260c060a020f01051303120b010207050a080705130e0303130c080a03030f0e0106030c14040605040204090605011d01080c0c0102071a09010c08060f0103020309 82
    0x1e1000c0b42000404d400c282c606101607280182a40e00a14414001800062400240268603082400c809030728800346200482c01c000340c00301ca199000c480460200360454000c81c1009206051500801c03150b91510301c1d40b0703400c000410001c0d0000b10f50108401243d019584507074035481d0140103d404503551344001070000c50161b000341c800c81d08840c804014031300742000d200142c0091640c060000200c4446000d50b2404000d010904504aa0710010180710300c51070320300007801d014801d86401121a0401401400a04003000c0b905031510080700c8c441907041c800d620983e6440294a41030700d241144045a0551468110341d0040e6260310001c0ca030354484c801071000f0f0190010210714949400009014090500702c240c00c0c05007901c0c590745480ea4080302c0c0c59402240015a9900e603020300701c56038024080d80308010541da1082c1c03407443e820b4101608240c0b04884802c005d104011401c8800c0303d5004094907501c0c1c0103007500da501c009540c007a401840c0d1041402088840c4260f20b4038101c0740 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 8897956 1250 8896706 8896709
    0x308070e0a0306060504140606090405041401151505030906010303030f0b06070f0203120f07080307030b100201050105030d0306080303060d0f05070f1a040b030a05190603050609060702010e0604060b061201 90
    0x95050b0b4a01341003255007082c3c051080382c03c844820551062500c800458850310802a1451050765200c0000c4e04118030100c9074030444045500030890741500940103220b030f4130f40707010b070120080e440c0204500c500e105c1c1c400c40348601c002d100905001d17480c40c0e4040c1d02400e1a0425004115226a1004402e44030760014009490141c18a2000790400703005050030140c401408800d9901c0811a45800001500880700f43c0c5038403642040d5030f9600d481c2c3c124010401404103950000c03490100e0007a141e4150803d505a038411402d80e03c40c0da80464055080b11032600c1743e4403183e0400d100186280c6040d0391040103550280c217103c4c070503800d030340e41d454202780340743d00010056102d03440d041c03200c00e000f04201c4007002c2d00301107054078040c184a400003a034000104075200454662001640c80e004c10880000100c400f4602802001c1c0c0300e10b0900d0700c5580840e1065180c0c130624000406942c13050050300c0742d900c03c0c103016080588130b42d1650000f0b080c2280310f07590401000c10036011841038600d050350 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 8899206 1250 8897956 8897963
    0xd1d030d020a0605070f0203160303020d0603080a030b03010203090d2006010b0409050108070506030a090c1e08010b03011b08100e0c0c010b01020105090d0c02040b030708060402030f0a030207030308070e0a03 91
    0x10300c41d01d9403800000301d650180104c0c0420031003194000801e9000411102d0140d52102036020204403460222f000e4883c904000414500388000002040070150140190101540b001d000c8104940c092600700d010444403106190703c40c0c069200c00d94003507803114030300380410442c0314451200c180c5040c1c60500c00b03a100010b030440000e81008603203030910913035001d800d03d400905001344c50100010030300c0c080580350540f020b944da02c1500800008007200401000407000c0c3c807541740c5411001c1c003821103462107515050350031301c54111014035041c45030341c06071960b103542c048105408030b0040720660740c001c100800c038100d000307004103038007007942e6449100d41f604510999403074095041050075240c1c4a0800c5041d0ba04203418030041844c003050340101481c071481d1010300c0c002d407400085c000d8002190f8540d0540510b0101003031029000c00c150f1310650080c0c04556214204800305507480c001300750080c005070040c1c002400000d01c070b00c0d2415006200d6107050300b0000e079002c0001e0a160381d80e5001300e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 8900456 1250 8899206 8899213
    0xc210f0507060809030408100e0f01060306020316030b0901120f140106051005130605091507050303060901081c080a0e06090a020310110315040204030503030109020306130b030d1d030d02 82
    0x10407082ea404400d942d445003945000d14141840c0034402541c41e102515001d0005840d00400f1b44500c4003040010101034202c4001e2012a50303a08040009500c190307a54604c401c585281a62414000c0c000c491441e500506088200ea01c0c20340b00b4950481d104104071100401141410042601409200648044040005151440c040c200603003107030500e11901c18031100340611070203c807142d401041250380c107040103541e4451031800210480285494404c000d1804100b44e000e100c40080a540308500544014450740d0301c0d1131072266901c007a0070407914003440b82540100300c02d120300000341c0c01201d03034240450890343e00c68002e03050810848140440d81d10001e01d00d02985410494800007040c503400400c00e44c00107a0350000948402001d1003401a80c942c613144854072180d040340d00070b54110064a490b5616030b996400658000c2e28110700c103161040d29024030203664840c15400c03610081c01040d100003825010380e0001311300103500071242140d0768800319607107062140417079018103a03014 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 8901706 1250 8900456 8900459
    0xa02190c030b011806050d02030607030b0105160b06030d0318080717070807060b0a06350106020303011805061305060307050307080102090301060e070207030b0c0c160e130c210f0507 80
    0x203a004551040d0300180c1f00c2c1d0665444800961002b08581d500040c41d0702e0041034441c060700050341d02d40b185013400c00c4a0455802d0321401d102201f030410380516011025104c41c0b005004084056802c40c001d0300038112584508880007564440007011101d11403c001812680000011503881d00050350595441c00005091001c2010900c0713550785c14017040301e000010305d090900c014840a901d83d1030b501881c0c44044030011100d9418240300c221541c02e10920070560311408025200c0d0020311031603540c01c009500d160207000c15400340511030721000d041c1e80d00204411700c0c04070184c00090304894260007003400101c0c03a91410701c120b40142580b10005640c81c603401050600710749a66100da01071503140c20500c11800d901181107402c980d0080c4641680f901d88210441440c8104100038180b44985054009d40d0ba0106203207400300d8907074030020b205696442090081e11307500d0310801000d580203000180004c1b03401c20506180000c20401d0350705640513998501c2641c03030030000e05031100c0e0b00c083c20 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 8902956 1250 8901706 8901749
    0xd0203040201032901030207080f040807150503160302030402010e150a110601050306070507020612010e0714120613060503100504060501080f0d0e010318030c060b0103020a02190c030b01 82
    0x8024810907510620494030320320000b424a01c900c401c4c0346a04143e00040c0c80e0040c080c880d41684c0100306a001120b030340d59aa1003a550740d0310050300c0f810354451b401c2000504224010b0b000c1d203215080e4040c02541180d0359950881c002e520040c01241488030310100541e4540300c0105d05816441c0b52100310340e4031030003078801400c91900e41f221007841c0e81c400c40c0107010584001c18290f401c402d4604202d40c80f0388240c40091500d0152001c58020100c03104c00020318195007403012030007400c842d151040c090411900c00343c16403103034848603141259007030042143ca050020600b4200703086042c4c005081921080003030b00707102c0d601c03142150080d194024003051084034841c1c0b500410b501e000918402c07080040035500e13160400c0000303081c054400c15095181e4001d03040307100160030348651004a1030003883c02901000c0c95007401d0310420302d40b0402c001d065009100700d070b200000c240c000701540745100301c00c40c4142c6044d00c8216038400c0060800400a000a11400d010f81034140d205141d840a208 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 8904206 1250 8902956 8902961
    0xc0912050714030a050a080711060c0a202101020c07080703120201060317070204090b18060a1a060304050f01050c0a0807020a0804140a0302030d0309020117010e0f1305030d020304020103 82
    0xe148510a030801c000e074038006000020706da09281e60080f80c29898030142c0c1440e60f52804d04c2c0c0e0301039401000c0000c40400c50f82011900800725446060050985440200155101c142400950b608a0050003041e180b40e00035403807012000d010400003500e04141300320380b00d060000903840080c0c036510028003403081210040403070400c602d9034402045818516182c4910344020101d941c540380e0400101c8605645072034001d1640180c0151480790341c0d0400710000000340401c002d10182900841000c21384501050040b8001c42504810f0000703980d9039441001741c1d03a8006442101c02e841044c01314160018280a00c610a14581a40a4982480c0e80f0058200080240081c0464109003542c0300001c4610095130181d030303640340309161005405070105104141071740010f0350512444001c51003455150b04501e1449200303036034204a2081d41d0740701e030895901c01e0041d06500203c0030300281001140c0520194000c2c20310b1321a4154449640300c0604581c4551503002d45590000104000e550b00b60 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 8905456 1250 8904206 8904239
    0x30706091a0307020d1211033d050103020d02040e0106090810050603071203050904060e010906080304050d030f021507170f070f08090705040212040201030e0d0207090c09120507 78
    0x1010100c0c51450480c4009481750390007104d000038401486074405800300c05500c401c4884c59407124990740d07400c0c848540c008514000ca11252004003002d5816002010b0704c0f140c900013005440e000b40c1c80350810006601a4000901034508150b00340300004a48000d03c1e1118000d10082e26200301070340c2458102781c1461300150107021400c0c10603007440202e48000401d88101c0c3c5407074900002c66245442c0c1100d0300e02c20384030b071660b0250406000dc2150728000003401e040b0f8034080000c001203644c0350086a04e9000301d20031107134882d1110643c0310201c2d00551000403451400d2060b2134120700c010000d10140d0748103a41100c002646135416102131a214400690003050080302a001450010b40c0248280d4240c3d600c0300401200002081502e6003c2003200003600b4010820f6481d08400b600e580b001c3c02c0f045400740d0000e0b0504280044182c00400e00a06000d81580502146402c124160019001c00d100b24010485414400281a80ad40000903426845007002c1d2440a00d42600140c003440c10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 8906706 1250 8905456 8905499
    0x1103031003020f01050c01020d0c02070906180207050102040f060203070201120905030306011404050d0807060b010813080a140c0a051b030a06050c09060c0a050105010b1303080702040b03070609 85
    0x10814800011154548042103a604440018044025030012038090044000c0c0140c3ca43c004035aa00040c03500b03400410300060390791300321080141e0b0703040c070304065030000c1c49420f40380103003c0000d01020080750024141203009100140c6002d42d949110783c44c1345401e510900050300041000d01c215030b44451240710028443c50203224400180d22225180d1001030b0007681803003c1c544450590120f05c60540e40200340092030321203c1c100c9821b011009501c00602102d03007500e01682802c082d0700650616000e030f54441c01010f40003900740c1d2807500c0741c1d1041000009104c1c0308800300d03601070348000040c4a80300c141000b502d208203142c60060304d01035076840009a40e201182c000500e50310300213280710403160441004106a12040040840b0f0306c03d80980c0e82e001800000c0c3d100c0d40744800949080c84030b100d400208980c5c0e03a14803940d072217405520741c0e65000507800036007040031403c0b0320302411a440c0002c1000540f5510080045d151805503400f1a000c02c051500c1003101504d10701d010400d203100d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 8907956 1250 8906706 8906713
    0x10603061a040501030902030c0306011403061602070b070501060e040f12090b03070e010c0812010608010e0601020307030503150405040507050418120819021305090106030c020c09071404030605040311 88
    0x201e96901c903415001ea4010181010b40e0342c0590015903404201450010001400b61441542c482a0a513044842c199200b402885402d01203003445100d180c04140c03035821940034060003800c140c01900d2503030016109460720b43d01d0b901c006c0384076441444a0303800366100c0d0482580c02d80e0b0601d03203181e0001e1042d000034140401f00404001c405890412a940b2404510302014202210001601c00c54050341c0090040e11011070103061101030341682038180c88042d210342040b0b81c0c0c2d6840c0c00740c2c0721204a80d03035070040c0c1007070086000082c0034402850300300d00b105003409610840800890125074080354207803403e510900082055042611600d006084078031801d020188094942071080106181e142080107400c0d40000c4400040d2000e10301c540c04020710a5541d80c00700844045807400358024540b1032080e910000401500034840c100074000642c000e000b00305042c00c20001da480c0c00a08100078030101000c882c1030000540004c1c40a10f105480000b95410a400c0082401d44030143c960700c46c0d803 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 8909206 1250 8907956 8907989
    0x30a06050105090a090506031501081006050312040e0403110a031d010c0c030b0403020109050604030f08010e0112060b0102030c0307030c06051305100207150513030809120406030906020c030a020601060306 90
    0x8a4402800c420750b05007605c04241506e40e180031078580941b16a084482410f01c070004a00b4000119107101e100d62118010f101c0720341c55904054075800ea50510800e440b400b04030820200c0707009104550700078002e060401800c3d4000800508112a65030128000345400c1a00a001d80070370000010b00242882d2603440b868030f65035045043c90391400090150050305001604040c400d4200300e00082d440300c20340303555041914001d40f900c5282155100070441e00b50020800d8000062441e04880a031544182c850304c06443e40001049400b4005045000030000c5006841c8100018100035209a03600020907009080c4602101ca02401d9045119508100000451400521491908485903005a0301d40c09841c000c0312a540c0100d1910780c00c0d0800c81000705060040003210501402a21495030f140d482521083c0c0302d841c40100c0380c148640c20701040c01440c1c400d40c040a12070384540401440c0801070000c55240d50022010603006a206030014800306a05000e01401400282f44212304203 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 8910456 1250 8909206 8909209
    0xc0e0109060806030a02010e0f1012050603010203070503040f020a0506030106050c010609020702030d08090a0b10030209070215070e030705060309031b0312010909030e12010203090c06120402010e1201020a0302030a0605010509 99
    0x1340117850002c2d04226003800c80700d0460741d400c03142046205000f040308044c640024000340c08000c0c07541c0d001041919080c00a12181418001c6a100e0030301788d69000d1856072243ea41c4041c000e2a114140d800585669010410780c076810003c6000c0c00301a100c0341d40341c03542030f1811402d40c2c450382c12400c074183c0103000d03100041c5c80010b0340f080d052103e41094400307a601d111009140c040b0324200500314040300703400d21142600e0300c6200d500380c1e402650004c4003035072540c1040c0d95800c3c10180314203810100303500055016103d4155003030109030040079994059600d5002600b90f4100b581c203407090703401c00981c40c1d40000010340344140d204001c4c4040d5042c21884403420100c070005124521403203403681c03211010148128000c5161200082c4820001018003500c3d41c000e4100312103003412840741d00904902e51908d24165002c2c2056010031800396038996004468030105180c0aa0300b10407100c03800d0a91b048280041d00c141d03030b01036800517203c3c0b811450700d205072131040e1302c5541030250820007403005 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 8911706 1250 8910456 8910463
    0x1805010614040b0a150f110106060c060b010804030801030209090a1b05120601030807060f02070204150e13050309040b04150602010b0a09090305161707030203040f0509010506041a0d0c0e010906080603 88
    0x1785103d8100140019401c0206492009181c003e40f01c003540b81c07540105a95400c54007100105006010410003031400e03d0040d9000e490945001e008079180c0001080185440010760b94080b07002c4050f14412030340e50f510808041d000442650038903500d003009020134141020000c1064102c0350090544d549903444944291244410203020103813610280300100080303030110f4070060b502800400c26010040c1030700c0c0c0400410300990044101d1742700802e01c6956045c01d08001550020091440d141400c401c000042154144e441d4000d80c4500d150050300c50258000801880329400102d103012100003044820f1980d90820b00341c2c1307840d005244010a6210f804e842b0200c0e00f22040e02d14240341c0c1c1c2071000171020722031300c0b9000429000601d807040503408070251045400c803840201007161603108000e100c0300d09028954018800b480108003201c2c02c404003881d5102246001c03442d2484003600d00d025616011410400300c0c2041510099075607001c1140001041c0c1868074400d50f0030300c600000c0c2c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 8912956 1250 8911706 8911739
    0x7050603040b060103110c0f1005150405040501060504060312090914070e0a0f061205010503010b0102030708070309050d0309030201020d020d140a110f0105070906020f070501031805010614040b0a 86
    0xc514100c0c00041c3d0030f640a40d0000c001ea401c2c0c85605915503264010007582c600403850b00a40c18080d02c1008001c0079030314014176002c0c3c1c0440c00562104411071045c440200f000400c00d4800d5920745000107010384692107840043c0d4010070410384c0c1c0b603481040285c5110007e070306c0106900e2400c100f04001c0702e803000055400000b01d2078154004a00701c030014198260a400c503a900310300e5000001032158020300d00301d0842408120500144c0e036907204141c00c031000038140901680040201000282c0101c00821155102e0b043c507010f2103448002081ca0080b107510110003094508600b80195a01000500b540140380d200401031500300310b000410405840828140810010036400600c500541300caa5008000b0740c22120103e05000005000e80001d403032840c00300d41c0501011518600c04200085d03140c9a60b801803801d9450503004400406c0219501d0440b55a10b84244000801c01c0c056200140101e203014444411600300300412226510380e203500c12140000c04001d2482d03000c1c40c400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 8914206 1250 8912956 8912963
    0xe1003031d0102010e060709050a0e0405030a0f0c06090308040201080c1606020a0309020301020304050703031b11010c0303020405040c0804140706020615010c0f051614010503040609020a081207050c030705060304 93
    0xc0c0072100c800300603800342039102c02d03044140c040e83e42008800ea600110400858008580e01d001980d65107007540e2103e8001e940c06802900200040400d081c0100441910780c0f000d0300c0c0c100c0802c062a1a04000c03513400d448114000703581c03d020f0100b5580d1185403103401844400e03109103001200708442c11003404005009241380e401041a0b00d80c03c1c0a0307400b1313900044c2c018000f55628030301490810f40392005800214007003200c0e00d2001205004a008111080e588080070b01c04000d01140156507040d0380690440c1090b40811001c1180d4031640580341c6c00c8851901c402e019420280380441055042d05500700246e440741c082040007540c001030981d044240c03140c20f030010001d0400100c9840080c10300c00f420402c2e2005c3c07020708114000a03010102c0404851040803d500c540c0d040e01c8174400550340300d00050003400490b0100d40c40e03511204e4680e10042404075443ea5913081300d414001d0504120f84501c002241460500c01e040c00f4030402e18608401804c8090b05140005940340009803014 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 8915456 1250 8914206 8914247
    0x60108011d0601020c04020708070209010e04020108130f1203020903010501051207140d050609030307080c0702010c0201050d060e0709030204060f030b010608130503120612010504120c24060e100303 87
    0x16200c3e034000c2c03200d1141d01034040e0040d995680c00d030800c40780a501480040713014141d94000080e110000344401e0b80a0750b4141d4170482d10343ca41040e14055600380310002c5e07824803407031003880000825203040303000e0488054401507200c801d000101421a03105910260190500e056050a100c2c0e0204440c0d054a01c407894a000c04140c0380045980c0c030b1701600300240b580c802c1000b40b000c48000000950f1042c0c1e9a0340d20b0303000700e81da00865a0281e00602c08004e003c900c103004810019030142c8090404601e01400018440f13584002d050300b903040685120012030a01310701401581828011f903006072030420310b01c100036880c69580c80a0b102d814401c00041201220204a1140001344900c81881d0080d0403242c42c0c00790350807800c2e0240010390b4241e124003e09450a20081d4060003010320507900182e04a0200c0201801134032380351100c0d0002c40e185103507070380700c07504014210700707041100003140f040014003900f030507008140010040d0211800e130640c200204002680101c50031044003504244 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 8916706 1250 8915456 8915461
    0xf0605130503010f060f0603060302090109090809030105040b0108070506030f012d0308090103050901050f070f050903070f03060e120a0e010c02040f140703090201050d02031015020114060108011d 86
    0x100c482403001604015815400e1203100103200c5219008142542c04039040d0031169a45c03840144c00700c0b429888000c1d00401001d004101c0403542c2d43c0200d1049005003000c0d4075100c0e1000002c0e084460031902158102c0c040001402200070820140e40945400d46419195060212480040080511030f100348541c04c100916080c0b05034500d461007c60040b08400229910392420480c50b8003c0120240081c0c503200c006101c240c8140540340c0505041002d020030381e15201811035450049008031020f00c60200001402d40d102044030754020501d01e41c1d5811050306515044042d240043e00b00f00003644214071290314240365204884000400b8148002d2514003440141c80c6032079110000f039889407a08021900041c0550080f03000d417110700c00006800d50b00e0403820750485900080103400203000748652140c0810302e50080d90402c0c100c10364896001d944014800f50f88074200a1480183d45613118568084078080e060368120b1024284600c0540c188100f41080d03d480c0d045510315545030002 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 8917956 1250 8916706 8916727
    0xa060e070b070302060603010b040204060c0204050408090604060201050108461e050f0607020a020405060f1c0309050a060e0405070915020a050606040c1704050106080a0b0106180f0605 81
    0x1100c030060560307201140e202c1003107040207034442c0700c11911540254203007c01c0d000549024401c4030f050303424a03100d4000342c1035240c0a100c002e140040040741d01c3d0f0742c10050400542e480d08041e000406141d80003082640c1800702e22418040d400c0c89840d1800054003031000740680340031695042c0082a0780c100390410120245444a000c008406004812480110400368801c0b61030038103810700481c212000003c2d4206055070701c0344201c0340c0c40b00681010301030b10700619044c2c10891f04500c00030319440250b0b9041c000200600d8641013810b8071034824146040403d074114620200a0100721403c0781c40e04c0c0380c403d015000d00e141c1245944102c0d80c070030000d1080d5008004180c080c08080b4611880f0304102c0310041e40da40048407042d81c842c071076100050341b1490a80202ca4140c111640d034560b160591700403020050320054011500c8d95201c8001003071100f010050307400d03480d0041185803002e500d0a2800303000d00b4544000088003031b812a00500c00f50340d40410101c1101c1741c0746000355441301c1844 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 8919206 1250 8917956 8917963
    0x12030d02070303060503061602061302040b030f03040302010801090b0604030602030c0c0a05070602120c07090c12110301050f01020a1101051e070b090c100e010f030f050405070f050f030a060e 84
    0x20000002610109410080c194198480c038240d40003682180c0d0f10340c8907030400740100315440c0341172801a0b00c0440065101c000c09005205803e10140020416681020001341407460040810300d85520100b001c20556a110890354010306c0190000c01080319001d000c00d0301352240780405485503400101082c0500d034070300c2c00c0710410803c05040d40d911031502e240072502c8000501c94a40144030781d01c0001d00b1030541c1001c1f0740f00050104001c0190914011100d40035103880305d007180c140042860320010060030f034001c0300a9180c54500199480d818001008000c5d900700c1d803098115441030080d1400101c2800b13118030542400d00744141c82d00d404a9a0803600f00800040302000d2201280703180800416490792801402c055041d0781003512250144498240c0b94040305000654000b00b001e055405104002400d0f5450b20700452140703118400b01056880c162001c58446d0310044081202e5050701d07803040f01500080700d0742501041d060000954401140c500602070558030944c0080d506000c2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 8920456 1250 8919206 8919217
    0xa020303070e0d0f050a061b08150111150109060b0306030a030e060904020c0a020a0905090601030308070201060b0403120f18090b0a030f050607030501060c03050d0507030e0106090b01020c0901030503091203 91
    0xb41c142c042c5000d10716140ba129006e84408a510901780034a41c4002c09048280e183c0207100c980d030307144c0c490751507100200c01c920800440c241800312600314400c46510500a41c00c3e00840c00d041111154507100f482411150580d0110300b4040080c014405a540c021400b80c000c0d80d003600e0900e010f10031030740029115200d125035207030f4000d10001c0c050851801c0820540000c40c003c4901410b05687c914a54050741e4049401d030095400c00401403002900803031400c0d4006000c1e2000280190b103034020520954020780003074540355022103500403000c0c0e0003030b00b1000f1070b0b1052038250500c1d0081031000c81048000e0081c5101c01d5190380601c0c0744c80c1c580395002c0c0019a045020340441d0030803402e1035500c50300140c0c1d01d00c0009042c1030011512078041d04615841684c140d4500b407409941032041001003402410036801c05440f4800144281024094400900036a480010b200b4074540006458282c0c03030359415000301500f00040003c02c0340401540c0011b00203482d004860020040b205086d407151 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 8921706 1250 8920456 8920463
    0x3050a060e10030c050a0302090402330304060c0e01020303060d06110a03060510050903060f041a010305100b0913020603040c0b07080a110604050c040e03040f14150a020303070e0d 79
    0x800304024510510402e94002c590289103040700154a80c010f03c1988000e60201942140000020a0042c281020a00005886c52070841c0c03194100070441c40e00004500840410006d000c0107010521490b441103902205290804041d05651200082e490307000042c030381c1c3d1040b1b00700c00e00034040c001183c0000c01c0358103c41090316910300c084480540100040e0058501400105101500541c024021a072600100400070101643c54442d1000390040080040b80c03422000885422030071200503009028500c1100502803210452000717004031a00851102d01c10080d050901c1481407108500d07007001ca40540c1d985a5a60307075400c101074032003942c4c0e12156452500190241c2445001c1c00507200c1854603507914401c904000c0d12403641d6203005c0d60041c0c4250098108102c581c64107034000f02e00700c03c45a007502e0500d035503400d2603d186071036a4800440945a412074044a14003c03804001e40c06102d12030505000812200079500c2c04010090400d2095080c0010314035a240984007030807a61 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 8922956 1250 8921706 8921729
    0x212040b030714040b070206030a06080a0302010e010c09051302030c09030304080115050a03080313030905060c010203010503010b010503040506010b0c0705100203071101030b030c0f0411031303020d0215060103050a06 95
    0x40d100200c0e1059401194110005818540120180b142000848007100e01d10444030741040d00c10780800c005607001070611102a40d440f4800104544140005071126019400001d900c0303210010207801d41c0e031448181c10400c40c50034424013441c0d80e861581078540002c079400503103d50b183c41c8031691501c01d85010355410b2001050000388600150400103041d000030304004040d0743c2d0f8105001400245020044c4010000c3c00090300340e6100505c000840c60180c942103400c42d40e10b0010404603840b0715003036025a50000f005200c80c2c1000d01803582820000c5ca0942e01d149016200d903500c480040c0240b40380302200203030f14101800200120b00240c00f0050002403614001040690781e84d0150a04030359007030010311000b00640c020704c01c884007100080d0160040340c189804124080240101d4660300c1507a910790402100c0755003010f14452895030b00f0541c03890001c0c1c1000f03842c101c14044418110360041034035054403402c0d0070f042508400d003030070b0224981d01c170300d100344001c0d000d81d421401c2039a6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 8924206 1250 8922956 8922959
    0x601090b250c09110315040b0a030206030a02090405090604080304120306050303030a1a0118050d0201030906050a140a050c0403030f120c05090f1504120807080307120b0303070203070e07021204 85
    0x88003802040888125081c100030a0460f40c0710f0704ea0602040b14142c00c80e024401c41e5070590b00f86600407081c001c4c03000380002c0006442e680099526003090b9016a00c45034041500c00d55402c1074854103030440740003070080c0380074641956410b138240b1004100900f07980e802210000200d001e40c00c902c010303020080075a6140c5c82c00fa01c0aa0003041020b01c030340100c10080000c488254001c241020182101c00041041c1d10300b854180f00c4040030030102241015510030034000030580a100301d5000d06510304010404070040b8841064074100940070149240ca041c05000c1143d40210855040300d5144c00c0c81844160512026944c1a00c0b401040e8440d03810301103c4038402c0d03440401064001e0303044031010302c8940c82100380100142c140b11201500c0d41c08010600c038a5038a810144c400a1241104524050540d40c400520b034106a483c18041650340101c0880541203020303c80819070240c00541c1008440e40000c0d555155a103d4010070702d01002c0030030040ca10900480c0700c041c407008041c40d560f9 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 8925456 1250 8924206 8924213
    0xb0c030702010906030c1e0207080102070f05060f1009090206070b07020604020306010609030b0408030903041d010503010c0e0306060907030f06030b040b0112030203040e06010c02040f0b01090e0601090b25 90
    0x961040c10101c0c0025034903440410050f00a101e024500b0f4400c4e6541b200d8400345030390303104c905400040f00505510a041d03001030348500c2400140001441880400414406854000c1c0b4011010340024122244e00d030030801042041c04242c4100c8800100120f03800c036803070011468900c1262005004c40c440c00007000200ea8002546500440c030980440d0b91903a030f1000200e40b000603600001b8110079070303500418040f07410407003d99040741513541581e24255403045444441c07184010b1030580400c880d001080140303402e100c0d40d041401c2d5401c140000e600c0b00000a0b85401e8002c4caa030740304184100214051a200390b101142400d03410708100712503901c03410540d15102040790308603070070fa500c140042041c03140030b01c0301c010b0158990011410141403110322a016407004000034100400c6009401c0035036110700510001c0c45070031000060382c0700a4000100324180903005100c07510441c10920106990042c000c5007103500c4140501c0e10f400c5000c845000000401840d02012003884103078030b051 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 8926706 1250 8925456 8925463
    0x9071203030f1e05060922020105030901150608150102010606050d020c07050406090905010e030a0806150702030607030501090b030106030c050103021b0d020f0607090303020604030e060706050f090d0908070302010e03070b0c 98
    0x2c110440c1c0c0d1010507652500c02c541f4006c3c00d80701003210403043c5880c00c80107501900165030020032050000c10701c00805400c0f00000401c9620540000d01001c0a20004040c3e039004500c6c03078079080c4001c2c8400d0381015000303407042c4140c05c440380c8403e03400030301c811808105101e0280034100081043c840c4c1542c40f00844003424507044183d032194030700344d111101c040b0000700300e41d8200b1681d1502c40d02607030360404010341001403c14814580c0810454080103035014031400d0b215613455140040c8550408030005e0449418001c514000d07031500c42c00344040b5145410680032a002480c000d40d88051078540102a601d848689000e1840717616554a400f90300494090a02181e40003204c1082da60200212950101c070710000d07016030072103030200300400d1044140603822900680b81303502c1e10100e079507201f0464404032410044a0400d10a01440003024440c0b80c038011210310f40140500e040203032072a02c4101511009043c05012003460f192502c09200100c0141201d406103626103603915a601d0f02c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 8927956 1250 8926706 8926711
    0x140a0b010f090e0f090a05150a0c02030901140306030f070905040201080c04030b040609080c0d0206040b01060207080c0904051905010f1104032003030d090302031209071203030f1e05 80
    0x21821032078200741040d219140b6001211000780c012100364036440320001c080c00001d00040101d004604850000c51410065200d040c1301320941c1c0501c030300d082d030000412580900081c80454000f0000f00340540e03840104403845200d243c101e250f50340c0324500040d203000364041d48482d1500800b00000741055490340b00500c124001e0301c40d10391990312200c025a09224a0000038a071006040201303021410035404003040034825000107140149078a0f003146441c440003414801640200704000820004e10030b818010030450004007082401c011003e80c803004140b0045009000110000e02845810006081620712981d0308000d10001420024007a00322111801d00e400c0c10510b00740440c17404441207038201c03608403031001218880220440440e2003282c514a03454842030001c3c0c6c518000324031603000aa8840d4004660301c41d99030107140345c0488010880d2447c0c0d008071504200d10101540d103010038583c1882c00250310011540081c5c003c21946e004010f90b0280b103825a00c011520754403050 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 8929206 1250 8927956 8927959
    0x108010b0604030c0605030903070b090c01020c04151e0306021207090501090e0105010c02040905160305060a020c061b0d05010609091505030c06070507080a05010902090109050708010302060706140a0b 88
    0x45240c0c410018040544a140b10007002c0c03c900c2441048620312034405940c1040d03410b802c0c5c2e40b0b00322050312540340502d4156070f038200503000101c690324150780404c120b200415080e1010300c84100582501400018a40b044806041003031140030a0603004001000c040c41c0e12403c11501c0e00c28014014500040c00c541500c040b4510200120300c07913010b05104000c0300c00d54a800b403040c2c0c1c20074004440c2d62107515800c0740c0181c1c503001d040d030000314180241c0400206441035024800d10f50309005107043c001800b1102c842c0d20403c007100d000c03c00898415840020b01198500c850708002c02084076100307076182115040e00c3c0c400041072550b8045043d2040342c00c940380a00140d0b6070101000490030403445000e41c141d000700e40d100024200340000d04040e600580603030f0102c0c0e54500d50241484528a03044840742d540d400a030003146010b9440e18007504405c1d404124610703224101810325070041c000070b07100719070202d0084104061900224a400805020640d4904044010740041c244801009 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 8930456 1250 8929206 8929211
    0x415030905070f05031e011b020d090b03040c0302120a0803040c050f010305150108070201020405060c0c15040807030f1e03120509030f030402060a1b08040f050405070c02040c09120b010801 83
    0x79202d800c3d400201c043d2100203014055443c444140800c0e1100619080340780d035520303403082c0800c41d484000c00d02c2c1c200720150054801d042c000c40d00100703030701312540000c8510b13a814028070001c51500720b50001544c0d0b059070f000c040200c940740c2ca07500e48810001c0c001c01103580002040704002c01da01c100000c4480540d00790310f07185402030064003a201c1c200c840d0201100d21240300900c542c13040e4540c82d0401d0407400018581a180c03004925154400d8100e5501580305030f2030400705050112105041d103070b000305040e081c181440001c5850340c0091002400405030340900307a060180802c401c49016024a840726100006d500c0c001d0b0105402c5c20322000c443c1c2c40c100014407100408001c44100c1c1150150091440d5600d80c00c01c2180c0d0030007000c100401400c0e04c1109000e49001803074620281c000c44100b61640c0c540385950622607403941005e40614101000c3c400f40320f40040b01c1010240d81218081860403080000311084d0065034481a44100c40741000c5052100c0d099005040e1000070b0000e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 8931706 1250 8930456 8930459
    0xa030b0607030203090907111e0706021f051b0403050f0c010203211008070f030c0503030f0a11010b0402030c0a030501080705030a020d11150c010f06050f040b0105041503090507 78
    0x100803550044400c040c0158204100b400740e507203024410168480e809082c011090001c00422070f00c2c14040c600b103080d032035601000704031101c20104120320062690303200800194040706144010b54400005d8082010344581c0459100e024840c44031880c8040c0403265070310f80b5541e060660780c410f07010700c489009001c0c2c1540c548080d40b010040300e028030082440740444408901d01007184080040001070764099000001c12100740601c0a0401400401400468207045050480744842c075070b4800d0b4480da0040280482c80e5072000161990503540341800000042c4580e03c07180504000b00300d49a000d88004108034402d9241c03005415081060b5500300a285c1c0c80310680c1e43d0300d03540341c040c060781a071151038418010f240001c10070b01070354494004001610010400301d0030980202661840d8039001241c0040d5403502441468103031031924009219140c98907003c10404900c111185000e00d456008280344da0b40614103c034001c02242e24442c40103808000300800608004078112824094000c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 8932956 1250 8931706 8931709
    0x230a05030609070809030313110d03020607080702010204030314090f040504060203011e030b0a0c0203210601171006030f0e0703060b09010b03071b060b06070b0703060b0f0403120e0a0b0a030b 84
    0x1544d44940c03402c030015451a00d03403900000c85864000c130120361604403800344152035100c43c214190040d1103034000b04844e007844407010345440801000700c0116072051104101090b4400c414a0301c031041172403030a40c1c0700c2e845000304442000f41c1a1b1140c22609110070701c0304100041e4001d504903119846a00c11446960340c50406405140c031000d0030082c03110000c40d080900c0d607801156884c50a0046919200c03080451803240100410701c090280142003c2181d196001040207012081081035408980f41500c05031074420303624001c09080603030307030920030f00d104025520509140c034030700e8100e41d0081e41c2c82c038001d40a040c40b01c3e155400b4260b00000003c2d07214020f8181d034040c0c603494030307205000c203680290162901c94199080c0e801039110b04620059485810041c140d40d40aa000410340d40342c02c50700641510311a5000b44088503082118121901c0c01c00143c3d41540e50040200c3c051180850048480c5105500ca55500c0303507501000049400d80c200007004620525182803048006680 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 8934206 1250 8932956 8932967
    0x601020c0102191101051605010e0c010e0d1101050f0d0501090e01050603030a03021309020307030509011a01021905010204090c0203040303020d090f050d02010c0503030901020909060a03080703230a0503060907 92
    0x1442009070700f580303002c1080043d01c0307121409601035062400303d0400f002514540110302560302c06032140d035510b060a502102c4148480c040b82c107002e003825410203164501085440c904c40101400002500240503656072092040b544890f01000340142c5079000c0d00711550003001f003032144007501c41c5085a280307403204e4103000c0e46100321001405942851102001500603502015100034454011000820380c050984081e60003000c56a500203018030b0803c1c025421224541a01414440c4100503603006e6a400185a45075000c0180003108050080c944140640a180c1100301000d00703101058280c3c942c0040030f001181c0c040c1c1c1c00c60340c00f29200311080d0b6000300640180408034100000601c0541441d101025105106142005507480c0d83d031906030854009542c00622a5000258424286007641d01c460708070200300c80d1075a040c4d00d59030b5580e41c0c5104800008060141f00c0f001035047c45a03040702400100e103840101c179035074181d12500400c503a02c00c840c6c0e00e100d0a041004601c03518482d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 8935456 1250 8934206 8934223
    0x120606090e07030e0109060207030810080303010b07080c07031b0e010509060d050a0f0305090a050f03030706090f05061f0b03041101110a0606090504030201050609040b2406030702060601020c0102 86
    0x16111000141c1c1484020040400000d040c001815101c0c18030b50340c405024841c0c401e90a00955006844080301d28009020101c0980850000020803c09100241c0e02008490440e60b043c101741c0e50b10211860030703e0b030901403003409408a0082d1440002400420040c406c00041d080258950450f103401101c03142d10000e000e0f280d00164901c001911074205450407203041c500030011504c0d0a200c030b6030b030400792114001c0102c002803c00319640f00d480c208410398201030102110b4207916455450b0100e9664044d04230080c100645a10500303041c8000d015800200f580c018055482901e890728500380942d0315800b4204040005020001e020344a0405881c041c07940020301407008500000115030f5039952406c13401041c0116904980003400030301c80c420041004050201d0b4626080c00d019085401c01800d842c010304100e8200800600d1410444e548109000d9070303c46010042d160b81c01014454904031b640026001003071094047d000901284119000d03070031140c0703e4a41000481e00e42424 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 8936706 1250 8935456 8935469
    0x30b030303220201030e01021b0d030606080a02130503070605030708060909030d0e01060506070507090b060a0503010e070302040b0f070506010f0513050603010908070c03110414070302070302010905100c1206 91
    0x6000c0c1c000e0600201c031021442e214014500400c4002c0c015964a0032680aa00860701c00c8104000400e03501405204109018543c0d0904004040c58000d02502c140300040400d09d48076400980072203020a024031010150001508440c541608d0b0503001d08164402d1f030300b681c00b00f65080c0000e5002d24006245c0c0e845010024081c41c10f02041c400c5213009414a8020502d065484110214060302c4041c080c00110740540300404a0514000700f1030211a20203211a001d40301c10454000099000800ca0f41124805131800030b40342c0e600742c012802809190400c90b40c0341c2d400202d04080c108110050407400b8043c07025500c599030b89682003100f28070913104054000c4500a03802402000c554042540318101400126500c0c40a0741c80840070340c041c0701c04542100c050170382401400300c60034645400882c15141000240e940d0038481055940040c41c8808054000418004061017904103d0b84c40b43c1c050f007115921f1318003243c4140501400b04902d00001c0400140403103120391030117024200c518 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 8937956 1250 8936706 8936731
    0x506070f02010806010c060c0c0b0a020903060c0a03020f16050d020705010f030905011103071e020303090a060f090b040b01080d030203100501030b060f0301080c04050108031e1b030f0307030b030303 87
    0x1940195030002e0010540c0341401b003000440e50204032640208c142403d05a0303a0a50700317818904d80003e0500c1f015000149891041c802c4040caa00c00040c00c4e40c005030701c00840c0e5200c48061008401030b00c641003c0149101020582000650114076240480341c0310f001900d6915241d410202d81d0390446106841c005000050076200b0136000798031569020780510004140e401c941078020307410754800c3c1c4a1000165038a492007200710741350003104411806e144003031482c44c00d0100c0200d5071200c120070302409003643d91f1000c042c0d00720f25911031400c0301d0f40f001340c002c1c02d8501400c0074010428248640c882d5070190b001c3c442d00c5140701b8402c60b4410302c5944142484142000d0044009201450034650440400c008404540301300d02c0c00385000384010401007031030038007010600064030010391001241340d2052111030b1003003044207a202c00d10084240700c152100425000c6480d400084081003080340000140e0f10310102401005621440c020b44050188928460616640340304c1100c0118000c003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 8939206 1250 8937956 8937983
    0x705070b090303040e2502060106020a0201120e0609010f0605030a030503011e051206010501020d05190809010f11030114011718010b040e01090308010501050c0c010e040905060c03010f050607 84
    0x80d46000548110200541228102a260071000c1401c075019030310042d844030103200100f03c60400c42444820b040c401e10151035194940074000e59691134030786c402414084c01101280351517800e81e0040b12401c0f00c51040300c40a08100000c54000d1144986804138582051004078081c1030001301c0c91822981a500e1510710380c40c1400c0400c44a00302c1d880d5001940d41120005019a5418044003a00d141d0340064006c0c2e5150200280c03030841c1c02038600d02400018005c055482c0001c130b40d0500030039001e0034034902940c0c1d054809401404000245003085140001c85010401c521000c0c5069030b1710404603014290240006482500c2211603003043c0e44028800101e8544003490b01c03207a4081d41c00004566400d9a40c00541981c1b03400d1350700300d10342e95119440d03c141903008540600404081c00d1007442c001c8a40300b071507280d0055640450511118514a01a0392502d51140300c01a403c0400d58032281030021300d011403540207100d00301e00c0158450010a540c58a6011105610741c010202c82020 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 8940456 1250 8939206 8939219
    0x601080c0a09020c030f0f041403010507080406020901140a0201020706060506070f020607030507020901030602070203010f0e07090b03070f0e0f01330302120106030203191406060705070308040801090215070507 92
    0x7913000c03c3c5805002c1c04240054460f4264900182a02013110301c001a2900e050802d2072901d108001c003810710036170600c03090000090f00301510030f03002504104050781e121500001aa500d03410f485240607103501c0010002c181e40c0d07041d8040c107040c510800c030620031160383c0c600304405800b07031381405400241540011001440e242006004d214840c2c140700b41041410b40000c0e9100500340e1080d00c100360000b405108600e0288280141000a41010800300c00004440341d41c54000d8007502c2c0440ba41c03884800c259a0b810045ca00041041c1035105a0542c0c4070580c490380e82900303980e60004102464008103810142048410200030001a0a900040c1d050320104440a1054909090540c208000300e12000394000850103802543c0700503070303a0308150142669030415996003807455403070a19000c48035410065416001b4504503403c43d25404103090281c240061503200070b100c5480040c1c00100d0b600190081e40e0614000c550b03905924004441243c058442c4180c010030300d400010041c0301c50b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 8941706 1250 8940456 8940461
    0x111010b10110f0105070f09080a0f021005040504020f09010e0604080a06020901030b1e090a0209030304090c0302120f060102150403020c0d0c0f0f05130204061d1305040b04050601080c0a09 83
    0x8101802c1c121a0ba680c107050b41282141da041d1440030003e002c11203d402007980001500000340400801800d41c10300d1074641303032462000741c04001e10a208500000d0410740c071800039980034110040c000c56448110000c071001d0f070707800041c0f09070100d12020040c800500e4210151403c03203524002a200e0042c03e03a031004000d51100807050f050503905c0102c004035407942900d116002001440316a2000211410007600c41d00040a41c850640104585250f5880c00b0095404449244502003a20155528194060f0248004110b0405c04560410003e03550401c800c5000300002c0c2c094404403c2004050011641c080314080c002d81d01a54031003502e81400d5214448480c00b404000d1403250300c84890b5042002c180e4000e6515000d500414090b6107070020030120400c0c620320381140360500d00700003c0c113030006141000c07500d10501c40f1300304840e80f1802d0b00c0d2500d40c0c0724040c040010f03281c1440c0024802806490a40c0c0f0b0b13200729000413a80d590001000e40383c050303004000303940427450020003101 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 8942956 1250 8941706 8941727
    0x6050406150905040b0f090c04050a230a0e060606091e040509030a020f0a050a0206030703020405130207050d0f0905060a030e01050f01170a17030603030c0601140111010b10 76
    0x28419521001c140e4010080844007001e0900e40d503022070241402e0524801908014005200d0b40181105100040300d0018011041020503100480e0a650300000f05004201050001841c0600034080d8803030b007041c082d6140d1003001c102070100600498124000d9070340c4400c540f5180c10110400c40b58241d89490741441180044001d0500b4080780050007007401d580e01a11072950983c00800d01b660910f80500c81220903004c3c00b00202000c46942e240c40d0b90740e0070744410281c004e4100101040e6150b1213a01103801418014281d072540d0240c00c040c4000030740c00450242d40b40e009504155032131b141301d10401c001c1d0680c1c941d6402070440c200340402000358081c00c1c4210506546002400401c41d080c0101442150b849a007080b181d0f1402c0096800303824181800e90403a04040d007440002280710101103160244411001e41307036075a80c0c0200f071461040300003104103442000e000043e0f0b2070511f2046651102c1c07e03a203510490421108075802d0300c05c030b040300c030740c0c440844405040c200784030f01244003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 8944206 1250 8942956 8942963
    0x3021509040e0d020c0d0209151309050307030305150d020603070302070204090c0501090503030717031003050109051e0102090109030611040e0103030207230d022103180307060c050307060504 84
    0x10310348041080064100d0b15980019865034004a0218079401d8041c0b203100c0c40b00409030391002c003c0c06039a002540c001001441d0030020b030a21103c6440c240c0700d5421000c201441018200301040701d908080d55640c00202d4101c002908120015040302d240f5605a0401c1c58003500d1649035403000ea00700109508000d00c2c000030150b00340810800b60f50f4a000d007445950003418400319141c100f00004208000d035412141c01796004101c0c003400144201c96244a000c1211141600ea0b11407441ca41c1d00300f03c0f550b0014003107609081d1800c0c10303c88081130310702445130300400c80601c00b0704215001e4203034024032400701e0100f0207500c0d04102060300398000c881d03e642c91518480c80c1a40f200003074000e0103400e800660060b401074005008202000c6094500c0008405008090302004000110044915100203000b91225028a42c00c9540d01010640e21981c19042e03d0b1254407008101014031001820103101e4401c680d00011445c3c0544008070000703802034051840c1a066481e108068034000d0400c8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 8945456 1250 8944206 8944249
    0x903030b04060e0a0e010c020712051507080702010b010e01090e04060204030f0f110105040f030f26090a14030601121103030304060504060507020c01091509180204170303060a0302 79
    0x8000d1a40d0710b201d450094440c00b5140e8042d03003000c3c00c040003240c03200c40750036070140c0c54401e520120f0740d000900481120400da41030512660140381c000c0c20461751030f030f403610301c810401d0500000c40d030417824041c800e5445a008104a481c03a400440b0955852a0503e0101d40b80010500004403a41c0a82e0343c481d0040c40e01618195aa41d25000408411082641c1604040c1d010104000e40040c030380144000c24030b001d50500c1d041c240c0180e5246284e00c1b00821452080350694100300c09480010307596940011f03142c0fa045850f0620039050707407100d440240701d10f10080010402c0241e100c070b81000000003130000c0403560f0a001c1d481013943c3c900e501c01d51f2801c0c1c3e14000d0601035941040150300c41c6100740404120350404d498460700703994001d07200c0d1003503405c0800602d038903990103900b80c01101c6103484050040c11882c001600c05d55000e8100c08a2480d03d0b008201002c0309503001481151030408864103926900406079880e404217481450340f0000410040016103001d240c011007081c203c2100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 8946706 1250 8945456 8945471
    0xa050a050403080c07060912021008040303090203010510140909030f0a020a060e01020d05010b070b06011206030b0903030f010807080304140a050907080103020f0406060e060c07030b070503010806010f18090303 92
    0xb034000540001c03130903810643c0214001d104481d48106c1080082ca859a88122101318946c0087d03030303c2c102d0035019410020b6100014050601c030380c01c11b030318164010b402081142080381c001983d601050154074041810085900308600300301d0111849420200065800c0080304009034803a82d201c0d4824030308601c214a2500e0100c0c2c058400c14084151503000165141610fa52450940740140d00c1400d060740288080341c0414000c81d1090352041d030034030709081c0d00402d0000090082410380c002802c581000d008108612800100560140080e80d001e110243c0c1e0f42c03640d0382e60b5242a802140c0003030f0000e1000700701078042030501b24006d4400a1201864a0322071020031f5020074220f900c140010071007130040081d41024524011500780a807070274030002d410f1a0010b0705401c3c1800d1001c1c01080c00046004441509200382c00203564090400203050900c00002031a641080c0290f0045004a400000340c2044403240001120201e495006150800303001c10030080c05c0d000c1081c0c0503d0707111583c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 8947956 1250 8946706 8946713
    0xc05070b18060112050307020108060a08010e01060302090606070215030402010519030507030605090c18040b0406330804060203090f010516020c0402030609240409030906030c0e01050a050a050403 86
    0x2489407103109040400440c19280403501450240180c0c8900d4a445140010a02040f0003004a0340c0c01502820407821686500780401d040c101e6990203c0c15651070201861041079040d00544100e034001c035102c800c00d841700d1041014500c5800d1000b540500c81078111140030104c28003860748207005061450901c100c84480304180d0b100349469a000176555030400040507014403442c40a000b081ea041c0c02140781010224005106178a0035005108021481113000d6442c0c0d08210f101d480003410a1003c10b9803043c01c03590500f08041c01394503000c00c042110344151940c2075071283e480d01c1541ca500043d00c9984444c1e00a603c042d1544090340074800722400b80312024094940518910803a95441c1c0498034402424092760503c007074030860040003846056528044140d401c00c50005c1d134504c8401000410540c0320003076131075040e0403030305111509040c5608400c0340c808452654506000903801d01c2411910804104500c5003c144280306603800c0e24407445c050000c0030880d040c460f00d46626a00c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 8949206 1250 8947956 8947973
    0x12051017101407080a09080a03020f0c070e0106090902090102030910050705070f180b090114030709051003020a0501020f100506010c0506011205070f080d03020a0e09090a0605010602030705060a0c0507 88
    0x880e0703440d500c0480c0b010320180759400400694400a080003c02a52000e42c2d03810342a48a40e80300d100405401040080051030b06000701c40c001040ca10480f441075689600c0301450090074032404002c214400c10010380c5052500849000c841c059001d5071406950320200f10304410181c1d1090100101401080000b480401a0402070108941c6000742a45800e181c80190351a10a14090300d9080507001e403900d49401c58114191102d4850601180c00c414010a2900b001680807119050a081c1402440a9032080302c03020340f07000b50751920540307860300010f9907a5100340300c502510360301840184560140a5200340c0d0802414540707032545a00701c0e2601464010280c0002500389a080c90000800504001c8035000f40310000d44901c0b01460070300c5481c0c07160555058481895000210b90308110f100d00c034004107000c4002c041a4441c2400303820030790744000c00501140c3d00d9140100109400d4000800c0c1c803443c40d48030b03004003296501c1d01a500081c11a111110050010500c440c500092107030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 8950456 1250 8949206 8949221
    0xf0209120c040b030a02030c0f03120a0f02070906060c021302130303050d050f0106020307060e070f080d03050a02270f06030708150114070b060d05030414011205101710 74
    0x40009001d02150704003040119200010340a00c0382c0d004041050058a0109101240d010104c4407048240600360109080c07403010700ca030035615000054032403540c1e03800c00e1014a1510f201d42c21070740200d440742c01080403201a40201ea02088842c0000303401450503115007001c07040400c20240c07c205031040d00581482c2c194004034080380f0301107050400c1164170f2081d140d12601184031300109514040010703417280b00e60a005040c2540312020041603c03020480d2400424194003140070302036586500584416003887c400001a0034540419a80e800b6030081d02d82c5008030b52150140f540300c181a54414880d004120782e00325550044180b981c0c1c1e60b15028600c0b40d401900c8203005454038019004880a200c01a94140304c000724a01c05403864000688071000e80c0045040c4054403504002105a840c0d47c0c0000e0980c80001008200c201c1620176080005200fa01e8480700e03840c6903290141510381c200d8002244100e04e440400880116112400710b00f805041a0394070801c3c4104204c00740d6415 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 8951706 1250 8950456 8950489
    0x1504090603030e040b0f06030903040321120b01090501180902040b07020306010e04030f03090204090203100f060503120703081306020403050a020a060206040302070509100e040c050f010c0f0201030f0209 89
    0x1581030800516802c100e107441d004600300d90401c503d1a00e880020340785400040312a000340404800564011002c1044401458001c03450040c04d02c00c1c5e00400c1580d1400004500008001d40c0c0000010440c0b070103444030260301612031040725400d040c011281800c42180700c03030610303c0c3d21400241d020901d00c0108060902da000450340c030142c50060520740f00040c0d108d0202a1040340030803001c26405002c03a280c40300c451501103100c1c082400014054440d40c0400f96060288814060f41d2800a62000e05900d07480d20040c4662541c4108040c0ca442001d00c2960000008105020021780b040c2444c56000004522005440c081c80c2c07034420480e0401c2e01708a030564007505012066292501290000700514401070281c0e1400f84c2d0000c1d202d4099204a0340900c0c03c3d02c010032a000352160000e0f0181003051340e82503031441c003800c00d0f01620900744101d1f03000c4d4014540481322035105040e40710130980c000204a0840d03280c0d500440c000c002c40007103420256424000340303815035504c4414840389402c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 8952956 1250 8951706 8951711
    0x3121303140703020a0b040f05090a0209040c110105100302030c040905160b07020901050603010501050d2a0309060b0609090103120207090207050606010305010b160803060f06040f030309060201020307050301090506150409 97
    0x1075106000d12205c6680068100c0107041c0000c0154281102980c0705941054860002640b02d407054800a4000c82c01803580c45410060030155407548004484503011801d802449652501c1c0c405038240c804602010b509500701c0c2d1410300490070150420181c0900c5001166880c1981c0ca4054070114441e81000a2a00340018840258945014118051302085030701e50302d1545003000282092260103c0c2c40c1003e61100c00030940d1228a09140e1a000e4203400040c2d0500d030400c20060080c09600021580c041c5003d0b0411110f0a250082e00c0c0008005400e4200b0381c0d00b9a02e90700044910350f60484c0440c4214000460b0703d0f54a030010344451403042c80200303c1c50401c8400501501c4c016004042e0414042c8044410303116080c40c0313030f5842134102cbc0d542a96601c1c1c2c0c0b400b0800100070382e51456080500043c000a070100c031040c03081d044900a503540d9241c951034140482c02d0380710aa903188006001403005101940c256400301d41c0000e0001e0030f090700d00614004052286d0015401441e8595 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 8954206 1250 8952956 8952959
    0x402030c07061103041203050f1302030a02040507030b0319080708030a06031505040506070c0201020706031802042f03070801061b0203070305030a090f0806010b0a090b070501020a120506031213031407 88
    0x103d00c11500003040b509003408e00a91505d00070416080700c0003400400243d034140c821070190340b42400000d20031500a1f0041c4041c0c40c2c80c5d01c019004d00302d014400c038064885c0111301402c11321740f1000d115880307074403206161800802c0d845500c21504003034003591449540e14800800500d4031041c06d00c1c0041c0c05cac1004203940c600f40c00e243d13040050040401c400d0051134008000141e0b40441c0765015540c40e810b0000d050000d038a0151449a1000780094020f850031034008203841840e00b201014480400f10f1854203001c50b6002c000e0341c001074548601041c01c542c014811207029810700080c05001d240d80e50182051900084c1c50310307040e540140d0700b0303800000b881c245880d03100380300102900341248503802d0140340950440c0e5801c4140300704400d03181d000c03031411069813260080d10020303c5400c00c0075846014500f40300e0b000350b00420310350010a07020180845461580d00509215000040280000210a62000070b80754809400d114a07900c3c50305c400b00000708504074941d042c0e04540018080345 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 8955456 1250 8954206 8954213
    0x8040e091605040c09092004030501090203061e0c0702040b030a141c050d0b040209100504090c080105030d11190b010f05030a1502070303020904020a050909100b090402030c0706110304 81
    0xe12054020b107000380c4c01e165110030b26035008055103040390118480001c0d510000b80c4003540001c401842c13100030500020b03002042c04015000440903034001c900340c540c16150a100d45400b004951900080000640e0015204484030006016034500151021403401c9000300024100000290112810380b65030340102814081081208600502680205c201c500d0003174000d40346002c0c072484211840c0c1c4818800c841912aa01520010f81c000740150210340d22000d40649180c1040c01085880c603e0140c5a0312640e01c18503560f412a5030181c0644980240b2420407500d10050040b202401d01c80c00c81440405201a406a0410360060b0504a2a075040c40340c0c42c20088106e901c1a44658044419000410190000d03940340391591480140c0c0c910091801398041e0144182d083c3d031180c40403d42c201c080703402c840180a074110444c0c03403021075911040c40d10883d000780c0c05010910301040c40440c840781801d81c000c540105c007401d00766040c13524039600c00301564540d60b40d460103601c0110520040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 8956706 1250 8955456 8955493
    0x1050a12030e10110c09090a060b1504060503070f0201050402011704030e09090d080f0402010203030601230403060c0e03150a0b0103020f040f03050609060103120c0204020c010509010e0f030403020a06030908040e09 94
    0x20440b040312001c2c0a410301f001c90300d6079541c8102d000741c1702a84e20311910f4500c2e5034101e007014855016920302912140e80d040040c24540003181c6240100b030880050003c4644184901c5110341e50503144c1800201900400f0000b000c0010070032014401c2c6488840015900d03501e40600c0b0b066224000c0c512490806402840510702030a24801e00c0c02c45014840140c1e004030a0700d074005800e2900c4102d50b03e8010000ea06901a50001d81c42110005808030902c01c0d00c1d081002e01440c191500440c006101050540d00d450340004441620b00c19000f003104041c16070404040c6500501d00035081c5941214120f40b294819840810601e801040400070050140042940540020041c240c251b2642c2c40e03030320840034003106140030001c5409160003103550700d90503038260103032010007004149823040030f550003000c00038015a83c5116050a141c11050008119819680c2c00703400c80b41d14500d001c1040c2c01800b01044210f030000e006000120320541401e00140c425240f48004101c018840a80b03101c6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 8957956 1250 8956706 8956723
    0x30d0f0b030d140906160b190b0319060509010b040e01060602010506010c0c050603060111030c010b191409040620070605010b0702030a1b1d0105030f030301050a12030e1011 76
    0xc0c030031003d030100030b901e00301e81c196801918103a5a00d03030341e180760b42e41101c514046031000501040340802400807101078000904110180c1c510104001c00a0701c1c200740d903841d070440700d03050344e00c09040d0142c0c0001d0058100f950811943c000120303401207107900050030b4032108a01c04405a42d00d507410001a6424092203070081800e00380f09120021030307101d444211446010702402084000041441e90b40b2803a054400441001d0603261540900440680078000d841c0d215440340c00140307800750913440c803010303240101d4980340c4c0100c82c0c800191040c17042800d8000c0094900680d1610300d4181421070361981c002d407d44d0421070780e5443e03040d80350400890300d040e0480387c00c4540900030400103881c00540b4900d1540c00c81252100c210340c00031094078464854002c0400030f031025182c14503070303d1130558a6041c0d4008a0a440d020362821513490f541e400b007481480c1c4d02881e02101082401034495038140044c0c080d142119014450002188140003130649c00c1c000201821200c521440003480b400a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 8959206 1250 8957956 8957983
    0xf0f16050603090703030503040c0e0405150a0216031b0803040302070f06020c06070204020d09080a030f0e0a05120a02070f14011b05060a2a0507051006030b010b070302030d0f0b03 79
    0x50450030b100e40a96913030145800010107200d000008501880340c0350801c1801080c03204441889882c2074500607440c0c1c211405008140112180450000115030098400b202803e104021182e401503d040b01c2140c0c810040e000b5400240c208500450200002144568002c1d0010060741d482d00c29021040607241d402102103412844003046146d603203204513000f80750125405078480c00008040001019541c0005100e01c90011300800c0d20b0b50150440541483e03060010064400f803600b226072034100394040200103420014400e080450310b0006041c5a24407031040318140380c1c48d0b000066100020781c00c4105104d554211044045d0303400041803a101c130b141c20381c005600007540e4a00340d840402801030302065407200041c40d40301d2004442c2e480d0010000c0c0c0e004101c1d06800e803002d0722503405282d0a6606001e0549800405500780c080c03007003240e034864046502031b0700e000e07031f42030842c2c20050040381140002c01071590519500e002d40c2c80340a0307840d0707070004e40c2c054035408040c540700d01c00c240307032 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 8960456 1250 8959206 8959219
    0x7080f1306050703021c0e030f01050603010f02040308070f03050f0703020c10020312060103051905040b0619030809010507020a0509162021040f17010b010305010b0702010c03020f0f1605 82
    0x1600195010401406c50030302944074440d020a5110203a40b2a0041800c3e660103200b56048a5800c0605400450199000350002c004006c076290040081e80f289000280c0b80328000c00c0070301c000a10031010300903c01c0c0039203881400d0024800050580b40e00441041e40181d103c0303006041d040c9440c044c03d01001c107280c001940381c800b020600300d100341c40090403d414940d5910000d00c0c0e400c3c030070340000c1602400c09410041c5103010b2400310b600d00c40686100380114186550b1140703c6160304103440540e50800076440c140302d4400011102584602e80032600200844c5000540f5103800d06494000d030803221038058004600140141022401200d580301250b00002400b800d082c00729600005d2001c7e02c200c4148240000c5001c4040d02c1282c8c444000300404050001340307031031080c480200510410000b8800110203a004405945007070064008000080003454015070140400d1047d0520900541d080c0c40f10f10210390f410102888440c1140d6003111815903401c0105120a60260500316030a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 8961706 1250 8960456 8960467
    0x902010e040515121c0906050403110a05040504050a03030f05010f061101061e0602010b010e0907030203061203160507080d02030316020106080a030302040806060a1a070807080f130605 81
    0x341050140490a4001c695510114094030001e101401041c1006000040d5000030135001541c0c0d840111844048580000205014a07219681c00e5084039815a00c030350903d030030350301ca890642c000e00c0d28482c1d01c48242c0301d0004407500e860160f684a1760181001e881c040b0440e0a000d81640d804400480d0b0061900300140f14680c601e0f040003040d03500a1400341001c51204041364014202904548081c0d980f092506c0d83c0c2d1880b0110705410380e00c0344d41c02406030400c0070b40150f414444480c101580031f03000d0000200c7c218483c3d8003455200a004004540c5010220003060845e4000e02a020001503403d010707600b400701c04c106920081c0b100c18001d188200420000035141d01014103120b26074030400103c0705051380300350049409011040142d03031851045160180095109108813030f950300842c00001c8440c034040b5003200494041600307009203410b0400344103c0a51007200c0440351648240091404980484042c00201598035291a0745507140d950030740282807141d10400820600308074 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 8962956 1250 8961706 8961709
    0x1806050709180f0b03010513020a091406100219050d030b03060f01090914150f070f08060f0d080f0c070f060f081506070507030b010819020f0414010801060602060a0902 74
    0x89007041400310b0000350b000703000348110040c3c0341100800f07a244d070a201c24400411030040e400c08009200312050402c09a440079003a00ba10b01403002e11341903074040f00004c0c6035400c00070b58040c101c450501c184c1c0d9404541c03411501c06512b41d90707000d448550000e0442d02107036405204000c0c140804400901203803a000408000002050007590421034a400301e0404105a0144119074040060152a2611900501c00c0c050003001c9411b0b1444007040004102410b01456012024400580e220070b016618102030082d0a5081d450050304494030440600200300517501a0002042203480b0076500c0460850789403a01405800514040980d590100f100c2034000e61421001c6a4500b0034034059541c45800d0342c10020728040d215080b9100140040401030301095240c29a4482c2d5050625030340c841420b15074070401009210814422803440502510f0300300003414612800801c045112002c17134541564140c801c0e40100f1190303440743d0050002a406204541d4021981e181c00c1141900c181c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 8964206 1250 8962956 8962979
    0x40e03030a150b03010303050918040201020a110109080d030902040609020a0203030a05040609020909030c0d02010605030709051801090515011a0d0218090c040501110303070203030714040305011806050709 90
    0x52200307110030354a500b05016903000440c20300042558990b0305490703680d030b403d025200ea0301140809100c0e4100d00c8039484254002c20076540500e4040c0e00402040e505507540d0300705180d040843c203051200300315000071000d50401c900000700340a645c01080c038036a90300c10320054410640101079042d00501c4000011980003041c0c0b40c0c001d000c44408134640e04c0f98241440100740b0a400650070141c50740c01c001c513000c4000000c1c5503e10f00201107491440d010b18040b07089407080e0264541c0b54100706070400403250150446600315441360f22651004000c031814500315a10070100f201c0c250403802801b48102000e4130340b01d0061403090810701c2159842c002103a02842801d0b10068255404565040f248007001c00034003c0200107080c0c102282403039000c103180c0c2e1700140720303440c0000c02c090080890b02e01e0110944e80241340d107400035402d645032208196170070b10140c00403c20071039043c0400004200240503031940c8103d0004c1c203070844811818071106503203004210317000340010b1880410407c010b02 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 8965456 1250 8964206 8964211
    0xf0807061416020306070503150301050105060316020c120a030f03021201050d0317040309050f01050c10020c1c03050a0c030c0c0803070203040308030a020a090501020f03030103030804020a050603090106050f040e0303 95
    0x11030507556070312a1401c5500c00d00345031a4080e402d403054104014000381c00c01c005500800000306a10710b0b10300c18404240c2641c0007405a1604030704148003140300143c44455008a1058a0042e2200303d03d0b130310f0118010b0a070907182c0555503449024207005158000140400840c10380c501507180807449a45800d02c00c90620500303004090089107103003810304c501e500c80c1d40c803000440490440e0030207040080c8104003501903540305090b072802140443d8000e800300c0e110b20440c1130240140700c990740f41150094020301806a10340c09202d00110001e00844d06803155201e042e200040e075130401c6101041140d00e184602000d05150100c040482a040784a01c105227500101c43e41c0c0e01c1d03845040403415400b65900040020101009106036100250040c200300035041d6112052640e074ed0004980d00d4a030810b19011075081000103002080c4a0054140d002d800540304110483d900e0012901641c0708403064001a550713000f06011601d0020036810354003100b2103007485a0301d491200c2c180c030f901c0003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 8966706 1250 8965456 8965487
    0xf060c03030608060702010603060b01031e0b0d05100c020705010801030b040210050f04080a020f06040605030c0a170a0506040b10020322031b03051002040b04090203041109010f0f080706 82
    0x2204640041501c00d0304581d0290000005440c0c040c101444080e0103014580000c58041d41072000d0300446511911401d601e010f5a208044800700800100030000c0014101942c0c00640c0d010955001c605d08000312544c0c5c1c00c1001c00001d888002e180002c2c182801c0e40c010504003d046001080030510000829400c140c0458191100c4004148151501c0c807134404250f24a25000c24001108000480c00c004841e0098501c1160b110744e403030400134180f245004810100304148013041054003c6009000c40c50803c0c00c1c0b0b4003007400096107030034090000f200c1c2e1341d04051321882000007030301342030181c450042810b441800e500ba11001c0c0181d100e009011107505428141d0800941c550340300c0040070011368006c42407a0468181402c1400d0502c058081901ca51145000c0350100c4000303442203c0890341301503100360401e41010070303880c0690710140c02a40c0480c50840c2e03091080d514055540c1c000d0900021b0605824900665001829800da00018a40c3c02a41c400c0200c183c000c096410504003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 8967956 1250 8966706 8966717
    0x1a0108190803070e0301061403150105100c03030603080f0418090b070c0f17130608010302010c0f0201030f06080105090c030109020a12080c0f030d05010b0702100e01030902090a0504030e0a0f06 85
    0x1100b034001c480004c0c5030406943c0c550300700007000030301c55805000c5800c10502601590000050210a602c1c454000e11441d9003010007000f202d4501c070310410319217074243d01c039282c0800d01960300d850703100d01504a4292111f031400002000c109080c10811280b0002e200c2c020180940b442c6034403824011070300101400240503246800d0b0302040132802c48036844903480b4a20078100034101d9081380854121380741c184005048100301192a5003d4408203040742d505030340745020360030903541d03040760000808001c0741819211032484034603010500464000d400f400c0000501ca1a01130009843c05258080315406649030551600160f154030b1030740e50694940c046540030342803880c50400205d104000741c010f034038050030304c40402c40301cbc0100060203002e054031010701159803101111071140c894110025400300c000e81d50040000d00848100000e0710050400091042c05500401c0d11040201c0d07560182c036030b48804000800d41c019042401c95030054904808241c145410203640707403418040c07103040c0b14 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 8969206 1250 8967956 8967961
    0xd06080f0d0305090705040e060708010611060105060f0f07030c030e041401030f02030c0d03030e12030712050903221e030804060507050309120109050f01020c070501030e07090501031a0108190803 86
    0x32002c124680040030003410400c4108c240c45031150322000c05807041000280104000107030b00d40310340c200c1040c42c0e0011002e4403060b460b100030001e4941c003178144048160b0052121069910000014141c40342c06501d4070f0703403100943d1400415980020b15418803540c50070612840081c50300101505499006002032650f03d40c0740006440d0400020803641e011101d1203512040551641004100d12641012602c200760303a03003c000e04a0204079420710000d0b050901c800040c8540c0d412844c1c000240c48140c80c5441c070000c1020101309200c04d006801c0106d42c40c420000c5020078085441b021480c80e145402442c190303035078003d05100d00d00c110002c0010102e0f9136001d120050003100c0600200400304600508403241841c080d10b1682c2c02a94280100801c85c1c00c1c2d82418000c840c141c0b51010090a04c15041100540c02042d046048401601c541d9401007170030300c15031007a0341c040c46c060f2070104100001d058851011802c142c10850315070304900301c085080e2107200d07050b0001039800302d829900c03503 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 8970456 1250 8969206 8969221
    0x21216020103090c03050303100e0a0501050d02040911061b0c0306010b041503020d02070b0612010b06250506010303031407020309030a03050f133002031b01050715020d06080f0d0305 80
    0xe030651340024046000008c00d114802070040303d0388003254290004070700c6643d035044805084800910400e81c0000803603416800500c1c0c01d500c1070741c03c01c1c825010012410014804117403187c00c60943c10042c8454055100c450010401001c0f03034a000c214010301c0950306140c0c8a40140c0a1442180d4038402c040d4601e0b21014085d030192500300844e80c1085480d802e07c0d0806903580d4a080d41c00c24014081c40b6801c5010860600802c0080030300900745c549407008000c0b54040d051900d4407507034489035940c020040029400c0c04268002c41c0260340100c0c0948054420740310113100030f0840c0003558410480b05900d0f403000708550001d1178042c20310300d442d119107010b104511300c0b0b031920307415080141e904041443d20600403550325004890b9420a459035070b007403941ca4420107158000e5415448004007110b80303000c04d081005616010b1520030b00300b803000da442c03002c40c078810071030f04400d00d4021580d203810701f015114031030007010605e00504c82c41403000c50305916041041140001c15441e50300180d0710 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 8971706 1250 8970456 8970473
    0x605060a03020a090801020c0309010909090b01180608060c030a0b0108010e07080c07060e01060602100207080405060d1506020d0e040603110907051306030902040b03030a0f0809010603020a0b03040302121602010309 94
    0x501c12000295235519000501319180c0d440305120fa070114952401c0490600698030951041c264890510b0342c482c2d00f0405400b0403505c3d01203100319095215000461072010610155018a506c50320b40da1720390801d801c0718801d031614500310504000315600100402550b581d9816041012030400302e1040d110b80d000b0b44507510500d10054030300ea00344407034120781c5c6c40150700a100312a019400e841501d620324030504241d20800308040d10728130701800207204a140c0a002070002c404039010000394008a0464081c030320003664016009600082c400d0b41c40039400214041d031200741120300300007030343c1540d544142d44040c0c500d0050003206450700042480703015008465a5440c5000b0311643c25996402c014050b003903a6104900841c00c140e0b5901160600006552002c8030589079060000d1814108840800004021010543d01c545000005d030325000705c2d81b00900790070a0380e80c0d82d030718107810701038681040742144048031071040100811200312007604940c2d0548c2481c01203400c0142d414031600 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 8972956 1250 8971706 8971709
    0x30405070308070f0c05030705010507060218181006050a0c060b01210608071a121f03030302040305011401060206070f05040e090106080f1603020d020d0f050c12010605060a03020a09 80
    0xd4084009102010310040c810141d442910a07070401005e1034a460a15448011a115540c00314a042c0030400004603640c01611208132402c03800c056010907040041e4040d440040c00d880030048010600c0340d862605200100504800d0400918040c10b901000341031802640000c2c21060356065031038400d03889545008a425480030564403401c2075240c481c40203040505c221b901e030380b080034400184006c2051b149001064000102c1d414240b10740b0300d0740014031009001110505609502050245d400d26412010754001e82e401601d4074198a8010b0031105009080965454550f004101880d800a04a548041755107442510b00c5010310083d6028000d541020303002070f01080c00c0000542e415070012040720b00c071400715103001e144400241e446144881d01018400042c880901c0076081a01d0070301c1d01240b01801100d04940c9a85803a490019614030484003500422249509440e1070200206112101030081001c03510b040c0c0090014071400e0745040c2815004600d00144030b02a8400d0ba0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 8974206 1250 8972956 8972963
    0x9020d08040906050102060405030a080702070911030f0609060d02011209060e06070e06030c0301150c06020706090606082404020103061502070303031505090a0b1210050405010f0203060d080304050703 88
    0x840214038081545400900800c550549002c100060640c030004407140a182c0000c06545800b9901c141110070920052801d8150b225100000401c40b00d14440d26591628401c41c1d662642030416072001c1d028000784c0302074400e221900c244041640e5200f040c082c0b80b030382401c1500002030130b581d494024200d0142d020b0101460701c1c01e03d2986140200e0741c01c2c0b0480350350751101160b0900504025050006a907000b0203a4414401031101c1d00400c40544070006035414965607890040d07480c13506aa01441080790410b40342d140850402003039000e00d00140c401e40002d0008079050000d405141e2044840d03480340040308801040959000341d00ca035014200d0f10640400948482002039505c0344c203403200b140041d242008a03100903005100c240155200203040c03298540341c81480c4070241403181f0074194440c521560104460004001c074411800c1441d1f03005c91503281c2401c1c030a003181c0b16040c02145090041040118a036500c2120300041a03100b1059601c80c0c03900d0429510302010f907000203 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 8975456 1250 8974206 8974219
    0xe01060f030602180402070b0103030809190305120108010606020d0813020603040c080606100c121107090b0a09050906040b040501110a050919050604090f02090a090e2a040f0902 78
    0x402440901e40040444d100c01015450394000940144022841800390180030320320400010b0000a210386a265040401361003102d110400b1080d80344d0f20313040510001ca02146000405010810344001c40c0d034010304008000300101480d200c00a510380c0300c210107100401c140c035800604070102c80c6140e12811a000b41010382c036450140780c40031640207035018180241c410039000030308601d464920f20501011503030300c03c44150980e03a034041100003400416001e12240224901c87c0c0c0b14100104002041110400305400600c0310901191a406402c4114102c0c103010401c203154400003006a08982d2040c01400d0039610b9040c502d00500d000021031003561000105103170010f6210b405060309032000c881d0581c44400c0a082200c402e5000c0c410590409001d201c100f0124a050b481010740400c450000340c9040841c0380081c01c86251a0016040581d0385e0108900c80402006071400d0300140d450241c003082c1c46034000848440118145900c82e40d2110340b80d01b8505800d03002104480d5025205 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 8976706 1250 8975456 8975459
    0xa05040f03030f09140f010e060904090606050109050405040503120402180703020304030e030d0905060a051209030304030206010e070c0602070f02061809090307080712020a020a0801050103061514040e01060f 91
    0x10050b100d0007006100003413a41c200840c00c403c0c00f002820304420020312242448015000540710340e000200740790751295080c01180d81944844c060aa40316114190029555061000240521304142c100a00841c9003400b0040041c8000044441c40c41d0300d00d101b07400c20364561000811854900e19010100440d800500c5025501a0081c502171403081e11401d540c2d004070400d040e950614843c1c40d030005050b031007040116080007802855841e1030703841c0c80f070300c2c260440c00c0208a10b1410761f800304159200004100034540d06000301405000340040001607810b011000825805000d40081c4c94503600059041c1040800b08001e000e0542c0a0841a185c41d40c2d8001900c001034940c2038107004000850000700202008400c466074140e2085103036051407401d49840640e000401d118405611030425003401581d0b1320800000141402000030881e507045142c0384090311032041051500c800500000c1c0204501410028806c802c15a000500b0311060001240944120b84c0003c40001094a0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 8977956 1250 8976706 8976713
    0x310203011404090503120c160b0a0b06030103050616020304090f091703060a031b05120a03020c010305070903030815150901030b0a050904080d020d02030c0702040e060108060c0a05040f03 82
    0x15504aa03802295a07500c048207000340015182c1c1c5a000801c1d81d04204503c09009800c0d5803096000002c0508a6041c40c0ea000f450823100320003000241c800d00004010003d02204900507a0350700401969000e0541d4519a0344070f9442001800f560100c0c44010761003207407540300304207450080c0308105040c04002c01001204d0000d04828a041d10000c041020402c0000d846204076401440d000c1c1042000900d10b4540046180303407180d01b003000c80d90310000000e035541c542c1d06403d984420007024224000c16403602a25001070790303124906060500041000464000f21200202c3e0b405007840c000680d551050b0754030050741400c0159000111818107480c080d200400303400c4407075080e01c0402c500c2074141c041208401481c45200e0340040382d200024001070515025000000d201c84015003030070a0400044160707002100e004084050124526066162034041d0219094070400a800c507541044c0d410380c0c079203800810504804c00700182000d249403190b02124004c00a030301104590584030b19 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 8979206 1250 8977956 8977961
    0x90605060f0307060f050d060f080102090901080f0601090b0310050403020c0a08120405010c0c03081611120606040b22020408010c02060705070f02011704050115060c0b01030231 78
    0x210150301440c1d00c0c41800015040000390082a80e0303498503024008080741c1c400f118a030b808415029540c94658800080030002e04450b5005008171704000360f2a445c03498144208900140e014a49130707070081107030000c000e001040341350540e86461710110380d04000001007071819641e410300019407480c02082005144c0d0201e41700300c001d6012030745554150b6075500b95070340d46c02404045c40b5285108200400066008a4a0219562042002200d00c9a8944840c840b640105000a04039401c2c440380800300584844541003a4008a0f0b044800b89008074806941d041c6c01092940215540c2c0b2510074540d9400d074201c4d000014044548170104041040007019400900c81e08100e50b01303000c81c0400c19800410392511455043e618607040080c59120611116900700090303040c0011800549c40f003149090000d84a18055400400d81403040c4140b0f154031100c07540014108420007a203e0009002080c580f07044a404403080d44c01101c0110078041d0240c04022644282c11803072034454000e00b0240c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 8980456 1250 8979206 8979211
    0x3090b040c09050606270307030c0609030c05100503130c08030406030f0c020f190809040c050a0807050307120506030f0105040c0603060b042409090e0102090f040603080301060c0f0204090605 84
    0xa082480310b61160b405010b006d0040303201400003100d044200050100060100c020701030002000c990390780b5902c2d110702426107000c0d0041c00000342d081c4014000e0100c08007400c002000c055450f1103116401f03440c0186240000f800b0b050605140364540c0c01407240480e03210001c5e00511050381d99643d91108050000c10300341440c8010103042c940c070340c614940045404c090856030003024007948c200e64626203101540445e4100d48103d003d0000c01c070035031980e114070300482c0840e454140d0380d00e030716000103400c1440c014001010004100308000075150f0090880d404441c0711200410107465002c006030910315204016a02d0350320305820070090220090040c0300300c07007054030100081505c41c40b19107514840c0340504c0c04803401c1d8262954403c050101c0c08032110741e2914140c400039485d0359528058480c00941c1741880d07034011803094441c5c03814500c84400804100c504006507031550341c41101600052141030b05211800c0c1e014418401490070110300164014820041300440d480c001c130041606 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 8981706 1250 8980456 8980469
    0x901030905030c0d0e0f0105070803070c05330106050d0e030702090c0304020a06030501081506010c050a0501020301060f1e03020c0a061103040c0909050c10020703020d080a020d0512010302040b0103090b040c 91
    0x612511038503901b0041c03604450410103945c0c0a1920180d51180452030b400079007007608103e0002c0600d80440c8060000070040b40d0940c6106580c0300401040000c212003c00800c00480080001089015040001c07603010b026139000c042400110581c82c5419401500001ba402c1070340c0750104941105144000c5210f288203c48441032962146000c400702d0b40240154402c6611050364084000c00c90414640d0014051400840c20816a61032504288030810100c9890f0340110043c00700341d42003c4c1c03458107030b1410718142c43d0042c80096400409040045d140d810702d40c1c001201a0880000d204000f00d498200c502484402801c100e000c05a5004071400c1d5580340110b44007003007000160180b02030803030b000b80c014000c040d01081001803012010348510154401c1510003c010380708d202511141600a003a2552070f4107980320080d0030114040001c2041060030401c00c8401000003003c941581e406a0380001c014402a005800030401c07507034041c0021600e07800304000c0140201d01c100603100c5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 8982956 1250 8981706 8981717
    0xc04090213080d0903050304030201030504080d180209070c081b07051e0301050a021602040b01050418020301030209070c1703060a0902070b040c05010801080a08070203030904020a0801080d050403030e01050901030905030c0d 98
    0x11194040350701300140c0c00000c1031504100400c00240d03210f50045a0818021030415182628480c0c40c101186c031010b400307803185107400d440d8905600e445c10031700350702c10440e081030b220b1804107a80d500094451211116007280075034180320710840040100c1005440c0150604140001041320502e1000101260074807942c20440040c403040d1540c002e842880f00b092502001d110707059420400074020030f0250303030304201043c00009080240d111195100700890f03840185d072035065005002c08000000c0401d000d1000030500d540000d1075900001c0d80d0001c514850320349948079000091361146070342d03104116241c004105001440fa0341003407540200e00c101e0400071036070b642d04010744001009100b81041030b004a240500400c02607002003001131301c003d00f643c0c907001007035002900f00d802c41425880011a10700050109060070481d58040740900c0c04c02074101455603030000c0511441c40c0d14581048004107100d48564041d801281003a5848416213884401d0308000320342c2c600950122000151 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 8984206 1250 8982956 8982973
    0xb010902090604051e0618040b0301050f04030c03030912030e010c020c0f0d02030309040f0501060f0e06040504091e0501050a1503110607020d06020301060503010501121a090c0409021308 82
    0x40080c42250000341d406080c983c20980703400208644c5240c1c4a83d50070002d00c401843d0765203030380c07418010300c8540320000c071605004403020148002c0381c02c3c1400d4540641e01d4402402101e140d1002c84540c49581440c1184002c25985011800380192803801494018440c0e08200c245405400684000c1c08001c002c00145101d108100d0352004030004041e001000c00a100f0711505181e600b00e480140058212458442ca5001043c00c441c0040203e028840d80e880060218540c000400e07400000d0518200c03480d172b07020078005107251056100c4c1520490f901c1000f1405c1240c007150f40c6008440c0c28140d0702c0b110b10142070960182000f2200c0c1100c0500c2d2044445501d050340d440c0300e06aa130000c013090035404010040c002d40b0390241c90140d034007400d90614000080e0036400154040c0071240d0f02d150320f130f504d000000b45c000e010000c00303407100d281071110030b0b29a40c0c070040020080701811580f590303244c0c40b228240415407080341c019081041c0005880d0400c10141c2d04090219030075241200c0380c80 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 8985456 1250 8984206 8984219
    0x6120c120702061e090c060c01020702030106050303030c030c03070306050d0506220305030a0c030e0a0c090b06070506040609150212010e090601081209040b06030106030f11040f0306051005030a030503040b01 91
    0x1c0008031180040700c00304a01307246241c3c29039440356034084100021150429000400902c1607040f00015840a030b400040f0581182020b0003814001c25055006600f1400d0610404005020081900301d158401000080041707110b50000304c0203010113090440c08010f5400c1080e1100310403a400b510017600c001c040381c01988901d600007002901503603803a045440e0004800c02414174940303078004040d1525401e0f82c00030390a0010402440c0314508100701d8619212501c016145034211183c440d440601c0494041a000305125600035800f05000801c2902445d01a800e01d1403000c00c9035225102240e2442c0380140d180c0312506039104c01a62108503030f1007841c80c1781e4401007401900c40b150410b500700b000ea011084041c000b20340d001040443c81d03280e0304c80407076100d40099002c0400030b0344030102e074003012449100340380150044404203860a410700d045c00c480e00c5c50522004044070360b0f8000040b10010a001a840a0040141503840e44100c0d410b009180b500300340c4e410794030981c08034000a2407 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 8986706 1250 8985456 8985463
    0x1401030312060b0a050702062a0d08090102040b0a030e07030605010801020c0f0a030c030c0507030f060c030f09080915040f030305070510090f0803060607050609060115030501031502070206120c120702 88
    0x240b11040c5e6400e481d0840d20340c00e0014035080b048682841400080305a104222000b80c084060650b03140246000f040030136008004880c00751800c113035a44100030602020030f0440444822920f907050105404919414092901a1540c005041c4a2038040041003858064004029004c520411944440740368482c0d03c2e00ea005182c0010045030110800b03d000074007171500010628000c200781c520301e5980780c50b62004050300d031608455142d40e03480b87d0103039181c26110302082d00d520382c00100030035a05603540204502c55104507a1082420300f21116201c00440110f81c0a80001c04030306d074000f590783c44c000d482b5410050301140d0030701801d280b000c00500c1c14420001c40d26040804480c1d049141c0d01c40500f55440a000f403900b2500c02c00c110f0001c60810418a07024500400080041d90b240c042004050005114510101070a040041010803e0044664043c0880300e10040e0340754003510008002e441490040319510210000700100c81560364082c008161a060001866a4800208a07103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 8987956 1250 8986706 8986717
    0x100b06040306051e15010801060804020d060b0f0307080106030606061404060302070809030d08060306070201020a08060402090d0b01030305070b06060c0307170903120c07060203030105030604030e03011401030312060b 95
    0x420510920041000c2074454000d2a00200c031652031410010b8a081030381500302048481c1040c05501528203101968010401c5c0c3c0144660700d04060642466030005c3da08001c10040604070b40c0c4c860355003140c5603560804c040034100e0014208c2d0426695551082d01070b01480c03005680884c03425a002503a035004200341ca1503001100042403034281404401c0e4004c1d0800764007030381c10200a00c23030381d04030b07840c10400b6007500c1e1116258503d0600d808002c061801100070002000c5900604c910010990480340158100ca4221800f603103482c024004910404040076014180300e41a000000c01d041e000380042140300d0050750010520394450050200500c0340344d00480099000304840d501050000c5850050804460003103850540c0490000c2d10784030034060000010a00060701c0241080208810001460140099801c540c903103000030f5140d0800600103028016000c0864103990340039845030702c00c8450101401101d5031282002440b0860303a8035a00784452503c0d034040340b03800c03000050b9078 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 8989206 1250 8987956 8987959
    0x203010b0417070308070b0604050c0a0504050f0315070503100504060e040204020319060f05030c0301050702060106110304031a01030312050c0f1c02070506060109090e070909111203040602100b 85
    0x3441c0514080ba22100520b01503a0b401c000e0191000101c00110f88000600100d801800030086c907007081410081220300140031002600c9080103141c0c1440c3d0004152000c880d000c540410341000b010010906024040142d0f1556803000c40030007074030340d0b0070602035402880d101e45201c4507140c8980c184003c8503618051221451100d0001038014609a0003c1d0351110255000c811048864103200c0b0995940d60006866150b040f841407005003020003002402c51001c40080c080c5089c4200065281c40c010701030340040040c0c030b00c1d601d40010008c0048800550b40001c101d11000050007295200400130b000807030000d4031412000c0148085405400c2c061520900304620740a6031510740c1c041c80d03011860070300080b4280c0d402c1f0f4900c91789a1020f010200e0040c0c000d40f4513072829100040c503e4881d43c008000040c03504030045400c4400007083c9060312140140000c1c1102541003148192942903410f9a204054042c4080242c1012015204603690b68081761034148c46403030b503201561b0000a809 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 8990456 1250 8989206 8989229
    0x20a05121309050901021b03040920090f0d0f030201090b010801090b010608060d1a011703030c0a0e0409020904050a0201030c030b0102030306040b01030207120306030c051e0f1c060e0709020301 85
    0xa024440b8141d11a0b42c214509100051600740d003403c001000402101c10b58081c0d03000801c00304040b22030360191448103200c2c0c5070790f03c05810150701c4007042402a0744c4c805010301030004044540d40c4881c4a5221519007200c4070401c0e040c61860000c7c0070703101c02c400c01c48016924000024600c1014028850003680c4140d20345116820400102e0320b18000401792a0320480100445011640f0841540341c1050030192800d060b6050004c6c07200140d0703c400011415034010410003495007400c90a480102030186014802c640c12040000d0140c10200c2000c0d40c40450201480308114000446400451007038030144030f828600a010303411646a02002c40c0903030803c0000030f010389001d6001c4440740300c0505005007000610340350308505502840407800440e580301014000c3c08849080c1400510040300d594642c56146c0c1c0350a0114054240100d0040b030304c4964940c180e5403140c1c0d100c00a2000035012111080035410050040d101c503074201c071550b0295440204405010b4000c03641600c4400c00c0c00e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 8991706 1250 8990456 8990459
    0x207020d110609060c010204140307030206220302040f0902010305070e0a0302120106080d0f020705060f0406050d060b030a15051503040f060e06070f08060d030917030f030403020a051213 82
    0x80d1101c85514101e0141c2c80a0304020703c810320356550f0301610006480c00001a1528101050246518056241148241d00c442c02c10001aa544e404442c00340c0c0c01c070b8000c10058403501c0c03080d110600c1c5581000b036100b81013041c0015400c0300359000c4220349000341ea017880320f40c490701c3c0240e5041c01012415a00184225020b10240c00c110500f10840d00e80342e00001020355441d07200a040c8200310140d080080c2440c02d00421007541004600c010b441c1c11039510b071500594142455003072085100701030510002044038040d03480c03207902190050104164243d9a40382c0500d080b001417540441002c8500403c0001107508d007002d1440c001c019014100031491502c458030b910001751144501201c40702d80f10010b080e0240400c0c0700443c01591a40c403020302c0b0410880003e011018014512030094100d2041c41d03010070352041c2c2280441c0c40c5120250060341040c0c001c6c50452098178070341c20803604004240404c2550001e00941c62901410560305088440700c1c00e003041c1e208040050078030141c2c0040 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 8992813 1107 8991706 8991713
    0x1020406080f0a1103010e060303070203010e010c0306120b040209060a0305150a05071b060c0507020a0e0105040605030d020606040f0b1906080106020321041b080c0a090207020d 78
    0x6000c1c80313044000c2c014030605000500c900c1003014200e402142e01c6440c140216246240c028000344140208442800d000c0e044004517240003d1402a002035422104a003410859501c1348402030b040c0c9668081000c0d0040142c4030961091401c040000042c00401200c1c180400c5421002841c2c41c1c401059030440f400249941d007070104183d114000240c003089941c5800d58817641c00110b010106104032103c5c0036950000350060a40e5a01141c1e0003907c020540c12a80111818001036441d0700a26848400305100e07138015a0100780411898540342d0001841c0030000c1c01d0000310f80000000081e40d8110180310740715010740125051000ca9804140c6601510441c00158600840d00c5a1301c8c58a90b4601d80f1414800c0000c0085410440721084801103108649450011a6110340d001502d85200b05052440755071130b00000500400c9900945102c075400074140480c82c3c143e43c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 8812956 8992813 := by
  have h0 := BRFrame.cov_init 8812956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8812956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 8812956 ≤ n) (h2 : n < 8992813) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
