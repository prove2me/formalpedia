-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0835
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:03:57.837057+00:00
-- url     : https://prove2.me/submissions/9aae13d4-fab8-4ca6-b72f-18ee64eb2b4b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 150000000 ≤ n < 150179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 150001250 1250 150000000 150000029
    0x2401020c03070e090106181505061819150206180106180519020301060c02090c040f031403070204050702030d050f0103030f0807020a050d110624060a0507020d0308041209 75
    0x50784002083c0b41d040f8079250008150140c4500154800c8088a012070620a4541303141000d07a03544200100081e00f002d4400c41e107018244c40c02c691180045d007034128040e801c1340d4040e00e60b03818108032000142c000c0704030501c0311180c4e0b018006d41d00c40d010b0f580c044c031101e000060300b4104c513014807502040f216855900c800e241c8808460000428008060f0400102c0040c2c402c4001801840290302074005a2155807003520745005000d14664000c1603014680c008000c240580482e041600301100e9101032601c0351040d841041300e0650007a00002500942880184031096401102400304c040c0c608404025035501c0401d0010104401c1c4030280c0801d0150b501d60781d03080e00c203003807407640103949004aa44040040d910b4510380742030102d4420024075103203001100c00f207090080310b4001c01074604906100c1000255040c0611a50200318481c0c0400a136020a4900400c1950803e9800904051502c00e842c1405004c1100071070b003c49100042075030300e41c005030049400001751108603211904 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 150002500 1250 150001250 150001259
    0x50f0a03030825080403020d031103011404230f090d12020304020f0a03030305070e0901150f0228150c09170307020d05071511032502092401020c0307 66
    0x2e00a5000e00f25040b140010b403c141d41810765061078076482d000981e1800003e1402d0b060080c14031b100c880c2c042c0c00301402c110409040d0514202580e05480c0040344400c0300b448035800107001030100800f400420b091040503159203003140c200203480f07480320100e81041da907104d119540d02c0c0c0740b600b468900852348880307a211140c142c5502031035000c1d00c05450451740c6004480000c44010403640f003100000e4940c010010000c1d445041010b120005a810910310b50502065002c0c01a8842c40e003001c203c0c1c1c030301541003410f10030441c1c0e114408000700b4a0b208690400501c0c01c48103280003098425000410301802c00c1c0269200b13601001e142a030341c0e980c405060116070b40701100301001ca40b01d035110510098016903503035201d0313103200707440742005003030407440c0c5a1a002e0b000b81c00441c6505208254501c400f42e804084203c0e0700b5074a070320b441e884400064004481100b0f85591010f03400000100030070144072070740020700e0203100c1210300d29441c3c90002c4004a80d1140340030031640c3c02d81c005038010031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 150003750 1250 150002500 150002507
    0xf0b04110a0804110406030b16030b0a03051e0312090a03021216120207180b0913150e030d0f02070506010b190c020d060e06100902040b03060d020a05040c050a09050f0a0303 76
    0x1444084c0041c0b02107019981c03900c4081210340f00b076400c07014194002805401407a01031090100b030368801c0d24405c40581c40d40c0c858540714405901c41c8180d0380c0d00c4d0740450301102801d0089079004001d06841123040d00740302c4c41d1141e42e040e4080c000c901500c107a20854006081842c10b039102c280d03000d4192040c000c171a68a040035a0344d0500c20005500c02c0c00e9000c100d5180310425040e1240c80f4403800039244603118104520341e0000740c01c01c045075010b02560302c0400c002000081c4040b1003800d0120300e0001542c403c1c1d240d1300c0f0300c5100c0801a4030303110344100b424000e5001001094003070f9044a0540c3d0b21502e038003103180700d0b0500c44443c2034000d2107428000d0b4010744128810b10f000130712803010704840d40c4801007644c000402c40c4031250041c0c0104070b08903441101020242a0045046080c00e040c12241006031002070804c40c418039111030090210342e16410880050480a0410700c60101c1c5d810000c0c142c0d4100105040220b155030710702141d41c0c1000d85201c054804003d02050301c9600c1c3d0b85055 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 150005000 1250 150003750 150003773
    0x60f04060c09030b0a020918010803030f041b0906031103070602030a0e040f0e15090613031b1b150e060702010309020a090905070608090604051b12010f0b04110a0804 73
    0x1107050181100300000402d0032508198401e0903004409039a1304124010010301d44150001610601d82900040c46482c02c00810341f0740c0114255804400c0e5201c0c1e09000d225510880300341040f01c602203101003400102c540181c81100e121703060321100401400c0816840e00700d940203403030061340107000f003900c500d108030f2032f6450380c07a005407000404000e41e84000c010365207000c114001070382c070200c1801d412050200c0c0e4950b1103070a00700580040d04084405c500001c008141c0901040010340b04c14408242d280c200501e425400700082d006604c1041105070782102078410302414001c0d0142134800c0300c2c001d030001000158010b007a9890311800790f00540003000501d1050b03070004a41d1070003250303580c4e152003039050080c001c800404419103041c50083c00404d00600010325900081d052100040000403c64404800584000f4040300c0c0c03400401d04502c0722075442034040d802c01c0c000c15050341c0325074000701d1011030a0754180b051441da60b2851040d407103224024000075000c0c03800540401e4454540 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 150006250 1250 150005000 150005021
    0xc0605090a020d2003060a14060a06050315040e0d0e010905010c03140a050403020d2406031a0c0d020a030e07050d12030507020111180109050328050715020303010611060f0406 77
    0x44503050780c2e405012900c0c01c2000c448a806192340e500c40041500d00c0d4180d25a4460030407250f03401002d080c11070091150102134501020420151998031241c0d175103401060000701c00c0f40440b0a0390100e054014400350180c04840d01280640e100070900d03500c190302580001d034254458003020180f030440d0310341e01d5004190f004100803041c040400140c1d03071550084e45aa0061145c403541c01400c03030a0041c8800604000912640b602c01d0800004641041c0548052028400342e0360551318641c13480c84030b11075540c0104184c0e200180c050125074041e0300040701059a5801c0f6010f882c2c407501030141c0194843d070060401942d41000440f000d1007500126070048075480041000c1e404841c1000107908100e14100d0101c00b55410903800c0e50b40140c1c1000140000c5004100301c0c40b01d1410b20001010000000380c0c0c880d020142031003400001c000c010010507684841c000d00d06045100203481b500280100000150b00201c0c900901d4030000d02140620000f80e00c484071a00c4540c0c0b00e8008202500b403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 150007500 1250 150006250 150006293
    0x70803060a0e0115030f0b011b06110d0213090902011b050709020f0c010c0c02011d12120301180225060f0501090c020d21150806070c0605090a020d 65
    0x4010510b50720460711a4001c284895900350403a2000320301074203903140c0e000c0c600100391902d52036100c640c3c0e101c481c0398a0751070642040c032984d5649040a03000350802030b080e0900a800060061680041039005010f0030800b10140b542040c0c48501080c20741e4000d80c00680025004001c410030f90181009404019200700700b1203c5d043c0e60b4129440036030f0800440e900c0004d8002c15641c4047d1400e0090b45590b040c146451403900c500c0d94000380a851201d07840c803501c001081800140b685814402540c00703000c45c801c942a80e0400900140e803580b00b400303038800003101499095502016070003540ca040001d200f0350150407101d42d03000d101c9117864900a4410304e84a11000304003840c14824180a000e04a0340400e00c17508208020349480c640740000300400110748059003c46079590170051454188003000b0540c40d0900e504402c6880e083d4000301458020308051255250b00000d014401e50b1003814244050f959541e103494803020403290107900850303078208001c00108503840c0858030300706288 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 150008750 1250 150007500 150007519
    0xd0210020a060905010506010908060f1501020304090906050411090903040e0c0d020a0207080c031501090e0f030c030a080f0601120c02010e1204240203040b071a0406050f010e06010507080306 84
    0x102e92209031050120142c51a9554000340082d42d607202c21604041e00c0100c006101c81d003005c60104040c11001445803241e50070310000d4100f80c1e80300380100d80080040c0c40080c02075002038103040004040503a070468610359001c004409904040d847c1610880d182000745082c0b600d44400f502c2d581100030044030346a041081604aa00780300d02c00350600f6407141c0d004264150802c200c441c03400455090f060301c6944006010880007810b18841d6066542074900030030a5605040e25514004030812044114080880e40350340c01180000503082c001a160745401e079907241d0000714404c1c2d100990300303075000819120520840401c0f60700400410641d03840005050415110702a00300070388400c1c0b00369031510010b004c000164003009400142042034080882c907108201d00a55284282d102c0c0390410a400f242ca181484041400c0b503240c0790810300d0301d0701c2510b4103140400003040201e40d0320321000c2c0c03107100110300c58544040701e078425081a12180d103040d00d00c0d151000310750401402980e0090444 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 150010000 1250 150008750 150008753
    0x3010207060914010e0105100314100e16090b06180d080d060315020307020d0f030f0c0807030c0305010302060d0f0b06070602030403090608060a030204110910020c030f010b0d0210020a 81
    0x1441400300040c01215500255a4640f290b43c0c00d4915030054004168100002e10690800d80c00c4d1400843c2e40c0540f500340c0304038665034243e04141c0201400000301d481c00440d422880c001045004890505452645105072141500c4044034031806045400c0141804036040003803000c050792150740b20060032007900813841d07900d8107401d50000701d5465140e515103004104000b0b1900c075030008820001c0041d800e510b00200c000f0f40d110200301e405410400041c1c003061640d8001c3e0311030b40c1c2c00c01c40c48806005400100d000507000e40019036060002070300e0464026015886803007203a060b00d43c000d00f01450014558602c0c0041c000d4902e0282d00140c2d0346005800e50303075900b07004001e0380740f02d01030158581c40c003810090071820a5078020000c1c0030700c500411900781d66540d0070b1000d030703907048600198801012184142500800205d9508480c1c1c40c20002021500020300e650f4100d001c07011500204200c1004a080ea20802c00d80ca4009900d240030800520b40310341c4018101800d03104840140499 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 150011250 1250 150010000 150010013
    0x1009020306010309150c020d0c020f0d0f050a0605061c030207140609280e070912140615090109020f090d11090112061802030307020f190e01090501090c090603090203010207 76
    0x11032107145407599503417070312682e515014071034900d00d0f08e40c50401c05946061500464102102d507000180308205100900d020803090b40848406260041c0407202c0000c0145000c0004140c1603c040c3e1040c0c03500c0c1e80c019040e142c0410079440081d4107034080c00090780b03402124280c2c20f1051201c9a0310039001d02c00f001d10b035100c036101e943e901c41c1e99041da16541408180c00002c2044246c01070300f4500c0c0b0240030062071907003000588013110742c0b0844449000c81c40d4280445440345200d8813503182d0003501c06200507004490a41c1003c00811103080d4030590381d44200d402244900360760007100880078446036045242c0b684503202d00034000d5402104400c1c5180000b030782c00400760448100344d040456110300303002040c420704c0c14811440d600c0d510310b981c451300000d950b0700036082c0080c440d4900c503541c00c019484002100140028034283e00348000c0e1240c80c10820050240509180185007900000d011411809012061451502d030482c0803030609000718050300450301c0030782c2c066400f0850390000900 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 150012500 1250 150011250 150011273
    0xb0a0f08070e040c0909050603030a0f050d06090f05090606030102190e06040305070b0415080c070602090a09020c0c0102011b050a3209180c041401020709020c03090312031009020306010309 83
    0x4e8551350000c459060403201011140e001c0c2c10719000358020301032054500d0300840020764410b9035040071500c60b010642c02101910f140d4200800e024204070b54400c0e8050203811003401070b81f0355000c0e2a41c591b80c0780141400c07805840d410664005610030030f428100e000d224004202480545882e15280d04c075110f0a292021640c1f1250a0754400101002030004c0040174105100c628a0040d4943c10314004440c0300d80030701400031344280c2e80003a060306180c2d0340884060052904000554403510b00c22142038680051031407541c00340d4202030315000010b500700d106040c0100d1544515042c0f2900307034002c89550f0002206410120382d988400f01080d210381ea03072800b40d155240d401942c1c1c0c5010310b0038081c18008507004c0c070220f00740d0300051000c032400e42015241030740c1a203054002021b0300440100d2a040070340c0c0c80020034600c00908a0f00d505408070042c900340c8420f404988240c004202e050140d440300301c0e80b4111910341d10500780920540c9400558200c001458045103804a03500e030f00290700b0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 150013750 1250 150012500 150012521
    0x1e03010e011703071101120e060408041703120106080402011215260601150c0206030114090105120a080714060f0103060b01030c1211040e010308030708010b0a0f08070e04 75
    0xd8190004100d02080841e201118010000c007650070030b020396403400d003030308000040c80d130600541d441e80f03000415083e0b03c14423507180c000d011502d544c101414001d0a0f51703c40d02507249180208208807004070000822070303a5050303401c940400c4e168031300801150f0280300507100324100040d0002107140002c0d03d010f820200d1140710f81445015140c80c0e02410103265021603402d20400025640030062000b1607120304640760601614050560a4401c84500c000030400943c000c0c0080004269200d8206282000e10030030f503610690369803160100a407002c0310303e0b081a1264402c14000c0005660103000d0140d02d440340c200c000c00c03021031030282400d044c0c003110300c10fa05c9030b484d10040007408070724041e561007000282010401510703c910020001c110072911081801e03100c0c0e01c12059203452130103c0e0010800380c503440003d56140d1904007020f42c81511064002a0440000300f0812846422034030803000c0c50f00c80c03543d43c840c000300c107980900c0b00030104028003080301d11a01031511036000d041180c3c13 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 150015000 1250 150013750 150013769
    0x806010f081513021021270c1e091103040206042904090b03011b0c02060f0c0f07080714010519030605040e0a03031503081e070c140906010e0a0b1e0301 67
    0x1c1050f00c40000c13122142400c443c00d0750304009a03140405008900c00e58400081c5403080c204030b803682032003241c0c1c01a44c1d01400000049e41c40040005a001c00000150b8083c0c94081c0403007800301a40d000180000c3e038000e90f2102041104020200d50481200411110310071643e41c0f000500c03403058030640087c0d009030f500e5a102c002c950010726007071145d190b54003103803106e0710b41c031b1103000000030056101c210b0028014100040d030240049000380c00d03100071000040407100b1041081002d0344d118109031181600c14811810f001c0b070010f000440c8400d0200041e075880c0d0030010955903000d480040d030300003403007072643c0c0f100b01203145d4449000f100c800901e40c0e0001c1c40320040c9850028100d0740703608004004066244800d000140e081c80c101d13180c02e203035031010041e5a001068002c0d00c2e0311030980010300d00c44480400295030583c0500000b01030004035208000c0c0d40c0e40300019600c02c012403546690044607048140881604103000c0d00410b10000c20701000e400a03655410140c3e44280c0200c00700 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 150016250 1250 150015000 150015017
    0x50d0e011a0910150c0302160303091d240402071a1009020309030703030e1e07030b060d02010c0314070606030f0c05061204061e020d060806010f0815130210 69
    0x580c10403800075a00b183d6001c4902c4081c9280148202c20101c51400050401c100301c5111414103108001007803000c1100461200401d41d2440d015110070094071030403e00c403003011b2806104445240d107041c0709003011081200ea40d407d041103081401c1c1c645c004a98400d81c00d001a40118410903000340d19486490f00c1c44480313080114a00c60f11b141d00b40c0c40041c40c01c0c01041040081c500110a0f21040390b8141800700e0604086d020040c20400c100c0c071603007070030185860038001c02d0342d000403c481202c0c054034510a0039154101400702c0c000c94024064081801115040700191107541b040684044404005081c4403450b5142e4007601d00c5584141c03036843c1c11250b948240012a00f6240080408440c11171a01d00f0308170508006890003003014080c9613aa5003240d000040b00352416000d4405c240c4219641c003141c0b00824000d0126000740e0704548130f079100202d44c01c40041c00c039006030340c1c0000040c02015280055074482c00001800d8803e80c00507040d4480041e1618080b01000c000a500c07a80035 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 150017500 1250 150016250 150016301
    0x3050d0e19060e0a02011b0f02060a0206040308070809030a080903040503030c0c0a05040204030b0c090a09050c12011a070b090a02060a020a0b06041107031101090209070905030708011a01050d0e01 86
    0x2601d0f01141d00820700d800680035880141c0e0084080c0403140c2450440c140d000c00903040a0160060303003100079400010004407812800c0d80454107030310030346c429101c0c84103581311014100d910700d0381103d401c50b041e801000001c01503405281f005a1040d58941103918081c9c440c4003190864111903010121540b10b031400d4000f071310302a42e2407005040181c0f0114246880c40c1c54000368444d0150010359008000200c580294844840e040080c0001c1e11040c00141400f803800401c542c8a030700ca0803900d15010001107001001c90403408040d614515426041c842e00e919151001103001c0e0164042d07100340361940d00141c40b0314001d040c1c0240c450300036011201e81401e0901c5498402051188698540901780001c1398150056942d41c8e0b0b011701c0c00c01c603003030410800a40100f80d0820040e601078016000c00c000291310031052003c0e03c400703605541a06035510345503400e90b51001d0340300c8100b4012803000002544154044d01c0940b0042130302051401082c40080d0031a20b0030800c0d00c01200e44010404c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 150018750 1250 150017500 150017513
    0x106080f060108010527070918020915030309060a0c0c0303030606090b0a0c0f03171f1e12081c02091f14030c04050604080303090c030d080403050d0e19 67
    0x30b0040c920030000307024520b403c00c01c490014a020210544d00c040708458134606440411115000d00340d8484204002030759084100d03c0042c980000303c0c031a01038800020b0344856003a602900901d405001113042008840400400d40c108495040401001081d04400308401000940045000340c400113141810001c00502991458004c1010f0100030001c42c2c407000e9206001c140283d0b0841510b00d919810303490102e55040c4141c41707202c0080d40d034078103004421a0301c00d86001042c400c02441031520740c1d42d81c407141c00f00210b054003544407200c08508000b6444224003004909115024051400030900456900c0384407005074080240c3d804680f400d01c60404440a0030094216840401000e004420040554100400f5103031440b501101040c201080041038402a100007044291169201c8411503501d400c00c41c1d12040341d1040b202d01c8110b83c10b0124400b400e2440603a1024001d95460b01c1c01d0b550707a071001d00301174021a650b003103400903440244494a041c0104020840050b82c0701d003050b0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 150020000 1250 150018750 150018763
    0x5040b040b09070605121027060503070e010509040524150a030209070f020712030c05011103040507150509120c0111011505040e01020403020603010605120a0204030f0b10080106080f 80
    0x1882e459000250034411640c10209903141400b805244101d0b0341e40f07402c2a05c0d880755455022030b10001c6190b00e01009a600403410000f4544040d10401100b0b941d5002c041d940c40c0b07907104810b103e20b00c600060101d4181052081e50042c0100121208a006144000d858500b170034a8081e4100d00c00060001c101c0c1c00c00491844040c0842c0da4070350803070864000031648074001c0c16000074004500c3c1000e18590081c008203000b00040e2502c040c0380c50140c100900100d410880444013940f034000510103070306050341500c1c000e903000301c02003449a09003443d028084601c29804024000c007401182c480da0b0390f0743d044815004801004d484456410030000d0000c0701106284410790741003510f43d2a9081c04e1408800489000711000b00c2c1980c14070b40d280b4024456030b040a074203d54000000720f80b181d0001c0080840d4000014104910341c1c60304050002ca0140c0e000c01002c006040c0c4100c00840c1c1c409201c15009091603480100540d5110001800c49815600100041d0003a015005010105000d030303 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 150021250 1250 150020000 150020011
    0x1501030b01080a021003150b0c100b03010204080705010f022b300911041401050a060c0c180e070303110f030405030d050a1107090911010e0a090b03010e0105040b040b 73
    0xc2520000301c0c4e001034204900219102e04140c1c2d02d0701c0120f411211903002400520303400b000700f07a50360801d60800362505c030841949100f60741001005042400c0c14421203007141c41d0f11000c4c0a40394201401120b01c04500340041045101e0720f48413082280e141c00e44440310b4254007400382e035a29220304d00505800d0604902d03002d8003543d40c180800319066001d00000d60300d81804001014881c626040f05010340326205a038000b80342103420088019072100307440c10317075404484504880b580e80200715440e010501008040d025054800c1081c1151032039500c41c0388101c2c003004554409405d418501d410856403054002459043c03407040c400e5000e112000c140070300d1502a510f4541031001196440346654070000c200080010540c0b8154800c060024180d000d035015107000a82d01d00c50394000c0d2801c90310660750742c0d800201020f540c1d030003501901c8803400080e24001d00c807490030340c010000b1310f04821000e8055480740e0701d01107040790a00c80c49105038425000c1540b141040e007442841c180e4014203 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 150022500 1250 150021250 150021253
    0x9070302040e03211b12070215280e03070c0e0a060518092407020709020a3009030206180303010501051806090d030519021f1d1501030b0108 62
    0xe50300c443e1040d00014102c8021814070841a102d148401e890200b008000c1003101d40041012040259042c0c1524000c01c0c4a40c00c0b144201100c1c070006090141c1a225010002c0b80c64082b0000003204000e0500d1007a40b80310009130007009a0720a5040d5444080c017106c00f80c118040912031110b010031101d07000303281101c0c20414103045c100881c4118418138046141404860000380d4402020840c41c0041034900918095402d003044070f2400304802550100058003c603000030904040c140309450600b000f50707480c50000010f0b04107107000c03405941c5113040d440d6290808400900c00c58001c004049211b0782c01020b0501c0c0c04c065004000b10346062248107038001300700401c0342c0e07030340f07c425180906140d40c17043e888824a00001520780c421210f1075034020407001016024150450007400e00c814128200c903c3c010210380c000c0342c503030000d40300c040529480a07800000c1001c26901c040305000e5640304059418440600103407500400c2008030b14807409040c014800c200000c3c201500500e145030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 150023750 1250 150022500 150022507
    0x4061a010905060d060b13060206060402070305090103151511010b0618060d0e070e0105040b03070e1305030717090102070b03100317070c080c04180b0a0905100509070302040e03 78
    0x9050078500c0c80340d148584408224000b00e86070580c0450000c3c11543c43c115a0799080740e4440b51024003501c41c00000d402080c0c0021114185070003152580369050f62143d11700b28031400158010041da0541c180b41245c510404161201c8a40892121a010b9101c0e0340a80b01040e0402d42500e54001c18180500c4080c0580d8200d80d655052118040300211021a120f00c1420300301d400400400d4050480c0b0302c242c0600080102d00e040c2c24034180d840507141400103444102c181036842c40c142c410210b00e0140c000014000c8404594007045c0948550241c0349011520380f6a94800d164490143d0044c000024030b4540a40e01080307100c0080c10113260203411850454004807070043ea600c0003400c0345d0091103034040001c0f1034000316013456500600c001ca1260f218000e1303c1d40c80d1070385040d0038040c034504820356443d014003c028600040d401450302440355500d41c614800741c004540121042d02c5580b1004820041c00c0c081c0394850a2070300000c0c65558514010030060f41c0d64a203c0c5030b655007041 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 150025000 1250 150023750 150023801
    0x30c05120d061d0711030d0c09090624030f0f0204030b010e010e09030a0c11030610030605180304140103090f030819050f040609051207060207050706052703010b1003050406 76
    0x54885aa10011030700349403045d900b00107182e0707055205206241c0706c01c61074100d00e4645203400c41c2400059035200d40003004500d0715910f0715500d4000c00c5032904031183d1030010315580103110350070020018946500104044115260300001d98219400461b00103c02c1801407090b402c3d20364220340100880c1c48103646504103c241651a40701d1409400e08018000c400801400f02a026260501801030116412464912808420341030603000464199081202080c0300c101c14140d8a40c000c20024060740c03400749449042c2c4000d001c1005042e045c1a01d0380303000c0012480400b907907000c05000351580d6003030f0f00d4201a020f045184d220b0810540038070344001d00c482c00e1004005140d1040d40a80009040c01e07807801e001c0c2c500400c003540d5890320130300050010200005a005000040d00c20000ca441003610342c80c040d61107001d002c030510500200c48110600002850b044010300c01c00160000854171800f00105202203180c04040700840e0712202070004022942c484d00200c816001314044416040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 150026250 1250 150025000 150025049
    0x60602060a0e1b01090906031410151e0513050a0516090501050904060f030506040308060a2102040f0c02012403031b0c0305060c09030f010504020306070c03030b03060702010b19030201090909030c05120d06 90
    0xc80c042c001a1800c6140010030080301400018007802000344ed040042c030403207002e0006401e044914044807410040407070450445099918a000b0311900c40141c0c0750306020045440c0e4000c8900720743e100340c0780e000010340c0900d089500005075001e240500715503d41130901400100010f0801030082c01d80304e50030030500030f02450048140e14811045000c0c3c00346800014007400034401c1c88a6494646400c0742d01c035a070154080d4100e90000610882d0320010700342070612a559501c0301034042403506400040e0700540c4250209080d101d20301000e42661280c440700d2510001325100c2c40b0214001a501050340340401006070240c845000911003484c1c2540400c0c0c5030040a010041030000032844402098000d0b0800000c5c5a4040d040752194038080c14024041c0803004d103080e00030b100900d0b601100042001c10780058980686941f81080c0c903001c004030003003c01d02d0f0168204804145020700045040c840005904203281e003d0307485204413a5001c0c201e0b0700aa1020f180041e4141446620850 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 150027500 1250 150026250 150026291
    0x60c130e0c071208090706020f07210503040b09090a0e070b0f0c060c09040e160308070206090907120b06070f060c110a0501060602060a0e1b01090906031410 69
    0x800805003140303450355640c485090240d400c000b000906051004284075910044032840380b4219001c030b840d2240d40700020f90b181c010341c42580c0c84540000c441402050108184694a0748085032800c4202c60142c9402d030031074221340c0000740800000280c00c469480c201a01da030f00f0a002c554104a00880c4d445050f0b91804c262168144151010031850b040f05114015580a07420f4107058030050715050340d103070b00c241c0d00140589200da0310b0005886440f1100040d81c000702e00d50381d170f42c582c3d0050458444070016006031030100d0303101104000c2c003c01511640f501a010310501d03103445940d00503480d0000d054524032400305000d0f0f40b081c844a400318070405044200b4030740090000400c9203c020086505041038000010316200e10709041e420400b05501c410300b25030840c1d003981c500380c941120f00c400781c80701810303035402980c00305c00c5040e089950b0005a00d00d07907105041000609035159441d81c00c4c0d44a41e441500d0000301c10041941c0a10140070034071407061110701c10400c40111403010b41c80b076003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 150028750 1250 150027500 150027509
    0x110c01030c0509090712060b04031203020421060917030a0f0507121d01020304050d03050a0c05030105060c0f0d02210301051c0510050a0b0111060105100e04061707030302060c13 78
    0x941400c04142d2071406201d815220040511b800e106a50b00c0d1601079480b0340c4948000c484038840c219000c00e8080c42403081e94261549000861116020260005010305402c0c20544006903034480341e20000ba865031901c002c40341c401c2055500c921300305a803401262008440a0300031800c00c400c20112070fa2050f602d0f0900840b44800103a8580c0c4881600c90001114003d4600d6610010500c02071200000f00f29107030010030341c0c0c14400759462607000001e55220621044c0860010710040c44036290100150140064050440da01d00700724200d02480c040101c0d4030240542c12048240d4540748444400d441c40e82203040300b0502c1d65241101059010b030840081d000001d444000c1442001400c3c070024094060300324090016040072601000103014004030280468609404005503003000700d1010304982004002c1c601018030707158150b401da2082346009030b0050340c4600104031034404249186004202c1c2004080107410741ca00030745440c0c400740140c60107100c14451003980c4c07140d141010066a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 150030000 1250 150028750 150028759
    0x230607030e0f0601080124030807080306030a02041a101e051b010f02090a060e0d11030a2a06050705030403063b010612020904110d05030406110c01030c0509 69
    0x441214801c03400d04607051400a1503016003400064114015000003890880d4444100c200030800415001d442c1610b1200074001c142c188210b00108034084060740d800a0040c05035400c0c45e016600190459520b03212840c08240000303108030240c10310400c0c04045405a040003040c0301552542080b06041825103001005400140c182509100c115007061804000e07000b4400610540a510085d40000c83d40900500400b54005070b607503c45e0307903109030540010f0100c000405098071110b404e03442c0860802c1d0144070b8801e101001400e0001b5003803020000318240801c100c1c1c0300110744030340201540008100002808038902144000c1304480889510103400540039032041504040160b464a0340d440c906890214401c0d1010302510000d81490780381c0c020044603482c0e400c103840d114203182001c0d4024403800c0009002400c0b041070503041103801002884040701c581e8841c3c4c030b964040c0c0c205034002000202241610807003000242c0c1100c5090800380f140071200e240061090046a065a00c00e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 150031250 1250 150030000 150030011
    0xd0c0c14031608090d05070f08100b1c0206040b0409050a0605150406050c070902192a020402090a05030d0207060912031d010e03100603021306050d02090403050d060306060323060703 80
    0x1954403450f10180f02d42d4000d00740e4000035950200001011614031482c81540605012081001154800c0d0800f514008002ccd2040350280092a42641508402207070080420000480e4081005010f800203003158038000c2024a03000c0c5481085e60040da05c60360080040383c03400b90500e540802541c040d6041840c01d00c1d11411005d42035481c2421960101d4034180c4005a8051041a1003e0002d0030401c1c17a08d95038184000f40500001440030f0192205400d80415a0300c0300515064000746075450004008400c1140c88000180c145850804500c015a004440802c601504901401c00a004a24501e44441000e440103412100c00c0381ca0032001e0b4121a0f20420982e00850319124400341c060201c0d08c4c41c803030601c1d240000b4200e41c001648550300040007130180b100f240c01144140c0f64040c100e12244c50050342400b80d4020064401c0b024000c0034440c1c904038101c41d1161200540c0039483c0072a034145941006500c9540d81c0d410b0b843c10035500015500000e40018025422040e17074517001a4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 150032500 1250 150031250 150031267
    0xf0501110a0204110d050702060910021309020406210c050904020a17091b0603090307030503090a060e0304050f0306070906110a020603090325030e0103090204020d0c0c14031608 78
    0x140700301d00300000e6005142c00c8000c0000c5a080002d0151103400000401c070540300d810381070b641c3d44822502007142d40d0100d980009c03030411607000341407018850054801030702d0319030b0419816604682c01c110001040c9048a0301e030781d200c03541d0118a00300b10040030413008006510003016407241c0300307280780200d0300000c454413100d2143c1490341070301000343c001107a01c1c00d01d2078280307490b24840200310130460946d040c41c260300e18050302100d00810040c0021481e085140d81e0603a069000146401c044c0d001324068440400e210740100c02c81030345070b10051541d890800c000c107c00480c2607000c6a0003a0301100804c03803c0b680020400c4151107190030103500c1a50710f07000c0940303440d610030f0000303400c414044248071110b00004050080b620305200c140c0c4e03805207030700c4450148011210380900003405600d100034907135000e540310b424180c0c00900b0143c50140d0700100c0506603501801c2410004200d01107220601c46105040411407500030003540c80d1205803540c03140e880c07600d650f000d00300207030001c2c800b40c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 150033750 1250 150032500 150032503
    0x10b030c0708070b06030706020114010e0c09090403030609050f19050a0b0409060212090a03020604060c02011803020a05070509010f0527010f031101080408030f07030f020d0209190f050111 83
    0x30802548036481c20f0f03440580c1e1400c05031014007503074058001c0c03081c1c600200390305006025081d018206640c1030302c0c480e0700c2c0480740d92103180050100d40403c002000000d02546906c41410b10550080d00c01041c1145040405001c80c0d9005014540b00c0110f9024000705020100081c60250400c400200b069291764901d00d0040449103001035120b850a480e40c420400f441e0080c1c0348110707540c480246150b4a001c80552200c110410080c0141c00080000b8001265580700c0e40f510b121031320000034100c4182d1490401c00210060a901613401455924100682040200e0143c4026299800f1b00d515241d240e9003907413084c1c000c0511508088a180802c0c018040c801002c61080400104040d40d40b007402d140310f81c0490005480d4520340c20204503071540914040e030b008075480380c0040d1850351401d07444d04900034050300910401d600e40e900300070400700c10300240c50000006000180e8030344040c0200050406611420400400c00d04030401c03000c914002d040c0206d4100782041c45040c0ca203408881e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 150035000 1250 150033750 150033757
    0x50a1d0111060a0902090a09170310051504180e19080f03010909030801081212180a0b0a0e0109050c01210e010506040e030c061503030d050906100506030f010b030c 72
    0x1072640c803a48040144803001604243d070418003c2c0c03000c0308640c560f5035044042d03401074400075007030109900c0c1c030702a04181c1c1001594000900703e19400e0702031711032000a0b03d4150703c2c0b81c2c4c0941c400c001326003402105914241d40d80040d5001d00200010303010030346161b0301d0300c0b05104030303450b50104500f0210500c40080c080718503d024052401d40d980d81c51705640001007011185c2a0f001460f028000b05106070002100c0074000032100c2c4042c200082070701814039403d002016403038403480c4200219907400c0108000542d83c0d100da140c04216203003c00a00080700c60801d50301e0381d00d070b0401c03017101c02240002c01c100403254000e180c40400482c4100360580d44803440f1200c00f051902e8002d00e400c07209019480a4041c1c4011903007404248000c8050507039a0185e86106c1001d0b1b0889404200d140c041d42c02c254943c5d50014094030b040500b5004410101e1780200e4031000c040c2c014400b002840e10242c107104003e042e00319904d03130a500707003c15030098100050041c1c1d6001100000814135240005054 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 150036250 1250 150035000 150035027
    0x30201080a0b0405090708011107030c0209100e09150c09010914040204120c05040614060306130f09030806090f0108030f250503070b0604020414130e011416050a1d01 73
    0x14000c03800c0c0701c5c62080e640c400700c7c4100034440d41381c42010445107019000b202d840982549d00c40290b400503408116003010050324100146102c40c000103003241c0000b401030310550059010b00241001a0145880110b004210800e002410030241c88140e0304042c6080c20b45004d8808c442207220740c103001c11300900c61a044503524028251811082089121440c0d00340c40042c4d50511800c6d40d03891002c007170b0310a000c0f00d960b803025050000903800e0910140ca03010b00201094003103046100c010002c5d0494030100406d50004c1c0700b100800c95941841c0440b546c1011030050584000d61401d05041c0d00c0380661440070050000009402c03920030041c02220340b414107952805c440b81030f468600955282c0c04402c04545030508140000c0051402c0d109450484513086207101e1000c000a080086c2c1c404800861011a80c1c0c0b019502c0500000340304100c5196072840307800e01282001c94680c01d42021216005007000401c0000a0409501038151203c6402d800d45618901d0480300c0103a03045045c0000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 150037500 1250 150036250 150036259
    0x5090c030f1510031d0303090307030306050d020a030f02150408070528050108090a050709060e060a0f05190b030f0f09071a0a05120f010501110105151504030803070203070b0a090309030201080a0b 86
    0x240005c10348c002c0002c0c00e41610a8908001c03190342d0300244000c2d5262544003a500021420040010807802544442032900c002c203217510621802c07071444115027003500250b8065100302018040c0f03040c0002c103486012031541e003180c144024801400010398460045d1810032100c8000320380c1c0d8501c02c210640700c880e400710031360703041c55101c06580000b400c0c5413107443c840040800100c1c0f40c42c182025248151101603084a0485050105105050317810000c0040e84403820a40012154803101c090341c040c1c0b9961a8040490401d1140c040200d0b401600402e81c54004000407c404000c0c0c040da904d035600418261510381c50350410a07100f500a0a507580c034035442007410041560407100251303058501c02d07241c0c00203170103d5102e40380c03c0302c40807605c0002090f101a000b07005440d140501c5007800410800cc2843d040d104d64400106400c2603500d98050b0f0b00100c4e56004003c1928607050380400b17810003c0202c106941c500418107211440064148629480810f0140c0c1c090340007072040940140 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 150038750 1250 150037500 150037507
    0x60403050d020a1a070804030e01050903101a090c0a030c0e0409030c0201090603060e0a020702061b0c010e0d0201021e030903010603140f06010b0f1305090c030f1510031d03 76
    0x600203500c806038814100c40c5619144440d804e100314900456006120994a6501968031560709540c8010200e411a052050500c2924181d5a0402212100c01100038011543c0d0304800c42c441d000c07820801000d80b08a0440c0c2c03c0004d03030b1240c5030a99103040030340d02c0c0200f490600c01c90156090200c49444030740190505181000b0306030030551a240721403003a0b88140740b003565000c04404a480078024420688100c9002c0350300001c003500640300b1280003c240500d00201c1248800010300c000341000ca00750490010003502d513030011020034400c001a10325203081541e60340000e448000743c40905071119541001d01548503010000c0c1d456500d00640200b0040780c60b82005801d001106814a0940c4102c038041300d00c0b4440803a803181252000c0740131600346046440d1901c0e541d004a203110040c1440e00d0b07000503190740c507801c03054040c000080e41c00340da070f0800c16280071100d000205a0146200c0c60103500c0c1c60341d11942d456440388000c920300045c01c2c0030201c0c2d039580c000c401a00301000e28440807 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 150040000 1250 150038750 150038773
    0x1f0204030b0f0906060f030c0d050c04021209070617041b05120109051b010e1309081204030e040e06010b070503070c1d0108070510050304080d05010915060302030606041406040305 79
    0x100c000754040c150310030403288655104001c010001110b4040c003501070704132307000508090030006009400544101705541c056460710740130a040380c10405d420b1003401d10348024052050014072004020300010301e40f02c3c02c8400c2ca01c100010000018000400c040546c07012907041c103000e41c503900054030f001080322802c0a07003010a00d018042000d802d070b401c1c0c040d051440491000f410f81000e865003040e111800c1103d00b01040110503e4036900016801d51101ca0010004460200404003611074543d0790003141040d04000702800c504081c101e000c2c0e49000902445400300246050440c2d610f1200300b685e640f401d1a00600314010820003c015207803c2002080d8030440700c1d0041850304224252524580e60303024120740d140c2c0c40784640d581002410040403035480c8214000c5522502543d01e4074903004034109904221402640700c90703140c5136a40b03080c0d00d6034682c40f1b100d0001001d15103400c1d42981400000104180310344d01c180141d1400245401e1004c0d121a401d5070019600310003511803550b0b84 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 150041250 1250 150040000 150040021
    0x111b03010b1e04060e040b0f0405030c030c1e01090c09020309010209130504060e12030402010c020d1a04051c02060c090319140610030302100e070b070c0311030703051f0204030b 78
    0x22014201c0c840c84c102100881e00703448241d0418482c1c3e070425a50384032030300c0c0e001803042161000f4100390f59a0104119441c038090b0204001d1800b441840000d0030342440d100ea208003203025080600700e00f641454060808a00460390300760596418010040c0c0d43d0300c0c0c605181e0300a104184600f80c000500840841c14120f944d488103204501440090007800b21082d902031303c40101e400d403101c5001c401d01c003190140d440742455400c10791018200035681c0580340c40316015500410507100b00062014104001c01400380032030440e50760001c40481390010070742006500c0b0100142005550f81e00429500d030540e608000d04011424546105000c100240c1006040d19680d1001080c8610030346011500d101d80e800074840441e60168094001e1050f803207054405841d012150500c10300c21058003090655480300202030745881400c11000041c03030351034080c11884043c0b00503880394200440400c08118081104185c2d03080b201e5101801d00c5654404038001d01482d04054901c058a1040003902c0ca403 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 150042500 1250 150041250 150041299
    0x6061b0c0a1d07020a080301060e06040302150a030c09080705010e06041707080d050910050306040603020a12020a14061c110403030f02150613020c0f0d0e10111b03010b 74
    0x200c280b601c100581d140340c0203903035a89035050010280c80d820001001510302c41d10704c00209000081000c4e00d03099490300010b0302006586100c01c0c4980001a103c0d81083d003503c94215154040d040000100d443c01108030344a1040344189414081c9803814403a080d130703e40c001c481c0034281d104003c60740d00b64440e0019550b54844d020702d050910424600201160080301907034005030700140400e1428400f040c045500b500003030100c40e00562100c40200050360741600060191800b0700c141c0c5a403684d5401005a14517150340b102d43d01400300ca01c1e158203622854201d500e0440171060f0a44200840010b40d001008200c2d800800d104002c10007004050f071042ca0300506141c41d0342101c6817183c40401900b1848010368280d940310030008110101c0740c400da00a09907440400c2c0584644100400c007460514114519440014107851508100e0340350030300c100b0040241c5440d01048145800c034450707035140748001d2504c4541e0900c05030b0f241c150380c013504222504500500a12107018600042010030309 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 150043750 1250 150042500 150042539
    0x506030105010f0c080c010b0a1a1603031d060a11031302040b01050c0607020d0f030506030a23010915060e09060439060f0f021c0507020d0c05041406061b0c0a 70
    0x5070790270383c00200900c0141c024941c284860103a11301c1c4c1040c1c10b03513240c0c203400030100483c01c1c1512482ca0007680004050040d60614519018005078507001001d00308039040240b00040020b0203000b070002d03541c80385a4095800341d0640340011040035002c0143d599016031070102031107103da0410000da45a000c01c0f40c2f1090b01e801e0312a0b07000f40b400144203800f43c0d80d0031100c25415502491500012411100c110300e0140b01004213080300c2681031001d1401d42d4082c0e10280c17007003031400c0603200c014041481185d00034030582203040b4079800e0004405448071400780c0b01604e030321030b04168884004141d621b95442c0c4808102d42c1c02580043c0b0608400001c210303c10480440c0380c0781c8040d1800c6001e41980582c1365426406403074101403c4001440e50304c182c0c01084100310017806100c00580381d10405150315801005c4d000c007018038000410083d501d007400300b410348505030004c2c0003581d12440140c0b0500090102c00d065401d210505861520b0803ca40c0f0703d0f849049200c00060720200c4801103180c3c50f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 150045000 1250 150043750 150043759
    0x40e0709030515012304020c16031406070f08091005070e040e01050c0406080901020d110c19030507060c0e0306070906080f011217041208180a0506030105010f0c080c010b 75
    0x40110040e034030a07403d000d00c43d640a81316400310070039032400400c20960014400400060604000c0c3c820280380c0680c85e40515004985a0014818081d49903401070111400000900c054900810011318000041d64010b09201c00c03c00403031008141840081c0d088144141c04200ca840d04c050000d18a91401f80c045000381e15241689136400c0040c0241842081c68003400c603e481c2c0741010031114202c00a04402e225582070020411345e550b1401078003a0607504027000d540f14400c07034072054207080fa01c10a0210243c01017403184d00113130300324090304e030720a0300702000180c1440c1d041030a03204610703558481581401807000300008103800c80004000c0c0c603055951601503a48003000000743d91001e016810051400548500001c0e004080e03c070200d1601c80e04840c10555201d40100301030786440c0c42101c1c40701c004a42d42541f007d4501c40b181c2c0300501154108010707481c3c131003c1358240c841030248504000c5c480d0a00400140286000001e055202c481c40c2d030344400c42080c0c05d00030009829a02d118 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 150046250 1250 150045000 150045013
    0xa050c150402011206140f010504081506100f0206070522060809070b1213031e030c0f0813141e0102070501060510021c110d031409010c0c0f08040e07090305 69
    0x1d80300c0784500001d0301c02041428200390491001c10041c0001f01030142c0c10840704010204444000303000c5020300c440004c0c1041501c0c107020f400c110350307c000782c45600c080108401041e506141c0c0087c80342e41280b29030410350341c4d84080040601c0204026600701e41c0001809000141c125480111035108140d07207400c1c0d8030790b19122104e9640c503106102d50000c4501e03401011815005581d0002e540e00f51083c144101d10740940f810a10f2142002001c40c00800c0d602c400c0112040d811082095401d411854a03c6d02850700c030600300701e056075840001c1c0002c2400540d9040e10041044a80f10b10303803180e580c2200c90395801030028041e51040c0380854465007031110000f15400d003448803460b8040207030098008800c2c2680203403d69201c803e015020044402000c0300030241c00e109084004403035a80c00316280381d440380958806030f030180181499a14121500750213a034800c02c1c40726140c0e0301480088040805040c01d26003030140780c00444186450109100c0381603008468582140d2007042515003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 150047500 1250 150046250 150046277
    0xf010504060203040b03060402190c030f090b070f1e05010e0d1b06020f0403061d1203092e060803070309050a050a090c11030427020c0c060a050c15040201 68
    0x8590150344a00800341e8401e01080c070a0b100404d0155074010b202030001414a010030304200380c0b4032040d40301c00020602c00304400d018940e01560341000b121241c10164160f40c42e00c9000d0b05540304080d009000ca120040692040002d4041007848500d0710740b404d8200b0600a08000b8000c041f00c40c072401c114410702520224150260402030b1307184014012071170010300d0b075031210f5003c0d601c44080ca45c40c960302044044009040b500c500c1d1507440b02c0c8410404665081d030103a07480c080b0108010786c00c0a800b032042190010000681089200711103541c851403400321161507100c8040c118149011a0605c48040b50181000014100241c041e0340c600200950703c000b030200b09480e40c0030701070b004404000c05018004850700300070a07202079450446094104110045d06582098100c102d0201a00d5070040d03000480243c01000350300f141d541140b40a4441e840180d849240e1000315028280100d25903680b42e006200390f80e002407080e000ea5030070440400e0b00f004180400c4a00701d0105824080303400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 150048750 1250 150047500 150047507
    0x2d050906060102060412020715030e0d080c09010c03030b120604051603020f040506010e040905010b03010b190504090f06021324020705010810050a090203010302011103130b09040603061a0f01 84
    0x103010340341c1a006481d03503407180c0e1910040380c004202c0d444c00b075225080c0001a2180d404000c41c80c0b4003016a0002141e01880c103c05007800188000d000400402c64117011030780c01c0c017004603460700b00f090a142d04145003602d001d401034914040c03c1d980c40303041c1c20ba01c2070030081c002c664030384143e04c9032041c0c0380030303208038220700c00520a140000b940040d0080e5582e00181025805103070880c6050400c126000c006000080c191b07540c01004992036511954041004e0609004a8060080072205040c0840090300120b2940c1000c2c0b003103d01c52a107410000302808101d000c1601e036580c025200755502d890010703203044900c403140310b001038118a8451080075503500d41b0b00a030100031650302a0100c5407814004481c960390185c00c00e28480b41d942c100040541c1e0b05d103041802000c8000d000740c0c03250b2560001408907404144008016003040041c0c10b0710300c80d082c00c0c501c291080306000b1500e0302144004200104015000108000d18104042e19035250700c154038884070340b040710141c607404401d80c0110b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 150050000 1250 150048750 150048763
    0x110316020d05091003020d0c0c0302010506041415040b03150f0606040608040311070902040621060302030604140309040905011d071d0c091909051e07030f2d0509 71
    0x1c00082e0050140000503d00304468865952541c41c0140c180707003480394a0000c880b2070003030708000702d030b20040341e081016028040d20340d00040c115010011110700440011100c1401030406110360086103d601c0540d603140d006482c5500040c08481d6a000003130310034004040161043c03c0c40c0c9400000062480c54214102c8003900c080c0e50301c081c640e483d9039400307446180010f40b4039403071400386040120342d490740e9102030401400300b82e5914155501d000202c038004540e051051900721300300503091001d13032400151150041c0d0b20001c15803000304909103180c114010940000d6009051041c800305202054100c881c0d074480c04003135070f00c4885e0420440da503603514a200780b40c208843c48049011110784181200e5100100c2c8007a18900140c150010300c0c0907030705c0e42091000644680092021100b140b084543c08440d0340c1040b60740300c96440151070803010091500f810540c64400740703100b01040343c1040c0309624102c800761040c40f2000c1e135400300b0710903907108242c80a881c140004107032001c00030b42d9 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 150051250 1250 150050000 150050023
    0x70302060702060c1c05120a0603030207051c0f060b0f30030d0204080f061b04030f080c0d030209120105060f01230309031306050705060a05060d0611031602 69
    0x105291800590078450281c101c0703a4060064061405e0800e10000c940244034a0303150305036115940c921a01d0001d50441802400e603143d21854682d09100182e0002404c0068401c100d980d019a102d0000c5421092081d4170001448100020092020002250014810800200c1d4803041001d2000103001c05c084a000281750a070700c010000801144000c00004c070480c0820068031f1600054160a40923640716900a142d654440b6045014040c2c085c410940c1103054400200c0c070300101c4460b0b003540e80c02540005800f01c10b5043c401030410101800300c8419050032002da07002505103640c080c1c02900b05c2c400c0c01d405001070852442002ca01071148038850000140034089081081004580704180360a05c1840700e20b10b0004105441810342c0a1441b98190780000c55035101005102c0104002c180e002c002440001e001c0000094000b081d1942e02100f900d50015090390341c0400100000905000034000c0b40c51700b81c003011100402e800443c482c0c0c0c0b0012450064a018840499840e59404c01d07 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 150052500 1250 150051250 150051259
    0x12030609020324040e0604050703122c0a0306090308060f0a05241b070609060c050c010c030311070f140c0607080702011211090306011707060c02030a060c1d03070302 73
    0x10611200f07040c401845840342c1e0302810006908a010106510306041903906494943c4045c400f0030801501c222922a6443c25103842c0e004100e46540c8a0340c0b02000740e0304000490302d01d035642c1040e6103d13040c1200046401c150b0900019002d820003604040302641c042d4000c0c208941a0a060304141c404a01100c6c070150943c4410b04c5203208114548260000d0014100010003d020848151030480d0030034203030b0b8402500045182c141d0103403188009520039018455022603110114402080480710f0311800e00b4079010010703061800b18028222146808034940c40400c490061150181104000a205000160030b801c1030400d12580c03211000c10003584150100300c540000346011010f001a5441030408031030020003012420207490344003410100000b008074001603140f40c01c0003080c4c010141c0c3d008044856010780d0004e5100c003407030b000305400d004044120004544040260b40e810613040002080a94910072005052000905680004150b0a00d0f006007030328020500c082160350080 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 150053750 1250 150052500 150052531
    0x9020a0312230706090809040213080c040c0801170705060c0d02011d1906020c0303040809090709050108160507050607020a050d1701120f0209070509010201150e0c25120306090203 79
    0x1920040a007688480843d03881c0014087c0110700c2d240c9001130f121000030300d03000c003000e036007040756951034000d8500c0b41078071603410810031101080d000b41066041d5030fa401281e0214120001005144c42c0f06540a40e400242c006a07100c110302c4c1c04a106013848140340c0c02446020211101e804421012404c0301495800a2503500b0100004050052216126040150034030032403403059070030b43c0c201b2201641e543c900040c508800e46040004540d021280c1e05108815500b000002464040b009240c8105c090221035104035a40c0107505890505034040d049541516110000035110a0b0000d02100d00d41700e5441c01859182c06000d201910311031045508446a107845222441d106242900f500c2c1c1c0e00c40d00c00d060300980c840031015445140c01da25500d5880591100082c211481070f00003c41d850640b880500001901d141c02da038100503240d140710f440d8907000b43c1d102203201d1100703120107a071880040321104000c0e508a134022a80195103040003199512011402680b000b122640700210609 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 150055000 1250 150053750 150053753
    0x30405030f0a050d0f1e0905040c1e08090a021e03070b0a2111030f01051c050c090a0e0a0c030c0605090102030d0f06081516020102090612090109020a03122307 70
    0xc4101c1d00100e03d00b03241c82a050306d11004405003055150b500f28000580d40e540c10b201c070341001c0c09a003070b81030440d19080e4116006034080c0d41c401340d866040c010401211310b000c070301c008038204000d9001940042c4240c0c0c1d48403406480d00008070b41020458002d0103155070005010b1084015202000c0d540d0f00c41c05001c4a150380f0055100b01c940405034921666043c0c003403440d02c16500690b00c41c0c01e020803013224a504200402600024002004601d5202d00e00500d002540124000102d110281c9051545480d40c4690380e0140081d840380384094070452201c0c1040c0b042c40031800781102d0103007441d499400d48440c412182d41c442c400304940982d00400c10010002c61550100c0741e0b14000c84000543e9684402c2d00c14145902425801a5580e0007418014110441d41011007c1d1440e400214036100462002c280349025220400c07000081c40700004403c0c4400390406000981d00410084066461349454170740d0401086000d030024086069041140318800c0020103801080d400050901c03505 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 150056250 1250 150055000 150055007
    0x1050301050c07110315010305010c0809030a05040e0c040b030f0703140f06100c0b15010e0303130e09010b030102071a060907080a021e07050d080c090609090621030405030f0a050d 79
    0x80d002c4e40342d003510840503468a580c40c0b524002d40a1442400086107500300d1080091050307034007404000742d036003040142000c1141c01208480c103c1c1c80001150449a40b140844000d030b000c2c580c00742d8080d08000081140c14084600098401c1c00d482d2000c000f03a03030009414a461400c120b84c3c40c541d112603903000c40c009103403e00b0100d01c444514905460311101aa42d010126101964220b8445200c503844204540e003081c903250840764198001c0d070800c1c54040b0340c0000411507104414900c2da00801185188400b034001080e1082c4c0a00250342d100c0003480c04a01c40300f00c0b085500d02a03100d1101040300c43c5071050485002d030010383d0390318459031140601280294000e0381c0c030301c1d0100070784800b10b505d205880c400350070620b000703201612006282110185c2101d03401400c1a43d040010803511480c0d6507440e05a401084055620078280d66880340130030b2040700116150307541c01c4040d01250508c9000000240309852081d0252201400102e8916640d085010402080f540041c0a2104203a10 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 150057500 1250 150056250 150056273
    0x90308030117010e0f0c0112020f181302040303050405010306051012020c0a0506010f03030201062907170327070b09060a03060e0903040e0112031d030321040b01050301050c07 77
    0x408400015484200c4e081d190b1505040c00d95511541d04441ea450043e50780211000d07609450951040d49000c0c1d10020000701c900ca481c139011180300d070340021000700e9124412100c1541503070040441d9125100d090151040d04148242400a400c041c4041024106109100d10802140c2c80d0036a8030040b060301c0501a4101c05071a0041e48640481e5002040c0704100ba10b0003048016000ca048500b1070600a003954006d400100303410010610000700101c0d082c1d2000b0350603081a18903601da410700d1070900001d0f20302c45450641900d0100078441800b0741030703090703441c42140240440d42c00d1403039190403a00d80d0070a2003240e0300641c0a000558207410200002d101a41c0d45181c00a0800d484110a024441c401d4511180c9944082024003100c01102081809000c4005440120154a80c2c1c000d0800c51401b10032050140301441d0100b50b0784040068600c1c1c014090800d0243c0c900701c000c00d85250a04640a440855005d000001c40d41818455503001d01c01c1560360324504141174941030800300 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 150058750 1250 150057500 150057539
    0x5061503072114010503010e0a050615011211090315060d020d0807020d140d0c080306012613020306010909020603010b0f0c060c180109051f02030c010c020f0d0903080301 75
    0x211400c0315041c9407000d0320038110f41102068800645506040505003114800381035108a90301001d030b5140800e000165655011a4400901141c50340000040311540d50341e1035915880d03800d05010849903800d100240c25032a405408484500002404560040301d040d5011a0403070300c0305403258090308080120030352807809203524502c5e02040f5408161000d4806a0540e04904ac180d44002110014044030411404038035005d500c0c0d040d0368988250702c4c40041c0c0b030141404400104580c000c405104070540001c80d801c5448602c6ca4942d1003800742206481040380320740120000400c881c1554030503880e10380c1d0041c05890440c0c0c2460000d1030254003035038007400588000e1115603164241000503900c03a1200f0211143c54294911701100a4000c0e148640d062040c0000c2c14407076519100c440a0085070300c60806950f060520005a085106814004509500f00b0040d4201c0b5070300052540b0b6807030303210400c85150a02140c03040740c26240700d020040440328204010450b42094050010030340b07 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 150060000 1250 150058750 150058787
    0x30703032a0b161d06030a051f08030904230703021e130510030e0d030203070311221a040302060901031d0106050307081516140d0f0506150307 63
    0x2500584440c500c551040f96160003110f005921039507203d07400708048450f911007829400d56031504c140000c0d821700000b4505400e8958910008005191500000c0d4030712040c5070765200103540305d070005a106e0348854081030080e424036410b09405908403440803d0000b2181591205813511303401140030703502131444800e114240c040d0395051182d02030020010000e00112041207a40380800303004018410301300004c107151400f100080d20030307000300d10203080541ea0701c0c0043e903a59550100b5001072056180511084030085502010a203441103202c0d00c502144030421000783c1d403807688058048003405607400140040c8002c00040c10824041c004000c01418007140e8200d0340c50814900f428030701e401c4107213a91207250404c03030380c1001e00144000c1d080d6000035200313172051034444030001c91020701a41044200165424400c600c41c030400650301e2002401140d98015960381980070380759180c0041c0c640b42c0b40c00045215858034904130011030207200111400d607950000203840003c0d07051a54040c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 150061250 1250 150060000 150060077
    0x10311031608060115030204030206120a110c060406050a0b06040e0712020d090212060615031308070c031403161113020418110304020604170102090a09140603070303 73
    0x44020202159010b07081c108010f1080d58034001c010f0784641001500d10040c11310400040c005611124102c6003c04071018510f05151a40d500e0f42006051500e100d019038800400d4807050700a0200b001030249015840500c0241c8401c0e06840846130350900c0305500100400040001c108a40c4800d907110405c1d081c10240c1941d42903a070360aa82c0450500d005d107a070781d47d07440030442c5004003910f6819851034004002d40c0c85c11101050b00303c0d1324245980c2007620080300082c0740c20383c01240202d41a034400c00d0035490750200c1c03409105103540b038041100c0511a03001e044416400000940d5496510b80030500c031b080741e00d034841800020b103480e40b041c4c110001c208000d49004440c0010401414180e107080391100151000000b160700710070b02103e030100d08005000c0580c1d41c0d4010340d800e0b2510f00103401103080151a130140240700d0200c0d580c3e00098a400300013411016944110013111700e41d1142c030010f0b981c1c001015240c56180c00000c000c40c0e149111601c141c001d24603001c20244112805401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 150062500 1250 150061250 150061273
    0x140f1305190b04032d0507020406080102040303030624120207050a052a01020309030706030b0604030c0909030306210b09030c06010e100515070204110706020705071e0302010801031103 81
    0x111044403070801d854440b410001e010030507034172441001c17141c480000d02290704001030f0480d03001e0a110b180c404040003004074104095658980c0000010880c1c1c00c000c540d11596403030701901503d0f1030310a1210f1503038902c40c0051184108150490780d030180f9a00c1c14008450001003d0080d000240252864403a21100300b0020340c08200850305040080d511100d0385010944205a0341c2c048115941150021b00c480700c2d29440029529058a4403401c000c2840c0c02e0413404280c0c01d0046910260040124074000601b244040e880b414045020b90303402d0203c0344c0c40b00d800d6000c0300f50b1440003c00d8031241d26104c001050008071116042581c05003541c0c178022002e50014034141080e000f6043c02c441903407c0c026199490013150000705015030340102c00300341078443ca0807140074000c80640034585810340000c22120420440c1ea060742e00c200d0864482d812400e02c1b6030344038206d008030950f9000c580c0b0344919420102d2104021254141e42e2000300385c0c29a0b40701c0002403020341010303070141b00e00d4a0101 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 150063750 1250 150062500 150062533
    0x30a180203010e0a05070602010c02030702101116030201020c06040302130903050409110c0c090705030406051b0c010b0901060810060e030a08070317070513060503040c0b040602030d140f1305 84
    0x2c140f00d02c0d40001e00140c1c400703003010350408400b030b03102e103003075a141c00070b0030440700e40103c117072002640c049602c64a1100c03542d01c1503510840300001074070366028100e007088001c00001d19207400d41e4008e034219080701915505221035031049000c00b03948803074220020b030381d480344903080050000d2103460106d0805139200701183c03c0d01e10f035082e00f800e080d50220351120480001c1010761600c0c00c0440b4044564241204c019000d40f0001d040604065190301c00110100c4154540c44481010319200700e80d54580c0f4007140e4000c10b500705400f440740d00090000655140704290080c02179502c1d03079010307622501e03282e4251502d0810b0381516425010300085440402e00b6603002d040c245029454803034400102c0b02d040c480c0b00000400400c24800213020500c02c5c0d00c00043c0e550309840c0503081c201e503030303446504103d420030a280d405454010000640420011741c0070011b0101548641020f02c5040e821281034941050100c88244064021000203042e803400440342c0f4001600840a0382c4500c428109480c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 150065000 1250 150063750 150063761
    0xf0a170109062306120a14010605030702100b031902130e0d02191e030e0429030102041505031b0c070608070c0506040b070207080708010906060b0f030a18020301 71
    0x8402590384408005440c0b449070f1002d0900b80601801c0124003015000414030b00542d01c8480800440400207040207405a000800b0a0071a00000b5100e41c0d58080090203503004031015070044c0540c1c10b00300503000d000c0c040c0d8000b5520080244c000420f0406035611800c0719140c0c180da100c1ca810180c00c03401056846070300b040004680117803040110300c42019280104554140b403000584032002c02c003090b0040342841c5500003240c1c180b602200c140c10304640c9604030302e41c0c19a03c03a29041039a01c5403440b425056000b81e0548503101c100c8050042014200c4c0038521449952156040307103144400d204100441d0f105035000ca000b0030406a07119041c145400005049419501002e001e001650700942c18960100e003900e0000042280356403040e8035088003500c001c00f0040448040303030b0068000d11520016004440844079000e5441c40d025003c0c1c140d51109442061070140d02250304400308088494440b0780540191840c1c403000c0140d8020101c06503814280380f070178101040103076400c0c0243c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 150066250 1250 150065000 150065009
    0x306090f09030305010e0106090323150103050705060a08150301060f1409010504090f03030e030c0f21040605040e0402031c120f0b03100e030c120406170c0f0a1701 72
    0x51280030740c41c01030121501a0030165420409400410540e50700030019001d5951050701100e1940b5852011150307281c6955042051f4044c1c41740f03502c1c0701d505040406040b00c3c0140200da40480d52031050014502c540160303940042e03100c81c002110340d049280358041c11302c0064000141e071540e03060344c44181d00480d00000d00044510f64400303801c0c94020a050b001d000700700c500300848800c540e6020b040c0c054654001702419207030034849900c14400d205171002c003d189029a846010341400c25515a140c034070011030f00a00c410703400c0b05007680403004d071410327034405464282ca080d06044d54a214480010402c07a41442054414002c03460701c43d5246001c2c2d4120f45440d081d0765110340d4041d01790340c2d0b2018000201e5150640591150380c0000d50000d0311029940b00140350b024003c2e04600710320444440038010310030700c00041c00320401e04c001402115103595075450203482d40521084181700c1a01c000c0c0c880b0b40140100303500c1c031030b0340d04c014851001239040c51000105250800010940242d20 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 150067500 1250 150066250 150066281
    0xf030301090605040209010e010f0306090e0a060f0b0102060f0c04030503070b2205060613020f03070c120e090720100501060311090a03081308010908031009050601140307030609 78
    0x10401441c20b80201405008120380c00d40c00d184c0d07000c00082142d1403c1710401e04100d51241218001c42c002da0064002c0c04440000340310000f95190083e5a035200004212051440d000e032402251000d0301c070341c56110398140d01a04040d02d91000c10751001c0c0018240305440d4100b04000030000e8030070001808142d1083d00ca00c00a4179109807414002001800503030300004000e2515000210041110340d8090380480b0200d4023070b07064102007002030180c13034a52414107800200b808141504070941c1510716201c4c000681900c51313100402c84110701120011a0400c1c0100d0219a1250040603841101c00100310601c20b005441001e2a10341131400e0b5103400701c240d4500041c460701e945401003800da4102804864617003401080450b0011400744400b030260f07100400c01841d04628084040000c20180c0001e000010890503d03090a034026100c07100341021291000034401440c1c01a284620b42c140c41e08008040480701400c080c0d80011310142c101652413a02084902152140210200c000390 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 150068750 1250 150067500 150067507
    0xf07060e030d0f050307021204030c05090c07050a0f0f062a0507031e0201090503210a0c0e0f011806090812090a060311090d0308060a0509070e0d0f050f03 68
    0x15014042103004910980690450480d000c0500d802229910203010305240180c1d40e40c5c0c92200407410941030128061000700e00060010a0100400102c1e050301c0080340c0080d0503494042c85e06580d031244410040c81a0840c003800b00104101c903032031000c410f01420611000c48101c1d601c1c04112841c0100d0305036900c10b4400038922035140c03c0d403c1c00881d10203081c801d1910b130785501c025200c4203000001d448810013040c0b18020b031a100303401c13518102d94044200c070303110419a02c1012007001044110000c0001c2c07500045c83c88440b0340034000c800802a29410010b841040503c800400715400e05418032a2000d034070040c01c40d6124212000b01960b0350303441c0a550030b1850507810040c00480340c950700d050501489481d6513422807001e00b11181410002103821030410514011f028401000d54007552508521050580050081b8450710040392840d0007a41c440040010300241a2907078400070340b6078030384220302d42000d00d02c507040780740590844810b02400d5a01e00d0710f0300c58003807841d210360741010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 150070000 1250 150068750 150068759
    0x50703020f030c0307110d090915090c080702120a080a0504020d0b07050702030606040516201903030b030a03020615030f0f010207150501060c291510091208030907080f07 75
    0x200d0240758201041b005001c442542003402041003046003c0c4001f8070342d940c60001c0d405540ba14640d001846111003d00c0070b07110000d006494102c04507a080003500828a069001e03020040c11030b07803001110b41b60400c440e100d844e100c00050000a004070b803c01c01d810381202c0450760010816100d1541fa554140d5a40c1461041c1400e04a000c2c000a0155003000107101c0340000982030152640c020b4540314400d04450060580c900a010340000f0307907402680ca0381d110b900c03001a154140c01c1e0280d00c0074400200001c2c00d041e640c82c1c01d86c20250040e0480d4010611a0030504c01c60303c801c000040481e0100c621040381641010240d08541d100baa50000e440810400d549542c10b411038951802040158075010380a000e80348108001440840345515402c6004000e0445581e100e0701c446501c05580b6040c8580518520404515480790b0012003618070500c2c40f034041e0009488505900e103051740c0c2c2c103644102c1c1c0342e040900030f407409000c1e00e180800c4a00e01003204e250141d07803030350041102030b141 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 150071250 1250 150070000 150070007
    0xa080a110d0911040c0309080d021e0c0d1e0f030209010c0b0f07030501080a0308040605040305070b0f091006080c040902010215070c02210a0f03090f0602010501180519050703020f030c0307 83
    0xa145c10744052608081a55001c54110401da514110402e4002340e40c0d0b10322815484103c044042826a000c42e011035001c90380040000e517601c000c40140c5410a02c0012154540c0348160302d01225800540061a501401c070310035005055041c0040c107140c0b420300c1d030b190b40382c5a03240006c60706100700e0141c2500300001d080d498002c1c1d500402c09600680054070752624020181c1800400180c150b41d10381002c2810148100100c0e10125006070307075040c00c2c0c20081040c0002d0300c41a2260a43c0e0310070386007240c980035428814403007100c00000080140c02c0083d0140b00140400742016815405800000a01e00381c1402815105031569501c2c0280000203104110b00781380100040700c0039400310300000b98040000207074280700640110440450030043d240845c0c41100c0c3da003181900c039100800018003560150400c1e41079440c80c0c5501c0c0b14503070035121240300300c0d9421107100d00280f28000d1b41000d140416031010780c04c2407543c5805441c058a5450100b00d903030041d079882c43d80c13840000401411950 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 150072500 1250 150071250 150071261
    0x70e031617061305070b130b040b091002010c02070303080a1113080d0903030e0603090c0a0b0d061e030f060b0604060e030c010e010518131109010f050a080a110d091104 74
    0xc110398030b800b46400c1500d401750744171090b0040c8000004005a081152900c0491110003010720006660741c880d200c001c8120907400444005000300c0d0300c401c1d008038242c010b01404c19880701e60344c010074900c0c2c07070b5803406c82d5418405048003000c0c0342d468a050383c0d407240d0304004144041644558154151034510380a10700408001807000b0042e60910900000340c0c44003017030101c01c1c801c03110302d80c49444460401d03003000110381445501594040001072844608005080c041d151901d040010994030610880c0d0110748002000d11120305401c14800660028100c801d0140280c800080469488001c5001644103400660224580b07003210400c034901003006006051003840d1441950b000d40780040c003503000750202040d501c3d00160354000305495110050900011a500501807408140c0c01c03c0001e6014001003030000d1720100c55101c2d484d004104644d10001c50341e95004071642c0d4181c2c4000207000300242034803441d07410040c100649001e4060085050302074000a010002d40c401040304482 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 150073750 1250 150072500 150072511
    0xc090d0c29070c0509070203160c1a070f0b1008070816080d0c1104090c0f05120a030e0d06090f030206100f0b07080309070512011407080c03070e03161706 68
    0x204200720702c0003030381c075540c6042103813010764544880f600c2d80d0b44240e0460050606020714000441000c2050211101001c000c4403480542c90b188100107a6040025120b0500054455030304010000005144000800e601400942e50904150385131180207040c0100b1780d0010b03000e90300908160b200034025084841c01809a9001000e500302e1818019104864102000e442c40011b1810071486886a8102200841d400000c0303048403a1151280c00800d031040c060280a0484501d040307201d440b00140d10300800d0f4258460505480a900070081001c40041d0203c03800b03916580781c2400143c8041e10a5801071103600a40413030f03d40440140441580e1764441d0004203020041004807200620840f080960000c900c0c03135880d42c079100c402d0714100d01d81d44903a40180c203601818820301810350000100324044101c54441e921281d50442d2001d000b9100c841c40020104045000309014003640303292807a000d002d9030342e0214a035010680c1d01d4042d80c4810300a41d0b02040760101301c0c03018845290301c50b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 150075000 1250 150073750 150073829
    0x309140607020321040f0b07050f0604030c0b041a0408120906060109030611040e09030a0f080402010801050f0109030b07030c03240b0a1b0609030f0908060c090d0c 72
    0x1881c15000207030341c0c0484076400715100c2d2100e82084113514080c01160081c0c800010145a81581c5040301c81c00c5601045065941c0d004030303072151f42411804030b8047d0081d50956210710800b221a00c510032894800f070404c641c0e40203001410b1001c540034001a038032540c020303004581c69540c4051500c02c0c0000042510b00180c00c2002040103582c1c00c021500c0070341c1d400c07500025075805900d02d191003d101c0c80e0003e009032a040c4080001104000008100e0010300780d54040c03c85e600e058054515040a17200240802c050380014403c90400d10008a1034200516150003440e40d07079216071100c0e50068500c540002d03144c1030386c01c03013090701801004804103070b00701c0300b41d1940211162401400c49601803581101c04c0042c55000480c490747d2056041003844400c06040d020500e040c0d0300074203440d1811800b0900c9861070044c2c250040b22600c048401400141c0764903079403880545c0c01640802e10700e560246440ba440d001042400f1400b0300940051100300410503402200d180540c1226036140000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 150076250 1250 150075000 150075007
    0x40501050604090e0c090f0402011202090906060c19030305090d021207081e0313060c03150e190f230c12061206150a090c080606090105041203091406 66
    0x5898071001c980c00c80c0e00122000802e000c4001142d81401c0c0c92444080d0701140040900a200f21240d04143c0518402d8a40141198680d4054400e90054455850340301d11050001035850500794010000d84040c04241c810304d01d1000f00c981c076a40320101056001a40d07804c1004030350b000030415900111101d00062089152541d50710080d81300d01400208140c1010500030210b8825568203003000d044050b1032074a034649080b000b101c99441802c19156903052010401c81d260092140e99010350f07601c0d01001c56036082032056074100e00e0141c4511150707102c402115802c03440c03520545c5803581d04888042082c0680b800d200814900c0340e032070b41c080144103506100c002e030200030072550f24151103000c901c000c0d9561f000042d0070401d40f46460b4818000c20041000b0395003035065141c5040411241c0300342c43e68844041800b02c600e414080004109801301181c02c030b1404002404505205240c00307407401d600c5103503c8687d1007038450b08501080341c09070248207a40707000c0b455800306042550380ca8203 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 150077500 1250 150076250 150076259
    0xc0f010605030c010912060207050a0f0510050f04081e0903010603060b09010801051e0705091806100e240c150106021b0f060c010f020423030106080c010503070e0a030c03020f040501 80
    0x6851b0303d50300028061079000508104010301803004802c000d40200001e0b40705601d90504548407400344840080d407914080000780600008003c0c94012604003c0450400304d1090817140001c030503106940214809001168a03940d00340541805180300380c1012652a020900388800c80c081a0403610040e4106020011088030b0000030409000c0081125201c40e00c90100588407427055200c0150882880c40707201e01102e07140d58201d801a0400e640505030140d40110880d204070800c3c1100740c1c040c4a070307007081070248210b00035185002000f20700ca62030008420f18251070102a60b0075202000c0c450801005960780600210400310a1190414a10594000042d20b5880808006413081e580802c80c2968a8400d6102c0700c46803040840c215030351910341c0030480d08000464420407484801e00504006803c0c1801400100c6502c080100f000c3c02c1005c0054410303810040a00041140e880d85100242c5e032040140030086000d1840d05610741d0031401400344a400c901221801941090300401 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 150078750 1250 150077500 150077519
    0x5190b09070503061f05060d0506030c04050606090105131e0305100b0f01030504030309060f02091c050a0609030c0510020d0608150a2f0c060708010e0103030f050c0f010605030c0109 80
    0xd60051858403446080d00a2a00b20384100c442031b00019089840800c200102010503031025000321011001c48104d21300740010401541e0007104c203180c200e80d06002035205540290090401c01c06292107401415468040020301c40414089100c3c60603032081080040c0501801401100f08001c0024040e40691002003880a2244001c83c3e040540d144001010302d803003a400f10a14542c05107040c003500d640e032010017004c1d4202019541c81040c40d4600002016000040c40584540c484054105141c99072980402032481c0032064040c0011804803000007034041c03058140160103443c0058540c451104105c04036262a000340c14954040d03011b05400c0c00380010919844894142c02044075840850300d0705401c48210400d0300b0550100d21600e241b103841401401c00800790f403089600f01e030b40781c2400b103e488030203218242c8129610001840400e1180d000c000446082d800d025142c11240d03072805142507802c142e0721034203954801040c800c40c602400b184410701030902c1e141c0360850078a0f0421 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 150080000 1250 150078750 150078763
    0x110a140105070c0504090507061b020d0b040203120c010c1404050315071b05070e070e061e0f180f01030e030d0e01110c071a0a080705130305190b09070503 68
    0x681480300c0031031102c080000410540c005404041d00500100319507141075562455207000340400302e003c80e003a01c0300d441e282111511501350001d024030a00621526500082200030704140d0701801101044000c0001e400000c0c85010034a4000048640d102c0e90014100811050040303a0300078204001c00561ba000900007080c01400d074010301060b128000d0998181e03080c1e104220540380002d40e034206221010803400100c0311a03080006480d51141811900c03500391000060b0700480c240f1040d49c104481071001001c00c03032031b0040549400300d80102284190003018081c5072001c81c500c108c80081c03d011409005541007800d0070b1104e0012841019264010903d110003c0c0d82c1d2514040d0305200c0035004481f0f4401640c0c02c5641d41e48802a06617141c50b05401000780010800b0500b595800081d03085624207030407595104202d4503031000c121001d40c0321069100842044c50030200c08104280010024020340120030b05281030305140003c803603000148420f000390071140c0104243e85021440 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 150081250 1250 150080000 150080039
    0xf011406040506040e0708100e030a0c0f170414040b03060c16020f100807090f060c02060f0909070302030106020d170105090601170108010203040c090b01140c100f09110a 75
    0x4a503c0c3d4034040032400600035030101410501c10300b04000350400300402c0070409940101c1040c011200ca800005a403480341118030800038106404080200315600300070094144a0313585908004500c0c00e103d91250010303081491038408811419120707180c18414088442d000790040c120925001080c42c110b401108001868a1066800f0000715500c4045038081ca142c0180511454440003100820b9010110b03140c0d40411004c1c0004140c00b244030141d101121001d07914101002440c0c0d090003250741240800a074080d00501c448142c1d03030380c5c01c40c0d003a00c074804a5400681b070798900030000380303040b2805904005001100704a419001007600c4410705407002074030300290984034100102c54101048400e010912044000441c00d08019002036009a00036503d2140e01074548001c0b00c12a24034140d8035020808140c1c0c02011001da0300060102c00e50f17020306452900000400683c26143c0c02d154030004e0039540d075840d004101c0c0c0e50400320340000065641a081e40e0411000307118a00c85d0b4880c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 150082500 1250 150081250 150081259
    0x9100e0a021513050402030f04050c010513031b0803071110050f030a090f02120a030206070f05160c09111b030702010804140a06060618081902040b0a0e040c03050f011406 75
    0x9100306258020f854090051030b0241c402c544d240b8042107402c001c80760642c1c08941900a807814440a50b11136000e4540031108240b145250528650b9826060341c1c06030303e205c0700400c032284000703181c3c40240045c1451a000e00780407100f02444004008541070b41d1943c950511138144146e1400b0b400620035242e0100d1860070001d428221400e1011814455000c0294440c6d04020300600041c1c003c6042c07507646200c4d40884100307031a41031050302c1500f8080c00500000704144a900039038041d049207800303c5801840610314080d25a070b10340d020b030f644114100b02200300c0000e0803500381c56400000748201829002440c00d04034241d0000f0048039024001501c810764078000001680d00074040400740710f034044d6017000030940e2400003600c084c0c4050050248070796002d50001d030240c1c000c0ba0a10f110795031300008110158080e82000000d00d000000d4517049058201d01184402145a101d03016500841c08140024914a0514901b54042c0c6501c02c5a90600482103000304043c001c072600102c00300c5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 150083750 1250 150082500 150082507
    0x30310080d050f0702030c0604170705010f0e010c020d020301290f01050a36030506150a1811040605040f080a0201080109021602090f060a050a051003021b030309100e0a0215 76
    0x2450940141595a2300003c0060300140d0748200344c00c518180204074041d218419a02d00041d109030034070500326004143c140219a070300e07612072100c030343d0300760f100a01d610710990054021900b103413045074503540000e91800704180f040e140c2404060811204480c0c40040c2030136800000c105004060051040c002c803401100c0e902079955500210f8a181107a019120075104200f00c070b1110041d1105449502548001c1140034078103400341c0e049000c010b800c003040149070282450700c02050f48841d07440c05070f0719a06202481420300041009201d19509c031078032541803d501030789296030303980110001c1e4410385100700141d03000380800d81115100c46005031a102d40c4c0d00b40100c0c68207080e20080d804003a1004004540268004040c029402654000351454403841880411250b602032942d00041981c2e04044640c0300c1d4006021111804021101c52144018041e2440e0003c0e14842c40641050103d034541003841d10900c60f94840710310091420ba00c01d500450b622010ba80d2848141c41d4002 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 150085000 1250 150083750 150083753
    0x90b04030c06030e07080a0803010e13020f0f03010e1b01020717060a2c01091e0b010e0a0603050601030f021008060d060c0509030304090902031501081506011808030310080d050f07 79
    0x17846031100a008480651308100c0e864030b0170b507c880e8402d0290248880180c008540382e2003c518044040f15400707043e031031380c110740c110403c80c1d10301c0d04603009035040d0341303c2061400048050042003d0846002d60350041c0d000c8110019013841041d4004000110100f07101315400d03480017170002c0d08000c10503c005822000b10785440b41c80c0580080c00c42c1c1182c0c0e1150b2543e0907440551107078071042d028425098620318100c02031192502210b0020700b8903d05880107110003034424100a4000907003402c0011030b035036039913185070a10009a005585a4102c1d100a0003036003003500b038500c007105e40ca141c0804546070480000e464040107540c0078040603994200805018040d20844d800000000d04907612142e40f500768202410b280c04080b4042e0061300600c0f41c80e0510140c946043c0c0300c0f0700024040101c800c00d01a00c1c0c4c0c620040250f03042007410301c0280d40c050341c60580003020700901c01c05595a444e00c00c000003120300d00350b800031002e54402d85030b44178116404030a41d20500f0a64008a980741042d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 150086250 1250 150085000 150085003
    0xf150109031205090120070b030619030b07030b040c0918090c27020414090903070c061d0108070206070534120905010c0f0204020c10050106090b04030c06030e 70
    0x103400c02480301d0800000b0581e0160010064060034409036a00002c00c510542d40f4501d1801050041076103a10004081c4444d03001e4101540c0d0043c0050000e410b26001810402c3c49001c90382d000351910341c2100140041c2e81d07030500070001900001c2e1410300072411040340c000c0907444140700e8400303444201042001a41c04c0c9421299032560401c0f0201a41a01d415888509400c0006a41401e49410b0300e0b20b82c000b05540240d40494100740d00601b0400c4019090148540e0010705201040c00200000030018031140b10000c00341c101665003020203804032075060712178407015044078144103030b00c030412445c141e0005000382d220b84d086c40c045407030b038840101014603c04100d82075031030120600d218a45c0f90421426200d03980f401503110120320300b0712400903140b44189000345800111410759020210342c0491b00c801c902ca01c040d000516100c41015201e0130005060440c050103031b1124010022290700c90b098102410903110854074152440d03403100140101c030312170758003856212100300e481500d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 150087500 1250 150086250 150086267
    0x90601031d070807091a0f0105041d010306180f02060a0507020d080c1c020606012a0b060901060f120509120406080403080a05010501020c0d020a0506120a140f1501 72
    0x107410032001d071600030102086440760402e0041da407003840b860b900082e03094401d010350f828550071304262110190307070b079000c0c801c509070401801c03818440c04002c0019008050bc0f0360300c0d150f99144001c02d000d5415882c0c03c80c207448044600e40840250b0121260119035080703855150f4a40c112015569844240d005844a015490010b076124001c002d501e800e00020720010f04c01181030f01d056038500c9030310303000680e0300c0f00020f035080005910080003d88554000d2070800d0842c04004821a9150f40380c281d030b272854002490080302c007090340500340300c0766040c0400c016001d0030881c02c0880b00c0500d5410010648410031000b01000c1c0e4a40e00841d41e4003000f4042c5441c0d00d105902c01d650746641b2048003402c012000c1d41c1c220005958580040e10300d0b4124400d60381603030300507805402d19080410400160000c0350704103991100d000350000849950313a1005100c59400d001c049182440c01850f0841111420105003440d4030100c8200320414044039009684202501110103003403202d03d004030791001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 150088750 1250 150087500 150087521
    0x30a0c09080f060108062d13080c0a0507050a290c030a050c06070f0909050711070602010c020c03010207020f190306050406060305010b0d03021b0102030c010c0305091b0f09060103 79
    0x74201d6642e9401c1000c10a14180c40d00788046611a4444001d10303541c594980c601031804a655182030700038500382840494020f85d008041050410140c0ca035594a0b5004200c6000103034804900c0340100f110600000b001010200d0742510801e10300320901c00c0e00255900c49580400700c921440c1d40020601042c0c6510b60b1404040b00c0d1582000d50003c1e01a0340003500c508118416000000d8405219680101d541407860352021440c030b15010111020348805803601e801c1c0709141c2c550103403180e41048000000d1010350300228030b540344940042c0c00c244203140c111b030081e40108100c0303001da207480e030140000483c2074900389000720503410203e00c0040c06400c010581410503040c0800d22580d90842c00559000e10300801030010010100704a044208074001d0268128102070000100c103031501c1d1100e00010b0050b01d162a0b080d014203400c4910410035000031a5880080c0710702c05100f0092000e11082d0301d900c2642c40d052000000d59407121030302519200d07000c25400a4040d074400c1c1c02c04c6005a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 150090000 1250 150088750 150088753
    0x901090308030c040315021c020304150519140c0712090801060303230703080a0506040b0a090c0207080d021903030f05190f02090d0627061a060f030a0c0908 69
    0x20305100b0100c4916031310a10050794050041e601107110a2068402c481c4900000420003118580c2524040c0180d00010026690741c5000b40940788451002c0c06624454142d81030507000c801340035222603086904c10440350049070569410016803446134012910116000a2005091211280c0c2110b1204260b0001e03001542000b100004041d0000c950041c650003070904220b0202c010340b00d000c01c50143d0003020740024156400306513450410351085c1e800450203000407510110000129041001540c040b041142d60f804910040e2a414003800c400703170883c3c601801c1d403500c0710880290303101100981e5452026409000d5402c05000340d2025040f074801c032105026920709011a403d206058501d10f00b40c0c9801c2042d01c100551880c802ca44c903030440106900c003101080c1e25800007c1036a4008400750040041540320000002c8424002d0390b0702c202c4021034241f185181041c1031810303d0000c107000d01400e01210b0441000071007941c1c0c0c0506081c81c001200c00301c14078100e52801c043d900001c9907 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 150091250 1250 150090000 150090007
    0xa02090307122a080d0e0d06050603030d0914010509060f041202070f0b19020d05071704090e03030a0e030403020a06030b040f020a0513120f030f17010e01290409020901090308 77
    0x41401c3c2d41000307011250710340240d58105034034500c1503c40c24099062181d1000480300907200282c5107130b11940e00074074040c0c00c4900f0443c142c40c645088912281082e030300c40c11079030100000c050003402510751091000010b80341a080003940c42c599880050401496442d0310300a0310b01c020710070040b61000307140c80c10b0750f91800b941e030392551400d503885030640404042c0c00c2024149250300020707104181c9034455031050700e4034a140d200c0d084503610604c2d4140312441c00f0000000c3c0c2a14900401030902d903540d010b903a4038141032182c00110707000203005100b00d420a100400150740c50030001021900103080100d406054200001c0c01040800f030828030803440415100d8010703034004e02401e00e0902a20100c04001e4860703203107021403541607100400c1c1a605102c9403000910881a80003c0c02c1281030114019010840341031024030260400c1640e100b410004002c880d035801d03882141540c5110003100520307681c03821002c0c0da2103140650f410340750f0001090101d03071b4421a0203500075074201442d02c2d203 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 150092500 1250 150091250 150091313
    0x3060510050928050f180d020c12010b090c040e010e01030302280209040c0603241710051603050105010512040b1b0304050706030b0315060904031101140702060a0209030712 76
    0x10041c105441ba000154212040c0d003100ea00001444000308a058004240c10703900c4c9400c220703050342d06001d00340707943d500c4040c2982d098541070354082c0990700034464a901c4900702040001c458005070720115191040c40300400100f9004580b500ba12841130155285600360300503140d4a8020f1210300940042c210300400050000351210b100070b03510203036030034030412075034400481100c250035083c00811000d0300b4040000415011401504c41954015994428501c85229045580464005944103c4050b0101003140d0610841d40500001d00b05281001504c0c41004d10b0400b00401c0102180d107518040b4845985181c0442c1011014016180d580d14007858035030345441c1e0920481011a050180c00b44c40da14010801d040311020116603440e49130341d030a080080e0050090011341c140f0403125800e40003e6004c1c0101d03c4030410484190300c080c02d090380e0007842c080c8000c2ca01502c583c41440011019038005c82e0b003030211100702c5500119102d003400c201e904003c881042c13504202d4410b01c182d1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 150093750 1250 150092500 150092521
    0x60405130f0b07180302010905040c110709091a0c090f0406050d080c060c0901051207140403060c17130206070812040b15030105010b03060111010b0301020f040306051005092805 78
    0x1845841c5942c4c1d6498581081e10003400410b5550000074081000c5090030f000d94107155205072090b0041e8030b00301c58030440110074142081402e8102110303084d100c2c007944007070050042405140074182c00c240044c42ca80114006024010700640520840401c442626151b590750004c00c09000d0092111410782c1d01454a0a183d034803414021405004101c000343d00c0490440c00d6494118060f1601c3c1c1c40c11040194030310300c10b80b0003403201c01071040380c000c0103444444d54406800a584a114001919410301c030020b09441d10300da84801d000d0401c4010812081802410480300340c0d41510919200d41e81f52070641250700407000c1d400e910031740d01000c2005000258405602400d00450111152140d500c01d00d82a10800d0042d0003502c0c1040001c16890b500c01d0340070040540c14580001444d4085800190999005510200f20104007041c00d2003808014404d080d00502040300d0151114a4180802c0c00040010454403070951400c1d1025496413213a03480c0c00204010724404c02242c45c0050218 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 150095000 1250 150093750 150093773
    0xc0f170d1a0402030106020a0f050f0313080606092502030d09060c080f04081e22060f0201020c0604030f090317120703020a02070b030c0706020c03070201020c0d0803060405130f 78
    0x285401001c00c07442454034142403003128180d50159000d441c000c28281c9030541ca00381c0540084032207105920034489108400d0025005041100d00d0400b4203601d04081c081c50804c0103492548110300303840a000108070b000f4a031035804a8041c40d01a512407001c0b0041c0e0842c0204405011080d00342000e44003048020b80c02031803010003a0b00c1b0552a03856100d41d10303c022000f1240141070314020008059292040220408129114100713146401071103400d0301d24001c20301020302e4982c1c1f410381c0c003030210715040079a104d1a61900c0c070086041140e500d14980d07503288040d0010b000d0120a410f00942a48a59541406545c0064082928034003404084c40310741e01c258443c581040c951008544118481e00803070b4100720459008001e0380341000361050065001921801d0b820300100f20400000c3e08034005000000d090001441c0c9440c22400060f082441c02c6003d10320840d1b0803000790000962071015680c000d60107071000182955034903040e501680c4001c401407c1c004000c0034a4007004800c40c0e90 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 150096250 1250 150095000 150095021
    0xc040902040b04090e031e0d020403021305060f060a050d0c02010902060a05040e010512030a0806030f0a0302011a03070b0a0c0204110c0a0c050603011811121f060503070c0f170d 78
    0x100701c03003104c60240341d48900411000001d02052840c0c4800403e001fa009420313800c030526401490190f41754001588265078803440b00203152140e080108038504040d0401001d4000d440151508141c44030080052085086840002e40e6902403070820a200354051031030642e01a003c107035a0704050201401c01e0b00584104100b12101c1400803405092203da20850494410001c50074000b50440c02c5c0c0d11032030000c201d6a0188228041090343c1c0c0803c008500a00c1e000350000182089912003104052108203c002c0c0241d0280c4010003841d41030101716003000c0c019152404281da0a84000b5010b01030040ba2240340b038401140311480c54201054421a161191a0b203000083e42c5100740806400b09108100854202c02c40150038040290003100d4542241c1c00d115140291482c07100304000700c203440707203007210519403075050700700300003418500140025081440c114600744400a01d00300e2410b500030550131038200803c0800400c9488402494000f00c01183c072070131400d007480d0040410404 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 150097500 1250 150096250 150096269
    0x608040b010909020a09050613060909020a0e060603070c05030c011406040507170a0906020903030703021507050301151b060c03020a030f180605040218090a12020607170c040902040b04 81
    0xd602c0c84144144425694003808104038035141120000c0104002800030750000d1002d001079020716010b10409028290b0b240c4000b4059041d070043c090705484d0354014440703900013142880050740e1801c0983e640300500707207450810901c0c036180150550081080c142007960030a401030b44000c0701c00034542d210301811b0354208156610761600302d58541d240d1b1190644052106c010921401c025004107845502404026103080c118801203451a4070890003580160040c502c6851040f403201c0760550003280510740075085505140403a0a83c0450100880a0240e4058414501a042084a00790307540281e8100094207845102030041e40c41a01c50500191a201c006101080c0c94801c10400e099070104620700c2d005c0ca80c1e1542c1c0144006003080e81d201c8628501d4103010813201448a1203203000b400030304641650361038030001d5050041c180d5003d41d001001001040b65201c056422140030510000d0f01039241c0c40d00d0b6003800c5c411500089903860002401080a203c142e0040c012151307400ea = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 150098750 1250 150097500 150097523
    0xf0f06050a0b030a020a17070503100204030203060c0715020a1407050a030906051c020f0c031606050a020403120804020109090608330a0e150106030e0d0f120207050703020a060804 79
    0x40c03c160b100c00c01070380001c3d03014290002c107001700c401c0004464008840c04045488140d155400070345841c81da107051000043d0006000e00c21800c00340410341e00180b02d0500c1d40d0a0042c182c1c1e0310035040c002d4221480500b640880d80d0591507100d0360301403541101c000500369580280c0d003061900c0e0483c0c1c0703500b5804980c01e00000180031348201c0c121003010003001e040490307140d41c000246010b035110712408990100d041c45008860041840140721403000c1c061100544001da14201c000d0b540018a1014040c1c07043c0001c0002c101c1c190a040501c800c10314181d041c2c0e95aa1005807040400c0750400e0700038038138080001c591980c0010740031040f044440c05030a4108014542c0540702440c00b400e2061145400000c50000c0090b0b41019121000d00415500041003a5403480040d10b0300f40d100200083d00caa003003038840c1c1d00603c0515a003031139a00d494200780141c084090216140c80455081403540060070074140300301804404013070f550003000c0504096581720000c2151340151002e507800d50903078 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 150100000 1250 150098750 150098771
    0x1050711030901090504110d020f0406092c100306050a021c020a020a0305070f08130312030b06041a0c011406030607020c0d0b0703020c0f0313050303030f040b040f0f06050a 76
    0x1c00d54580707400c140c1d41c15540500f000140006494201200140340c40c0602c840c0642c10320600150151072000c11240f604c85152080c001c6c1007074510340c0301c01107006254010720032152a540400e05241034010045989844d410503441c4041005d03400604000d14020601042e02c085030000c3c040c10b510005d00f24901c10096507004220300c10070460f200581c0c03150200400081c0208054190326004182820070742110381ca0f8082c82c1d5004280000c20307042c0c403100900410031000b0344202c180460380b40c200f124842102c00b0034100d2207640142d040d034418403e400d840008511007102d8201c03018100a1283c2864070381241021032041c0c0f40c81c9d109001e0080000c25041c80003840d444600c000920301c0354031480a032105444444090620401c064081044110706d0104004880c1126012002190340e8228031500305a0003601d41c04c581d21942081052100161070001d105821640001140319240c40e18501302081070032010b00113145040c07400042050049603032205100f00c48015090004103041c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 150101250 1250 150100000 150100003
    0x16080c0f0a080d1407080d060609061106010608090a050a0b0103020a05120a02010f120e1606090509040204180b0f06090109020403030c1103010b0d08030411041e02030a09020d0501050711 82
    0x4501450301075600c0070046102e003c1c8a0a0180f6448126401d0384d0703d020381546908496600100f58004140c2d00c40b00c081084a6121720744000911003883e00c850740f400c60580442d00c0b03241c180b01d060100401e07840860038004041c4980c0f05025402000c0300d220541501d851907142c0024402a4482d100348040003a080c21304440080e044111403024000301c0805034010745074080250408010000040c4c103d021001291140b0600000c4a0004284281c40c8204e01480711100b604000200000c4d020104900d4980150942d0410ba041b6000705da85c02513510380c0c890620040c0d0300900400300c40014042d04001a40040b40902c030140c42011440e0703214000d1505038452403100600140c6c4000e610008561480c1c031100825600400105584ca0440c00090404250500680d076183c07001040c0000c001e03420326444d201c0d50050758180407002414014120469001c00c080e8075654000002400340c03003640d4030243c00aa80140b2110510b19a0b08201e402800110785480c0480c500c28506600c0780b10 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 150102500 1250 150101250 150101269
    0x114090705010507060c18030605090c2b060e010c0c0c08210c010f020d020a0815090601050a020118120e03070f0b0f040302040f02210f0106050c16080c0f 68
    0x241a10f0b010319200340c940c1d500c0001c04200800404100c1c07908100080b40b82150b8540000303501955010805052051103503080500b111101446442c1404c2a401200c854414001c0a651490864004103119041c0b26025064802290344594a0203207540020745d00030b5440202103001d0701c1340d200301907100c020540c0c0d10401050f0300e66414645404c0c266201000300d0040181c14103410011403944501e05540043c0d812040e0b5406a60380c000c0380760094258001507d90307200c83c4882c1d103c8000b0aa480c00304410b800060166810001c000a0032001603000b50008036a400c90b140031000482000c2c200030510400300c0940500060030310446a00900d400a554010f0310000c080b56940c2a00e01400703c0391035844100e58000e0000300f80400009681d45220703070b6412441c0140d0147e40d8803516144643c140c08000484500803501074284181e50f40c41800c01419958142800e0703655000c40c07440d40b840c0007494a01c0c1d00481d0f00014011400040210b418608100c00703841d01811200d0383e6041142204 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 150103750 1250 150102500 150102509
    0x70608010e0a0902010507060f200f22150e091e06061b03030c0301030c120f082a0106060306060504120b0403091206050f060609090f0907090c0201140907 68
    0x10840741c0419408000d03584000401c5105040007854101c50303940307a10503207900d1082840d185032741d00201401e82007407602c840120b1000800640c030b08141c0c446145024010000341040300c1205402c5c41e210401c25100c200080c05849203c080d0a1028500040c42c40051706070300d0b8040e40608001c41c0798009010345e144002d05444050001135503030201440000c3d00103d0031a0342285034401d0030020702070203100640c09404c5501101d80c1d42c0d03055050590401070309a110740c0000800a401d10301007011405261840c41c0d008185d683e0750140b01480d88030b003c0c0000f4a2040d00b0080d2a90143c42520544c09002102c004d600d00f405020740d034039400c1d1013a000700d00ca16a0503401c0c25200c1c1001440d1050407540c003600c02c2c2081454a0b4540080341e01102c080e40341140c003503070740b41d0910049c3e8401e0010290711840c01c42e8840d240000744000308011480141c02c5c000c00c10b2040c400700701503403400e00540010300000a81000a2001303040000d000e80002601520710518840124410300008981003040d00d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 150105000 1250 150103750 150103769
    0x50c060402010c05071509050f01020f030d0b0310020c0309030d030b030c040f02130b1c05040f020d0f060c0507061803090612150603060602010f09050601170c03190507060801 77
    0x10399498006441c50038491074104e602e4010a075001c19a103185115a40980c01c0c55644c0d540d115091400340002c440301045041d043d0f521400d008040c0c41000000c860301c0702c070740b95008a140604140820314100802c00c0000081e40045040c03801120004040d0200b95802c81c221080302508010a50444000d44d8049416800051801d00075091a4000000000324680014500707070800a0300341244070701e078001019801000400102c40202d000c54038071490003503d000c01c0b65003410355a02030082043e11000f40180790769540070b024841000b188000d0560400014803038201e00d0b0ba00185658052242126800d2030040b40c12222010f0301c4a4000c1c3e19410b494420486040403000e80b0707a081e107800702030740080e140e800034131111044c03032105401450b19450200300e050800401a09550380d15000400003490050505d01042d00091000c0c1128a00408510408040c03040704d0300b0004450881d42c7c061041036048402400c0f90b01d1a448228068810b660311300b91100f130221400ca45c284903a2104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 150106250 1250 150105000 150105013
    0x303030c070c09150e0a060b041202010e300102090616021f05030411040b0f090a110301030b0f0705070f06050c0c0f010c031a01080103060f15090c0f050c 68
    0x18400540300509209006840c08440b4982e652103103000c0e128800400040f50401c0c00c1c0803c0541000941d440d00907820303020a000c00390078178400c22181d00480c416a41000d500d12450030a43e4003460710090241d00140c182e460000768010355400c2c1b480c2c0006808400701c42c030f42c0400c2d1546018070940c2c42c3c1200c01829940342c0880d128a94400c000110403c1c0d07800599415030082c00c410511b03841002088544038142c80f49480d080008081c0c10139500c1d40e0046051500c20800360361102e14001c00418200c86006190700c42c845a04c004000080550540110000001c8180002a10024800c036142c140014140d80c035030b42c5c112964000d4070130042800c103418200c030f400030312250810b581c054100c403210f9040007488c402d011702c0e102d4602c0403400d10380d40d1032921080c1c1a90501454401c008a031403501c01054110300020403000b4144070281001e40d48002d00e50b415074103500700c0b120319040d03d007082e40400e8441d00540008c0640091460101345007046841d0442e006005445240303400c440607085c0d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 150107500 1250 150106250 150106261
    0x182403190e1b04150303052b0207050f0706030c0516060b040207030e030105101211040209060415030c03110a0302070f050610030c0503010501080d11030f0a080402011d030303 77
    0x8554118000404880d1115074003401208108a940803000c1000041c0c204210014248402c8a54075401d0280d00c0e07508110510100e5040750031207210a88030316040c0445602010f0355103881c10700c0c0036030200e07140c00020086c05010001034100c00740100c0400751078a20747d0b00d941c1038003205c114008840208a0600c01d00d60001096504004164024000810010340c1140000c01b2a401404200c0105a940d040c540190070709104140d80706018400c221721082c10710b143c402004201001c020245458009514050340b9603405842c200d09019000d82d4031103403240e1007034242460000c0198006460b001c0c981e500c051203405055055a001c0600c24544440c005040b00698072060040d0349951008400e6800a40304001441c4140082c159006c203490440c03a00150100b8154841480b90f0b042400501044001040300b10440e255801c0602c807030b90500003114154058881070901c2400041103401d4815041313402244214403d80e41da030911507100041c020301c101000d0000e60542c0c0203200203076 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 150108750 1250 150107500 150107521
    0x61205011a0d06080106120605090601080c040213181b0315120813080303061c081803100219120e06150402040806181606020c010c1403182403 63
    0x7012030001000410016144c00c4494256a12644141740c0f4000d000800ba00380140e0b0322500d50090084d0000c0c014075450109855500e0703544071641c0d84a00d900040280600355081c0305038005003002c1e1400c005860012216130300400307580c125010040c4c1c00c04602410070744a8030072044180c0c503050900d02641e0510841c0782c02403091160072203550004104450500346c030405018020315950006560300c0c40d00c8030a0144191170300314101c140c0d0f0101c940c09800030f0520000c0c0c42d824000000c0b541e403030903d03107400285002041050340740e2243c0b001610103840e240f0725030740d0121201e964030780180d000104141c3c80201c410902044899800440c013041d1300310303000401031049082c002c00c00750619894050b101d0800c001500c110060107404103c1cbd500c004400d1200c0328000e041040040c00c698035002e00a5151303903141d1100c604103c403e054400070041400c030604901988081125103c169106070700341c0381e03160740492a01c110f030326050b480120558a07030341b14080484202c1d0b442c01c6450720384403038 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 150110000 1250 150108750 150108757
    0x2130e0c030106080c090d050d020d0201020414040207020a030212010c0e0a0506070b0718080c1c021c06271704060905040e01020d0e07030308010e06090105060304060b100207061205011a 82
    0x148208009086260b603a0075801100640100301810781083c1220000e441c0c41092f03070340c2100703590045c0302c1004901148081201c204d00306a60250761841b02d8400165000003075000250311403450903222020050561080c030302940c583c1c032014440b000b0131003080000c0540f031080780e5115104010480c00511071940072038014071942030416011001d02c01c00c048403d000c0e00511815801902c1551f60740c41c01044020440d03e00300303003110440030b180d00402c441e5000702504110780c8800769030394820004541e010180c405515410b4150645109a18a07500f072002401940e0510541d12040318001c20310007110216403454980c044d0584c5404e050101a00c0302040790489550701307014021464625000302000021420090042e145c00c520700a41010741c180c119102d185c010504202c3c4944a08090702c0c103413101124084e07143c2e5510b24010000e40000c515207a008209043c220a006400103540003e6550f141c0311003845c901c4003a550003c41c0c400f4410342c2000c00c41c40f01801d82151285009 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 150111250 1250 150110000 150110011
    0xa0506180d05031c0f06031e0c0302060f030702010506030c0f0d02120303070e120c0907140c0d0e01030b03010506030604080901110609030a0306060804020102060105010e0409020301050a02130e0c03010608 90
    0x46003040340540c54040c02e40c0c00011a8004e00e11926240080d1542648a18240e00309005001c010140c150384401440311185500700b04800c09441c510414010251100e1005503030040c80150b44213100010101241c00c01d59020380550708220200b1310924001c540c0300e203580000b800da85407000c0c0002c208a00024502d0041e0b81004803220000c8030300e01d05100561003045942ca900541e122a44280926a0070001c001c9605d4ac02650351004580e42d280110f68000c0a02e10303104850142c2100c07285001e00c205100343c0740034450307000a0140e0790f4010f04440450f0f4000d032420090078660b041854241c170400c484403681a00950000303400680d141c03000c1e00c000d507c18900f01d190300c44112440c500c0c0403424bc411034002d038400b1030111025035050203508060101c13440e1051607030415a002039510354041c050701e414000e070701d034031001562100c0c1c0c4118942c0e50024000e00080c1840c40f0008004d600c00d8050814659050001060f18111031030000e0145801115003803540c1e1038600c045900d404058007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 150112500 1250 150111250 150111259
    0xe1023180d050a0302070b120705030c091305090c060c032502100e03061e060d05030d11041a090d1e0b04030819050108070501030207062004140a050618 67
    0x30521180d22481c5a030020284601c000380b00f94555400c01030710300181540400c01100b41004031a0300e400c01100910f402103d5400c01607140d489a9043ca2500d00420400742d4200248116504400c11207030800790041e0041000c0c0c40f0500300d500b0a02141388541d02e080d4901e54010003a1454441803a0a00d0701d00c4101e91403035401c6203445500040094600c031000c0d600141d420b1a103000a03190078080d1030b8002490b00c0000041084061802e140c1d2000204120321541ca92000d00003072003400c1c42145d03140c0c09229420410603002007408036154006020300c000405460030a003090340000f004071810100010305a100400c61507443c0d00080d50744080c8008003518161540e0005150220030a0041e4840d403600788251401d0018080445031113640310242c0303400c00c40104400f0401083d078030143c0f04207180c00b42c0c6d55820f50800d640906810300c40d882c0d01848014000c0381859112014100707686100411414402049042245603006405040d0b4441400c000720980345a00c4d09940c82591009003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 150113750 1250 150112500 150112537
    0x721230d0605150f0708070c170f03070309060305100b03071d0a050303040522091202010c02062202030f0609010605100509010207210c0e0702210d050403050c010c0e1023 75
    0x680340810040039074042060a01c07240c0c001104c0305c000740324422b10681c02c00d0042d030070710b0141d0f18000c0900b0340a11480060542d00d00100d0594185040744a01900c1d000680710f43c0c03410610002000d4285a0b4441d42c01100c004165907520728080000104035000213005606141c146410003a0044040040880301451060b10080f111a40c2c0640200759000b078408090724100520003030300790360341800c060086400030030400c1174241c1d00084040c1194071964101044a00c0e51001c00d00c3c1c1054488500369501c140e20810070501e605401c103000b590410f994006415008100a484034003444003c90f000d60070000b02131022401c00b0301c0d104a00b00c8203041e00e40e041c0342c0c0c0d5102e030900010f00d078020350300d0010b40f0390401614a80400101c8400782c0002c00c40e100724150300d405110540150040000c1068840c0c01203800d05d4418815503601054000c000c00403034403e01c00182c6005c0d0f4881120740980e80d00448860610f02803580a1400c000846904084000118410303030a40d10401c000506c031040e80 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 150115000 1250 150113750 150113753
    0x10216030203061f080a0c0906050103090f0b0601020c03060a060515070503040605160210020c0a1e0b09040608120301050102011103222f0405010b0721230d0605150f070807 76
    0x30407510144501507c162010395091641100c20707201950019818542001c1401001940940f94100006d803c480d5100a945131400100d0138214126400e5506209001c1400848031003940000304550080720404941e58403541071905c0b40c041c01d41d02401076001408100200350144000704401d4140e880040f000030441e90001e80c06000c0071140780300690007030300105410f04000324584050801e9021800b94a0700080c440030400415000c0c0c0358640f500440d028003203440c0d50300444003070032a581c10368558030130708403022401360404d20507a0300540c24545031503000b40082c41160b0003007000e81c0760303090340404000c5a0384030201400f0301113507900c803030001c641501c0c924224082d128209401d8034803c0510004100015034a041e00061001c1c10308000d1000010b041400702088002c60044d4003a14108642040c0e4400407120098603071044109005c8e0b00188106004181141041e43c082042507141c20500510306d022610f040f036100802c00c061544031151034060701905114046461402d01c0c1e9 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 150116250 1250 150115000 150115003
    0x30c091413171c020316020f0d0e0d0606062102030f07180b04090e0f0607020a020d0c0801060b03040203100b060a030207050c061603020d23030a140c0306010216030203061f08 77
    0x1880402440f055002c41845999000412803580c10b00403403009012a0a03c64059901c1e0305240d040d60b814400710200c0d20400e41c8640d800d21079081e410580810001d507452601511014821a0b8000c22422000c0358880601091090302e010340380c081c0714412030341e6503000300341d48a03040c3c6c01c10342c060b40c1042180026641505c000500c003402c0c2c808408908004002c07086841d0641100140c420707904203d04121802e580040d0240d20140c044880d6050064141012942c080ba603400c4407009500b40307480030903102c40503c000c501032403080c0d0849202c000d8542002044841c000d04e142d500c04420051052506c0c03094028240c201e000c1e0050303400344026500050100d074411055800380301108100740c000d1507018004001048814105031030081e039100356a21784e01d8002041c1d0311070640c0c0132000c11300821055001010f1104403050b1914942400740c000607060700203e03131044c014441c202213001c01e0103060031198100c0f175002d001001191070b00c494000001040c1c0c00d03110042e008aa400044540c0e0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 150117500 1250 150116250 150116287
    0xc020a020405160e03010509100908071203060f0509060d02040506041805060115080903030606161509020301050105060c0604080903120a030903020d0c150b0f0a030c09141317 77
    0x805884070f81e00181048010784242c40e1040041d10992612040003185607001c02c000351110030000380040c1404051078036200a00030303000c0103403003105030105000f040364041d031080c41580c90345818140324658450030050078800072038140d50000280341500e4014203241e04816040746c00104007140c240c3c148082c00d40c2e01e0b1080c90091742c19a100f01c0042201d1980d1900c24882095140350120743d901e424031000341d4a01c00036042034042d140000b0240c8030038418100407104643d02c903482854858043e65036801801d080070040e0321039440c100001990346040c108440301e1001d6400644541d5807681c4070070b03040c0e0b0803512140c0d8150003903a0001620007402d100514103441b40e510001000e16050a00929001074480000f0501501825140100d180c5210000100382d20b40e00104150120b031020942d0340c01f2a0401703540101580202108100302405208103585070100d082140404d164605040700364240ca00700c1001e4007c84074071000c143e800418071100000d0301c4400340341110001e5a913101c42c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 150118750 1250 150117500 150117511
    0xc0a030302120a0603020a0b0a12021b1606020703080c0705060c0d03051303080f15030316051204030b04080d020c060a06030501200a030e010605030708030306180411040c020a020405 80
    0x303500280720000c0307400342c40d078407900300c14100020030209085501090003016140102c4058900105491300d426228032844411a81984d03425902c0b840381854401c003150a030000c00d4071601070251610096004014248121207c0d5401050b2003451522008642c5d4458040c82c07a050099801c00304907500c0b04c2004201c15a106001029242c04500c40103089590140c4134a4030f43c0d4040041c000400d80c0a0301060700003030003045c01c4120361958a100c8581905141d0700320b41500012403684210802e59a040c81c2c960b0255007034810340c00e40580500d00d18031030307804020092144640440c003c20108006003100040900c0014a00f80e041a000c41c9031610841300300300c0701074032000c040c81006001e001d42c2d60010300b4a20003003042c1c4a1000f103e0010301404900e1000c00d41e43e81c44d8010700c844250441c000410010b001e1360719017074403102a29200d170f00c101d1741c142c050525181e0303008400c05e0700030000340700c0e5400c04186452101d2040800c0098102c1c90350b00720441c440d2480c4c1d480580c3d110f1003028003e5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 150120000 1250 150118750 150118757
    0x3060905070c0b09070b040504050c0d14390715020d0213080d0f050903011806050106030612030903110d060e0a0b060102010b0321070c080c040b060c0a1203020c0a03 73
    0x281d49850201e07803c850091415400d60024038080010802c05070556007640c03c1103901040c141c0e0b030348036481c859004580c2416410390400120642c0c001010350120300800380600902031541d000001107000080b800d2844040d80d080050320380c007410145c030103071240c03078490940044201c0c4980810b41c01e98006000f00131041e54005a0a5120f4002c1c01d41c1d68010106000074140310040b01070054110707050060140240070000980d60803da4003948640d403006004000302c02d1560703d500303100c0b0041c07800340945408640b800b40302042880d56101000700c5036900da500e8030400d41c1950341d0800d0800d00c906122b0b4100d1144005203001075554001c41c0c00d91283c042c0281551307005420203115488015141e2415a45400360719100c680380403c1000c0c2101c2d040550760142c011a024000c114442c2d4813024090210042002c40d6030391011459540507002101d040c4a44905401000018402c0702101c0300c00e0b07480a0202c0d40011081d040c2403490b49440d040042c1040116a075890500c00a485d085000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 150121250 1250 150120000 150120017
    0x1502030d0c031b030902060d0222050901050d120201061a070302010b0a0b180d12052d03070809070302060d0902010215091207050111070f110306040c0504020a0306090507 75
    0x3140c00c603100c0c00d11140d00c03900e0240000540505a207070b52a40480c1d51104043c0c482d4414002d6460340003c90704c24040e210403c55450000c04980c4e80350a203092503c501090b00401c0000321894460903090680d0f000803c0c1c00014140c1c2c0d500e165800d203220040c0310135952250000580c070080c1c4111081c0340096902c00b169030340a03510b002801c40b8045030150313204a2111f80c1c00d0000002407016102d001c103a80900072007200d01c001c0000e003110f008100003400b80c400c0c00e00c886134850b8400c01070204100d052800c4284220040403144016030700034948180b03010f0500002e20907134031419030300d900035186000790b41d10181c40c0c4c1c000c140580d00200c4035a001c0b41d01d5020303490855034100074129101c01c2c031020f002c1c00c90074000c0a194940005401e0311544101c0810301600b8040300390702010441105481655807440d0b0b85c58051001201018141c5069440d199020704030f04001c1401032280350701031541c00d6414146007c0000a400046a003820950313100c402040707068051292600624482d211f500c6d1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 150122500 1250 150121250 150121267
    0x50705030109150b090f01030204090606110d0806030a031209020907051c1e05040305040b03010e0105100f0e092211090105060f03010504110c061305241807150203 72
    0x1c0d80c00040d180302d00916840030402c206410313201600c44007602100c501c81040e0401b0b004030044e0003113801511185180c284009610b981014440703070458082c1d000c6d101c504132100019070740e028007210700c40e405820052240c800a44540d1041c0c0485000d1000002d403a40660081030741214210f813540e01103000001c440071a00f41a0450040d041c0c45000284041101503183d03600409862040c42d0f080b54440c40400c007010300170030983c1c01920103d07010f0764496a54162141d007116086c442c190103840300314042810f082c42010045e10030050343e25011505000038003401083d907002080300360790340c4980383e190720080120082c40700042c1c014400001040c07088810003020307550690126100b0003040010700c880c142e440064030b044a00450b800a5101d400240c0b41801b0b2203000000d901c140285020006004140b030030103107130741c1c2c0030b241101e5a0384000b100d407008010303004110f1a40e01c21006e001850814000405540075a42d034002d032a0f0781079132403028000700a440051030300941c201099140 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 150123750 1250 150122500 150122519
    0x3180807060f0b0f0f060a020c0907030207120f1b0309080f1015051806030a080a0f02070f1d1801060807140907080c0a0903051914070f23040507050301 67
    0x3e00c64400ca4038496951040d000240380c1c992142c0d50107008103c0840d05e0016240280000004180f01070000e020903e0007010080003580f155504403103001100c1e014107092842280b04d941c06003801c0d10b51a0344425440b13802e00c8001a106c404808128251201288001051102040c000c2a0700018528280607404140030350301e13842c8021121030742c20392080246541c0c01d500e4442030b80007414042c4040c2c8810011a080041c2480060300f59100000c1527020164841410305030303038540303900760b80920b5140c45096003207106501c5825080180764841114008140e4129034000c02216100b80960303040c15401400d403403a50740300c12a203403c82442048002a0140d030900c40c54422110030302540f800c10405840d144002d403104110441c0810221032585c0514090805590041708694035841420f10102030682c00c1a822107a191019803000c1410400080b40d0040c2c90850842e00344190408218036041e074400050720b00c650654011550280d00c0703a10400d070051200380e032116503030b605044468 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 150125000 1250 150123750 150123761
    0x150f1a0306090c060310030206131403010506060f090301020417010504210c1101120e030a020f010204030b01060807050d050a290f0f042a030b01020f060703180807060f 74
    0x160007604803030100245101e0200f0140480003080760f50035101d13210004428101c07012078100940000001580604a100701d03603c1c807003100d5410000c565241c401d542490700f6034006403160b580011742070155445145014000d400c500801400050502c0c2da07942c061801c3e403844100a808595542040c0024040c402c108840203c1c0140e03d406080003240c81d00416820714140c0140000b04900428038103684505440c0e41c220200c1c1c203040c410503080102d02030b00c907400300c0001e6026100d200c444d641020818001e0b6003c5035005118000282e180c044182c1d41d010008040b1410000104240c6501c00c2c294403c46000d002c060000144141d404191031805101e414440c64a03010502c1500c011941c0340c00f41d10254078410780da6291050044004507011700b4410450f103140c880208401400c4051140307002c1c04007001560180043c0411f0801661542d0b10300f04802016040704001400c418001e80050f41919841c2000c25081121625050801c1d0443c1000300ca0b0307103445014120401e0100e002c4c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 150126250 1250 150125000 150125051
    0x10203031003080304060914010501060305011403070905060406030f05060f0a0e031603020c120105190203100e090304050402070b190b030a030c020f030703050d020d09051c150f 78
    0x1149142090301c901c1d81661a2840b00620f0088000002003c0010740e8000c0c00c1c034254000142000048006c030071901034a024002e400009142100010340d01801d4070130307108480310140190000605010199028000041105810035102c010000000e01c881401601076801a1b0160101d8200100102d80c00607000c0c0c40404c11a05150407501c040002000b211540c0d0150300402e81c0001040c9401c0c0d05041b8403200c4d0aa00041022842c0d030340b00c0041d0001d911505100c0caa207400801c100286004a001c181d6540c03245038140c01051000b07400003101190410b101c00212414075540c0e10004007668041d50040714284031940510503016101c000010b865850100c0a01c07c81c0c00c14408241d440190359406420460351b000860255121000d030710000d400d0240688140c2512824200d54420340c03051070100602c56061a02c000c20300c204040c0d4161140182605008001c13402003d0245405410035580f4088001c2d801103241e11520544d0600c04071214041a00040c80f582a01907250100301e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 150127500 1250 150126250 150126253
    0x230c160b0a0912060b06030a0605040f020a05070209040f061d1905030d09060e15091204030b011814070909140408040b07080f0a2d0206010501140c0703150b0102 71
    0x200100c0250010b5080083d21042030103014510b4450a0020140900b401d0f61070704a04000300f0310021480c15000070003942d00640e410310030006800a070030300300d1244034201c0b000510240052001071903c10b103180d80242c0205881d00001289032552800c90f440c0b00e014100c665080c14451401920030f200f03246c1040e0340409100001501e60b1141c43d200d1054440d4850181c3d0780d008410200b103010703032160140440d04002c503120080105090207980c00185c4001c090bd20070645d0b80c80e403186001e021582525031050340420188d2170b00b414549001c0301d40090b06440380c0c0f142e1800d0406041402c000b48118410303030300c68000c68a40305a07001111380c40c1c4803814500e000b2600700b1001c989200101c904545550300c0130f50355401c0504014450340142034036140d02c0f540009802c1c9c0400c0c0e003c0780505c1c124000707038045064240d01d0008004401c41e24844840940c00c03940041002d580120400c43d09484100030f4946840c1118401342e050240e544c00c02c80d040300b40509500045420f52084488105c002e00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 150128750 1250 150127500 150127507
    0x1a0702040b031f0b010c05070b0306041d030d020f0909070206041101091a030a0605090c18040504050d1202250501200414010912032616230c160b 64
    0x41401080a80581d0750f40945032100407415911802c1d000d0030081d041025210355980300c0300b02c091107510aa90b850711983c10501c4030f007911441d180c2d0840d80406440010340c03401d44601c1c1490065000b0601080c4282c0e030034466802030f0344034210064801c4203030303501a000c40e10341494a510101c42c100c11480c10491a00814080c04040701801c0030105d15110042d40c40b986d0f40034680300034201640019800206900611650542d0304002e0328080900c40510303110f1107113801c1408100d440498010300160700c08203601c3d05003070150000c88c10315450000e000d85402880011525901100c44015007010004070088050001c04e11a0068180031404a898250081810200b0314010ba00901c6900c400da40b000c84100d0703000f100342400406050902540b80d51039410301500441d080f041586201601c0240350901c22117aa800034403428841070a802503010301081212883e0015004102c04180103009000b60000b81c1c01820380c09007240020076403d01d4a55020b00c1805203179001070080340090 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 150130000 1250 150128750 150128773
    0x9090b0702010203090a06050402060403050109050609191109100510020c0f030a030f14041d01060e01020721080702060c0c100809030a0f051308030409060e0402090402060705071a0702040b03 84
    0x446c0201d29150040c00110b200d494a0001420610455000900c10362804d500c100811201291a0384100640001c0c1c0f400c2e640301031407000349141034050082510b85000311031840c0e480e0050701d2039040001c0e810704000d0390f43c456001c140e135546540400740c0540e201c00c10320001d503e01074001304070107607055002d098007900650b0040c05104451501c0002d002880c18030421400221054a0003001d0b00100c0083d407100041c0c201c110804207000300000107000480c001001d500008001d8225884240d01c2d01b00756504c0000030503144142c481c00c55000c503040003010050b9607048054900c0400c00c8001d888200701c8082001448290480340c0e0701403000460810104c0c0c1404419941c2e040500c1c20189800b1146c00c0040320140325100f08210030070b00d507030404680c01800201078010f9034280441000315a40b203009080c0e8244003124021350005a01c1700013801410800c018004052003074040f6030101f5110013080c0301d032001503004100303440c00101e07294065240a026014125005501800700332491 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 150131250 1250 150130000 150130003
    0x320d0e0129130603080702060f0f0301150f02241f080c040b270604020c0607120c0e0604090902060c0601060c0b01050f091501180605070c0e061305130c09090b070201020309 76
    0x103d1b90068810b00c0c01240d060a8148050b00b25004c8101d208030300c4e99070f0f42e114401c24000048440285001070104000b2255043c000a500400284400071072021103107034006001441c40020004c5801410268401100901500c4810090100c2c40c0160181c80d0122083c0011160090300e0320384282c9402c00c000c03180c100a01344a081e8041402144900d0307603900000f00f40644074190098689219120401020380e503c04031001800c1c41c02841484000c01c518011140307144d03039080041e880700302004100810b8043e07a100014007807010346014281845203c002d401c210307090348a40041141825030000704071a14140a024043c210703503c0602c0c20041000c1868800001c4c403403800c0c0400610040d40981c000e064a440803c0c1c0c2c0b0f01450002d680300c441c020240c0d04061821240703035070040c4010400f01c041d410401e2080308064080b0518002a600f00070150201509640742c0310402404d00d004940d0140c41007020700b030021404149000705281c204200703940285081e086910500a2143c0b0020 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 150132500 1250 150131250 150131257
    0x9030804031d0607060c080903030106020c06090a08060c031e040822080102210609060105270301060b180d021509030106090c320d0e012913060308 65
    0x105841d00c4114006242d00e00000c01074020304259002c0408140d0504020540d0031403071804050b95100e201d191a0501da2a949000a0141c1c40c0035800104006195040c041c2c007500080000410580c1043c1c2e4820b900c600b002401c3d1000940d6220000c20040840050300014111241002e461001c502c0c040d141c0c0e03440c50045410400864580c0300c0044000e241c1d14003c40040c3c0740201c000c42d41c6208140460050450138911105203440f0200084e085147c81108248240c0040e1a400e292100700d004d50304103030708410000c0150356003100c185d03d0340c0c2d103003403043c03402418001d02a039030390b245005d1003440030324038614009128800070340d849001a290b11014100781c10381c040361240c484510000003405800e407a00070802140c6428100342606500903015406400b40080b600000c903010012041280907154481c0760070441046113035050840c940c0720b030b54100202030001800003d020640c45511032040da0340300751901c0b5104001d200e4a01103600340c080450b1260100280d074038582d9403890310301 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 150133750 1250 150132500 150132503
    0x2160b0a03020f09030f010b121906020a0525021809101104180209270402010e150307171003020f04050411090a1505011b02040506210601050301050a09030804 70
    0x42d00811a920100103000540d60000e20040541e8810144038145d02d00030400c0c850390301d101e40701040342e072049071801103825180c1000d8104030749003075403060300e429000c3d500108034201008806c100300c0806054602082d118110407040740c402d258110700401098044e501460310b41c1e030300c00c001400005100060407460189015801069000c4040c0c000c0810303028503404103807100080e84202401c5d6034140e000707100f586000c0b581d100004c07502c2c1c10810060040500c12440d481110000f190256015402c2658800b42c0202245c103001850b1444034090b030015601180864003013845048130862041c00e0b1580000443c1c0503406c07480c61500003c080411070641140199500c0c40442d043c402d84040304281028041e001b08001d0408607018001400081c90042c2e0760100700101003030a42c400d00907040b000c4e580c070100b8030744c02149800700002030401034410340c1d100404000c41d540c2d0b901c0c8441451707041c0342188090b04280d03140005041c2969401006681030307a02d440d080701d0009812280d906d1304103 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 150135000 1250 150133750 150133757
    0x70303110c0c12011d0303010f0605070506010e0a0605101e030c02030a14121003030207050301090f02060a02010b100504061713080d0b1e01032a0c0f020d0506010602160b0a 76
    0x150910080c03801001550301402d201080740c0c0403174030041740000056040710984110303131a0701d91303441c0000c490501909400034282e8019000401c001001a03a803160008518400081c8a60b6903400080c14411501da0901c00720f0002e144110320b03000c610300340c1c04813940181400d0000704109071009480748210500c103014843c6000c819107254001c8400c1d1400008504641c40003800c000c0442400c0d0902c2e4030048bc014401d00d0300211700780c281802040b81346036004590300e90780d4106508002c000d802c821030b03e1045640c1d0b04075130b05180c1e0710030000d1030006240707464865455050290091042241d4030700c070014400390009000040c00883c0e920504036420014070b6803500c801480b03e101410f038110000c1d0707002c45a0482c621030701059074041c11845100f40c0f400c201184041080200138081795010f03500240030100d81c01c600a01845218190600c2641c28000102079030740020b0348018407103030a8901d40e112000500c0a560100132450456483ea1448500d1500d040c4403200c070343c40703401402401c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 150136250 1250 150135000 150135019
    0x105060a030207120e0910080a110102010e06010311040e010b0d060203061f0210140402030c13090b0c030106030b01051804090f050102030a05060a0f0e1501110d0203070303110c0c 79
    0xd24425030554003000c2d4054484109522441c00c010082500120362a10507a02400400e0120240c0348100342258008006400c05208035100c0311341149011000905554840340340c1d040a04040c49100c1c040c44c454201d69070704070814000e100407030f802cbc450300d401c0a80c9041410385c966641d040740a00c4040d803140c0090f81d00d9035003c02141d120715107290b010b100c3e000500910b141094001c144038000c1d25800a04002800140b00e6441080d58269006505500710380d0300c2c0400c0c2e09100d01c0f6040100c000020210b005040f99452496541040b0340d01030001c20040010310104ea0300d0b0142d1840c0920074640f180c280028410b0710035000707803d03000b00c80c40349a039142c80c5010402e103208a0901c140c1c101000719200e183c01084000a8001101c400e88200650f0310b0126040c00030441d04801c0c0d07419042d0580e46680c45040d18101d42481054940c140316120400e41c0d4940c0c001c01c03e08181084507806180c586049280240980b002c0b05404119010140071000301c5290010744100c04100880d00ea516 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 150137500 1250 150136250 150136267
    0xa030209040807120f08060a0b0901080a15030305040e06030303010b12041e0605041202160303050d020702150c0105060a0b090f010309050105130b060306040506060105300402040b0406060206010506 87
    0x1164841c0481c001d040d0407043c0611483c2d41d030171030040020034030503803200007007075942004015501c07000d805003014400d800c1c4514030080d4807403043d5a070b0012660303000042244000701d240b060206242d1080b4006040003d0a0020904492030550441d030194000d50941d41805940c2c041402007002400c0001405000a030a003c0d0784800004a5408240211502c101c3c90030510f01402080710140c410392007048041922034070025081090704212600b50540a0466804a070f141d8000900f0b05042502807003402c0c0503990f00840b40c021108000f4445a076202d0340d80990b1300303586004103148d218400c4540c08000f032598040465492100841d80c0c0242c1030044e40c010390023000710900141c5150300c0c2204104608600802c80c840302790240c40c40c1e0480755942000c01d03640b80c2c8100e900404a80000e0045071455000724040e05800c4400e120300d21004c41140700c112141d80c1240d82e03420354180070340280001d6040ca407084070301c090300030f680a1041a04100010359114410700ca941c0c000d0500085042 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 150138750 1250 150137500 150137513
    0x70507050405010902040e07020a020306160c050f210c03040303030905030d060306020c0c190909020d0503070b0109050a02090d030516020604030c050f03030c0d08040206040e070c0309060207050a03020904 90
    0x802a0900800c00c001c60758403802202c0c001d400c140124440700000300c0100e003174940001805a03143e58001c00502c019600d00050701d00346500d502488040c4803003012607000041040c00030b09900f0450500a0040c0040e4a0352150808003c1c881d125402000700141c125002012042318284c03501810089041507041c03a02903e18803801007141c00380e40c500381000c810031566800901c82041502e04940150788000c041180101411100d01882d92a11100b0425400300e90061041e07180024a03c0c0d003510b1003500c546080d41d002c4c2004684078150a00140a1184503201e030b03682180c01c00c4400c5081a02d000085550200800000f90070301c407001c664581c901c200c14804c41c20309607014200c2038032140c2e2803504405601d241c0c0556403080401044150460500009450b16040c21000815040080b4002994058005001aa00450300700f20100f0300c5c1401000c43c600882c110390703c44000207101c2c100180442d01541002e011504402c1c01080366640f08442e0390260b07a011245030101d62100d26164 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 150140000 1250 150138750 150138763
    0x20c0103050711030c150a15031103070e0a0609050c04050d0b100b0a0507021003020306090f06011407110f01050c030a03050a18030206071103030601120506030a3906090302060705 79
    0x14182c1c0c4800103142e4198400480c0346c096a12181e004d101c4103840d450340e42030a4a0140a10314144100e944c408c00c040b03401850380701d2034400054240c410460301e4401a0100d103030111044809152034880412010702d00b84503040e03000c82c101041074100703401c00c0001001d10f238180709d001d05200a09000305115154441c4128024040400095582c000c0868064a590448503050b88100c0003070161110b0320f8013a000b100e01c101e0f0010a64417041e5a09034030f0200c0c40f0400360080741081132041424240c600c0790b60042801ca4012603a15a0755480c2000b003007078080004208604010042c050848402d10000030798034030964138140810285c0d200c0c500c100041072400302d0302c0790b00711509580e50149074000c2185409040320703070354050110002c4000c4564921041d502c050004210003c4002d80c0805a03000342c0c0c104000a040e503200f12142d444082158080d02103001d000b54030060080c0041c0c190201050b44401c41800002e0214a0128050029148e42c44081d0151500181d900104003051109 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 150141250 1250 150140000 150140027
    0x3030307120207022e02060606032a120a020d0b040c092607030318060302130603230a1a12061b0409020406050d0c050c06062b050312010e07020c01030507 68
    0xc551000180e42045c09001d50a14410000d40110404928541090070403248103842202201c0f051910141030040e0b001000442101c10100c00d100d801585849412090302a55410b000941c4802e20251000c08540085000340c3c81585084544410f480c0c025091004130354900015a6400b02c285458491050541b010115280039a110200c05c141d00403036803414a205809410724401e8407000194100d1144022544410001d14803c10210707100303402000c4081106050701d06501d404010005c1110815640344e1529510382ca042101c8083c09903002d0070451003200c0351040c200c182d419290302d5803c0580010042054801e40c0440e40b0300080488000300300680046584694401c4000d105420540d841c0885504003400300c440640b1580a4580b10b244842c050202c984a081c1000340e804d081c0241c01615003445860501007110060400c2070749030090700078540e80c405405049807000c80c160002c01c4026000401d100c4001c1d40001c0349802e810082c00c0028140e1070f0500d060313512100140c0e0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 150142500 1250 150141250 150141289
    0x8040b090f16030b010f0b030a0209060408031201030b1b121b07050604020112020301032004060504090c0e090708070608060418030e01030608031602040911060708070c050303030712020702 83
    0x5203680c841c0402c0201c44100c81c0154203401d003a988985402c203482100d40b040a280d0f000c1400400c40d816107e40c000c000c010f2004000761319255407200c895056801c40650740301002d103168010801d00000020300e5500250358200407007a2255041d030302c0f16601803e0282c2d6143d001050007d030529200e00500000320380907114041d10b4221905d4107940d100c1c011a4101d00044080051a40503007450082e42d050303c1c0e100c9a10311003e00f40400c0003008807042410b0590047e219280050301d80c6840c13081520703150264100c2c441007404c0020614026202038402441984442c00030480c4540201d01d4500790b64051502400f0307500c400340014042e01d00322402013814540c2086501c1055000140c0d03070b044140c01e80f02800b411795980a0140c50303014046080003001144030611005190950124034154442e0454140d0441003101041003900070403011100341000203840740c144407811442c40c008080840045266191028006140000e404844800030b50082020300456941d445041d00c0c0100424 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 150143750 1250 150142500 150142513
    0xf0c1507080906070813080c030d080711070b04090f060f080c010c15150603140907051002070e010806040309080601030c090504150e100606031a09040512040b040608150108040b090f 80
    0x10982650030384503c01e0101508c42c00070f40d04450304002c1001440b09426481d21421507844100907a030f851441e0403c05c540e4003665a001c10707414003580c0503001a02d1000d01c0098030101e0b29503924100c80b0103070000c151005081c0d50400100c500019400301c000c10a107400c2450981d249040c90035041072000f07108460303041241c10304030344803000846e4084500958041c001d0202c241c81090b6090410f41d03d01752a6040039405102a05140c01041462403076441125074065030b44a80300d4038058288c10607841070700300a0034801410b0780001c13860301401301c81014200c0d6514554078551051568814040d00940b40c01c0010284180c541d0300d50408807800c0340622003070001e03590858a54100040c0104038a10380140070030740611a00c00c03c421289000b40c1c02c2c41841029041091748900108215128030400c624194660022006040100110f801071501c450a111018140e001e00506e8040301c040b00396071400d11030780e000d008580c2040c1c0201c0d88070090344030288981c4c20301c0070141e66404c1074400c45 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 150145000 1250 150143750 150143767
    0xf020a080a08040605071d091810090215040f060309060209030d0e040515063f100b03070e10050c160305010b040207030c08030a090c0303020f0c15070809060708 71
    0x1000480c0300f2442007504000551721090706584001746040c00e05c01800d4200c1c0c244c441410f103a2900c41d0040150175404204278070085c101803515076007541a40300386403964103040450402c1c0600c215005600c050042c00c0030304054a0003202c0f6824811041050b8a030f041c60400d202150303044801d0107002805a8000440e0804c020300641c1041840da402540f034000001c5018000d0300ba0b0004010000f80414a404074103d09424205610950490804200140400300c1c00c10000e145107100740c54040001d803440c3c60740788002c080007103511042044100f001004841a0f0101080441550440741c031020011130340d80c110307a81c0c002d40c1680c0d09148603000c881c410905601c0961001c5a114400a1054181c81002e12041e80140a4010040b820880e8190005140032001d140d0002d14041c0001704011142c85a0784d5032540d50344154050380001d9080200c1c51401e2001030050001501c01040c4420581e6490304d4500c10048041c00104001c52075442683c1d4034800c40b21003e40081c15541c075003241 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 150146250 1250 150145000 150145007
    0x501030308090706030b0f011d04022107030212041e15020d0e0a08040509181902090601020a020a0b0a21060501080a05010609030f050c03160603180807030f020a080a 73
    0xd641003102c900c119040022101d00c280254140c020001d440d240c481180d243c01540c0344071340540c8628004211854640d03841c0c64500c050850f08181858074260300f203c2c02c591130114480a0504401c05004101a416001c1201c0d034060b086a8801d180304910082405040c0c01d0748100d071801801503130b080742e08039015103003034001d01150381802a04224000442200598424003a030780207003011418003081241340b0f0310050307070b81e880791500e85250710b40306094110a091100300301c840608607105c2e038101019030500c4518681c2c068002e0006160b560030786d400244a82c0130b6031242e10540907001900c901b02c0c61203400a0a50b4510010310308074801440385140b40901034901405000640b2580040c96440c0903020301d90407900503480300c0c0459401c50315031120b208124201541d040c070a071103406103685c0342000703c10400540c250b020402c450406000509998a48020004034810300346044086824a8103d80c01c6550505003040c4110592a0690400c1007032600944030448c082001c0b401e9540 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 150147500 1250 150146250 150146267
    0x4050405010b10110c060c1203090105010f05090405061b070506090705040510060c020609010306150e0a060c02010e09060307030203030a0c060f020a120b2413120b07031e05010303 79
    0x41115004480c1c1c540307003000c0703500065000c4c540074164445500103600e81005c40c001c01d00b50840d041580e01c00e1008481c4048103500542d00722100b0381d5580010088d03100e003a60100d010300422140240e44d800c1036110160b41c1c3c107001c0d0400b1550520000c2e11030070b101c6c168045420079907000e4107403480e84c03800903c080e807036580034400c050240e800d00c40050701024900f100729083c0d0b0a1902e40707404854864082c080d09070000e400040c189603407444007084480043d903004424003001d995080030010040188400000340e40d2101d81400b04507a910380050781c00041c00300394018181c8a50310690742d00c000091902801c0c2d44065058000000c106604c04d51040700210002d003c0ca00c18031140580303482280c107c0c1b081402c000000b800803030707408135211103940098425610091401403110a079100040606102d45078900d003d075000650808503450580c8207400600e44801c06200003030641e1108000301070014442c508165480503080c9426030700f44a0380b000b403c2804000c02444d03841c0d14000d801c0c2c01 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 150148750 1250 150147500 150147521
    0xa110412060506041404050a03052b0c09080606030307020d0510053c010302060d11040602010e01290909030f0a08040212070b040b090d02150403030f0c0c1208090405040501 76
    0x34100005c2401e1a44007100260203503a2050003005101040c0e101218ac2e604040542031040c42801041c10710854010311750803070340c040c04800040c20f801650025142c050b0b143c4c044a9031390450002c10405540210581c3c04458040d85c280030840c0c56403820758242a19849051106c0e86483c0c1801107070006103042c2402d800c6411407820100300c40041000c1c42e482d181c403c040d181c0403404018001030402501400e1603039400c40700412000ca540302d590072960010b82054006039034a6101400f66902409110585800d4403001c0d4a06007000c0340c0c8000420034129118094511710300802e40700c031801c00840c1c000c41980b030f01d103903101d420301d5034002c10004080c0e4050341705a1111110001e02000402c0703e00480307840380344840c07915141084840703490704040301442d40b0a100c20b400d0009600d402401e10700350300301000d88603515400d5250150100c1e15036030508042140c40c40207a800144c40780c04203026100a51041c140310103103450461040d100305052075401605080c01d1200300f000541101d071001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 150150000 1250 150148750 150148759
    0x420180306040302011e0501030507050112020702030109080a020115081207151418060f061207030803091c050c0a0201120f0e0109060b01020313090c0509060408030904050a0c05030a110412060506 86
    0xc000076110058480a02000d00702f0303000b0000401066008120041da00384a0482c090b00305001070700003c3c21a668024260740341c14002443c015000e60a1240d01c903910f05180c2e051101c01d007058080d030b6807010b050004440c01c00b40000e00c2400d1100302410511107600701d600c20f0040360f83c003070590f000c41d01007910007000100c000384200082c000040340561041c9104001ca414076a076010811a40d48090303541442d82d800758117004070114143e0710056200e54510b02c000c01081160350f52240c1c500803841a040700b0000148010003035401c0c041002406079409103451910450114550b0009211003c40500902e00d00203080e1460720040d004071304e002e4040d15080010303e0f92a00107a880c0d1003103120880d120141100244802d0880b03901c22020031034903241c005e003481e5400d004900c0d9540301f900410019031000c505003406d85024081c1e1076001082080500ca01580100b015000d0301001d00026040c50301d54421440304131041e001c1e50300610784041c0206102c4000c0c24500c008000544526005 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 150151250 1250 150150000 150150041
    0x70c050f0106140d05060a0908040902040305060f0106090f18152402010b0a090203150d0305070b0121030e01021c0e150c070302012a060b030c042018030604030201 72
    0x6450040d4480d118117800c0b0019000c079580d403402d40c00082082250454075104280404550b150103407002d4000395205500425041c2001020043c0703a03c4d05911203401c1015015052081c1c5454a0302c000490311885c02e51154031031001c4541c3d02a00061084008040b4201400502407504080d840120139004540c810111001c0c0000c900742e0350b40880c1107400c910b9070101040011045c0c1c0c01154009844800640090b40d08000a604070302040070503000680e0109061051042844c1020700401044807450b01210002c40d003010426107107030b0050140b00d210740740c0c0d48681e402881145105c452100c50300c410000303240e4000d071031014a4400b090140000c5020700b2000102803088a802c02c03401ca0080c4411440c41e401111901062071b042c2240e07104284800c00354010f1404c05407040c0d842400c0110720341e0a4a418549440110507545100c1d508016807940740e40070143c44850100e030a50034031036440f0b100d9440842c0c142c0c075400c0031a40500c0703450100414540d066000d01c03c0100c080300c2c203058 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 150152500 1250 150151250 150151289
    0x61d031903020d0c0c060f1b0f020c09041110051809040302011b030e0c030303060d02090601090e01080a021c1110020309030601091d16060305060109090c0903060c020d02070e070c050f0106 83
    0x84400d11418181507245000205070500e00420127003228030b03414412104022083e801280c0c016078151001c44000140303114503c03444c600040c600418184918101e41005807403151001030388a10526207010b410540081018140300390400d20303012001100d110b61704902c040005004040811500071a805106108506c925005c8102ea0141703900406140c2e01400315001c001503113902030b01c00c9040c001c0100000403807070030134514540200010b1002d461820030500510081c0351101d0998241c0c0320200e002500007031400411038400980c15036205040002d4801c040e4550701c0395180255040c810180002040e109641000071801040740c000075014082e4541c0307a603185801c0745640301d850703c1d0007410b114040c825800180d00441c145081e1100503070ba200481c0403200104018000100b4026040c4180116805031040744030a504c000c11942d007084c00029140c052901940303500b00010740c080740c3c100e8420070054480582002c203440405034003070003450090116124403402806403801c400d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 150153750 1250 150152500 150152531
    0xf2916090f1d150d0809011202040303210204080f030c070b0a2001151202040c0809070501030b060702030102040e070806060f0a0c0c08030c0307061d031903020d0c0c06 74
    0x101200c440c00c80512500140c200c0885101400a1218081c01542c0c00c403d071040d03541c40c0d03490209038002c171101541c801d2145e0004080380540e4003e101c0f41030040004000103948807800000480c2d0b010a80481c40c003440050350003178825a40042c0c1544a5012250340d090800700080c601b0313042c0141200d0001d65952207080c001e001f120f55002c0451003180710f40154803402c00005150005580000400c1c121901840702c0040c42a041515025a1415040c086040601c104006400e860915600e685400000c0c59910303011400345a0400da00d442180100c0c2d1110302c10b03103c0b05c684c010700035503d480d110066200194002c503980b00000b14840049a05400c0038811909840c644200361458500036400680303502d10f51080c212031600d20345000046102d01400074000051810016658901144c00c0c504151400d100e40c2020705403200e03c0e0f2907520480001101d03090951140e641d140320301d045005400a0003080c10a0780004c0c100549d0403040d60340013503031f2540c4910804040111a1031a00c008 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 150155000 1250 150153750 150153779
    0x14030106261603112110050114040605030c0f060403060501090b0a1505030a0c0c0b07030617010e0705010e0114030a0501031e02100509061e130608040f291609 70
    0x190940c02c00b003038811018148444042a010f424442645517030342c0307680c10107141507088825040c03620750352001071025040c10860510015000c5074140035403810500001d46940c44900da81d41f03d040b144100308001d440301e0301034800658100404002c95a50f54603c503024000c20710385c1074421307120840c011810b00ca05510f00000c01c00e81d50780d514155543c0200d000d0007003008929005c20f22400ca40303440b001030b044d209250302c01c1d2841e60f40814407510340440940c0e14040800d1026a50341003210110196100248401c01c9400c00d2910402c90b594080041c1d0307031090301080b42c0d205468008100200404107800081c100c80c46103918040d180c04c11403d88a000d100110000c0d4400b0100d03a003102c81d10b11600142c107170110002c2000c4e00d04911040c41c4881c054007030b25031010200e404640b2011042e10000064003d101500f0810fa6601d0181d44020b0341d010500b030300602075002c94140b0001004050030b414604440b405034518541010042002c1c2c0350701042d025030001e00d400402156451068005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 150156250 1250 150155000 150155003
    0xf020a0e0319081c0905010e0d0203042d0b0c0d0f0305040b07120e070603090c0e010803161a040305031f050d020607050f0a2f0a14030106261603 64
    0xb1180e044a5580d10081503501000160341c030240c00007031100000703860b1300c03c811046120b0300c00013800e2442c090015040070202c0004500b5500180310410002c842149184080341200242c2405c0f1200310355485c1d2222400d800c121512000410300c1c100f0b80c00c0000300038601c064280c81d50f61425005100440960b042110000c10000d1082c0c040f0303213900c0c0901144090001d0020001c40d40c459008070b428034080300355201030f00190f150701e581d0040c0a48060420054198001010350b5507042c400d4088d56446002e0300081c403d40302d48075000500207000f03804c850040001c20000c0703250519050041032600291501610382c44000404209840d49180c9003084170303c05440c080604186030200f0425410809045e81d40d03000f0680c0b401000b00045c00142d510701d00c581000380010f0b03c0505210012070034032114000040365001103044543d122040c0008448600e010104105803010102e40504429404070143c840350110111151031041c1150000c0500c26080328440d040000325040500700c180700 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 150157500 1250 150156250 150156283
    0xc0f07031106071a1509180303061504030804090618140115030207060216120309030c020607050f07080309120105010308030105010c050f0f060f06010806090f190f020a0e03 76
    0x2070300242d0910402901c0c0480c0a903d00044203c0c0c0300501c0c100901c0c003114200b20050b001c4180c0f090600d004c15046400880b03c0b45407201d1010710260140c0d40c0c1c8005400f0300e00c150181028807c0400c2140111405150b0114102d034031961f03240d140d84040c24242c0034594080140c8170088460907458800c41002c540c1c101500030319030746002054030100c031041e8040000c01da02040014007003000ca00007030038600303031400e48040d2135021130070201448505100a8010542000c2c08040030a83c4101d034001c000e5011102c0540d5500c4519081b4580710760070042020798007031810300081514012014088000c015100b018082159185003403c8803400d0100526107001030005100d80c1d441113aa01110f1441030040b1000d5401b0076001c0b40c500982d03031141815176444107041012490301c0c7c0e42c0c0950030960a0038548000c3c00c0c20000140781e010010420b00c540c07041d003000600a840900b4076616413a04551040044d90134215a134000395002155a9002c0742910724013903018200064120010110300c603 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 150158750 1250 150157500 150157523
    0x5010905030417030a120f02070c140a0f3f05060405160e240604030807031e3905060603060106020d120f061a070209060105040b090d050a0c0303050c0f0703 69
    0x4031b03580043c80c0c0304111a8286034244004400203500c80d036100f0141800100040700040d45104124801c0c0d820b030040041609460400c02c072442012803000420388421a44030b1004013120714038907204a554603165446640c41000c1002e0010200d44540524001c0041d1501c48503a02c284010105035840744840310314105d0000b038614002840c100100101c045d4066481101e40c800055a03034010f0303002661482307800101390040542002056403046c0d4861609682a89010b1025060854981c0034410301e603040b402c035002c5d0400c070714850040320b01c45082122048800d800d0880da5110f0440741d407070180c458580081002400050420074500040e071b500341d007048409042002403c207141c1c4100794142c0310700d004100100c1440306009540986440240c8402e49401040900840a0109414071408000911080c083c2e9030480d19801c6040ea510101c2441c1c62034010300c0c00389138040c040e00200c85c3c11004410503610500600c403841c0a2000c4071021404e401150792554114400180781d0030070b41 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 150160000 1250 150158750 150158777
    0xe010c020909030c160e060307030b0f06120105070f0e090f191b080402030c01110709230a14012102220501080c0117060a0302091305010905030417030a 67
    0x544440b5840001882900d050140741d208580c034104000d2003c0041142c1810144004400e9a10b5103910480c1280209182c07031540d1a06c0300342204c0601800401080b08002590301c0e141c1e140c4416280620400820082c58070000041180410300c801800040d18201c5c003460918026900d0350103030300032406100103904c980340c1c111112000101440c12250715081145e00c2150703501c114450020407615060f203245024070415083c00e18200240f418883e000340b80e021100400607409080e00d2028000049004400e86100c036000e0402018245102000342040348098090300482c1d0883c0c50400d2801450b40c80b030810350102c0c0d6075192107226044504001001603d8103804c1d08481c1490000500c0d010b4403e16034160503110309800c4115594819000d40229591042440b021807109007094881810100300090000b11581300103407142107002c1c040703440d01213640c000c0580b10f40c2c0071380208007156551070129240d40003407240d41e42c5090103a1800c0c40c00c503030200c00c9405c050101d030381d00e21000061 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 150161250 1250 150160000 150160009
    0x18090203090a06050106031e022703010b0402030408090909030f071e02030d09030c08010608030f0f1908041b0501050a080403180e0411040606050f071a0109020c010b010e010c02 78
    0x14000c00052040e00c0b101030114650344a1240070340b00c240d50201d01d10a8009026200702c18880c8042001403040203c10800c0d000c00400c0e421900400e2503003807102e01410006409030192042c00c95000d440001804104001000180015035050755940c20603a101c0e0103ca440f070240030b059201060007000f410002410410b45a07003025601c070040603070481036401203490007102091100216101460600070300c018045004001c0ca8400c0081c400340782002c4116880e8041c5541d180c0d40850041202e80c945045001600e070800140902800e00080c2d461000b41000800d4409641401c802103561040c41c2600d504038003991411b8452901d0200c061a003121108401041a020803140410100182d111061003000900006903a0b480b5400c25003081f9540da400050310b24400e5181c11001c118141e000801e13038995030b445c0f00e40386898900f141803e002100268108049075a025400840d994410758082c20303c03079545000802ca00314041d4019900d5503480002280402d6540c02d000d00180307030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 150162500 1250 150161250 150161257
    0x11502120313060c2102040f1202040e01020c06160507030504060c02240c0f0109020f060c16090606030b011d0f1c03020307031d092403072301180902 66
    0x16900b42055181607a803281c408a50184002e0f100042c01400d40c0c00083c10441520035000003102021860145803000b20003101e00c180c80f9940700070381ca01440100395503550f4041c48030070300701c02c00943d070354110700f460642c86440c2202c034005111041c04400300300d04c0c403503030035604080da040d281c9a04d46800d0201c252204503c0c450100d901908180e02c80d00c240d0705c100135080340242101001a168141046450704000001d4103150841e854008510f02690340d80c20300c0c4001c1e640544006955109540d1814140b100d00303001c3c103100c14000c40e4001209000e03607007d04101c43c510754003000f01d55400001140d208000e01d0882512180403521904185807034080c00143c40f20080485086c111110010340080d000c3d84801d0b4056000400c0c0281815000741c0c418801002c0d054840c0c620807035005c0024407040c0050100c1c0355164210b11401701c0001c2115164020700c0300207007100e4200b0f50b1205442c144800404041c07030004076410f018601c82d400388450011021401d01040d2001e414218001d00942 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 150163750 1250 150162500 150162511
    0x6040902041e0204060314040b0105010f09080f0604140f0a02060c010e060a0b040b06040b0a0c02010903051603060f150b0901030b190501090e07020c010f0210150e0115021203 77
    0x41c0da5404001281c2e5400c0750589031400710042c00358403249008030103802c4a800740b05c00e80402482004000000d010b415200703054400908114181221000b03003154409410b42010401d441128036002d2855070018180c0e20a0784104404001c030309201c01d03130503281d94081035207040795400b4480f05070040c6000009402840e8581000060700ea91801180349007807015940340742d41554070801c131511410a4080d20604000c107640451405141001500861081060120400040c001d91200b16845400c0c14001590480c08850b803825400607900c030102c042d8482100c03101d103003081030ba0001c0c0c802c0c004c2e410081e260071084200c3c03500d48412003080d03500660b800380c10159241c066558968903120f44009544464400c00c031414188000504100704a0b00310214034607401c2c00f040820b99001500c459196000c0c07078580d402ea0200c600603490104402810600f441c02c00202e404c01800b8010f6000c00c480b08604241656642c03015810154440c40701c0c20300058014031a0001071401441c01990081c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 150165000 1250 150163750 150163759
    0x1b010815030313060503041b030308010e0a060308070506060109060926101b030e06010308160309091d1203070f05130801090b0916270f150501080c1206040902 70
    0x1142401456000e070f0a400400c049040801070206210511880e881c0c2104c80d510b420203101d0941d1405440e40f00144592900c4854100004010441c260003110045a200d0601c54407490207180c16504d41008580c0300c1c0c00175140a0740000c683d40706031802800ca0300b0840e6a2038408121a500d400d850780c80084615a500c20f00d5284c5203c1c8410b4400e4082030003090707110b40300b00c07002c1000040503100300c00c01c41d1449070300642c01030011503502c1040f60094066101c1600c6808443e15042d80c0c003092592241c0d6020303180810038904401c00e2103a107503110306102d050b544404041d0801d5030f01d50105880842c006102c0026456089000d9030003441080402440d2000c2c00e583c5615090a4403915074048480700c0701d00d07080c44003868081101c103c521984200c1c50a40f00d00385001009110808128816048003880720454580103560102c030302d4603101c000c140110f40003800041d882080921034980000d4907080010060706c0b400f03007a40c14181c1d11802101e915152041000082d02c595402a80d00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 150166250 1250 150165000 150165007
    0xc04060e0301061e06110d0912061e060f0e010e070e030f12040f0602031905031e1e09060f0103110a09050a1b020a0302150a11041202031b0108150303 66
    0x12074581ca000034003d5000d03682d080a0107007807117402000b03c0300303c3c04501c3c5030783e203c10301d40040c02d50001d503480e0036030300304801150520000d41402c1019068081c00d102d4000c001440107800306507240c0201080d11a001142e0036219612a084034024000344a091030181d4900d01041200d071190807a43c0440d0b00040c01c440e682000940b0560402e540d80842c5543c16400141c1002100300081d402d5000b0231680c00950700381b010314449103261a170380000380c0c4200140080007031f44540c000c0e000d02546411500710f41c0e280c2e240c06204503040b650540403954151038440009400000f00240041c803410a50007000c0a992a40e0f0300c0c5c0240846000c0f501d0b17440700d459640401c48540c01e100f410720034041000081500386030320310404038030b00501d9032510454010842c0103021940008400e000c041d18480907000e5959080c404500038400e440c41070040c2400001e00181c142d100300600c205850086040e905001110005071040b981c003042010301065100002480d000030400c603618090002509603480c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 150167500 1250 150166250 150166259
    0xb0322020a08010912030e030912010e01110d180c12060906020a050a0906082a0c1c020c0405011206050a110a09030b010510052502030307150506090c04060e030106 72
    0x107182420b0707045282d80743e5441e0081014081030751405000c500d6030742001c00030b4400b4810242e41320b01c0f0300301c242405003584800c02e02c100d0401f580718200c0056502c008000300b1100410f6080300d580024414403400781080002444815030415000100c2d030b000e4a40303203100380351401840301d03401144003e982c0c0580c0c54200101084050000300f13803420703996413002d50761100000d0203001815030341c001000300100003042055403003409105042e4255a07904034000052050000380c2d48bc0315a09505015008102c2503960740326480c1016800425950295482c290440c0d0600003140c00034440c0c240e00134001003021011a0a03a4042e030380004540c0004603100c80c20707007010b082a501040d207120019840301d00820500030745000417030140408079210104003454000082c8140130340c03c0602c0120b5892403200c4044c8208250400c45035602409417611425507003402c00302c0d05601100d500c5c15a061400061261910b00200c500c2a800c81c44031500301410820100c0e4285241450079406642e00d01000c41c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 150168750 1250 150167500 150167509
    0x30403031101060f090b030d0801080d20030c0a0b160c0f02012607120e0304030308070c17190203070f061104170609120307080601080703060e07080709050a0b032202 73
    0x1401743c92809008150b07044450240741c0b610850703001e0002081901c900500c031080c030105800e00c0031031140c41c0850301c0b04080790840b4408903064203083d405100019481a400700e0204031910046d02a40c4800d040350b40d201002c07242c604072545030038000b42c0d89020240001d9088080804118010b150400110039204100030006801c0741c40d511049800c0c0701003050b025840b180c1c0d02c007444001d800c184890309940e1501596400755010003801d000b51900000e407001c0c401e8509045081d00200c552a814040c5800d9011070350110a105001c0f980c8420540c079a50700000846040c1640002e003107100c0c00b4561210401442940c0c02e260f03048008000c0044c2c11150b444038000c040070040d02505980c10846541c0e8501201003a030400041d6051080013200364102c00e0050b8418030a0a18070040d90700d24000307d00032301d030b5030f00442e2407011402d080c0580294082000b6228050a440e038528142d2228200507825a0501c902d600c0d81504000182203000503007600009081d06000c2640510125400036 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 150170000 1250 150168750 150168779
    0x23010e1801050711060907050609060c03160c030b15011e110106030305030906011a0714030d02040e040c0501080c0417031b030715050c040501030b0f09150111010e03040303110106 79
    0x3c40016039080c40a042000007070005942180aa038020042140303020086035480c0900701c001840707034001048000a00c1c2d0309204403030b41348031405000d500d14a00c0749408802020380e40030603192001c0b03030f400141e03010146002200c91031005840d15407101149600141c6900c2d040317a0308004004a140e01403c1d035010034010000918880d440343d030744918198000d1490408141c0c4034040c699183c580082000001d00708640102e07410201200c2600e812041c002c0c40d40c4140d10399254194400280054100d202283c00c5020307511030003203030703c0c0b40740d5940046411420a440742d41549008000402c0130700180614000e01e82012810f803400c2c040f500050f0144d150600700a4446c0f40c2002070704204100700c0010b00400452980000c0180d4101011044201c1c021030154605050b40d4681505059558480101415900503c103058a113407104d0034441c40308502080301c2c00704281100d41084500c042c01000e5904020070300039401d01e0b140d600c00303c81c0700007103002c03201d640d5507500000f065003841104d40 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 150171250 1250 150170000 150170011
    0x40c08120d0f050411010c1712250207140109050a09060810021215041e020d0b010c0b04030c03090e010b13080102090d03110313031523010e180105 65
    0x1120748841e08900c008080d41d02406082e103003545403030208400591201580d00d8021401e1818000000f0549006400705052074150768480b0070114041102c0c1502e50885445501c4001a103078052485904c05102c0601105080025800100051200da129603002803400d4005240c454142507540021030403d20031b83d005090b841c4e80701c4d4014880000100003140e98000903610461600c40142c2d80690040005018640c2c0d450800c0341caa20039a446400503aa1601c40000d48074001111451402c000e40c00950790340302150900b416885158040d04d40880500d8219501d410720b541d40790783c02c594100503020b08405005102c90049106601d0081450180800d001c00c144c2e11070511440c0001e6155552101e0781aa0041000700c00d161540c0407000004c1c1c2c3e040c00c10308007000000c80700300d0641c081c40c0c2e010042c00c2c1c80c80308002f060041c2004d035010006952101082002581c00004414003071007500c0c544014404801080341a40740b265030782e8020741c000d40c80381e808980007410f90b0955800313499 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 150172500 1250 150171250 150171283
    0x5060c01050601020f0703150f0609020c0c0310090807020607080c03030f060a0e0103080901080a110c070e0a0608030a05180d0503031b0319110d020a09080d0f080609040c08 76
    0x400c0700d1541c04020140c0d0324020380300200070403483e652303491030100da031800e0701e46015444002c5018280020f03080500500f00c2e503070b000e6450340d481002c0d03550350309908001c5502c24454480c0c00c1c10341c15400d01c2020000c0360050b503258a001c01c2c58091011603403009404841404040100b1811188240051070040b1501d512640b503508096040050300001178020701c107403020081c01000064003c0303045070f9164030300b0300f4440c9031955404020401170640d00390a180285000072400707401b050100c0e846046ea8040020718965450700180031007110000d01810441d43e00030840c4505990290025291074603403010300c0c2c07403213000365004500000c1854904603056440030003805100d14810480c04034858128140d00d0a501d0181d420054648800c8880c40d1102c0e541c0c0d440519491f00c0030120b8520311186a815559540c000c0c0780108604401e201d003101078000c1d003c0030035039548500000c0307091601c0d035a644501919032a0810403255805030048410080d030f40d0000441a80500c10502880300009 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 150173750 1250 150172500 150172511
    0x40c170a0605060f0604051002070834120b040809040204092a0e06070f050708030a120605100806120706080a060e04051002130e04080702010e0f0d14010605060c01 72
    0x340c601c05076880038110740d1180c0c1001c1c90225040d00d900302520219142100c00c601180d50190041e820070780d058006040c240180074055160844410032041ba00e040341c0d040c0104003403003100030240c0302030358082c840c0041d40038544180854001c610740c2d074220b40150095032134401880002002c0341d02c035a011441c590348400781303010385818400c0c00034150759004a500c0711480e040a0000c203c1c0c01005c500c1031280c0c002080b01002d103c07140c03d0301d28440740e02c80100c45140b031702c8003401a565008482c980000800308182c2ca80c40c0f188500640c800c03100043c14050000a000000303850b441001001d140d041b05a400c00c1c0524000100100340090880c1c0d16600c9050800c5050b1070151005604404220124030051000140300000d8404405015140068070f500f1032400111030312010390300007200c440b035041c1440140065400186880c1c1d100362140c1c0d05440c510020b001200f504040c1d1154451745084108001c10000304d10f00005052040c0002101c1c3c0d11040007405070740003640800780d41c0e9500c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 150175000 1250 150173750 150173753
    0xe070317070b0604020a3507020d0f051e030a0b01090b040e040602090604050901180f06150c081606020903011107020603150114070501360b040c170a 66
    0x149880d00c42000d0314004038a04011915040104580500568007860b070002d603900a1602c00d0701c4128540d0401d0010f40302c0e20300d2112800300c5001c00f4140098403048034030041007900780001403410f040005600c540e088a0714007403058550341c00c0480d1099181e4203801c544181e01c4010301c011032007510302880005002e00703410001404082590404113400070100802e00a82810704502c9901660201d000340e44c600500c3d002c00d4541c0100d40c480ca40090758400081065245400f0202c603403103890f0800c20640c00d0000c0800d065130b6051003900e215081c0044441c1c94684145088a840c90003103451038685045400e40d9440c1c03d00a00302a1691503011415075018176081c090a170048a4000409051400c40c1c0c0001c0c00d05c0c800900065060310303403211164041e901071084001c03000108054240c95203500e0402d61b02030018042c25180e10180517000c1e908503000cfd240031040f0940c1001101c92040c0c40e950340d402c2c42c09400f43c82643c1d03c1504020001d0503028404004120302c0b1200301038107114240f03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 150176250 1250 150175000 150175013
    0xf0507030f0204080c09060a050901060909050601022a0d21020f07030503031311100c050616021009030504080d020c1003060b0708030a0906050f060f09060916120e0703 74
    0x501c84108075401003200300b21900002034003c0e9810000c48422410780c031a800001e511503015480070740c0002d290740c00000c2c0b598010188004641c2480e000f0300040c0c3c1e415004986521030546590441540600300d540401c9d400303d40c51540041c00b03080101c0f00a41c5e03485210800d418607209404503002200550381c8141d040c0459000541c21000500c00182550303100f540b240030080c4010aa400c2d025404020f008440000c4a808200074096285c2d13514034040003415800404000d039620b00c10600071403c60744084018a402408942c0074090f1813030911145005461480420303420000c01340000300b08103005000207035000c140340d001040d00c0044241484801c400c402003000a0610708a420045602031200700d804150b40051200c1d907a5884500703400042410000107044107242204001071030030960400d50040000701c56854440c2d4901c2c04200da0020101c59043d00301d803840c1c6c041500c1e05c000e040007942800840c101250911040d020482c11100c2d000340c829416070185404100f403000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 150177500 1250 150176250 150176261
    0xf0905010b0117190203061f0e0f09060d0201080c0d060b120702030a0e04270f0b06030c010210050403020a02060a0302031905012301140c07080f0109120806030a060f050703 76
    0x1128000c00d04d09490226040c01001c034405100c640c00000158069407540882114002141000141c10b03101c2d81d4000c00166610744005e010b4401c138100440c1602d0507402c2d80d07100c0c0070b00401403040704a296004561030400a08010b0901c1e20500045280e00c0990254501034841503129a84070720942e031016140a40280100d0250b410810501c45000e51107142c10740c03031079001c0c0c80200b83c001c14501c2c41201e2400e400807500800d0000d185d074004000401082402807401a01c24181c40e807628000c25459025a640d0039015912950300c049040700300c5d40001ea4481d0090040c0c5138810754940100300e20f07600c4071080c140020703400010880e0710450401c03180c40000071040300700f200398100701d0342c03150744110f0b141e209003150042000000d41d0b80c400d08020a541042024007038036005141c28480e9501070901038801c0901407141050f02c0795905206141c2e00a4100080c5940003004100a6400107400707020943c00d80107004a24020520600621050205106c00060310385401107009080780d2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 150178750 1250 150177500 150177527
    0x11070603051e101a040e01060e010e03030a0f08040c0e090307060609060308070602180a0b07021203070b04080f2802011401081b010309140a0c060513090207060f0905010b01 76
    0x142d10050002002c08104103200fa1802c2c0c145884d290035402c030391801039002c2c5910107104610108008150260300414140308584280c035201040b03902d00301059164010031501100141081c030002110600c03c4404503005809505510400c40e20f550340c080f41e4400c102c40c0303480290f00000781101005098072503840184903107030041001c2d900f156260320311071007120300142405130040b07402414103018002904000f04011f20780441141c0d61810035201d50485041030f071180c1e000e0341e03d030103e0f410080101c958096201107042d00315901d5a8510360707150488040c80518103002e00803225510b002b44804110841c00454001d203000102c0c10090030b550075150310440304034605004100c035403000200c0d038580320b8005890b40c00c00b07807400c00120020080c000000c2e100100c02c84581000002c082062030800d80282d80c3d500c035858803080d0555552003181000c230450b01414008103c07050700c0341d000d046454452440415040c61480743c0e4030a88280c07210a403002d96403682c00400c5507801907441140749 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 150179856 1106 150178750 150178801
    0x72705010f06031d0307081c020a08010e1501080423030d05161404030f0204090b04060b09150609040b010203071b06020105010b0403020d11011107060305 68
    0x901d03151152034082442c0400c039080c10f5454241c3c01d502a01054019443d10405650309003650b0302910b01c5601d0303146201940280d441c0345000504011801c2c0d5a0035629505040540b00c40e0100a0640c0107120401c0700404582d0b40c011000960281d0042800407490b20300760242c48440d080146808000d0200280045007620359510440c051036507000700500c5007050100a0b1640090300c50b40c00340c0410288000c10010725180c0a2840d8980b010b0801f00391802d0aa03103503a41d001d000d440845140d0b8841c1c0c855500b81c24800c81440d4861542c5404000451011000c90743e18030a01602038012500c2d0b449619560b4002c00840d95410b03070003212a50001c200308090149034009004510055092400029040c1c580d9011b4a0a0340d400500e2122200c100c0d03a105194158406451414440500184e0411034028000140144203039180400c080c90140c0c0002e84078010501d0001c540d = true := by decide +kernel

theorem cover : BRFrame.Cov 150000000 150179856 := by
  have h0 := BRFrame.cov_init 150000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 150000000 ≤ n) (h2 : n < 150179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
