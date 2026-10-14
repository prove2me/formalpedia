-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2570
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:05:40.601754+00:00
-- url     : https://prove2.me/submissions/1808f205-7a31-44de-9870-f027fcf4d472

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 462050359 ≤ n < 462230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 462051609 1250 462050359 462050363
    0x10905100509150d2a020a021003090f080c030901080903070201020705010f11030f04031b0b090f0301060f0806060306011403100905011401090c030c05040e010b0913050a0b0406080307 81
    0xc1c241101002000710b4200c0c20700c03101e5060f0030200310003000203069000340c4d080f802411000210200c9200801c10f404898058100c0840d0805a081d0b401641c9100c0d03c211400071070716020980c00082d050001082c0d052050007000036200040c10400401e0100141c080c0c1c42090301d0320f0301706035203d461007a1039220b0820001d0058100420a01035036005004060585800c1d00d0400c3c07040d00c411030746600c0c59210300c00141245401081c108100401d50780907110000301d522044040034034016070202c0c81d000f0f8100b002c0c4111140b4800d282e560f01c0c25030000004065402c81107240350755920825031241d00981b0014000c1c040c8000100e400c0696034141008404042d000b0a40b13022900403042c01810f031140116100e5498076121944001c8601c1e20764040d20003107034001440b44c01c3c09000b40495525601c0f103000c0c48000d03c800c21403041840c5d20700e411079801504181d03403411a000000d0a40c2c1c03d01c1640760000b4545402e1105042140e8000044000e0540f420043c40da08c40340c0300c5949009900300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 462052859 1250 462051609 462051617
    0x121b08060a120c0e1e0106020c090a020c120901020c0612071709071404020c1606081b090409140709150b04030b150111120315060405100c0c090603060b01090510 71
    0xf004020004600c49512446070303105c40441800c0e40b094110311079801c0e44200d0040c0d208020001c181d1a111f22602e42051001604501d42005a680c1c141c8491060205000c1e511000c00d8000070303a4024851003003d0440242120394501d03807041d503400c4d0715106548020010b200c942c3e540b400304900c01341722401181c01400410509141040310b81d1030141201c5210b030803540030302600c0741070340007006440010b4100f260b488284ca0b040100080c03034000018000e26042096240013003281c90038038201c840d82202554041040c0040c1d040081550341c5501d85807085109031040000e001240b6031000411038038143c4680710956850503880703420b000e40c1c04042d0114405030045809001e04205007100803006040103207a400c2ca202089003003120b0701820900100c00001000242144035407106940502150007500300b90800c0c0110300d544042103964424001030039a82018044100700050090214403420b0040a0b100c1c0b4000c8013a080b2441d5240c00300e188001c012401380780400d583c50142010341c3d9 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 462054109 1250 462052859 462052883
    0x2e0e061f03020604121505012c01050d1e080406020304030c090507050307210c02100f06030f0212010e06010f03020405070207060e040939060f0f121b08060a12 70
    0x11780002410108a02102c0721400b44160358014525400355600034510306c80300049000c45d0b40a586207000340552142e40300454000140180c0da5445840c108042d0000c11031181a201c0c10405046908500b1014002c440301260002d4410303070020042c02687d01c280c00c0001d080f5950380084054030070684910004c1402440001c1c0f205100d40280c4c440007030034141031840c4012040d00340c41120b1b40b4080390401a0405185203100d02e00d00d0203a003070031a80c140c2e01040b01d54030310745840d000e141074034100911584a1030b042c140c0000c403d40000565961900698a255a503403a9880e401e09061200304c0c0203d081070f0014401c64000301e101d0040f5026501d51440f0340007044100802001d680c07204641c2655540707204500a445030400d80380503045200080b004042400240d10082d0340e50b07200ba02003103480307050054240e83c0000f405a0b190300b541070408208681910900141c420507001c80e4595007002032040d0b1607940480c030700b8010300c8141c030384903c00fa0b00c0c0d101442921410310f00107048080140 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 462055359 1250 462054109 462054119
    0x22109010c120c17150d0c061403040c03062c0601051809061909060f0609181502160b040c03032c0d020f06030903120c0703022e0e061f03020604 64
    0x8002c5030744081845c6200e04003540350381c005003d41c0c0c480030040d10b00d066100390a01c00c1c1500a50461509403500e190b160643c5003d5551072481c1e6194003000b0800c0e500c510548018000b050480580903c1880703002c1d00b440c81c4030304900d0b95408244695803240c01c0302d401e030b0280c481411411034050504c2e44058280750752404850503006074141040110b641c0e544402c0b0300440e5070752041070368031700d841d00001c0756082c60103540d0011390740c1c40d400d500314003124a4906000104d44608007074294024020252300c0d0343e03082d4460201072900b903201a000c40c605504200400c8103110b0b240b010f991282e100d1810041c3e5440300580c444610160095411001405021107803403c84c0004003020f00c01000284030300301800c08100d03190030030b846005043d4004583e29404034a40c150095219554075202418a09107031002962500748002809214640546501c401c5618075046d5110040d501000e00010185080391540e59404584a03029583d0b5008003080550420b00c0c07030404c4a800030141400d081c104 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 462056609 1250 462055359 462055397
    0x3070608070e100c0f080f0c06040501060501021504030804060603060c021c030b030a08030a02090604150e0402070b06060306010e03190b0603071223011401031b0810022109010c120c 80
    0x1680c00b03590031b01042c01625804505400201505d590311406032509041c503160007400c0d54610f400c07007410364200b101e021200c45020030400b680150545806031607030301c46040805c000e10075030300b0150165040060b032841c3e90750005902020325130b11901942c400d00d1500812003c84122001056064100e180a407010550090203950070070810440145000342c0c25000500544c442d6202103190540040710101d550341010494090580641b020f500d01001c2e50345240560740010a0107101d01c0c004000b14505900c102000c248245e0050300b16080c002000c02660410346030207001303c80d4244180000b13001d03030502040150480701240c80301d20f80c910305070f5a040d94416100508801100380100c030340f81d24040034054440511404031500c1032030750560401c40c8444400c0c0c845492855101d400402c884803000690745000e46840d0801a20703894040e00304a40703940300c409034101c0c1c10404010300c0131b401d5040d400362020442c1d6403500400c0c10b08081b245400e0780c00d0700e1208008141e42d003580700d001c0541 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 462057859 1250 462056609 462056633
    0x1510050904150e01060807140301050a03030c03030e06041b05040b0f0402031b03010308030103140102030601022a060f04210b0a050c0f07060b0a081906180203070608070e100c 77
    0x34035140802c10030b468468803611010b090740240c0c0054540c00a0009882e0840d90301855408190409481c5605003404280014228840141008608051601454442d501c0000522044400da80f0070741817900f408102001e070b402d03401e00180c00103640019585018450349200c0c2c0320142050602490328010407000303400081207042100c031113540c10041c80703400000841c0138500c00c807405500c03541142000c06004040b04020517007a0300c108180001c0e6a00061b40102c01c146114100480000e8a41043d00001d1504000c0e5040040841c003025003410740b001800c06d0385e030b4054403e40c049000b138030724a1440e84017003000f5100803c8503000c0b500d0503100d0703004036900100300c5618074038101c81c0c581e0841700c5a110182c20f540b62503a4aa91b041c140c030301001c00c00d00500b0394100510303501900400c026154440c00b00018161030342c2d0a000010700d048258011900340e0014180d0300c0056480718041e008040444014001840c45611100b8038546805c1c15110801e540c2e90700c6420b80d002d0354840c000021 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 462059109 1250 462057859 462057881
    0x203070b030a0e120309070f180c11070b0909070201050403081b09100c05010c020d020706050c0109060213031104021603030b010309060c02070e091203071b0206030c031510050904 79
    0x384a60003c0d0300c0d0042004141100d59141480f645d0b645443e281c4070b41803907107603048104581403403c8100240c204801196800c2c0694400000b114143c081099030080c01c1035140301c4403070103168030015083c40c1c80400f41c4603040b402d503030b0155103940f0b1013000c030708071801258000c001c41d055001140042407030310040c094500910001900c0c2020480c001001641a21b0003800041c00340c115102c2001002e000c0c0c3c1c0550306160000301024080340b40041d403204054000d2000b040000f0800c4041e010094216030441500a00110354441c00114412014000ba01069840c0800580c8044450615100300c3d184100944441880e40306503030703030440c0908001ca030100d04054862101402080d164407450044100035002420802d1400d400c4195400b001072000100f13030400311200314003400e000b0071294482c01c0e82c80d014541c000442d07001800d0b4440001c005e500701101108101e100300001c0700030750160846982c0c040e006004031003000301d4400000e10301400594140000d40d090305240e00500c40040c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 462060359 1250 462059109 462059111
    0x9010519030204030b250309031d1c1b0f0b0d3b0d020111070605100b030106020d0806030307050a0215040902161b080d0c02060f12180a0203070b030a 66
    0x180d1300d4032400303200203040c0c944404501c2d081e03400001c400b502e5a00141c6807682c6050500408085440c042c0000311000c4c1d085888500d0505051415078443d002040350004251280110024908012040b040b607c04000841b6080706404202140c91134416800c407441528420724083c03207028614090000d0b01c5090107620744001c54510301c02c801050b00c20050b280c00d0808070205008131940c5117045050900003066901d8010030510a048001c01c5840c0c0303d070480c40214181e01c1d40600104042e0141e80601c01d0751101000203e1407030340c04251034030210320980e00c56141e5122a410075403070344914503009060b9484404144018100f40b6440b04d2800541c40c441c07800c2c90b50b1138841100740c1c0c0c05104c0040c0c4000140f400c1ca0201b200740d1502010300f000202e06a91070782d042643c100d41e44c5407103064410070310581901000c11556034004030b0310783c6884031a80944500040b03a03c0710944005450503c90103003001c0c0d20064150b80090014a4290020000c1841a1401200300300382c1d44042c1482440e2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 462061609 1250 462060359 462060367
    0x3050703141b0706030b0109051002070b030411010306060504260705060a03050a11071e060b0d03031b020f070b13050a080723060307050a0207080f030a030e0102090105190302 77
    0x1100240300038040c1c0c064521600c030002c2050b81951814141550044002c0c10715011054050766813000090013640da081da10030340f0905c070f050420381c0f410450381c0c405030440c4400400c000c00c00c207540141447d9807034280c030300303000f0a9100e42d4162100d008501414030148440d400c03181540000e1a01080000800d00079240050344410104015031312900d030a80100781ca030000d00c000f4a01070310030044d8095040224038100882039456034440f1601700900300300c8240f01080a014000b80d81d001c60642400106240480345251901502503d204041c42185000340602c00000c0c42c00840c05036440c0340f0f250094001241001000407070b5030061151880500c07849040813819498408100c1e01604030309004000051901000207520680d1038507091408540109402e560713182d0105032600b21020b130800b5030701d60740702610484c50141d881d40b29581c0c91041000e07101326800e0210040800500c0d6540070b000c3c007a00b0300500742c240c2c8102486640011005c014648000100c2007403889800e520f4900035142c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 462062859 1250 462061609 462061637
    0x12030c070209061f02070e15010c0f05010b060706050103060f090b01050d0c090c090e07021b01030506060c0a1511180d0c031506240207060503060613080303180f070303050703 77
    0x190b8400b240c8840540e00c0a0410712900c0040c4d10340035401070320300302440a802c94040c00281603403400ac0300284921160400c0c8010490203400001c12800c010300080d0b101c0e005414845c000c0c1c002844151811441c05100c0c0f403c0078450b026813002c042d0081c403001c409910700740c240300765200711100690f001035104030040340f0400d42d4042c03080d00914075034800d46041d0a045200100680c050700302c101350761140864296101d81c07951045407611003424005101d80d40c40b004544a840b800c0401140360281032100c1e401c00c10650200300704820b140404000126816504040310b20880011000c48062408511210316100e419045018800c0010011803540daa9883d81403031031032074040c140d603a124a014081125072180c4099a0303040b1030340e11070744c901c030001010751a0502c0c0d0003500100200040001c0658449108603601030f00c07101c9002c041d45a0b6a00040d0b01d07900f0503101480e0361032010603c0020440c0c00128074a520703142802901c8031600d180d406a03003035444003000310180325214080780c7c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 462064109 1250 462062859 462062899
    0xe012a03091e0b070207031709010504081c030c0509060405100309020d2103020315090603030c071805150303030a0906140411040f0507020a03030908070f0f0512030c07020906 77
    0x210b01000b03460b04842d0b0380082d2503c0090144000d160030115800348000700049000403440310700510109034019603d514040c012641441540c000284c10310440341c410450a0300c003800c10a0b00071042d601048007503404541198144201c07011a41e109100340428002450301c42502d08041e80c95040c0080c0d2214554042035920028900580d61494480445551039051017000a40d1050074681142f451800c02c1d42e10132003098400e03400340200d0002c0e00160854030b0800480b0390104060003224416655598070300603000c100f94240b000c25007440041095843c0c0e4044031403018a00802840c151743d514200840248040b680c00d603240ca44421402c00800d01d00303450540194040c0c2560002e09105805200581d0030034401141c00516060800400b280d0204a40351800d41c10716021440408605004c00b00d80030718a0b02a252540d148101002c10072400e1020313407042c5c4508182e56040511101070003035070104642d00551910304201366401850300c0c0c0c82941c1e02210090200e40c0780385407203044038 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 462065359 1250 462064109 462064133
    0x606130b0301030309060201050c2209381804031e080711060f1611011a0a0f0602070521070b2505030d0207031707120e012a0309 57
    0x200411038000014028143d101280d080980210300091140d81808080341040b4032925000002c1158100c42c140c6909011142140040c00f883c84180542000e075500540410014041034601c507003a148001d0500e0500464200710030401000103079000441d2030780744490b2500610450800121000c02c4812443c00e03010110340291541c1d89028502d8070f20307000307040226404800880c5a001c2800c0000c030611001e0302c00d500046244001e42903042001e825903001522980c1c080341942051084034000e8440702039010394030b10450308211901da86000c80c6d4448841d03800f6600050300650001c2c07001d4103002242285184c1e209c48a5003094250710401400e002858109003042c420000742035502010f51151440c080d1101d50404903e00341954451360b89110746060042200d0300416410181800761b45c1c642498000c5078940d0000f0f02e04028010601a00c6d56482d1600519246600781d05810520820345160508403140200c5140c032011b61601c1114401010101500d03524100000b40000400d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 462066609 1250 462065359 462065369
    0x2030d11071802070b0601051612020102130e100b0a020c010807050c0102070c0311030111160305041d04030917031b030c0a0b01030203010b040c05070602210903270315060613 77
    0x182c482181740f519500d64100070741090704001050103c80d0f60303200204c40b0030f54000e80c4807003031007038580c16424140d0181c040c1041c076000c1e103a203201000425107600030500344580254040524815210891103100d80940d100b400016400344c41c103803001e94001c0b501c03c0d030840c003181070480c10080039644250990780059030486045007903600805c00c020130009120b8980d04200c000f4051021242e84c1c0c5459030040074810014508000c2201c420325000d0011075020300082854002c0c20350f441040582404010f40e41180081c1c80303c00005041c183c114200a402c502e00c001440c03406a0403c59500d00f0700154000a401d4003080046a5200c4410840055501d110b4000c90b0ba6a605d07500405003103584804100c0d000d98200140380c083d403540803085030b40d1207500020040c0c44241c070400380b04000d10880d92076005110340400380907143c070700000548984401c541c00b0b554818049030041c07038658245146a505544110043d0300079000340c02d681030307001c00054032890405000d248480303c1e514481c2d002c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 462067859 1250 462066609 462066611
    0xa0b0f16030c060e030a020f011b050d0e011401180218010509150d061d09060621012307090b04170c0d060207140312180f0d09050103060e0402030d110718 68
    0x4011b10741c680610500111000002c0204901c60000320010b00d0120a50b514800b0007400140c9007400030459407001d141d040c00301c8020410560320610140451000f0f004402ea01e80f40e1315560a800150f5008072481c0c280c882d00e03040382d2014000012742e8250001f01c2c545038040503400750036618094007006407101509079074001c03540520b0455002042d120010100510300d80d09020045000c00005449401c81c0040d40c0d280c030031440d4038920300c1904100d018000215400d19403030700b0031785083e00c004214001d210301c003041440d19074490a8950316000d100390b05200c1d1090104000d40000426000064070070388094070390090341030700084d103184c030701c000100c445070350100f240414042414600c000b15660600110b2400c1d21044517650725020040c41960400f08085914500304001d020410082085c0da0884080402042015200119074040e8600013840c244001035030b0840d60b00310601907500907014040700f80388100102c83c14144999010710300c0c411254001008800c40c8400500f202074008 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 462069109 1250 462067859 462067867
    0x30d09050d090801140612070806041101110a03170601020a0b0405390f010e060a03050115020309010e091e1816060e040b01030f0f06050a0b0f16030c060e03 69
    0x6005400d007a00d60f003004040768500f82600c81a800f05915664200d401101c450001c00745008002c0d141071507a1b0445c010b03d005070018001041500d0b0348100c0350b00c400344c035412030f104403144c3d100b40d5443e100d80000d4000b80d804501d01d8a6000c00c884425000039040c81601c07038540359510f4032400c0d49030035903040314564850949070040b4481ca2040c1070403c0c60505400810001b01840c00d60942d840c6d101d40c43c0f045480b9440000303aa070003032100d030401e0038001d4510b076100c00100c00041d00401c0240314110004c6280c01c820703900940b002c411102440e0058413103100550500081c0314110b1001092003580440c0c0b011180400748401072201d2180398018031044c65400740404050614031828246642110001000d101e8550840c0c42c0300b1042c181034174002444c1101c0d5004a0191071a0304031064800d1400b44103811118903a00110243d48080d9040380400e60307030300510702c03991260b0a040c1364040300911024010744000600304000e5070091a0000c044206911502c0840320404900300b86540009 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 462070359 1250 462069109 462069133
    0x172d07030b0a050601030b100f0504150c03030c030b03030f070203010221090f070e0105040c02100507030204030c0f0f0b0a02010902031c03150806070e01020304081504051002041214030d0905 84
    0x1c083c0e55880718080c6002c0c841d01c0c00c540c0100f0185024030070032200307000da91344201900c04c1c450740644005040c54035a8100e0528000005001d4002e500703020b0b40003034181805000c5141c02405090b003c418090020f52411072082d0300000760ba007014004a030b040d50200300c1c50f0069802d0501c4405401c84080c014074160402032a0149494003c1c2000046a00416000c00c0403040020b02a411140d0907280030a2052450034120300b052201c812821240c0d20381000c3c400b074a89e250b4007420580333208015900c0c5450325a5602e41008403a03114482c041d145d40f50341481040c00e02c02c0944071340c001c40e00010581d120513500003070030444083c40c100e80c030700e01d00704d900110994107015481c02c900b910f1522501c543c0c24028070645605000b00b80c5000d00c81000300d5448039034820011140103180e1030064408a81c420360b0030b014040421b070782c2903920b81f00d912840e00441c0014800c80301160541d50042150400036520fa0311000b84512141a0900085c4540783c003d4540d40a00e0381c1d0740c2e02c200d02606030b002004d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 462071609 1250 462070359 462070361
    0xe010513060312200d0e0117010e040311120d29100f170a0207050c0306150f041d010c02010e011a040e0705121006172d07030b0a 57
    0x45a041000d01e0405004101240c0d8102d0641e2070040035240802200300e015010000308056800c3e01d44851140c204508841c0f81d00100038036020100340d80b03c010b0303200384c0000d5009084003802241d2901041001060019010340b8040303900103544425101420b41c0180f1100190b00074034004010980c60781150702607144503201c500f034402a030440d8645070b2082140410401c01e010244501406515829180b00a0003003048414108581c0714000c4641f82440207000a5000a00100e0f007074400c60030f002c40c05150124907284540c0c0741e2032806800001d000104810030a0035914a6001980c42c618142d402940c9448402c540001c2c100208036000024002403c44514106582c00340e450b15005490f126560008611000070444d000702d801909589160b0a03c000741d80562b40c00748044550b07205404c004100d40001c8020010108007442d5a02c1c41c6450003a281c4510000ca9000411383e2510b03c00b10801c0048201203032429840e942021107401441d04100740c2080c1c0e801e280b442d0802000700d8017 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 462072859 1250 462071609 462071629
    0xe0f121b06010b190507030815130914010506030a03050d1e0203090c0f01031104030b04151d12041a0307090305070b040504050c09180a27033b190e0105 67
    0x1079845c14501c0c141039038800800d031000252244040c100469503008090b902c4003803c9501c8900c2110401091600f85032248a01c030b01c0804510007542403a002540c81e00e00480c105c1541d0b6050385940740380a030035400400c010505250030013111910b44032f00444041071031024600c42e400700001040d0400d007100c20400003003220020b0301c0c1054100703c071240781c0c00b01e00401c1c0c400302c03036100c0000d402d20b032a24540324841d005c0c100300d0405528a081985132203400b01c0045841d24564400c151150310400b005810040d100d02d00600040d84041c441d500d02481d1302c2801158803240c240380c880c1606440f507a4160424055600032140038001080912462400c0c1c8241038001070090402840c0c20769640c04904180070400d078004151142c0400904400d00c03907040120300060210a02a01c00001c00310350290b907003400d80c2038000440781d14a141d114070307500755868010001d481c0c114070000030000f82c08070000d85095446400040b4010012010400300040401038940840d20000a60604c0c1c02d000d64110 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 462074109 1250 462072859 462072907
    0x17100f211403070b130b090609031c0e1518030a08270610060f030614010c1a0907030c050907020a060509030705070807060311070305040b16140c03010e0f121b06010b 73
    0x103c2400589c0c00008200d5050020707025000c0404403001e4980002003030341c40303080d4016005220702040c40101c1403039928440d52490444802025402c0d01d0603949001c2c552180300810907010104190b103c000c1c08a0340078120446009003030202e0030700400d04001c01502c0e010000c03190808280081504620301c81d25034403203441c3c00c00007545042da03410f0310039030400d00039810b000b28800954240202e00495035407241442400d0042424144409640c40030b0074071050302c150890700c9010403640f400b101c215018441580c020b140d41c540d542c0700c000081c44042d00d221070a103c00c02c480030003c0da0a10660000303202c0352014181b090300d008000380c181c2d51044610b1021001c200305500010307800805031829109801c64080e120901c0c00d40024101c454910f000c1c01403401c8013804030303a00c0b84c005500b00380c0a1041d8000c1c424840c950b03000070340c6c50483c0d031010551504201c4032410503003031181c05002c4004544201c8041d2003c000401810302101fa08820300314180094800019900d031850704240302 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 462075359 1250 462074109 462074113
    0x9020d141303020a0b0403030b1905100305041a2e0305060609061003050705040b040e062b0602090f04060f140303070308150117100f211403070b130b09 67
    0x6007080c0d074000c1d19196103800003041144894046000e05110303600882c21090090160202904c041c0c043c116030200f0b900c56117224001d54807140300c00601c00e000e014015680941c94882c0d00350900b143e6540d5500c01400b0103804c513040b540d0707081034416a401210312409001d05007868903046041250400c3c0d4001c01c2d890140d02e20f00705100090700d812442042450051400180544170240d08803510b01c103a0340505030500e404a00415035400040c080d80c09402d0031640756003503051449052503039201c0170011405c43d41c1d0701c00091000c07a41940042c50305c50401004c8000c0c101138040050304a4a20350071440a00c13a094005220002c0f1513042c1c0406a00220000c509184955400604032840148040000c00381c8081650260340202000c2030210001041c01000b45041e0b9016080034650340314590522815400000b002c261014400e111121046503516003001262111181036558052031386241c0710405c00c0201195908042170b000c0c00c08118041c00c00030050400c090387c900085d0101001d5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 462076609 1250 462075359 462075391
    0x91103011514060f31030b240a050103021809040605060109060309230f06010305010b030d0903050c010e01110f0a200109061b05030d02130b070804030201081009020d14 74
    0x1540c64020b07646101c5d60800d45010034404841041503081203440c0b5101100180c01000c0100f10903031001d81d2040c1c03070741e02c4105501000c41c0308100000e2401c041c1c10340c201c01303204024003440d4842d8000300030003450300100d081c00f00480b10115412520480342541c1d101da5407030502c80e4035a4030071080c070010a0746242c10300c100c803511f44510098020b100440c06104904180320b040c02d200c00c0c055504030700c803148142c2c0c2080d03950b802c0c030b40d010308408072440d84130703000f914410014a4002c411040551360404014520324544a00554246272000081418080d812842c540303516020021001149046406051b80c2441d500c0e040b01034200b401600d100901d25015598000c0c1d03440b15800d01241d460b490082071480b030362001100312400520020f0481e00000a42141d80c0815400900308511120400401e460b501c2c0184080380c050030758000d085c0329040100700b000d50b224800300c9410400400c2c0e101d9642e507483c5c54500407a84001c0c00701203c50b40b1107a00d0700b274004216a003640d1000b1001000850 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 462077859 1250 462076609 462076627
    0x903030b15190903080c0706020d090602060a02031810140f0c0a0309170a0903050f0d02120319020703020105070305160c0f0f12120609150909110301151406 69
    0x1582c00350089402070600000440344025115145070002540c11180d51039850702c01e03a0041351107d901d030185d00054030600130307480e901a10032240722007203a14035405000b4644607021910301070b510161491408085004000c06044414040d040d164000081b002800c00c0b0441d404440c60403008000c071417241412401c00815180803c1211000704051074005107105052510184402c1c4242101110400c00309442e0ba0300782c0c01c810340609583c024400c68981c41504030140355111001c0100200603004460201aa408040043c40d0407501c614005043d1007801c0052000f07d070041803050700140e444005018800703805119143e00051890070070608000b44500207040300040070001400f00c81210441400d2080e034044680c1d02980c040083d641d90f100ca0b4000406100642d8070084480d860f00c00d000419220602c00c181340450100c002001032031070072280000602c1e440310103881918150000080790780c0c0a202d4005a010f200c0c4800041e03e090180307440e41e160401e9000d600916040080e090 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 462079109 1250 462077859 462077899
    0xa09080106050a05010c0320010906050a05040503040302150c060f071d090714040306050f040302060a050426070507180b03030c03090f03160e370e19060903030b 71
    0x244c1c1d101b82825052402203280456900c01038404800c44080b5110040a4812042d000b20750207500614061106031111725112088a10955000342268410082040107040030718050001005810f0711300e05086010030f940c0c1c1801c00490b403d007454480c403410400c0f0550010056a1082e0380900900c205a0040002c00c03d000c10142c480310510100c40c0c41c540c06502c1e0481141c018652040c0d080c0b015051100c481e18007810162800c4000d07004403800a240c0740d2091089030300c42c50b0814589400241d6031030b001114403c004400c03070064241040068007044081155034010010001c0f191194203400440000700c2d5a081e0076944242c00412000c407603000e000042c3d840f40d0178200c804442c03180c13a800001746854003d8260104d0a05000d130b002560079882040c641c41a06000d141c000c9480030300044000341c241c1e00e002c40d03510324000961200050019032240d060400e1010865014030300c0220384403c400c110440443d40c041d01c4040c01d10405a15010f8440c0d0407009403103000b45100541d03810344d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 462080359 1250 462079109 462079129
    0x1b150106050f0903150714070c0b030601170f04031202040308030a050903070c150e06090907080603210301080d030b030601030611071e0209010e0105011d0409170a0908010605 77
    0x19040007400700d080c020400800d4111145940e00604075000602206040f8000600c1111407401080d500d0a0350380d5110300000465501a52001143d0609400c1c07805245103074201801640c10131a40d0b50400c4031001448443c0c501981150b01d0505140c685468001c044450b140119491580144401c00009900409498110f1034284001c038203a83da0040d1586140100c40010f050070200d000006210070404030400f940025654801c455600f5507400c2c0b01252142410385500031552000044240344250b92540e0003010050641d14112180c001141500343c941c5800011300900000410140c40204001e0749035000904050103088011000207845440c1440b001d45404c0e02c40341c800801d985603808a6039890392002d19548000c0c2101040d41c5a4180424101c0c003031034280e00089407912400720310a0490300140c0d2060305030419080400e034291700c030244e030b190440e0722903480000040680385100c00b03129214114070b03150521290005c0505e44580e00409080c0d00d003210a010940f40c0101345 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 462081609 1250 462080359 462080369
    0xb0408161a0901110f24010504060e040b0a0f020406120e010b0307171f05070f08040507090f0603020a03080903070906060f0518040f0c030b0a0f0302210607051b1501 73
    0x201e56904d600485007842011008900c0a002d039400c0c00392582d10044203140203026100940c10907070380300d40502046413014040c0400711201c00c00058001180000f0760382c2e11050400c008198032280c4240341e4242d03001034000d003010031846081c60040c0e00c128481c0c2d0b2000c00350300000380190340864011a413211a24002c0d4034078802c1420381d40300c01d902c00300040041d1516002518020b0412038080d00d0041c00305455000024450090750b02e0740510803004c01d805160001c01612500b442d0009000003080d1011000c074035075490b82c00c00005655a212858011400358840907905c0d00c0c42801c244c204001d9401c502c0484c3e1070101c0c00d00500d9030140c0800c2900030723541446030351103003016411000b0080b85014140e00505084409682901542102d2001307034040d102441000c942c80100b004002e860b003c4d6050a095418080015262807400c0b644441e40000c07004000c4001c0515280c144507080316500b01007040060f10300c2440807850141d02c20f18420202a142e09110032100c05480380041c810 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 462082859 1250 462081609 462081617
    0xc1806091f06020c01090e040b0711150103050604030813080708031005040e07051e03030d020f160b040b07050901051b07050d0516050a29040b0408161a0901 69
    0x2110701141c5544101140c480d40c100e180c03001d035035200007982c1c0c03050383d0300943c00103002503c000380007100c901704580113507408110030a00d580c1c2c0c50030440d84111850b10207642481603c1e44c5014611034216a64003960141001c0c25040c0b425080140180d80d01034001070780b0f80d04216811000c54107090544847c0e036880013070140c0c3c2e510766043c01c800c90746864100a17809842c203011140002000203651044400070f4801040848801c011061070144803032005405420030020b03041c0c0d50b0210f81c010030030707000303892038032414a00803a0040807170703038100d0704101c80b094000002d000512035000340d0a64043e0745403400f1071a06221600080c03040c06020003150b0300b1850044005808041446204e01400000d410311480301e20b641400350380ea400c80000108100c00f84d07040418181480c0020100b81c0305051900300d2130441d500b405000d0425948070440300e440c014000403912a00b043d00600091090394020200301c030103a01d81a49415550f0f00c411121440c2c1d85034050184e5007101950701c80354003424 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 462084109 1250 462082859 462082861
    0x151707050d050903030601022b050705070f0b0a0e19140d14010b0108060328061103040f030806030a150c050f07030302030103030f0206062b230c180609 67
    0x601640d290180031a8981c0071410202005202c100000103544501026800c039029403a04445020402c03072407001d440c4154411b051407030f4105000707000030100d10740b00e841281c0700320b55140800b880c101203640000d03454100c00200c00b003c81e50702c04415654a1400c4640401009000c43d90403011000c80c424070840440240c0c40356415070f40d4a0140200603042101c07400c3e44060b00a459009160800d00c240c04070b0980030220710705040c00140300c502c1506000ea19040d0403801d145112030802000005c0f00e041c0e86403803849808a00383e01c06180500d218104070b04208510349800f50031480000d1889020740d002d41050000b05081c54520502c02d603d091000590603c0c0c003c0486080c07040141c0c0200031324000544404143c1e0643c0154101da0180e550b01040320400d1030101c1e2107110680700300754800000380c02005035018580e0508204401d00904c8010712031035a40b00c41680000403807071400341e00414012001c4a20a002d010240403084403aa004070011564024520601034462401511440 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 462085359 1250 462084109 462084121
    0xf0a12080a051014130507051b0307020a210f0503040e010801051b090f06071109010f0e0a0b01260702060606130306111e03040302010b060a0c121412010504061517 72
    0x6004100511450907086c8101d2600d8500a040d651001214140d00d040c041d0a6005042021090b54001c13580103007292145854200e0f0503c1c0428410b025411041c4034401000c0001d03299580c0303100b0244140099902e40b40361040e0740420714416400b00845905042c1000306825400c103040c520070416a8000740c403140b80f2408500d501d120610036070f40188001a040090292840000b41142000c8814840c02c1e0b89900034580c0d00000c2e4820010b041a070100403440c41e400640000030003280602d800d0300f049010003c1c800307071110040e03c400c00c196000030522039a1541400540c6d03005006a4409182002c4913000020500040c84060036280d62000000c0c103180c0031004403054100100c0010072007031611070100300203a0003aa1304801648c40c0c110240658100503095804103151a22020310168481c1c482c0e0850403416000b0301c00b00102098040340028080000d85000b105a5070403130555030414083c402285c04580104103003170b0003c26031110781540682419520030041d0500009912a6 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 462086609 1250 462085359 462085369
    0x15030c1002030d0218030c010f02070608130b07050903060703150b1e07030f030e0d09030816060c05180306060901180e0109240e1c020f0a12080a051014 67
    0x1143c0400401c9000007014800b840051020700c500400440944000c3d42c0c1c4031005440c3d0a144140c04070140c0c1042e9802c2203298000d007011a4440f0101c5400880c0703c0d169620904e90300c80c110b8400c00402c0020410360020b01f800c21149601c51800e040070000804a5400b60342031284038403620352080c0001444402c1c8a03a91903046420007800600c10ba2900160f240c05001d2429070f540110000c1e19210000360701c40c200080441d400b9540352070701c1c100c16042d910341c86c2480d8080302110100c220380340504000160380d4403c611040711656200b03130f215800000c204036040300c242c1d0014425401203061104d546e03604010b0504442c10b01340311000280c0f046d00e510707002d0103071001d82000329480d028a01c4203118071465442d0900c8082120b032060500040404002c4808548010107142c1c00754113400440201c25203010300488140c0101c45000111610340e03443c1c41408101121194107001f200103050f900b1010651b000415044107126134640541c20040000192141a01807090a454502e0f41c0d114 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 462087859 1250 462086609 462086617
    0xa0b1c080c060112050f15040609051c08190605132a120524010e21100e0d02191a0a050f06060403080f0d0e0601060e0915030c100203 59
    0x1d03000b03440c2c0310740c2d44a00d40070210240c1d0b00180c40358043c501c0701d0b440485004c51840c4c130100a01602201c180c40303503211007009240340c40742124148921010000072089034003019001400e1961012200d152012000e81005604030201b00d603213003080d8052110381da03200200d074040a600c14002940403400302c142541e02010347c0d5140203141c006500c448840d640800c0417005040b01c10b0090201e0f8a0343c00f00d031000310180410354030b100c050162201406612400c507100401ca00100182028815100d0100d1032030b0b080b840182c0b0307a50001d0701c1100821134a01404400c105c4090160855407086d120180d181d90441c048280c590030032091620030882101c04180d032a41640241c0556858030030401e070003e01c41940c1011140c5055000603155183c4802198217595100c903a40e410700e09101e07412a0342c0c0c1c1010459004950312020381c030240e55010002540240b8040c0d0701c5101903003104040c84404a0042e200b10707502208680d602c14503490001d101c0303051200aa070110720300f8040400c202d0035402 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 462089109 1250 462087859 462087877
    0xa09020d08190e0901050904060c11031b0601060f080103060b0616050607090f0f092007030215060f3006100609150e1507020303040b0307080a0b1c08 66
    0x7602107444402201c8010440c000b250842e107400441924030b404026072503200744a1194484034804c0000c0018039950048400381d10300d810f24030040300d2100d036081c0c21604030001c1038188400901ca14400c04c0410004240100000d0900340d15010b14a200204444d105000c058007a54a03a10060070301d0300c4500866103140c1400c550608885107524116890342c030251181f4000820203d80030607a54014104c880884a91607a078215840c9412210005801030703030b6950350602011800034425031501d030000d00700a84030390301908000202d221412569000170b4641806404540301c2d43c203c030303100c2c107600c40c520400c404001c215460b240e410079089402109104034490040c00309214a00c40410311075000c0da0b545888880c00c0a0301c0311203d0390b40c0384004c0c0640000a24500d1012068146400d20589a00351114030310b03d4180309030003091440d80a42c4c0074000807940001048080c0b03070b0082c6000d410580c02407040c06451741050000e0081d000d201040d10441240805000c10800c2020880d21410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 462090359 1250 462089109 462089123
    0x12003041a12070504080d08090d12060f0608041b0f09180f0804080d0c020a0501080915011827080318060c03160c0c06141b0604060f140a09020d 64
    0x4941158004c020b40c01904c01d403a220304c10ba429501c03041d40901111403103128140d00401590b5100d51040f1004111408200401c9543e1600407440d94004200003028287c01e458808071401c0c6460000084000030442100900d09443d050100d00420701c140d500711882e020011031244445020004240e000385030013421280c4c01309581c4200140e00380500704598120007960351000c2100307010b8450001040d002588030302503071014412903005842d0300d6049400340040f1282c003520040d000d10201801e0b04541c0c440c10640394210b82181c0c1c00d010ba0343ca8020341c1d062004440100710f07a0106200060000140175840100000c1d9a404442d9014142007620b501180c080c8d09051030703001c05640c0103a684020f4542d0380101244054041c0008801d84e59004100c1c4181030304d0b045086076040d01980c828054110204000c280b000504c080d82043e001040d0090116401c0034a0000111401049401003c03800d00600c3c0742c0240c42200d0080d8440d1650314040b401074210300c0050540c5e05801030081410f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 462091609 1250 462090359 462090361
    0x51c080a110a0f050610030206041703220509061804170c03220b040b030a020a1803050d080603120904091a010b180d02131a1c02012003041a12 63
    0x8004520f82c5800c1050080003a00c03e10780b1a902642d20140241c00f0203908180208402c105031454015400180d40151007036038100092501385081040c010b00c204115440300f00b40500452a251001c0c0c0c0d0010000c45103a05500c40c488404a1803600c0180081d044e10130500071070360a00c405c3c1c1d088a941486500580e075403600591404404100c8007102c21030266409000410000c25100854013511100304180d4119943c9480c08400781d8400e0250600300610b05846400c509130711095000514403a401500b40110600340080c95850010400352180e8403130030101c504038000100300c502c038480555010034400800d00f402201043d1100c1c900d010300c0d9600f0000076103d401c43c00a046060140c00b844000da2100070704026540030255800303903110110002d80766502365160b01c03a02c030703200c1d280103140f60861a800001d060040c8036100111f111040e101203a08540c2c1c801c001041c5401e40014980701c0d0500100402d07500c1c09980a140e0341c8040c1d4210a60a80c6c0150003664080c4507410a00c52607 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 462092859 1250 462091609 462091613
    0x1030504030905060a0c05010e0102071a0405030d0f0204031a060a0614041805160302070809012a0305091c0b0f09030c01020c01060603060602030901211d0d0207051c080a110a 77
    0x2131b0050403200340c882d540f9280448540040600840f10915048130412a072110503580c0c83d4841c24001c0c000302c500388420842d00b076450b203d60254022803401624010b031290310b1130074800c004603603242a17001c0c1c82c580c4c90100103840e52030031030400564280d4544068100622510310101e48034980004980038401345011440c501c26400c503521030018001111902c42d580c2070240d0582c09020001024020140a0a900c55114004448500100003090503e001c5050a01d60101c1e00c242e00a038005040040c003045035041c0500740290020342c142d04a05196090344510780d010b0400340ca0348081d022440b01284901800f04262003920502d00000c558503401c0c5400e840c001c1038544908008682400d01c00160311340080306850032001c06854000d221800561a10020b200160b00b0440d0716a44845111400300c00f00303042c00644107000010311090201b0310700070741352800c194403440c030a4001032580b0404500d2000d2020b59650b00074181034036003000780c109903452000c03040004d200d03216080d51502 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 462094109 1250 462092859 462092867
    0x3110f0f180907091406011b080301060806011407050609060709050303030109020f1c06050f011706040c1b03090e0f01080d0e0301140405030304030f050c031e0c0d091502150601030504030905060a 86
    0x700a641c05d0308d510703252016551030301a91104000780a45000421300042000030300440740daa40c0850145001d0740101700300c001020033a00a03800139101680628200003da41040080d43d4000d0800e0a1010307020740380100090740d03484140030712403442d900801c28070301c8442200e040e02e501d05184010401e45501d2404a64000d1a85200c1c2910400740c16a60f490300c0e5000c1c0d000383c951040740540c2c00701260381c0c000c1400003415261f1010b800300074521400c21907040c107000500c481d041c0f103035030351000151604604103c0541e0180100152031035100040000c0b00c0c001a10527684649400d00887d0109401d0000b4010079600700082c010196403000c01003040404001144900d02c2503c69090840b84060100d905000c1ca4241424650003081268221014001c420003d1a0780d848030600e130030703230b0b506800e41003c02407072160010a241d002e05100e00007c04408002d1540244001c1c9001c1003041e41e040030440010f0301e214185a51600800c007414800e642e072102808000c0c2503195181b03592a4018 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 462095359 1250 462094109 462094111
    0x7060b270705030420030a060f0b0109090b0d120504050a0608010302030105070e09010612020c030409021b0604021003020c010906111306230307020708060103110f0f1809070914 78
    0x1000d01006200003800660180341900d001359002020750f5003403503a4041401030407014125540d0315101c1e441301c035400248107010304100c401c1d8030400840c20fa03c0410002d010b0807240c0d0070406100b0b050403001e8030a41c0350484480d00b802d400ca90341d8003196140803030980b000c3c40380750451908820029000304506401100c02412070703100768003c101c16902c5010890306078450f5500e0030b40c0a1a03c60040203c00d1280c2100350910035807080040c0703030094075441c507403640d880384e03000d0074500d900482c036034500d950600204d02c24802d41c040178100301d00c0c15500040f01c16a03016181e0052540c04030310000010401d5101d1070880b0761050040046030b540800030078080d0020501400601c8a4400205046220312040c10401d1090360000c0e0800300003011040650b0802070082c011842a030300c0c00a0000c3d010811140218000e62609107800ca602c41030052041a440c035040c015500e040351101e41d0384030081080854890101542c400786c0f41c4940de142000c101e0351104981d05e052501410b10806030071411 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 462096609 1250 462095359 462095419
    0x30c0e041707050c130f06030b040302071d070f120f060314010603020d060b280306060617070309140d08160305160503040501090c030302010905070f0b040b07060b 72
    0x240e8000e51210001084034414002d00509a030070890810781c3d03e00300000008640c00040b00c010a0000c0721030040c00c1121034a80c81a260741c223182060100303154041c010140507048030340003264450541c10032441c11283c0504100c007000340044400009a00c82e00344403100480c1294184081c50301c140e2500c01520f4140025107940d0300d044030306c0c500b0000511801f000c4941c00707414041103000070744664000700388800d00d003500a0751800101c0601c0d0640703550341d061841c0082003001000e045003408821504150040300512900f1340b941c03281e40d03402d4216180c0c0040c40c0d141c04108510b0503c0c0664a0020780d00340c0415a06c07400c1c031003c031140e41003000103100750400340d88409030898805080701500c400761022801ea1a8815501da01544104c0003591310500803000400d075030000f0740e524040d03070003294401c1c0c0050355500281d80400400b4030141d0024400c58680c82c002506008008046104520038401c0c0064002107031020012140c008a2182c0c600800c0c0082d0840300071b2a020300d9640988031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 462097859 1250 462096609 462096623
    0x3021c02031e090109060c06020d02030708010602010b030c090105190b161a1e0c04030f0317060405010302150705070512011d0d08040b060d1203020c010b0909060f060604030c0e04 79
    0x780807880e100b071003035914500d8141c5d140c1d001d892610005440e2504400e005581e056001c10030302014481900085005900701d6a480b07102d0340c5803003802800c58043c1c011081c07098100c042480f10564400322403a05403178045801c001080420012482d15140d81d42c420301030300c0350120781c450550050f40c0c041c600d60760064544103801140700001c0203c0d030b9000c540d0324141116200e41b080d50107070074070f008503407188404d0700c101e141503100d4503a5110400010350803000519541c2001c0c40ca540711000164010906607814002541543d0028040c104007684400f01d0a0001c1048418081d0804c901c00041802804c0c171409800341c00e0001c1e01034102081920036013450645503e585120000301a144000165505412074840760b403100d07400180074101a41c081559400315000ca51f40000309648006541c400603590f04000c0125802d50303403544040ae11482c002c20411600a102282547e40801c6048064420307507a150001940303809181c02c064400a0500c0c0d000c24590401a20640201e0088138 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 462099109 1250 462097859 462097897
    0x60f090703141f091e0c02030705030c07050a080a0f08210c07020102011506050904090c0510080906090d0c0f02150309010e100504020d060b04061814090d0203120403021c0203 77
    0x4100000d880314401003042c00030500c0311178030000d9070f01e620040e24440e052060787d150401ca0b40340c5501d1600b1032541e8080c1900a40020000351030000e00c1d4400408520001c2c1c42e5586039604c0e070019002000b8406000114009542e5880c2d50200e41d130036041e10044080c903e42810101d40a550b2904111000c0b4055868032102d41c00c40302d000100d0130116022956034500c0c05c03045a041c0405010000c0048070402018100070070350307070365803503010301303030804560b124850380c60000d050a00d01070025114420a4001e0110001040d500802c4095155000690800502d034184041980081d40548000055a000c4140104690706401514074294824200c4800980451300307141110816100250b10040002c080000941d194100d01040d0310014400034085a0f110b01050400c1e21400d84100099516105064020700340f560440c4c0000501d001001001134010340a540c03403003088029101d010202000404251007004a00321b8884030f070161048074003105502960b2500101c99003001120000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 462100359 1250 462099109 462099119
    0x11091e030a050318041401180207080d0203101a04060c0c05120a0b0127090c08010509011e0501122004020d020a08060f010f200d0e03060708060f090703141f 69
    0x400303031b81c02c070850341402c4c02816440c10000c071034440d403400d285034401c640a00c03c00003c20380e1b1401402e41c2d803042c1e43c005a03413440e0a00c1020340c0300504e9000303104004003094001018080e1a07040d03401f0303101d050034501c2c500d14050415605a030041c0c2d1140754000002d55400c104044d010480c6980030344a0f503011101641c0743c0c007040d00c0e0328400c414140349568884205048900c1140c01956825018031000f22460361100340241c01d6440485600059079124100f200c40c0f0b031001c5110525900c62040100071650400286007400c16442901a24500540c0752910286941700c1d46c00241c640014021540e591131003103818040d40254100d480803400c440c00086603401c146d1400100ca90301603445080b603d1070068103a9004040d0001502c0d20700f890302004116402c20400c1d210b501415445298025003400704161034200000d103140300b0040d81d2414010795445107a1900c603004400c40b40ca40312a5a40d2070200d005224181200200c42805000d0044801d02594001521083c0310a54820350b0340356 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 462101609 1250 462100359 462100361
    0x9060403050d0903020a081f0207020d0f0c052812170301061e0509030a1e0c08061024050901030908210c07020306010905060109030812091011091e030a05031804 71
    0xc00c54600703460440c0e0862a03442595600800d0b8043c4004c0c65860400701078dc81d40001e0811400d003c03554070105500500c001d02d07140500c0e000b0001d18a042d89010030b000e40c0c9101c5044018400c1110400b0b0048010b001c202c00340c03210740c14032000b9942281d225a036800c0024a0540b8100000105015051000f0f4500b80b0445c101d814005001c0e0040500252a556102c0c07043c48103107110660401a1218600040d1060030400c01403c980000f0001c904140c100d500441115a210501840c144842060b0007182c4c0700300c4540085c05801c0c403a071100242c9005034054003034000002d0504000081d901c0c0401030348150041400440d00f41440c0540d2401c4005a0324030903902d0181d40360344001c0041145000c1900300540c0400185000d031416a82c03a907424480d030700301c1140b103ea04020079003040380e0685c013002034410000480308148007000c0341c1a02180d0500c16041e03030310701604084d0b5025040504810000c8500840541164002b1042d824020703243d4000c030003012148142d04031404000d1070301d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 462102859 1250 462101609 462101623
    0x702011a01111e071a071407050d060c090e160e03121204050703061401150807050a272309010806010b0a0c0203060703060e06100f0509060403050d0903020a08 70
    0x61009141e8076560030300a0503000b49840d050f43d070324031418802282c540112142050181c014083e15a250071a030f203440039503100c110302488140d51000f4000c010a41c0d92401491031503410180c001202418440c08441500c1c064000c40c0c8841041030a100c010568140c2c41d01c0243c600350b6a40520824000c02c26132540003040c804420701e441404030a5408500050060700984900f00302c54803541d03650303100303025203901e0400c00e444108410010059981215034160140c0c04070300e414130700c4c0d20340701001078007134080e425049041220302c200d00340704c07407060351004440c034200302188a207041d544141e0344070991801004012041503940d0140e2807403d080308464169441d00000d4012a0309007108086640c200842100c101300041d0550070158070140001d5010f1041a5400300d1700301d0600c611052030510160895014003880222001da950340300d00c050000a44515106603158401c0000490500aa8001030480e00401c50480c203440c2d0040034550031244295520301710243e46200d05510740107 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 462104109 1250 462102859 462102887
    0xb1605370207060f0f02070302040f0b0319210c0c08100605010c08160f0c08070302011134031407050f030304030309120f05060f0403080a091a0c040e0702011a01 71
    0xc0d000103804e00250107401030783e41c1a065441201c4002c0c1e940e030002030540300d581d401c0c07004507030381ea82c0401201e0070f042c4084542c004c0200c901e9056484d030f940c1d51043c8440130458071120800c02c40d8910b95007500c031711002600e00b904581008030b0241c40c0c02c8070b00d0b00e410142d05c40644280c034111002a0710b5014298054543e0380001d08603082414a42d1013034070058241500319600c8a040b00204001000c120028000d0800c0c98020100d26040d07200152200c100c0030601d454650220001c44920100e45640c41080807581d82c0d0013000c954080304040200c0c030260001082e4981a800100700e00000254940c111041244c0020313000115106042e10f03840b4070300000d00041d100c64420700015291000a20350740f0f01c1031440040d80091512500e081543c00d803001221664414140300625921000c0141c000d15052004c1000e0900f681ea000300918a594401881080348000a0907050001c0143c400070000c0c0c1d0564146850440c00082c028080c403040210944000a403413425035228545402c00c1c20 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 462105359 1250 462104109 462104117
    0x1090311011505010c082a250b070f0224030603061602100203061302070609060507050c0a03030e0307050105040326040b0a0b12070b09090109090b160537020706 71
    0x40c42031b071650301a0b42d1002000103403105081218005401c41808201714034100d080c00761410b02c1c41801c141d80c803245940c80001c00f000c1d48903014490701d0f9180c4225903800390f100540006822a910214204402081a0503a072407d540f641040f4074203034500540c440d403070440a403011a5100700503910b034054030081c0000140d000c603048c00764504840d4029500110f004061524a03a0b0804019044c0c1c0e00141c01200c45a40b5030603c1d0b030800030103000d199080403040c28041e040288060103665600080382c0080c0c101521814520005207083c4111148290080028801d40c1740c03e080152005025a841d9a0101d0045a210807241e2402c042d0078025603116140d041d540d110559050f000d4030183e0002503111140d100318488020040142c500180004c0116507101c19860013000100041640022500e50401040350f0010b0b90390720810ba80400112003920448071160b0701140c20780107006424501d100492405c4503011510341c0c0c11800350045000701e2259070603003031040345c80e00c6052240720045 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 462106609 1250 462105359 462105377
    0xd06090f05010617040c05150406110106140d06151e0b0f0a0e031603061e0912081906030c170a0309030803280207030e0303390109031101150501 64
    0x802c04113968a0304640910f043c06500c90f1214005038103400142044600b50070006400c00201c0c0e0000060724212507020000c0000d98680b011000720203c464200601c651050030003101000a03541c444490f218050381d0071708403291a0f98141d60300317121038156040007a60719000051044540c5040341d980c0318281031120308020902c48150750007840102125458050081070100a4400c14103540046000d807402190441c54203466803a0400b561001100640c2803000301c80100d114034000c413840d40c106103040d403e941d403105071480304003091503003058407030b4240040007040c00b210b0340703941c4d064582500c2088913181030918800d40d60b03019800c0003400300300984800c2000c036030320001030340d4089400d42540c41c00320860034101c2c10141446020743c06080d40400c2c0e0b01c0078154000c02a245409040e0025440c15100c40d00d255401195001d25003013081c90343c1c01c3e41c0c00e8511010851051041c98100a004c0ca84687c60060104d105091a0701d9056290000d40076210700803035254021160113031240301403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 462107859 1250 462106609 462106637
    0x501051e04051008011e150e1504150e06030601060e03062703160507362703080a020301150809010b03060c04060909150504021308030d06090f050106 66
    0x1d850300824840348200038420001340d0301028044e001045040c00118107511241c140014202c440703052080c88840440d02091050100c02070703071107400c07035084084892014403110025020704100880e4458011001c04c0c00030790741a90346e401a00501c011400c6d18a0382e80c9035030040707420559000c59558107521a0010410030013400f2075090f5009041e11141c08401000a1003910f990f0000700307092440f20705e03460314000340001800381001514681307801200e51200301340315410301d03583c0c810180c41b090295822040c050030140d10084000340c075004dc800e14a01046030101071560503200580206646c0f20000e0300a4409100f1207060320158a40810a0030985030122100b020040a801403503603608401121070b9005c1080620840301041c500b56140c1c1007601c0100010700d150700114480d03003841a001c4600000c1180041940d00039100180c4507101f07c3c08150b840c041c640c0c090042c6000004100b91100d0702600058151003614600f807003001e03c002000400c0300c00c241304107000030301d0034868203103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 462109109 1250 462107859 462107861
    0x15010509180a0f1505120a0218070507050a0803070206090a38010308030612010b010801181d061501021207110607120206100905130303020f1605100501051e04 70
    0x1402c050150b034000754200031000008112048070407103003a0b44079072001c20021032801403a080c014019510150100c0c5149601013041205c40075a44880b07070700403a002503c02440395080c0c0e00c80c4c41d04041210706c5208103080541c5103a1042d1103075030060103140c0000b003031070030005044032046610402c000802202c00303440101d64900c0f42035428540c0500c400c0404984d4a80c1d0700c80d40a18001c1c00385a03564140001004460a034052583c4107030790404006071207a0f030700b0515841c11286950550b008420404003103e008100e4103498290300c0407520040741100c031000075040e100b06200d024503404031244000680c3c3d06c0e5501e504140504208000c080001081c06070249441e00c80a0400d0341011015560b520344855001ca0820040e40141c00300644c01080d15611002480d00e22000c000d1810324559902941580080c082e0515400141486c0310b40e021000310b5043c411800034244418495180031a111034280040c2c0741c004e41000004111032404210086010450942c1d0398054018001480 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 462110359 1250 462109109 462109111
    0xf0703080f0702061c1d0d1b0203010f060512030c070b07020303040308030415270b0421020c030717190501090807080c011406030c010e0301231501050918 68
    0x20510009000c40b03801615140060070361503600700e0000e08844032526000b400c81e085955201c0c0d4480300c41044043c14030000c1507508900d04146088901e060030703030b5880c2020100380c11000790150b18205100f180414282d0100c1300762401180d15040e0381603011007a079a2030145a0b8004d40640000c44208010300b070450003000041d10240c262802c182c2c1d0383d2030301c1c92346401c11903007900e183c40c80205645100242c2d1003040030201c0d0820b40c01000d925070b04012403045e04250b00003824580c105000c01c1c1880002c4911144010200d00c1ca1500c0200310311000b500e0b035800344e48850291141c03003808585640d000740072020754101400200000d00ca050003000c002400700005481c0395680710f542001180b0307148024800c141c0200a0140d403240c000b154039003102c5405e50380000000c402c0c002d000c055640801d80920380320003442c24000081c20706c0b00203801040501164010400745140c840d0101e0314a004581c031414513001502200800c40c801550284070301d59040d98401c082c4d0301c1002d485910001d0351 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 462111609 1250 462110359 462110377
    0x506010e0f0307030803010602390d02040e030309010b030609070303020d20010218101107091d0303090d1101090b0f0403020309091005040609140402060304032706030e0f070308 78
    0x543d40c1a035a51107000450380203800c8031005800101000b0120046841e0941c010340711003076130103048070104459000d4880d1428201e4450b155505a142c01c0d0760311501700d4055002100142ca540c5d042003a440f500800c00e20000034000c2c002c3d400019040d04d0f0200310343d02181d07010f402078002d80c24046002ca07522010b030604030803600034000d02c0d24040c6209101a0a44c440c4000e01d4410840807201000313500521403564108100c55002020402c1d50041814422618804004240b80c22034655004514403413110100a40c44084104000000e0005202403640b401e511060b1404800940c41402c0e80d000700e42c042e107035852981c046a80b01d20b5107507041ea401402841501c0c14100c01c2c1c0b00064848100f500c46c070322076110b240401d000d18a803d10408004280b0f4a400b006903111100c0d044407980300050010b8444d40c03000c0005000c1c035004511900030010000d508070307451030700303a240841410a28040c07200000d02c4c204049070070080c000380b42400101c0b140d005004030b900c1d40da12804036510040d66 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 462112859 1250 462111609 462111613
    0x19061107061e0503190c0306030c1203140901050d0203041a0609041e03030f1505030d1701030206070c0e040c03060c0302030103051005100f0b03010311010c12030b0a1a0711040506010e0f03 83
    0x2102c5d441801d02d11428040300300342d5401045040c5541001c58144e407030382c0c01500ea90840303005113000080c1c00c882c03501c59400419079411384a0781e00f040140c40e280507004c16085000d0000003001700f08105030044420b00762881d03c505e0b5890302c4403020720548000469008007103004400480007070302c0840c1c012040e524460300d000704644e101600900e081e528042524896150f07100302c180600c1c0740500107014a0f0070680f4011089116080b01080480d106100190107810000f41d000180203814401401904111940e400e55043c00e207010040e15802d0311066900c1458000c3c5092038502c64000c03281281e410030010500c15465098000080401803d641c6180001940c00100090203c2118008020b841807040e1258594206001000c2010701182d0410050000200c00030307007040303620355000840e45000580d0f054002c0c08114644030f141c202441c10582404000041d40180000b0140c3d00d110308626004001e210040c80305407901610340b07a002c101d120b00400ca103402c1c9800e000c8800c80c40101 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 462114109 1250 462112859 462112891
    0xa080a0612050d080c0307090b0c12040f080c060307050301050f04060905070f020c03010b28050301110a17071409010201110304050a0506010b0c07031119061107061e0503 75
    0x601d032540082080100da075500302e08403c084441d00041c00c42d91007400302d070f4624550314045c070000303115240c1402200b0075a40041007440c41d000e4104503600c1c40800e81c600c815651510b52409101c02e004500c03403070880e8418000e40814504005094901511164a0380ba003980d003000208240075644c0801d10fa00140d69071000503111b00c203402003500614064a075110529501500281810441c10180d80640c3c1442c00b0140b2a0300c0f078403400a103030207040800d900e5441701648000b038010381c01e80c407541e415030078140d00e246c01c210010002c00c1140519100c8003130511f482ea001c04605141100d0104c089110020903412000792080184a9094148000500b49195500e08103103500240c4081d14594852040441041820010a0702410503038110505059214840e40d5607410940030007005081ca5071404d0020b0b403140c00120300c3c407002c552030014050fa00d030a0010010141048001500d209901000900d14086c0e240e14200941581c40c5151071900c0b11010350306a40040c004c00e8840345029 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 462115359 1250 462114109 462114119
    0x120a050106061d1815061608190810090e0a0c1805010b040e1611240a06180b010c0c030c0503010f11120705090a0f24050a080a06 57
    0x8461500500030b907450700e107801c2c0c1822000c404204404010a80500c1568980c03001201e20404a203500000c1300d004101440e2014010500a0003403004240c1e003081c41401a20400c10003d014040700c940fa080030740412880010221251441070b1601500300c141403500340100425900321481100d617000888000300d4850707560400d10503643c0c0c040505443d400d00503052102240c000c0e9401841d25500c09030504d414070503140c0400c040a420107110402e200c0c06540254007070343c000c10840390250b0984031030030040d01c15149036400049010a0241075200010350780700e114800d01040d102c010103032a00509907211041e0040c40789004082c1400b450200384000070f03c080c80034402461141c445400c145181c00180742c25100f60060100141d41001038241c8012002030545054031842c0c040b40440d5121081d0594061141c0e500d829089a05c1130340118852580300a07085c1207440c80f04a100782951031101110341e00401c0310301c0b000060340400c014101035105000103900700e035466600107840d44e622 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 462116609 1250 462115359 462115361
    0xf1810080709020408010b0907120b03011b020c0a05010809070b03041703070504030c090b01080c070f02122506050301061809090f0302010b040b1c06020702040c110d020a030e120a0501 81
    0x10341d00c40c1040b50b40008041c003019100b80512030f40c44030f080d242c044960604000160034040030100d181c02141d83c440410ba040e40d07007508110003440c1c1c81000c1441d809a2032000035100c07200004800e000d111100ea002619510039101144200b103180083c00700349041c40502e08041c4e0010348181c0303000500318142c00311039007010021409000c4641b0390594071465840c0401c001d5540398082003403c1d180c21107000792a41c0000b591540805c4e8001903550303a903c1703464080a620100003001e900300388864500d2044920000d00c2d4410ba0031003101c802c44403410040c0003401960310303000c0c0340b00140302440108801d0b8043d81168440c880761030000e1160360b40303032552601100d404850aa84040307440c0b54500034550203106181700503406a50a11420f6540404a03005003040d20f40b00141c407103908180b6060040355819900d200b50300410501141444007070003030059920345c2601c1041e0148444c401000d90001542070328540d4151154819006510b0411843c0750a410000d8440d0041600100004a007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 462117859 1250 462116609 462116623
    0x30809040c0c06140f18060a0f0e1b18150d0203070e10090b010305070f0f020a060515010e0d051b0d240b0103150e060103150914060f181008 62
    0x3d100c03a41c4d2925014408020125000c3d00c0c44030221180402401d4004d4081a080e070b02001030440410b2005220a6440080c1141610b035000c0b0300840708070044441d04031512640c008c0341211045002c4c02c11440c10b19080c04252a02410480d20451103241c43c2803107148000ea0724001804c1c0c540499448d04215180300044400d04500154100c0c180304030240e51107080e510040038601000030380741c6070b00080c16401d10031105a0520882c1d580c1d0000151080000301401e540c03101091140b4100b00c16005115541180110b0100d0104001c40f00b81d810140c05103a8041e8100c8001c143d243c803007480208604080b86822034205410400300720202e0320785601a00ac004410890900c007900301d000d440308460050420b10304060a100c0074203070000580d8028400c3c0c40c04003c2da1420381e290180140e0041800c981409c0040a00d02e4000995021950114400c2c19200c0c66010b1196511004c00c03035018481c12903994040c40c503c0e06c08001c000020017690344480f2601c91078064035100c0403141c1c90306034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 462119109 1250 462117859 462117881
    0x10b0904081201090605010c02011121180319080703020309150904150522020d060b040e010b04030807030f030b061b0f03040b22050409030305041407030809040c0c06 73
    0x9000a42c01048105289140d0041800c0703501042600c0c24840000c11411002c070000e0304000b01555440c1c0030901c14040c0c294404444250859203c0301030648201e0780d08400d411150b00012040c26403003d0902055141000b0b000442420010f6a1965502840e401c130040030340440c44140310204454480d0200c808600c000c64508603215445841088281e44024618018040c1110000c00035501c4165400205203403035452800c41005000c1e8403002401076144c0d28244030b0604000096040400004005444c2c0380b04050348181e890b60407244107807059100007440001c0400004002c070340700752548070255646180115880c5003207400038280e03030448211035800440300d0840c5e02d1108010031141440c1001d66026506151800e030702c607445406091107801d1111802c50307640481d0b50039031440c131014140c005c0c400c125038161030400400501048034101d940c030303124060986001e03000240b140200c81e800b81115161142e060284409803000038480340c1804910740104d07000480900802203816 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 462120359 1250 462119109 462119123
    0x6070f031b0c170a03020c011b021f18030305121909050c0a14130902010c0b0a0b0f0d020a03021018090203060f0a03050a0b0618100302010f05040f0512010b0904 71
    0x1824a800243c4a070031921441105520104940700081d40101d0850821802400c212003c00c1d565a812002080314401c0298416000c030305031500303a44900780d0080c03040129640c800d0301e021540e8950060b1101400040c010500a000513080d1a0240142036401035440c030041203600368620705542504c0304660111156004003130400741a0400140c540d0003800010910200409032202054150709205140c1c0d00c2c10391500661015a4002d9918601380c0d58051a800a5450301189960040128460042c8201e541140e440020304c0c00040300d24080d074008200a41c3c0628581c01c00c485003103088038032000d109040c60340d010030361913005800e002407900301805640c1c0d11b003400411071801c941120082c450116241d061000c984005078040380307550f220300c0b00300d015281c010004560359000034220b10503404810401060141c8800c03498101c030b00c01e032501c451a01000e801902c180c082c1d4000e4080c00086100200f0403403602050307021029001c11b000141507941900800d017001412502a81e001c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 462121609 1250 462120359 462120383
    0x3070311121305040c0e060c060601020d1e0e03010e0106030510060509040804030f02060f190801050102010e0c150c030703080403120513060b03070f0f05011d06070f031b 75
    0xc0c034000d005460005840740c806500c1d10600010a01203102d00d40249070081d40c1e41c00c1c2d101c4105008403403403080518010491610f038115103540d5552280100d82a90060180403c0301c90000d00a01c0840d0500b41e1020304044031002040048910720740ca44007941c2d0540d04c44007406003c20080c415000514000c1e000340110003080d01c078060659080343d01241c06204000c0420010038007550550b0142ca5121080301c22201d03007030000540d140601418a8800c071000241c106003002100a0003601400e5903c2c0e5801d140e80e541d0040e0300321100000040c0312500052210030301c81c500070b4070f60010a0a41c441503420049a05071823840c54000c0c1400304d02041102c0c05020505400c80d0403801898850403050089151000c1c084040c0a0102c10042078541c0b45c85580b400c960301402807001409050141d400365542e01d814440d8110458803c13903011405015400a02c0035802d01400c0301a132000d8a83d5182071280da585440610b091042074040014446c00c0700754504000b0290724005024801310104 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 462122859 1250 462121609 462121637
    0x90106020f0c03030403020a05090c0906193e030d09030203090108091b060a030b0d08031506070218070903050102030106030c030c02030a0804020603150d050312011707050402071103030703 83
    0x140000c00381425202e50304c18802000143e071180e40303c409454043d500b900d0240c907800b07a0701099005100780b0a62001004c140301743e56101106000018128694400560203030949140e0040b106045900326001c2e0080c14100030400ca00718640103181c071081c01c8901d0036842c040c1c3c500880d5246881180141c1000400c0310444d030b0b21a10711074016558902601c080380d07590400c04283c241c0410880d000316408035500c10954000d40c0800c0607000c0180140b051010940f400c0c0a240c1e02c1210303606c80301d011003a00701d41c2c541410002d54002c0381d8041c080490780c14921113003000d1104018800810003111400c04070003d0300038000b5500074426620046803141c1c0a8002400f83c91480c1c815004540c024402040c405501c0301c3c00030b81058046c2c41d083d68a03142c0e0322a40a4414000b51202c0d000840da0008100300310002004190300e170382c401c44078000c503622045061a41d918104d60f0b9038030741d270001c00144410b103001da009008140c41400c0031044007040b4800300b400c64000c03038400e50110302c5810303044c25 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 462124109 1250 462122859 462122863
    0x30d0209010f05030702060f10120507030605070c020918011e051608070e120c0a060203121003030f05030a2021010b0a12090501151802040617070905090106020f 71
    0x84105080c14074071300358500f083c3e009544110040c8000c4204802202181403660056450005414104d41520040c0d8060030407a6030b8030400c0c8002ca82c598503020024030b2640c4500440606942d00810010194998294405506041c40d8507417503155a9050880d071080b03260f00c015000c01304099030120b17062400f0984405481e08480140e02440301c0c034820030540e2544010500b4551808445c096401142242d28928040711450701503040250340c000441d2403600040680000c0c4180e00d0500c0481c1c1d204280440410031520005010030a03c005440103640140b01669014200650000b920b800710401d5041711040d88441c110b101c40f002900d00005031180c2c1c00e0310614581c45032441c0d02c551501262691600c41c1c0c80b150350403c50540a5200c4030441500854081c2e90424000d0050340441c03000d030300c5107103000d105860f400481c549801e04002403d000751000c0b01e020381c4840d00000a046c4424140000c01400c1034100270b41c00401142c595905005c45000e8500c6078020315803220303011207141c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 462125359 1250 462124109 462124127
    0x106030504030503220c06110c030109260c0109030e030d08010e07050702131401050a0909020904030c080705070620061501140f030a1e05040f020f0111030d020901 72
    0x1041500301001c01001c603030070600322030b00300510703402e1500c440c64440105241080354280041c03110701c50325000180c075540700b000410509034000541d240c4c1410303181054201c50741600020701074600a28041c6800c9480c1c40700608a2a1703c2c42c070340d80f50505e8520600d084a0401004070007148031484080c141c0e080800800d030143e8118280381c030341035050050720143d00345e0040070f90b070420000003202002c6456809509603034010011051041d24880d200d0300c54041d00034003800d0700400803880e0001c3c0e5110140034002c10660081c05801d01c5840da0345044400710304008007a101d044040085074001001046030070300600e10780d60360f00301c1d08036005000e0513451000d51143c03409030721910602a1091001096005600c000d08100c2c05254100d4040f075101d01403040880c00d01c01010080191035041500030f917004410603407000058101d2510000d007110000e8a01400340c031000d6000304014208603144800c04d15050602c01c482c1c8044031045072031030740042120b85103960040350361041541c0000c0c01c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 462126609 1250 462125359 462125369
    0xa02060f070c051005151c0b160503070c0606150c020a05060a02120309070e01121b060815040209030102040b1801050c030f07020a030b0702061006110c0d0c121a01 72
    0x40c0a50002c0c07030b00c40555501102403042c05580d6500c020441e000e10700040c00c0f943d800040d10f03029103400300700340015040a820000350b44c000c0a0311300113101000221040a044800c40e1181e504507201d04108032109400b00030300b1030320329545040216445220030784100c1854055640c1c80300242540c8180008005c40d540042c2c001c00052191101098010230040324810a8040d52912659515800c42c500350007540305218459101c40003243c6100c90710081000f09016201800394070700e0074404008403110510424000030100404950104540f90007503032114070051015040408400009089a00940c0b228005080004d99000380d081000c607074184054090030100d0910000400b074944074480c1e03581092084000094060856039904611005980c00050303140c01480c001602030340c0d5403010380e01400645001100043e180c0d11441c80c18105c030070400f0180000b801d2400038031600904824044a124a0305d001c0825201c1d4113a01c2012010700600e60460a900714046100d642501a000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 462127859 1250 462126609 462126617
    0xa0b0a0b130204081f0213120506090d140c070b18011209050a2310090203010f09050c04110d09060606080f06150d02190504090b0303031009020c0a080a02060f07 71
    0x7004441d00100301c1d40080a8807480c0e6000c1146192a500f00907c9030601f111400211540d0108814010b6000144003074030410403036540ea211140d1107540c410003840d000340018035140460840b20b42001c050080314041800301c901382c3d5220052402c09403c98211011811303000d01c5c003401d0941c2c1c08004103080184070f4000b048401926202c03a92110703c180f40c0601900b00402a64420a07179503451524030116244c1610307a12030880550001038020500140d120b90300f00380c514108801140f0944140f07540c404000c15820000300c0920000c0c18005000201590060000194010081c015851030342e10400700041c506050a4010300103d83c05014001c00d00b4075901002102d4461115101c0c01552041b1603a44a8555901200191092481c0c44108d6040c504015011941100242041c0c030740760301091181d4081117003895603d0200303e0340340710303000510a020803c0e80c41c182e0081c8540d40e051402d03a00c00341d00030380f1070715406c1d800700341410f0041c1d01003010070407081c90001c455a0000d41c140341c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 462129109 1250 462127859 462127867
    0x9051c021c090e0f130f030806040b030c01120b010e0405100f29070f02030d080604050105120604020f040e151b09060d0c03021309091a091902030a0b0a0b1302 70
    0x58070f080c07030140c000d010700d4050f11040003040910500500528046611003d44400a412483c2c000c040703000654069014505000300702c405450003003204846500103940e08003251640c1480140a000327450922030500c42d4141c01c0c034069898074002c0c148103074404081c400c041840c0405441e01d80c062544010780e0351001303020303a0112030702c2104045a201c10001c8240c2d180e20030780c00c2c594100f1001c1e00f4001e5040c4a004a84014107400c801098820082250700b04916a039840074041c040b20b014450400c0343e00b03c6000500180703425100f850140d000544005031742d0f940c00e401c541c5803119203001980e021000000b0082c4841d604c4002d40c1105290400c014189807440c1701151181c002c0740c40a5207419141c610040700c0ea4400c0e41034907080b4038020604a103040e9241551001020040030644254101559a034020040741440600400403d4010002000500c0204482c02001d0740c04a03418028551050702098500c10064001d09001d80d0004010040b001003040d0030030f480d40440240d82c0140 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 462130359 1250 462129109 462129119
    0x120a060f030b0402012105060415080c01050f04080106080f010c1407030c170a050a110705060301150201090f230f0d050a0201060315050405060f0105090a09051c021c09 74
    0x500c00c0012a03500c4003907500342e500d942c4010b844611080c180c42001903600c481892509416401c200d01803071040d40c04001402e650038100000c05c80b180140b41c0c440d800000c0107107841d44214000c1c00c1c2c0c20142c508650610341c680301c006007940c000d0b074400429540b2004149408010a200320700b010105410322490010400c2101000c6005100005d014040754021140620020802d641c1c0401c00702182c46a07a10360b040070140c0a41c210008144c000380d100c604000303401e400013401c1002d456005028604581c43c250320080030b1014810103004554030f81c3d10002c002114903840550641c070600c42c0c1c4010849203003011099036900300701c5080603403040701c0030b0801c40710110340200d005c0400c1c60150798400143c00c0903800350070241e1008040c02c66070b1240c0e6880e40c0c89a0311007401a072103801074400c66180c0c1e101c3c0034004442070007205e5020140c0d80209040b000250700090007244140b042c0c03003105200c08500600030142c00040005a044944600d1200011101008810086007060790b120340c140 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 462131609 1250 462130359 462130379
    0x30c03010c03140a180b0408070512190503101e080105070c380a0905030c0a06060821031e0a0b040c02011a10050f031e1501080a050402040b0a0308120a06 68
    0x9904068141c03d020307000311f003c0c008101e04071092580c11108480d45105e15172400b0b11554031158506a140044c6000c526201d88075800f26401041e21224070950070b800c101072002144c05152812019200700708000561000c01c1c02400e22400c1180c88942c503010765810301d68441c0e040d8010101d22611880f80c83e038401c4200d2030b010b80f00c2c00d100c103510079480c0d540c88181200600b540714024000303200100701c034403884c500005e1011030f5a1040500748205070743c817800300d03650301c0b0310110031082c0c000e4004461b0030f880d8004020f5688140304e50000107040510741c12035940060251142648a40c55023900616401c2c14050640c0505442c4004c005005001c0c1c03602400341c00003a07032a44a520421000d10074144180306036240c2c40d180e042810341d6410462001d6000c11800d0610000100728840042c546002c1201d2401a00c0d0040e1202d416a503518000b40b00141401801242d11598903e5500c040b0344407000c40310091480b60802a84e14140c15810f019450703001040100a1410039000744208660 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 462132859 1250 462131609 462131651
    0x714031212190b03030f191419021207030c0303061a04141527010806090f100306061e09050412050d020c0604060b090703090503040b09030c03010c03140a 68
    0x181d5102481c0703810603400005071403500f941c0c40c0d1610002c01d07505550755a24000300f000c042000c0d0005546d2a0501d03040d13401d501d850654220b000c00601c100c0b17800701c000c850314420b900590303c15a4032844164000301b0040d00920002d400242c84032110204141d090310607d00034108044c210305003000d082220744494411809414030043c01c1f0203904010b91520002e174104103a8517500607490b2020701d8039181040e1580d6070701841c401411b0103104510b5001d03c0605005080c05000c0702500d580c1e400d20408051400b52101e0050f600c11007000001c10782510510300a8242e55110640d0200882030b0004015925001103070b46d5850802408002400036800c144030003140d0038442d444040651442e8001d02620700d0903252401034104110401800307502100325094100c911440640320300f0300440454055a2001b000703a0300c100403e020090f0003074040d2280107002012501341c0842c1201007803e660494a0850229890b800d00a200b007050200056205039041420070040710300c030040724400c180c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 462134109 1250 462132859 462132871
    0x50709170c2b0602040e0405300a0e12030310080609100b01090306110702012d0813170d060b070506040209190203040b0405060a14040b0601020703050714031212 71
    0x520955141c00440d81645850380c00390005402c64175903035201c6168002ca0070494040303a80e0300918401010310030701c2c00107006010480381c3c0c804410154808104840e81c2c004494142800706000301c41840c0d50b100300c40c2e490155000d002a6449041540300340410100c2a00102c01e2030300440100040c0c0b40000540e000000700c140b1003c03d107904100e0060703844071419000131b02031600341000d40c0a5005080000d1070745034402e9a0b0300034032070300c80034604401006820716002d5a60f400002d4800d6180f040f51070075000622000b40d880e4107031007070340d4140d24040b0031442c0000044000c6600b01020020344103640003418003c0800c0d260208564402d901e070b02c00144000d03c00d40305540480c000241142d2140c00d074813400c00b0210350700d08090070140400e00c0704070340c1240d00b40300f00c0000501201c020b010341d0051001c030180d03101e165140c030f0b40c81c078014120043c1040e0441c860740c0c800002103001000b004004200c51018401d090750204140340c180030100f01c00c00e03202501000580c80e8510310ba1000c0e98841 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 462135359 1250 462134109 462134149
    0x3161e0201081b0f03010f030c0e0105090f07050d0f0b0f010509060301061404050d051b04110406110c03060f370902040b040f06050a08060408041215050709170c 71
    0x325604040c1c002c90042c1c090342d501048000c0b0000c100e04440d080c400c0141c074011004c9607404c54ad5207403031018000d000d015054220111402046140c04c40050781a000341c1642800350401e05403035464401ca071506605250059114203a003030150601c85a00342d0800d00c00c3c070700fa030f01d0b1551100c0418031511040c0706010400801d81c034071401e100034540c283c45c0a888020050111a440c41c20541e90b5640341e014090417480d02019171140a151922806050022070607102c0c2c20145440c0c0b0660340d80340f9648410000c3e000700d4803540c1c82e640d030600c1710078443d10311400c00303001c54108281c0208840c103400080710070007c01003d4140010903825030401000900350000b1584141c980b01181c0900028280282c0007402d08505080c120025004a003c0d218192041400e080d500c1581e2031756100d003564058681c00040100b8851010100509007141d07018014034081a02c00d511200103c07803088508900184240f40184981c4101808140d0320814040007005640091030005110b40c00004a00103e1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 462136609 1250 462135359 462135391
    0x5180402100f0e06070c08012f07030e27090d0203040e150a0801020910170103020d020a080613140c01020d0f0c050f030d0c090b0d05040609020303161e020108 70
    0x56100f055030310714610340074040320303103424191500a184181c0743c01103540135400c0c0003400d16100a281980000701d404507008170500c500c1012208519405514250100083c01c02c0d1280c194031080d1060304901010040b4800e2041c80121043d001d0320043c0ca00c4405801004040e015240e000040c0d0707080d02c440c50341d00c0d200703a2658080f000b850380380400150381007402ca450002d1100c40c190b002d0012401c00766900400d1100c0c0310004c803501c0c0704c503110f51200008400c00610240c1090344480303440d00d2005e0105a2000e07128424185000301c101d9004405070108a4440304005440001c14130b9030b00500024101d4140060010391181a1809814100b24040704c00a0b035591040500352400c503040702c10703144c41460a010403516039001d1070394101314a04001e1501c1c0b40c64840c510b80c400303c4130f100b461507044c051284ea28901918002c1e0054a125440d200024050fa8041c0000c0c001600c8010308074498206615144821802111015682c0000c03802c0c180c0150740c00841c800c1c0e0003100306107180c0c1720f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 462137859 1250 462136609 462136637
    0x601050708071211011404060e0c0306040605180f030a030b04050c0702090402010e04020d05150d050d030b0112050c070b0c04060c0f05031303030f12020a0e040c0311130518040210 79
    0x13004074495142256081116004040b008441380c1c42c011030041209002c00000c0c0281143d860301d06003291600350384281c0010f00030420782e9028031303003000d8a525900f01c1a14001e11141c6030410100107541213400000b40b1382a0789401d0b200e0b000e04950103450500240c0f4200082d595680510800a400f400320ba4001804580c41031a1502c1921401081192100303034100c580c1d00200703404c4452065420f00c5c075460b20300c0d614016654941c8240c2c003030014014909004422000713006003802d91814817402940b003a5001040e4000d05d03116000b41841162200c4450414140c0013601170040c6450103010401844050790090000407016000008401e21101c5882c1c407910710304c01d098516207010b10300d120200802d40d028030000c14414003a40c400e0b011041090f003043c02ca106103062900440c416440642540c00c00744c2050650740e00303a05000034180800c2c40d0a41c01039218644030507039401101ca0130b001030305c1c20480c0c440409400c0c4003607061074941917010400d59030511030041c09200d04c560880c00c03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 462139109 1250 462137859 462137867
    0x60306091a09070201140c070204271407030507090f0c1e0c080f030c040509090105240120070609061403070806030712030201050604050a09020109052b140606010507080712 76
    0xa01060041e070b8141b030b00c1c01001c84000e40d044010100d1050781040074240c0305001c81500b005011010907070a41440c900c1d1359032503500b041c4c60219006280280030000000c64001c1c46408028040d10710081207003c000d0b905201100d842c8480070061090890303014664810405001540d20758034101a0103041e01410920218000d40600c003d8800000040040700c149070005041120b1050f11540103607124601d00b2402d07200c045480c00c00c008403400c0c61035030405001404103070850040c140244008800c1c54009004202180e500e1219800348030100811507025a000340148414680b00c400d100842c040061240f02c060031038010003040001245030350b5414003117500140b0b61040d05008162130340c079000e4040d040844000f4403461800c0c0004094810750f01403400c1095050b9120030726542094204500d0460001100010a00d881c610402d6010500c682110f403d000c1c201121403052a0000c40d494044010411410410103200600c009600b000a83d408076510144684947c0f01d100c0b0215 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 462140359 1250 462139109 462139121
    0x30c022b03030f29030d08130807030302090607052d0303060d0809090f191a100201231603141302010c02090708100f06050a0507110316060306091a09070201 69
    0xa134072000052401c0b040402c840c2e000480d0901a41034420b8807080883c2511000011121408070401c62141400012200d030024010580b0030b050050814070030102040b0b80c0e41069200309c425912004045032541ea484411441d40f902900b80e02c0142501844019201d0001409260045c1c0c800054107080140d04000e69074054805410341c00c0c1498441208507140c101507e1441c03c1039922040c400c032072409800346200000454840f05001030042d420b100d1a0344880703800c4000c55683d201011048841c081d20490784401d641110105400c1c1030281c99504100c003c0401d0070f01d441c14040c40442d2030700500c01d583c40041c00740500c000174002c0c001692241c0558000a6000846100b000031a1360402e5030240149401c1d000004002e444071409828000759026200100e0420b0090b84c203c80e01c2034006060031841504e0483e000c040e01000b00340780070710030a130910f498920050140b000b5603061007000005e080e1101d007444000e06869080410000701000c0d140940c0c00c41c00040e2281c0c0c001d400c54 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 462141609 1250 462140359 462140381
    0x50a020312030106180b09101101050702030d0513051c030f05010b0315180606090d0c060f2d1103090307060f030e06040b010e1003080304030c022b03030f 68
    0x5207507410300c0100c2955180d4000d029403808583c194407003500482440682d2001e035003d90600500c0c2c40d08441c20402c00603104d451203020009c00014145001d80300303008050003a40541c0080d034640500440c00c500f655401001d0f8400d50001804180c0814400200c8108841c400103840210b1242010214041c0038810300f07070400641030100000b54040d01d03100452140f10b140010b80f1040310f141d030402607180d50281d40c41d500002c561700842c0c0f4900d00035001708003954004000b16141d0041e40d44401410326507502c00d0010540d04c54030914510380004083c02c0002d02c0400100c0720b02c8a61006a10000710103014070104201026005c600100030021910700c00300040464421070380d00d4038010030b24440301c004200060308280da84a281140007c0c2c55025a42c00030b94002c00e60f083c61070945c07c2020050540c0d00a0041d220000082446007000354040c500070fa4486045d0300d0280180144602d03955000f0840f000c0c40c00000304103011804041011a50500c0c0c003103000a52100000040c01940d054 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 462142859 1250 462141609 462141613
    0x4051006030c0219050607090503011a10050c060a060518010b1c141003061d21070f140601050d02031b0102160609080f0c030304140607080c0a0506090f0d030504050a0203 75
    0x907800070b100c80051551f20401c0c056985602441d04e50052500f070380d4000c24192170400c40900074000600c2c080b800b841406c05a86405c50410b19440341440c03070034109540004900303a40300c9041c021414803c4a0941984851442e020070f5454007400c0142840303403041c1d61803030302c0405089400000040d00000d046044054040340e050809a101003821480c51108a81c00d03885c200c80002c02400c188441c2598002d0700e0041c05502d41c01d8100001000301d40182481202000c0000000140450010304500c90042e00c120030040880c00c512407420380182c11182c490041d48021000603640000c0d1029240d40d81d07645005002c400c400140d03d403070003162100340c1d80a08010081801644000c0560445540c2c500310341e50aa6082c00c0c3c02c2c0c50707240d14100c160705504104414440d06600d4403440106503400703012607152400c19150302455800161000740e40381c200001184c140031040110940040190000d0025605059655541c868001c0c16080c24151114001024403006000c08000390b500541 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 462144109 1250 462142859 462142903
    0x3080f0c0f04061202040f180e1603141509030a090603090c05010e18070c021807050306060307021009081b07270603140c01021504020105030f190e0106050f04051006030c02 76
    0x714012401311188108e04246060b142e5100104001803070380b4035182c0040c100d01d0660950319101001120750402001610a2454001e0000d50344006140700e41c09200195407034207041d8400403c0e035905984502c00301410f1a0981021071180b40c030b04406c40701e00342080000d5815407008036100301329031808001c40c030400c070342000915604502c8440701c0a10850300d488040d041d251b00d0504110083e2500e4001400070700c0000c509061882c000c5070001d80600407203204054090b07101007555072090085512000116244007150315061803030703900401004c00382026500300701054401200780c00081a851402d01001d4415010f958001b2014680214071551400001b0f05102c1c0d43d9242102074034018845c0f440800c0c20075040c0c0000c14001c1e0780c141d44042c5140c0301d0002c840308460003d844c0140310070301710140d41d00d4400c0500c10240d18204220000c02c0052401e410845621700034001d0034003071410142002030700e80007400300c0700c1541c01e5402e00082b8106c0c41c0c00120b1500c40c1c485511012195000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 462145359 1250 462144109 462144119
    0x141324050a0f051b0a0c050d050a030507020303060f21010f06050906010f0f0815060d050f060a0303091203020a08210a0912140c0a03080f0c0f04061202040f 69
    0x14004900c1a40401c00c24821403071000024011100c0c11524000040c5201e015000541c1c1200000c21191595240101e0748280030380740e15043c40d0828400e4408a4400286003501e036806020356548400c4a0001d1421803402c1400704403030f00c00c0010011312504c210404c5c0d0321081c3c2d8004501140d00c000740c008000410341400380100500303d42c0070347d912170f001c8503001803c00d40c4030b03200044010340c4540d43c0c04121074454106440180c0c0c05480f074200380941140d044550b444603030107021519103103800443c1e2414445050386030700700081d040c40e0181e45401000c3c804603400019200440d07844901140d903540311420b0482c10000ea09000404540c0d00140c0f00441041514880d60b01b00035420f0a080c842c1c403031920b080102c4c0c6034041c0043c041d295802100c44c60a016000340404100c1c01e0702414a40002150f2030703420700140c2001100404c8020091202074014190031036444004802d040b441c0c040c64850408080c0110b1146104200c1c1d40e6000700e0740f024054056a0082c0b0400c40c500002036250 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 462146609 1250 462145359 462145361
    0x61a03060f0301060b0d020f090d1a09072d1e150206060a03060e0f1608060906070c12020a0f030305040302010b0a14060d15080106050102070603141324 67
    0x2500e40910400500300000d040345010700c00c460840721050301880c50802c6012401c0003035080641408120802030012000030b4844201e80c00a0304e1003200b40e081c0c008108c51240e81d920f08050b050300c42da6480700c0401c0c00081d01c052402ca00b025100004030b002e49030803500501c01600c10303400004948003607015240c90041e5425070a0281d070740c86407070341d541094282d20490fa1810112280c980c00b4007800d10401c04078007654407820394455080140c0b01c100c041c021019142c020201030040801052500c2084419000d0086a410640e43c03009800740741000c1c04000c2c80c0600c1a0030190402d80064040d17012540200942c0307400b580d115110701c2c00100390f0b00300a00207041c215003d6026500700703242e1744154500310860300c0603250b038a4040c6242c130007690b0030b0100300d4010002c2041c1140e525a1205481e000f02d64036400105104400800e81070308000009040c02e94aa00c1b02041c5800d003070030f44000510f85408035034040c5500301c01741c0c0c56494908210040204010b60701800139416441d4404074005 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 462147859 1250 462146609 462146611
    0x2130909051e0312012711030a060b0403020d02060a021c02010c0806101709010f0609060305011b0806010c020d021012050112050304260303090d03110702090f0406061a03 75
    0x30384020461074051219241c030b82c403c80e000a07807110300c0d070710041c464403403008241c0004584406d451000419107990000071100c1e803102041261902104001443c032103806010301030040c1c09061420a49184e011400300c0280980c003d1040c103010030101c036461700c200200380d14450b81c55442101c1c80804035010303000341403045100c030000b50440e001a107282440024091025413640d10040070240c6804a50b00c16980600121032030354a640340043c9a00950090101524018800190451841c0350280c01c40e2601100404102a50000194095001156254000d10a0070400c210300c54900c00078076200c240550081d804851140d1824110360b01c40d1051864030000780c401c22150340c946500140060050070b0090050f842007006100c0a001030301c5141600c3d0242c03406000c01c03958031030f080382150021a181c6c03050354042580900c0c00360303140c0101107140764020601481c0040c1c50700404c0d0b03007140081c801007070864084007183c100405075100c2c900510320720020303d40000c23a020540c060307640 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 462149109 1250 462147859 462147883
    0x200c01060f05060313030e030d0315050d02150c0703060504080702030d0e3703030503040c050f0901060c03020f07080f070509150d03030b0303040905010509280213090905 75
    0x200e8a00003140c09280341e410300e0103588000b040641555180842009118040c12046040050212982200c2d440422001c8a4190a40c030042035800848851030702c080c40607442a8400c64141001e88050f84802c2c45002120183d141d0544d52518525546841d0141a030310051000303107410200014400c0300d001900900e4421015940303d040e84100844174415000d200550060440390780388905101039814840c00080c1c654460040b46240180c4005a1100e43c020381c0421000400c000400c07903115220b002034201150030316072400608010400e05901400b40307200b4000300650050905000700800d0300b4020031801119842526a81c0094482c0b801480021044c450b090001c140ca29002150307601c01c05d0f01440d070014042982c07080101c2280c00980c140d007810341c0c90040046c2030b00c00740014001307418004404101ca516240174040b074044002c0450300c0a50303c0801c50700341c882c5c500d460104000d62050f000b42c2c9030800f42c9440868101c0581c8020350792850700700507404000c0c01141c5145240 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 462150359 1250 462149109 462149111
    0xf020901141201092001030b030a050604050f2b032a1409280b040e07090b0903061b040504021308010c080f19060306020c06161d04050a200c01 63
    0x34500310b81a03030a07a02c82c00e000400000c07a003002c100f900000c080782d00f107450005240104a41c500400860f050014000d02a2695000705c2c0c02c20050001c00c00003e2038211003500140440e00030724108211039030720f24080f00c1a0201c181c602180c0d01344260024010f1182d1a141240031602c20f103070300380740f80b40209480404210300382360341d45055003840706480c0c1429001d4821001d00e01810350440312150300d00745007420000d1440011500c540312a000d007003c2c000c4c00c4a500741c10f0500181c0540491220b901c0000010410401c03d542c945022403c0b030342104003401c54084080102140b086540119004141c000340b001c101801600c070241080c1c402c0318000d8008000d039140c0820122a680d000302c4a00000701c0801d800300301c606420b560190394900f50000c00251050316940d501d8180e0348180505d441c1c607031000c0c003407081c905551241000103c0380d43c200081298400014181c0c1c282e040300b60381e44910340d600001454821a0f4100c0d0410211030402084441c82048254019402c0b200651280c0c1d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 462151609 1250 462150359 462150379
    0x3070504020406080f0903070b150f0d0305180406090e03090a090e0a14031c1409060114060d0e0a030512100308040e090a0b0114090a0c0c030c0f02090114 68
    0x2908140c401c0b241a40d00c01c1c0d803007001d42d999801d052041500003800022407031108109030710201d4003c0c039416000742d440391040b0110300d410707000700b00c2101000c2e1491441a0305140d250703c0041d0b0000d0842daa580008101c1c2d9090b052440f00040080c521a8400a940380c10058903182e001c50210042080310000c9842d03414090312146198100d83d549102d00b070880d400381d44820007081d484d4803554040603158084a00d01a444942d00c40c0f0045c0090403540c04544646800b50500300b040b1b411a80002d00d04001c00a944c034052002e401440344101e41ca0040d000000c079003041e803c20380c02045100201d1009c54061080902d40104980e010140c81c2c41500884800301b22072030014115076040300d800188040c103150919891114100014250581d24810204070800042030a00441d00a00c10180c105284c200c52609101481d00c2c01000103650501d07010303181c521590000d0840000740e41600d0005601d40316890a03041c0200300740c07000703540b0202000000031190401130342c1440085042c1c82c04000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 462152859 1250 462151609 462151619
    0x20d1104050a0b03040f1b03050c12071202010c0b040302070602121204080901032a020f0118080307050417030301062a080c0a0606030f030201230106120e010e0c0307 73
    0x440c09a8050954081189001044031510040107160170a0103401c45c03440d0301001da5074542c00500c005110310484004000c00f001131003000d21000e241910107031407291103020a00c1d4a140c80d01c020340500f009001c040e5908909591042c00000b00712a4040c61101035820a0b00b4040d5807002c562194100501c184280700d414001d6001c103661020040030003848040e00e482c0d56900c0c01c2e0b0003c80d402c078101507460304503050340d034041c8441305141101c6a10307011181d201960f000b807d0060000c070b071000d96810700c0c404810001100654000d02900040d03070707076101c0c0ca407804201c1c0c40c2e2043e03510441c50b074140d860011461840110007141210120344900c00c00c07441071081000c0345444d8601c0c04a00d250201410f82c04220000700900c0b0a82d5040166054a10310343e444038200c4005401c01daa00e5a04100d07010304240d024413a1081c81000401c1800100f020440c200e210641b050003480300704095800f80d40c06110031a0810460b54900b2002402012440c07003072a41d0700c040300c0920350b20038801e03941e000034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 462154109 1250 462152859 462152891
    0x122406030901050a1b0215180d03090b0604270204020c0601091505010c030f140d150f170a080d09061802042a03240611010b0405061305040c18020d 65
    0x400f901e89401500031047c901782e8a0000c200d0091665210350400381d00401200018400e040390031340c06460001e44200207003044000850020400343c00381d8501030954100c000031050714000e010001e040d00115245600c0880c000e4011238002d07090f107100790b000124010f07078035400003041d00710046400c10a03250b446004464610810070050081034400c201d001d4468416513006460329407259455142143d0844413004841c41940110464018203805205100811400600904c3c88202150641940c0b07180540c85011954006241c82c41c0010b101e0b142c100607410407202d05400c00020413244c11400c80d46040c51002d8041244964600041d80101803e41c0c5c18545c1c15400d4041c0c000041002800250000c10860394040d03000140c09240c1c0d985007100840d00800b42c0070580c0d070110003160b0030300341178207445c1156801c500ca6800c000c01c0001c944c68036600d08442448014002c14562a1401d1500040255401c400c80e1001140e4000c140c0800d44d8005003641a480c910420004600d814041 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 462155359 1250 462154109 462154151
    0xa08030f19140402011803080c03040611030f12130204091208060307060801061209080c0a030f0914091806070305091614060c100906140c122406030901050a 69
    0x14400740e050b280440c001d54812060040c050390805818403905031252104c01031600450b000b01c00c1a0300025080c40704590150120914404880080d8209504120130380031038000e410f060426410307080d0008104181c07000c145181190094400c1002480318280717181b058510150040c0030030001008110326040000d00350045458503075500c1042d908000e01180d00812203840700c02c28985480203180031815050003068200303018002860010140e2501902c0789910240d00010b00c2141c2000f0807040040e80a180c0391201c2c1140d4229040c1e40e007041001941c4185044034000348542c00401a14070780503400030b400b4003d14800c43d024071001c8120007a90020500480d904911705a00c1c01d1400c0c142800644643c0300030b5401d485020b46000c8400080790340c03000040e01c81580f2244d4404040380c41c00000c60b08000070400007480c0c05a03c0c960412507841c0130301a00d400c200c0658a0103502629042d0403054800010440350356400c06600c018040c110a0300d030448203518040f0840c0703807070000004030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 462156609 1250 462155359 462155381
    0xe010f0e0405210c030c06011a030f0703091e110406150c08090d120e01140306010c110f1504091107020120161712090f09090a08030f19 60
    0xd04001c04a400054101c0b200118154583c0780306001c000c51803c800d0018000300e50094004040d658500b40240350a250030020007201084100203001c3c010140c859040d41c000450704001c1205141703032070311511032488c4680703044540c02a0101a401c02c4288844000c510004031414409540c4030981c09120070000d900707107404151184d0400002600701c501a01c034502c070080250300c0c3d03d03021340c8404d000ac01e51940341c50006001100400559038203c0032030040d45010348a01429403803c240080c02c0c2c44152440a08a080d0707000140f5410b548850810b026048094041034403000c1400c11055181c01c540580c0d020396050103410715101c00034005a45c0c040c1d405940e0000c100000280810810f0325400d411000c40c0103283c0b141030706407502401000141400000e1540600782c5c070100a0400742c0b003170740200c11040101b142010607510201c0d2113420341000c03a80494103840d11140140b8040414100030010740d404400c2100102e14900c1e03030b620401a401e25420100c0103042c005085079072582072 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 462157859 1250 462156609 462156613
    0x31e0f020706080402040b0a080607021506280f060507020307080102090906130f0c12140108100f0609090503040303080703050c19110f06060a0501081003080c03040f0e010f0e0405 79
    0x1c02c601da224402450b0841d0002e000007030b02d5110140400c04060040d0040941a884942800845941000a25846e00f10703406141480e08004d000280c00908015411050418281c00400040e0bc020500001040540240c19519a480102400c96004028164824051440001690031040c002c96028400051034550035550f50030400a01a056417503020703d103a512842c0358041c1c00280304800e55203031103842d103000052021040b417058517007014030070a40c100c1e20401000705180001d40d403000e030400000081200d02080151800612060b0700c180c20a80c202003484040c4040400204103803070003030746c810f40f15668400c0c0507000d8550030303520400070301c000b04640d0f40c942030070b0002e8040851292500441c4140080d8005241c0010f5510b45122030300180c090084520346070b460040245802c0c24100803030f2408005184c2400c00c01d01c0003520790800060b0001c1091414411500500b00300c69401d62120307110103e01448260034041d0250034102c65401160114071110308a21031603000340 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 462159109 1250 462157859 462157873
    0x90803041809150507020730060e0f1b030106061e030c26010905090109030509060c0111070b010f061103190203160819030c1205061804031e0f02 64
    0x2420030020709402e00d007580c07980810100d0b107600340054010a030083c181c5038000d0104605006460540100400f061132001582c1a55441c4414902640802180e044080054402940824141028000c0403484000c1c010760b4000740300440d41440051203800c1c00e800822040380c0b50002560340b8507903000d102034072194418090030340d548a50400d5a07088003901d40ac5050507a20000b1080705480541300b6000b0101680c0184003800300c620426600910440092000401d6504c010384a0721942c3c0a282c0100c0c00080c40c1551402c094000f054034440e50b0340c50960310744813420b1071a520802801210509022484001381d450301c98036412517001e02400203107280c0142125103080050b0150207802c29804241705a441c4140e1071a40300403528010550b440d80c5070a900000074400ba603541111080c1490007404403041540a00300d440f0018a80c24009420740b1140001030991443ca40f07801d170070301492020001055031040e043c160002441c12452030308842107600781d50740c00c204c0d9040030041c0e006075 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 462160359 1250 462159109 462159149
    0xa1701061a04030b18070b0a08180c06180d02030d020604060e07030803010b130e10060306080114130807020d030f020d0f050a1d0d03030c02070e010803270a0f050109080304 76
    0x8144c110117900d440084031a00c3e0741e20300b6078042c2c580121a8210104e000c0d94100700880085d208038548050182000d86120301d03c01c000075401340644d080d035884001c0c030b0780072150041d1510044031003031036002021110240e000f010000d64a40c0212000c40d00c650a20140003001c40d0005908019a5031000d21581560b007003441714402600f04c1a00b80c400d40c41011b6000882658803043e0034000d90100c40b80c60195400c040c2c0140c103885407544410041da00d003241c0c0e030444102482d0a190400780da81075000c038078211404c015801740035400c0f0103036012400360040010540c10003082d1030b40d16078036029211540300c2582c042d642c2081c40406203004c101c0c10442e205185200b24841c0414800041d55010411502c10100702c1c5402c8004044000c21382d5a0108405243c0412249004282c1c000c000c005640c184045642c403801909150201081e0040300014041c1000714024900788010b404102c2c1c01d40c0c2d6410040312507040744985404203110f140041781c46036000c42282d054820210390342981c59105 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 462161609 1250 462160359 462160381
    0x60806092803050909072006011523070515071806050c0a020f0414180f0303010b040302040915151a090a1518030b06010207090605011b020a1701061a04030b 69
    0x41903503003000b00c403450141003134600040451020103541c0088c04e5035814894080da01d044220062001d019203501c0180303d0314900b0040170b41c1d0f599a003605903210340300c40c501103191070b030a41c10803d001141d050030030100c59403245641c031141d242e980005204958501c416034261080800c86071854001403040f202505210100c910b0400000d440003622640d05040c0708644034080d43ca03003070a2178081c0721070015641c080101021072003066000c1d42c995403419032041441c1c412403200a0245444001e010300344683d4500741c140c8070b449924180001c0c00607194068a104d02806100f04440070783c640c0d000754881c14004c6d96805603024240c4031906082a903c5180c0c43d01c038081410070088030244401c200c0c0c2c403180d107803030003940b060030340030500d0416000290034040c0325085108814034003d42006103a03800301c80701e00440e01100007103500481c10300200302a044180c0140f00603100c140000e41c800c0c82c0540c0a03004682c80136005469800041c0d6034200d0300c2c071a5110250441080d000424050000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 462162859 1250 462161609 462161611
    0x9140f010c0809030f0a060b01080f19021e0a02060a0b0f0405060411071a0601050a092612180a290909101404060303080106030f060806092803050909 66
    0x1601d0302c07900740404200000c0c90403c0000c0192400d4009480364810070440f40180d41b0301c107001b420f00710468074080c6440030f0b60b000001e003144048070044185102c1410545d048400440c021000781a44130200c08020b06076a005161241c018883c0700000b4010301c01c42d208041d445c4000800200d040e1800404220107040d001d00802d80c0182d0f280d9040500f111b0380001030000c14410480046040d0b0f6440c0c100290110050005061003803c008a49a282d80002290142c1d02d0b81c9076a544455000948003070701c100c0c2110400c07681d204d0020301c6251a020400505050038031220a410440712000c10b10590040f00e20440c1108003580d4403e8040100d0141306124141d19140014180300c440c00c0060a140c60a607800e120000f170071300050205034080790401d414040d05450034080546103a40013082c0007414411001096910440269005c0042c5c1000f401451f0324402c03a10300742441810140c45812070700414030a02c4000800d42c0d45054031404603a8443d400d515090300300405081807082c0544 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 462164109 1250 462162859 462162863
    0x601120212011e120f0807141e010c111504080706050a020a0909021303020f030f01110903160f091a06030412030f15171f0b0109140f010c 61
    0x9024060000804107a010160003031103014010071a04900e0f00c4040100c06840c0c1210700c141841c4004840402d6460710b0180f111030703205413a5a551501c2c0d0402078405002c1645d0a44130b030041a002c201d8a150581d03014001c004103000810a070b07130240c803040d0b6800c4603901690009410240c0c644a06484034180d040d80036006008041c50604150780d030104444040300c0030080d0075804200c002d00320746d00c240000040d0010020451a1160000780c051402469100080c880c00742c8000f0060192018004200010f881800a014000000c080c0c03803d00e4000040c41401780c401c00903104010a0540e401004490b41501903200c0c0c01c3c10034100c003005e4080295070740842307005280c640340d00e52101c0300118440d90003101c000f01c2700c4240c41c0004040d1172038408600300c030350b00b1b141c404030000d6040311a04d401c850f44490314000c0c0700603030b400e0103050280200d289008a64002e000c507010705410f4109030040b9009170384841d401926540381801c2000914091500201000380b0000a940078031030300e41c0058 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 462165359 1250 462164109 462164111
    0xc02100c1b0c0303020601050f011b02150c06090c09010e0a0e12120615190e0409020901170d0507200d0816060f020306030c130f050106050405031b09060112 69
    0x141041e6410a901c025510202e411103004a000c00034194107000203400b605046915200c602281c50000301064441440b5050003500b60b013903601103580301c0d003031000440e266034682a15260041d0003c3c0c3c90306000c6951011a0003050b58042030351400450050682c3d00482440e091511401e1011008028001c041c14551180100c040006030351302c1d010742041701140c641a0200d2900e0310038008072400791101203002d1002030150040b02c82d82a1840d01c0403081072300d400364007100054000340192071131144c0690049109000442c0d01501c0d51150242103031400300301c50401402003421285881461400b0740b40010302d0300c180c1d82c0072906017040019200d00400c45a2110070f41d07290320060303520060041c2d000840d81c0920368200080c902803140c0c04c0300c41e41021415458050082500c84004000e40c0c0c4c4151000040745d02095003d6210341d00c0c001508004104542e1a00e002401661081c01114403907c13070740031486426548943c2c0c2d9050400302406208003902c40c5001950002c24070402c1285903 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 462166609 1250 462165359 462165377
    0x11071d0c1e0d0e010c08070f0f031104030602090315040b06010e0111150604151206180503040e07080c0721021f0614030601060e06090a0e150406090c02100c 69
    0x8029000600100e40300b01e2000110051440610350860f2120380d40130041c00f181d2000c102c0c58075000034014510b0b511500304001701000340300044005083c4d0603210001c0c101c01150201c01e008072a4017a20440c48194100c910421030040842d0030710b441200c001b41502070700c400048455100303516101b062681030500400000241c5140f81c2000c150f0104100282d0303409040280b10320b01400342d9000c020700c1302d0b00c40240c5800d02d242212000d5941d1000740540ba124180001801d442c0c0482c4050f040c0c000c415680c90351340b00c4d82c00c50300301d8100780c68040c009100c00000c515071415000880790340c5540a01010740d0041c3d0a9220aa401e1486421206501480446018500c01550601200c0904001c0060381c54104a0003880d10201d5108140c0660f02a20042c1f000c1c03500000c82003003d4604543d195221005030700085c0311000079802a0301080c0c407042c00d202000040c104ac4101c1a64112000d020300740c2c03540c990a041b00e0713010070070f6801a441841d910b5400401c660008601d410390340341c480e0036 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 462167859 1250 462166609 462166657
    0x11e08190302070b0c03031803130e0f0705040b0901030b0f120a1a07121a060a02010b010e0411120a1d030403122d1e11071d0c 56
    0x349580c680c0380c03a03400034102002038100340d410b0040c007024098901c0c80310304100091031001d41c0e030700004103154880340d86151490341d09a000c000742d8a0220f07001c540e004a13036440703001940d101c6000703482050500340140e010447c0140190260b8081e00e5030030b86030508107414000118040c1440c0c0d10003a801140d482c042500e143c58202c812010030b41030000518050821b842c1080c0e014080c1c0d010341d1000204842809081a404100000c0700da00f0580003084103071030034617040c0802d644c9414455201100240350200586c040d040b03501c17141c1090b21600400c0b4400814801991025070348c256903030208206908204400600050300301c01c01100000c0c51511141c0b0306001000501e040c00300e96480800c00700200501c7c40e148240689903440c00104140310008405a1130b518600c4c0c0203104440c030400070030440e100c0c80c006407104500760701c1429a003080e02000741c08800041d00640690003640404140703120241d20b01800e8107100c140c0304883e0fa07118100741d0143d4200c1c042003400c8802000404d03072 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 462169109 1250 462167859 462167863
    0xb04091e150e0a0201081e010515130f060807020706120906020d020f0306031e0d0e010c05060a020405030f031603052b0203060a17060408031012120212070b011e08 72
    0x2041600020003801c0c0500c6a00000d401018001e01fa0401110051100c0e040400492150790466a0540b07040140c40180c001a0b291750182028850020140c003800003807202d50f08100e0021950651900071075a1200c25080f44c4610300d46c003030360000c26804581d206286e802c039400205c2d03003405410018240b001c03501c8000c09991100303100c03204401002c424000c03240750078001c120707611001d011080c44100d0b050314480d031965003040304501400744a45900240c0e90103240788018250340700c1c0c1514290702c1c00a2008000390001d0003030038080c3c0300d20620070303480c40c20020032516529640c01c800c034010302045da01165a64456003060035030405001c200000c828140b0250f90a044006802580360b150010900c00002195844140d4020744805c10040d0703480e010909070703003054001d94000c0d9250b64100c3e1440418a103035002100007003040d94401d05001d0040c0100082c2c107200d5084d00c2c21a40126055140c0b8014641c01511900607040100002c10042c1c055402290720024800c80c0a680c6c1c0c91a54 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 462170359 1250 462169109 462169121
    0x605130b061f0503070e0a17070509160c02060705010906050f090d0203091201150305010504021504120b2a0d0e03091c0611070308041202011b0e1c05100b04091e15 72
    0xc0c8e086040752900c2e40e59150305029507406000c2c190b0b565406854004000c04581e00d0550383c3d003044c401c0705034226066480c0d94044400480d0460020f00101d801890288000c0004448421501700b41c1c001249404201081072210740072158021420680680200150030a0400c0400155903940c1d55000c1a11800700011004502a00000071180381a005002d01c10444294034551924100010301c08030483c030ba40c08031182d80004241d0400d079544494603c14a49001d8440c3c4c01102485507407480c04460401040c031180c004c0010b1054400c604da03070659074024044072591080110142014500c00000102c030303014082c51001c1502e1904500e0300d9490b90203000158002144d040400040c032800040d0132034510160720080085c9a000a810208084500200000c100480b602160f50f1fa4409507940c40e400804242540400840c0c900650740316800171009401d03a0034100211100d15051059003030040e001206002604090210b152001c84d8041d022905a9840d00507041c035625288219 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 462171609 1250 462170359 462170369
    0xf09150a03050f070503030a0807050310030506131106070302060f040f0b0c04060f0206040209010909022202070c0603091505091e1006050303040b16030c0605130b061f0503070e0a 79
    0x151048100f22941030f4146443c90300701c103010303038402c20400300d813130b071703110b5650f50f80800c041c40c00f030b80c60391203046503a810161030343d00c080e2003482048144051360010281960b80644100e01e600c004201f000d0a002e141c0c012032034041c0c0541c0008000859841d482d04403140e105108628004002c4400e0366801c2a0303d0054584410750500880e0a200741c54101021100d60402400100003600d4281c3c00180c0002050003142083c61300c509100f811525900d00a2481d90740050040d9245102c480081009402560f400d072440041c160001448034020702c20021b000c0c0d00004100359480d101c0d100d590142401030b184400381e11031440d1f505404001c3c11039810300b04143c58068100220a102418107071141500304a110341c0080108020b40003007242141c3c0840c08000c0c400d001c410007403c0075110301c400ca0b50051b0500381800c003080200419503410030130780d0b44100c4414160fa100c42040c1b0503184000c0c3c0c41e8800990703a40010001030307802403002d160701004a00e08002000040c0c0d000c0b0368642090385c80b03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 462172859 1250 462171609 462171613
    0x602010b12010219050c10060b220b040e070c12022d0c040b01030605091509070305090c040f200c010606080702030f0a0c2301050603010b0f09150a0305 67
    0x11a400c903180800c601c0080d070850034025824004214001003001070f8501001003031240004060240c01c000384281d242281c0e84617410001c441d6550440780c41c43d0312601110131070740c0c6801d60025803941c2070704100007940c10815031181050704040c00c0350368115010300550f050060907048c040004900c91808400d940c4168082c1c000c5c0340701e803040c140d45c062480316914080b040c1e4020304400c8c1c00000070503000d681c03030440380071592207683c00043c2c00800a0360000747d0001100c40401c410805071400340b01401506445500881e901c80008404844040d5031240d1141c010513902e0400307241c0350700414400381d884140090520040807040040c0150390300e55030614440800d1101c5c001c0c02c00c4c8101401412141801d0b0070501d045038000b0345910600c0e80c000000b40012401024003031207005003107171aaa004240d1880c424140c420b00c0750104030344008082d0b035800c00000034261306040c001e84400b101f02400c0c80f155290948104000070400402d00d00304607011000e4103c032652a00c4080c0019409180 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 462174109 1250 462172859 462172871
    0x415361b050a05071e110a061d12060702060106020c060a050304060509120a03091b05010c020d0302010b030d0306140a0f090c0e06030a020903060f27100e0c03070e09060103170c07060201 82
    0x80c0c84500c03c00404030140c402c0c0d102d00810007232182c11882c0e603040c42c100c80c8242980350300282c0003c3e0039200881003114542c0314050400424540002d4003506845994007207035007000f1400c0c1001590f100e09203803000025800e101090004a0030b0b000305401c0004501a202100c001c2d012582c1d040e04901c110070002603c0e00780c0310040c4100902ca403004580e40344485620349042c200041c4c0072809541c0028007500060303240d001818070030f40c40308400103801025140000c1d1a240000c001c0c11250142c0e00e05404164403000c042e02d841c0014000300c413282d1411141081c64a040c2c2c40042c03903401030010512416010500030356803244011441941c501c0c00058075a555441810300c2c0c4030700248a1085641c0034018880d014506804c0c201e090481203803004440800f4141711806c0c00c801c881200710060808424200360f00020803524020746091302194109036407581c1215586000b641e82c00d916801038401800440c03005541c41e070010703900c58101403400c1ca01456203440d01c00182c0c004801030355102 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 462175359 1250 462174109 462174113
    0x50d06090215030714031302060f1b0705011e2a05061e0117060a0213030f06050403030b03010204051e0d021309031e0503060415361b050a05071e 64
    0x20901e0001d45c010707040003504600d099500c00c2a129090100070348500808102940f90b45580004c03a80090380e115840c2d440d01180c01c1d5116034444c2c1078044c1c603011408410381e00300300781d0766240f00c203100c9200e0b07550f203d481c408124414400510720707078006400071741e102044a0101340200401c60107941c02c0c144408071000c0462244503c1c003410b07009800b10090b0300c1e1030720414141c00075800d500700a15890042e80d43ca00000c3c00c00e003007215940010a4440e5003d64201805102e82c00346108034082e46040c02405211801c05080380308500400307130302c0018800c8140c682e81003100c803a00000d00140040e906092507400054170701c00600190441e5903150b504101c10540c0c04095520440c5088200f03141c014040100a41180401404a0300856494080314802840391440034000c06241c3c1e1041c4403102d24181240134903280324010500e41822401030401d4000074895100d040407640d840f101103004814088842d03600041d078107001c02c0014080311000c904048102c12140b0200702040860105074 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 462176609 1250 462175359 462175367
    0x30621060a05134d0a120f1410140603010509060912130512100f09030c060f1b180e04030207170a0602041205010c110c06090102010e0706030c0809010510050d060902150307 76
    0x5500100c003c041da03038017400c0011f2940403500300000c0c0d000c02900d80e1420640038403841e012181c07881419540c240500344d146080003402c0d041c00303041e09400a01c440c2e80d4110050341d4074101516034280560281481c06024041d0354050494101040714518805a45000084581040c0041169641c00c8880c80c40c05040c0c0a100d81451150150810f114865450700c1c043c021000d0040007405c9103845415003607a840d500c8c1d04c11489620103048003d20034002d0b0390300824200c080b00c4206042c44000b03070041580c031740d8000100d100d15032650041207a9030400340548420141c00c06a407407a0300c0381c1441940014580d002400103882c160045041603255070500c2400d481c039000e42281400810b02102e40703009408518203c03120020744c1c65558135000c50f40100c2c0100000c410b40801805a2113001c80d0182d0300d82c00c1122102a0303035a80038a2500c403007083c142210f4041c1c8107180ca0712650300041143e8100486984a00350042600180b28410350b004a0300944034104030103860300d00041003050423604 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 462177859 1250 462176609 462176629
    0x12011d1003080d1d01330503030f0702120604080d060b1c0c090305101a040203060a091a0402180906100c030e01110a03110d050405090c030621060a05134d 68
    0x9480011006d10324107004642c5a201c0e500c610000000006244c1007952151203072840c9000e1001c04503090b80c80c00f030030300e00345503002418000c102d50305100e00001c000c0d0a4006035200c0d060848841c810501c6801806002081203214000502c51030723240000102c1c90901c4034004000c408180400c281c1251201c21144650728403000384981d2042c01800f2182c1c4940c410b08046c0c450300a4002035106030003800a04000a03da156580305000181884072448a00c100042c65601500d07400308507201c443c100b0440c00304042508002440b01c8906102080c0b10304040d00102034181460381d03518a03035002071810810103500940c0031511000030724800440410000058003524034003207040509000004051981c05032092460b0785c00400814103681e00d050050394800b0215520800761207407090030700d486290032111040c00901c0c00c00003034100c80401c0c6554620310340c0815102210041c4500c0e0410082904000c0c01440300c0c103c428443c10a1410880340200000310141710590320740c07000700400c00507 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 462179109 1250 462177859 462177941
    0x20901120c200c0406091e0b061905090d080309150c0a03050a1d1b0a030b0c0a0c14010b1306030305090d0812011d1003080d1d01 57
    0x1c5400c0710404026848942500c485014402080c50048103180c00e40c07030501079200490303215103000000110a8110b900c0081c402c401124215602d004884100b004c5601400382203401160400c4001102c800703a40e6000c80030856400c0c80760802c00040701045035590041000c881d0301100200b40654013408201a00708240c4240c1c00d1400303481d00c401c201c00a4047e08003420280741d04d65000c14140411500072000390351800382c406c0f50301e41080104d103590340500d48501c125a0480305024103903090a2140f10144c4e5000169940b042d2502030751003149a01c10001d0300c041001c0d601f6600001040a110703040c2e603118000010480c0d03016a801c0280e00d03030b0030b00a034040c1c01e840d082c000c0000981001c10340b40014000c6407541d42c621100c7c1070585441c46448000d6000c10700c840c2c00810488170f03047c4908021000b00710420031590360300b030300c0d03480c50101d502025140d04002e01080400032460f4000c42d0014290803483c4508203c410707800d50035070380070640341c02c1000e215880e64445020980e10030700050b0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 462180359 1250 462179109 462179111
    0x51201140906030106230f03030a02160905090d0c030512010b030910090b01030b1b030a0501140f150a0c1e020108060a060c0308061f0306050a120206030a050907030b0a02090112 78
    0x180c40d18082980080100e020008408200d0303c03110341561f5040103075980d1841c0501075a503522508000251103c02404038280301e598180400710340050766220781d45c420761550000344282d0400607015140d04400500440c2008400c001115060480e075420900070140d540405440c0e00b042000c185c10310140c0001c1d00e00840ca04520800899000c2d80903a0440381c21182c124055140c84440303902a96020342c0d030054403c0008244000396030207501c00c0d8101d4140c2014100211001e50410415031302c0000490340c0640104c101c0342e0240c0e0480020000c201d0030f400e00070841c1c0c900c0e5856611500d9001802008158124805015035802079102130f44000c003129685503035400c00d4000f50001c00c840002508000100303000502c1034407808a2080360000d550700d50b03910b8503000400140030b0660360007058041d0594080c0041c6201428400c6401d4588c010301c51800c640c0c030f111084005200c020304c01130035842442030002c00b0034450408203002d0110350360090303503c10510001608899070500111809 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 462181609 1250 462180359 462180371
    0x110613081e06011d040f0807020303161a24010e0301090501060f050f240f0c1c03020c03040b0304050a0606031505010e040c060e0f04050705070c080f06070c030512011409060301 78
    0x9202406611030307005a00851b40441140242001c402d20300650100035050721000400c3d0300f6000d07100101502c9244640203c030a40c28408a04210507117003510b1400c00400d40c9070000c10550340140c0d191158800626061000020314030004c0d09640b5884015a00c596446130300b4002079120983c0000944011760380503511000c504003291842418501e42a8886252486034450340d00c4101111001c0710011800c139151010007000d6070b1943c10710403144c00009028401c50b120b46020307009a0701440210301c041c5003414a4078a4030b19403a800200212640d002c0d003000440007a04c14407604d40a14050b1164400780b43c400d401d001d04441c0c041e0006840d0031683c104120020b0001810201034806519040c4a088186008220110780000d10f00d5801402c040c100085030b43d114000d030405900030221400b0441c3d803a8086502c030551b0402c041c13a10307001140040c004602403910213115506c40c0c0313003951420504000d0688a40303405c0c4c00c1664101406229646d17646003c50305d80e500100120001c00103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 462182859 1250 462181609 462181649
    0x13060510050102030405060d0b0d0b011809020a120309031a070906020a020904060b0f0a03050d0e0105040e0105060f0d020f07170901020c0909030918071b110613081e0601 75
    0x1c4c074012885040c0c4503420000d904140e220070341d00a50312030300d0040c00e11040324640e4904404036010901442e9095550f00383c4050f40b10801c0d0080d080c48940103000850914240007400d459a00c000d4000d600340010001c0000005888079614100e01d40e080d606a0b80d0307070822002c0200b119100e5400041190320000d2004056901d004c00542c20039400400018003490407404911842d0345004865400310843c00d0009c1031000106840041c5c038442d55a03150ba046101c00107407058081c600031907a0f0010030300c00502503802c0400090441e0700d03030940c1031414020110b000a050741d000d0552031404400119805d41007056410301001b0600444c1c1846080401c1100000d690f540745900840c480d4101e040418080380080c0300310f41040c40c010700f00d19035008000c0d1980c490f094007500c00000048100c443c1c5801e2025064403805034a40c05241d01181c520f0110400000d43c02034254002400920342000401071000c000c8040914a01b14000c610422044215820301c107050388000c0c44c42d002c40d102641 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 462184109 1250 462182859 462182863
    0x10b030405070b1b030d0606020639070c120c050d050d0e011b0302010b090906040b070c020a0504060e06031018031803050313080c1f0c030e0913060510050102 70
    0x55030800503c10341c403007101d18400a14451410004074290000160760107a14a068100300c05541840c4c0031500643c41360039402003a210b00614580469001e405405c1015440081c007804400850f0320041c24498240c884100150b529488a454a00415059020004070685a07030041034211105030710301c40140c440c15280c0d19076100b20810011000c6d500c5142d6070007412803100c480800c0e6211300c40e80402d840c0c060700a0036901540c501c10241c074400140e010100140482c82141d001814215584819109462911001d003080f1382c41086c414000c51240c4880c1716442c01040d20022040751400c2010516003011460814984400d041200d44101007540b02c5802400341c2d81844d000001030312042c21620103001c540c100800034000054000b0304120900d1290090321140c4068551314640b820801c500e400038026402c50f10001c14490440190154017040c502600030305040d0424409440000e40c2400102e5076001a0785c1c170704220800b442802d216242d4005c15640c11921100c1c00c04001079 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 462185359 1250 462184109 462184123
    0x6030a021c14030f0415140f130b04030321110703080117010b09010b0c010603170a0207080102160b041122060e0405030f0708040b04120618031e09050910030308010b030405 76
    0x12401d0f20390903103104206104107d41100741c000d90100b5a2500450001410b03581d210582a103034500c1e80150100340303160043c0480c1d0071207a0640722031501000903444500501c0e0456a80c0d1001070742d883d80d08400304005001042402c0c4265580a46981880d00b4000400281000c2e100320703a1510801214548071800c17281d0643d000e04030703040c0d101c400c60185640500321030742000308008282c0f03a881000403581e201905811050340c0a5440980c0c96500b501d00301d02901c44a240700e1000080f542e07002c00c007628251034004d0b0007a208036204044402c041220034003000e90342c90966082081c0340260388c64034030a0340064100300d0051a4581442c1c4c40d91682da020b45003480c0c2d045040040c8920030806e00108580040c400c01e49980e0305c0303503520480a0707017080c40001c040d6109401c0024103580c0e50307840ba124803030569054680815400605d0300c0d0328038a0311003021603424840d628001099a0341c4a81c1c071a803107080c003050b00d0a10740d811440c00420403c01079007d034031010001d1061000040d004103100c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 462186609 1250 462185359 462185369
    0x9050a0311010b040f05040c0e0f070c061d0718060e06060315030d05030f0f06010203071b05032a040507080705030a06050901060807030e0d05090906030a021c14030f04 74
    0x120000c407032114541401001c0311120194840c0c60300805034603003005a0480c501c43c9019280c05204296500501089030604841ca440840741c82400661810300400c1c01c04e600d076000c0d2400288000900b10b100c84a000c1c8202e1420381948007160410280c00d0503030451828032030450f014485d0398603010040798402c01c05420644a03100102c000b8180001d908540e00807000700604682141040c09006002640700341c60f0390000b4841c0000003000d8160340392a45004e0070060740210f1408426071520003007070000035a0640351003600000061517079420410100d80042103406807185440e240304503558001c600000c1801141031404000c0c241d0f800c820b205500c100603080036640c80d030b5484d2840004103030540100d03038081585070011400c10380c010360003403041446440801c00e040000d105103542d02d0440c061000000c804011000103400c02c0400c05401040c083c0441c1c800c1d20f410340c002059980580e40c0075407080c9002c181c84040c003003003440000940441030040e51070207a031380244541e280300314011 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 462187859 1250 462186609 462186617
    0x30610020f121c1409010c090e011202030f0f010b030f06011d150406120b09060c0d110c0d030c1701050f1c021503070e0102030f03011502030f0a03091509050a03 71
    0x15a40c00031407100610000f280c005035007048600611001a038841000340c904400c0d9600c0d00c0d100ca45070038041c41d4048140c0f40f0800110230700c0c0e03103411582e01108001460480e014050030354000f89030401000f107504060070040021851840c180c050618101611000c1411f5a0010340100720719001c22600f03050b000103000d207800d101d550b08086c80c00b6900001c15281c0e045441d04000040b6010301ca1180e02c3c40324865080707401c0c1605c80303030702c066030b2002c0580d10040d031200c0422800741d80020341d900060352030903074001443c1001681088103040220716031060001c00d8032181f0100c161907001540340c0c1103075280080c0b650107505201c08580e031602441031850166030a81000d0010307064161260203c1c5a00400c1c584e00c03440c030303410100c006420640700300b07000c11100c2001000540c004010f4552a820510341d05046a1801215414446034404030b41c05600003002412038200740d0350000e000786281070303d0100e408455407a092001101001c1c00c20145031408483c100060008642c2040315609494 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 462189109 1250 462187859 462187867
    0x1806031a060d0c030b0a050f0702071403070504140f0903040e040303090f05011d0c0a050d23030a030e060c09011209030302160b0f0109050606040603092402030610020f12 75
    0x1141c00c442e988140607040c5922510000f0801105840f010320500c2c184409110946480d5081110007009880b01000f603007088206000704120410b041202910080441e1281592140420300b181d4007201c410100e50174481c100b10310300340791580c5550498074000c015031906280c02103130b004001e4007400080806072104424410701c6185a00351110700d41000003080340010140600c1803064140c00d1090f00340c0160b12118246141c90841c1c80100e440c05000e5442400d150b40d184000800032070203010f820481e04a0390483d0040400c09441501e02d80d440004482d03a5104401d8a880002000c41065003000c00c99680140da11800301000d0040200300460412041d1509401038060f19031440340c8026002e080e8402e010502030024056880350740340c3c410a903203a03c2c00000381d807030854031b054110404002c08c06c00a803182d4800c4510b240204284071844070340740303990001c02850480c0386440b00e4000c024031607585480b1300300040e0f1059034001031941c0c0c99002c0c0300c82d45441c003000d1040c10680e0042 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 462190359 1250 462189109 462189121
    0x121b14030403060606020109021212091c08031306140c04150314070e0111010606050301052704030503040615050307090b130c030203071413090203090a020301151806031a 75
    0x2614042c55001c98203102840c1c40d0300f1300034000c021410080c2e226040c01005050b040030b0205e02c41140407061040c0c03524200041040c461007114058041100700c00c00c2e01d1680200c1c01c070b103000e0740c0120640c0d4100042000742d07007008819585180c0e0300710300344400603080c0800b480c1000704072403caa0091041d40000d041c0c415095000701050a0140c007d06801c004006001e90712018003981560240c0300c0c1c188400e281c542103422a903450240e04042401080140414503240d03852152900b0911061403500005900c60304c6611010b842c00c40102d00080188410845503004010002001c410760106c80c03803070100000e5035aa414800c0744212036580c05141807940300c008541515a010781824003901000c14001002944100c81c020005420208180201e100c0a0304031941d807030356202ea8104c0e0a00f40243c0d403000f948041d02c480006d1080c030b4002001a1028090000e92030740000b200007401d40f07442040001e8500326a0351441080c680325061000403801c034840c085240ea22103c902045c0d5640c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 462191609 1250 462190359 462190363
    0x815090d0207051e090411011103040f0605070503041a030f07020a02010e0906120a0f0317070c03030b2101060e01120b040b10121203110906070201080604020904020a020307121b14 79
    0x4031000642000c004406c120030711400710300c1c4800c4024280d0302c080810f9282800a6101d01550042c10b5000602000400c40302e88244094061a4007030360035a89820384e2050151400044038501c030380103440200400c9002070b030344c4401c1030f03202e15240050855186158002042100c421103103920492025020443c1038848a8101c800c81800004075503241d0003d080510110a40110807000075514000054850700f900140902441e50307520344441d03049060760249c002c0c5c4101d021154000c90500406801003006102010344c0b070a000000185032030510b1240d010440050b00703c01810340800480c0f800041d055848164019084680d440950312404044041a110365000d204c2141448031885c0a0240c034400d0040b54440715202040100307a4400c0001c00c07409040080c56000e041400b03100e000d175014100c0740c0d902481c02030006190048520016049800181c120703001613100bc00c0701000c0008030412091200800c0c100040101c034140f00c04810914002801841024400103d61501c541 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 462192859 1250 462191609 462191659
    0xc021c060b040212060f240703020309060415080105030118110d0b092505060d0c0905130f050a0e0a0305180306130b1e07030b01180815090d020705 65
    0x200600070f41d992141000701007644541980d13491710034802052190100d141c00341e80368268100002d500002d6114a4034400050340010030241c0c01e5000401c02e5000c1c0d550744400400262901c90400014070046c40c5004011000582140740660301d0300c0a2005503910300614120a503920074000103900c5001404100e001d4a0b00600a00306800c81080c014401c60101304003412922880550480e50b00c0400714610f1484144135254101004210f01d50105541c1d80080107100000d01700a90b600e541c0d01c0108010050000f5112402640e48184403000314084c0105500150381a00911031423004010194580814030802803c1c000001150044600000360715150b4050040660780030b464522038041922036040d0041300c1c0d840721000010714a403450344403488000d0405185000941c0c41450680062002030711460500140d0003050071581c4a100005000e0004c201c040d01d1940e1003c01076620142000d4202c0c0207075080012503005055000030b50408440040701d0002c840540111040e42c0400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 462194109 1250 462192859 462192881
    0x210403021302031f06050904020313210e04110901050a0c0f0606140118030b060604030203120405030106060f020303040b0a06080d1d041503020f041104060e100c021c06 74
    0x2103142100841e8a81e075028510a48450000d02c01d090018040b29410741080c0c000d050100d0000d0000d142d8a09055014603440a001c8840c002c01c405640c4800c49403d02078058070860744900750038482400d40c07122800c010200d003545c09228841c141030071001c075405000031581c10444007140e03440360b09208018203542e158004090164074a143d0a007100a0181d0b8003a1409008518000b59079a500c1600e008250000a0b0141d0700d1450031540c3d40490038802a194681c0244188004005a0303000d00c00000d0b540300e080c902c95512031410003810f00707407109030380140c2c2030064400c154083d841e0088102ca0f0300c80d9002c000a0031070796492414000408141d00f003900341e403240d000311015054100740c40b0107000c0c4000342c07007501d0506a90104030503254222807401d11048985010001420071400840c6041d6008001141c18104694624400e0300664001c03000503014008881c2d2a040411150340500d0b03007860410010007250700441e1095000204010125118140031000c1c00500d03402146400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 462195359 1250 462194109 462194119
    0x420901110d060302030d0e090402040f1b0c060c020604050a031101021c050708180c04050903070813030b0a050c030f070c080f13050409050c011404050d0c031b0821040302 75
    0xc0e5000140c001016140000c90082c070814031b0890205001e610a807030140801048500c050b03450303600340409415045403489c2200e403070350104c41030354100042204001c029a80c5141c15401c81b0304080f010f680d0400200c1d020f64201c04107000c00700300c021072070200d500d4241c1402f01b02c06850148145c0280f1800ca04c1065a1803040e00c2114203440755044603010b40642e69441c20a40c6404041500c10f14140040c0f150580c010358003609141400e4100d10703404001c01081d28200702c92521200181e502a803410b00c0c0c0309610320380c10f000300450343c1d2007541c0140c10100100624075110300301c00c03128400034140000e0003044500050300c062040280c500c034981e02011441e219103540c21291740c1601f05820000c0e5a5840060116a80c101440f402c121290460000c024a0f8075483c01940c090f079401401c09840d5901308400308076511242c002038990b6100d607400100030380c40d600306002d400e034441c0e10038034a290403003c04002c40d14000520804451000042c001c595220b41d2440340c40744a1544029041 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 462196609 1250 462195359 462195367
    0x40f050a0b01090f15060f050702041d070819060e0f0f0c0406050121090213050907030308090a121b1502030a15030521041742090111 59
    0x401e1440c40e040300c44200c000d0109000a0140d6800e0fa040c003082c207003001c1d4803180c0812075070740310780d910504c0030140d81005032030410b054010030140c44000640c5828107126220551203c04104424802000e00c800908141c0048403140d00d45030a1000010340000d80314a54031104440520a07190030001c00411146126000017901742c444000313000d500d1140f0b02d0003c0000f2594000c224181c0d04c460009014480645840c0414000300010103082e80c200d144213884801408a501c642c6000d40220300080201901c0e6107001048410001d000e5403ca4200300071a0340080d01075480101001c2450504400c07a0100c0c40b4080ba08407880303003024124580072138030f02c60000c01a0340103502890102ca17050080171000722038020110700c28840100b4a5106c86440707084445051034a881201140d84004e142c40da607102500e011200c461a030a82503000a549006844032540140140c1361814109103140094545403000544601c0b48001782c1c044000b0014840a03420743c840001d01154041040d21 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 462197859 1250 462196609 462196613
    0x30109060603030f0c03050318030f21010b04030f11040e031209210f0901020705040203040b0f06090c09041d0109050d030c1d240d020c120412020603040f050a 70
    0x5007000d03200c103401040da40f0b03022190107803040145024140d09910b43c0d44c80c4d911a00450f01c2d01c14000c0c1041c00c4240403d10032a20124a240b0040820f03941c020b9031000c0385201d00754404014081a8020722881000300005c000042031b00f000702c66074031f40000700c208007240e40c440410050880100400d0660000245110402140100c00741c0114051001c45018224180003802040c0c5501900d08061b80140700e914403116110000b00800241841a200303038581d600c0105050b030304151400c13103a03002e80740208544003145282190340304000721130a03007945c00c0c0001d42d43c003680b0916030300b24000c60b1903401408a1103010360561130060b0140e80200100100c0342850b0f030300d450000301000c0009040000c1d05070082c0c8a0420740c21100581d42d03c0c0c40b03515aa0004002c130045c0503801c00030a00c1d0a8680c1c80388010000f4000e8071082c0c211103c09a900c0030302c1035100e0b0030040c1130170707221901c03180a001c1409110b20160660b100c250f81a2203443d030b2a1564104220004040b91006003284503030492901 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 462199109 1250 462197859 462197861
    0xa030204020c010f1d1e0316030f030b040903081609050315040b090c100503040312060807050f0a12020d050a06090503070c080a030806061b0a0804030b0c1608090a0503010906 77
    0x1078586500c4040286417001c115942e031801c6604071503903040c1d010142c04030015589600503403103034018034210f9207007460000c00102c0c01c40c65241c00b507011a16482c00346624613050f00464240480c1141e04000c801529034010704029400340c580034200040c2596000c4d024011250714001d030030002c0842e650440b16400c1d601c4c1c414000c440440700c0601c540085842240e00040b03c880c0a60018203984001440da00d04903941d030801041501000076540d101c107400e03401d6200e85030280c00c901024143c07480c180320034403080e11482034285008155840c400c0080c0a40c028113402e115030304450054281407207040c00c0d8542486060040c0402e40303400098002c03c100080109000c0741303e040f0f42000142d40c0c41d000e51b15016502409000b10b08908005641480c0010041c40d158548140e2010b9503c0c410f8003007442d10241860481ea00a0001001d00a04c00c03000c12640d4850000c02d4014640719042018240c50b004040c402480304a010404010950741d4130384070342c003520028000700000340690801b00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 462200359 1250 462199109 462199121
    0x10207061104080c220c0c11100206010527010803091504120f0302030c0a050c09160207060c0f150f0c0207051e0411030408120a06120f020a030204020c01 68
    0x203490514100803030748481180829141158100c4018160030381c070000078001001408031005462282c0007100100d084c030320b4170822011240b5030741c54070028604c034030b020075200d210307000d06501c5109507007040c0b0607a0b98000f60641c10b480091b1181c42c0c19150ba4050300211222034075420004490a80011510b03140000c058400441702719094031180120a18400d01485a4003d800c0050308681403d80400d5001c105009200e220f48102c915181c01e000d03c07241001c11028040b00c813a08040d6994a0a1400a00c801c0d002480203004001d0b64080c020042e60b168864440e040a104102d0400c109001503404865040c68105802000c10345c2c800c004000148650952144040e207000803012032107100080c07107001d441000c0c12100106544a0405030610041071240d0ba0258541c003400da08100c5100c040c41c0038602c500074403610360f285001c0c0312049040c001d040d05092850100d0800494941400b510901d5400500072140020b0364000300e90f0403003140e00042d40043c00081c00c61651b9405601c08 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 462201609 1250 462200359 462200363
    0xe0a02040e0f21030f1509090f15060a050d151a1f0807050903010908120610030e1024060915050405090c090616060209010305070e0a1e030212010207 66
    0x10728261182182441007126400a01001018040c000035610014003039540f60021402c81946c0c080360884000112400e031704440d0140d080d0000301500f039812604201503210003400d0b03404000349150a0000c43c00c1c0940520aa5100741c003180000c0342805900300d0001c0851811003418004045001504403c030100c1c0c1c51454080c1001e080040b031858601d02c50300d017148441d07075034100c0c650301c034110100d880c0e81100c200329925540c1c4111a00c00212030100810b402c102c031403c034109600d040d200300160810020032003410306040c40286102d1441c0880d11203000b4241000010b1442c544242208090380c000c45501c41110200b90080b0307046801a9584084036820455094815207030b9a04079124080c0d881400d810100307035004105080201c4001c1c10b03402e000a0102420703c0540e2916401542002c0300a5035402d90018580d80d655901d170107196402017080c00c103940100078000c0800c50711b20907845516100c008d1071104401e640308260400c00110b400074812112034035100e864600031740c401103007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 462202859 1250 462201609 462201613
    0xf0606090112051e010b09010306140c0f040b0a17070905041b0c080a0509060d06031203180f020102010e07030b01170a0512030703090b01030506061201021c0e0a02040e0f 75
    0x60141c00c405482030090380c4003004d0f0402c5a0380c059001c3c00d41502c038101200c10354072030310015025144e03220300038000c0d0301410000c142d05120041c0c41f0752091001c0c3c0404490b92003000741d040c016420300212000c0700d0700d02140d05d94813a0840000c0751000110710043c50012402001d2010040d400b002d03080c140c6100311000c01030221520300c4002803e50402122001c11000c4070b100c0082810031002e0001d0424030b040480c5840031b8040014400d92060400a01c9655101000e2041c040d08001c0d541d902456030400f04070385591880ba00c3d071840d0a00384000c0c02e64903840800030440e4801e400100411a000c012a400540c50346014090100d090081804d00450300c000c18248682c0015410300303d03a0001c0242410040e80300e074802c0654001401403090503241d200c3d00c40010304144656000314040c0d00584840e05100b030070460900e050006102c4103038014860b811070004040d01c20601038825100000300500c400e03031400e040010100021b5881031074201000c10b0f000d400308115402e544480b00f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 462204109 1250 462202859 462202861
    0x7030210050f1e0a06030b19060e070819111602030f0703080919080616020d081909060b130204030c0602070806012105010c031a010507050303040b0402120f060609 72
    0x201070052504120f07500500045008140700c03500780318101c119005800d044000c100640c50740c130307486072410090702e00e070035007400314484110758450a100708405041c1501445045041203c0000c01d00f40001d003412800140c45100040118503a40c8100010b110000001f03807100d1018203007111480309804181e000b070040c12203200d03050701c000c1408825298000c03000f5003030080300800d01400703a0409902900b205a01c0c000030504103810044c0030301c610615040340c4019812554001d083c941205049002d102d581400c3c411130300c2c2002c41012050081300d0b000140c95405003410006402e0301e1544039003100243c81c00b80c140014940080c01a40d0143c1c3c40da51181d540c4074812030743c958052040620759002000140601011116980100101d600129256603215290345084504141c00d40c40881c1d902c0a46020f003004500d00750a0f80b005c01d003001c0341013408036210744c0d80724400100010702c2901d140c070004d0215540c4950108001400c0c82c200e50301e24095815a981e41d2100f0f513001803003459494 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 462205359 1250 462204109 462204121
    0x2031510080711070e0c07020d0f0b0109060608090705040209010504030b010f090b06070503030606090d300c1a060d0b1302030714011b14010f02120a06030c0b0a0302040504020703021005 82
    0x713008040700c01d00717410a0ba042e62039103050301207500180d01c22a8004c050f0300c0e1450110780300d000541d02c3c4074010200e20300a0751400d09480111420340c0e1100040c08000c40422007250310209096003280c0c42a2400f6a84507a228012101445260002040b0365909000030275048071a640c800251050902d0400085500f001007268034090014028080d52007000003078010308140b800382c019540054a6004142000c2c2d5480d10181d50140741a18200c0303400d800041c60501001481c0310301c2c1c030581001e00344c003a20394498000f18040a0344c441a074805841c04118070752100301e843d0b200719411540c2280310341440c200403101803102e4042039220707200c1d4041c003040d00c2c0851f030002980b42d00140c5420b0203800e203940400500b043c00c01c006a44030703c599211010404004c0c01100007544103000c0c01070743e45d13841001c80c481d020006000039081526011080c000030b0455001c40041d1915001141d49507100c416048000e0b1059402460301f003070021519804041e0001140142e0086010040c00b00b6650a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 462206609 1250 462205359 462205363
    0x120a080a060f1203180e0702010c0806010e060702010302033705070201051003110102070308160c0b0309070605030a0902100833061b0601030308090f0a051002031510080711 76
    0xe80219498040c068180c10000b80c060315117040021002c4a6401100f40c0d10040304ca1000740448407440540d442e00280c0000b980d00070101584010300f424244a003a80c1080810b03100d00811100034103041c1d00001003182003404524400c2e2444d42c1620740361010800010000140001101c1e5035003540c101400b25a010b030040c06440d01c41d0403008d98090071249103444d0719119081c11a0f0f400e065008500012011900050040802042d401804070401a491078031900c0c54103130364418011076005100b80000f400000c1400d40c11190103142007a2641c41d00030586000b0144440300950094441801c480c140d40c000c03840d2449481d9500800f458100c4035807100981e40d11038210350f14002c05001c1a072002d440d002000d000414004400c141010745031506042c60303c042a0002d03001725148004000c58901c0030440f04801d44110f0000d00740c0c10f00c0c560350b2203035160b103a485a40b03002074002c00000d075003a658407ca0400000018492000403e02c80c2c40a0581c1905541c2c0318001096507000c05c500e9000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 462207859 1250 462206609 462206639
    0x12071103061810020418090609050105040813060302091f210504060605010e0f060a140c0f0f12090d0f0204020a0e030613050c0d110607050102040608130221120a080a06 74
    0x2c101b001d0744c81d4a07083c8020294808110b071750969940440020807024454540300740c0c40f8054541d940da4044001800c401c0b46239200504260040010340156204c0403c0c03c0c6200d4029620b41130360025012090720740b408100700d001d50080b40c1500c2030500008030b030065030050f4000c800400400c0c1c0c03200011100244007501e55030304841025100324081c103028000b0f01503044249004d00d04492102c0105101d42d00c0800341925503400003076261401502445240d9022071010001c1143c54124112803040703004110307049106000d40b4040e07500b800b03442c10ba68442c15a00903c00c664a200e80240074143e482d802450b00c3c00b074810940011007003a608081007071066003010013020050403200402001d0307102c1841c2100c500814007580120754480101403d038052044002585131030800f04001c220703040003007a5480b40106881060090307186d100300040c0f00400c64030068504000980310520300809070920145c02440040e8400800b94403580030303030040c0300c0030005005141d6031385244040002 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 462209109 1250 462207859 462207869
    0x5030708060d02220e0f0304031e0312110d020d1b080118110c0d050d0c0c020a0306022b090201091e05060c1f02180d05120711030618100204 62
    0x1542c1404c604110a8041c0300601d02c9400c0e8003c05c3d040718103c030f00d46c14115050800140e982c0082814020400520001c2410181c0c59107c010003440c03c0d200208100540c200e100400b99546c8035080d2030325130742001c03141c0c0708020303071310940d5150904a9100c00920461000c6070b00c0d000d41e071210200c0c5503c130300d0240d8103c0309200c4031a1080804c0d021030320001c100741428940c105000308188029048140629007081515860302d80e01c4a45851100e070503182c02f040741d801044000805000141ea85481c0b4100752604400e00503142d942c1400da1390b40d03004c1d1003520181c640cbc00c020301207810403149802103c0898802e986403011540d507401c2c4140c850f0324801014086801c0c1807014003c50800c100908000140307039044400c0c41c8240c1d4202d515480c01c603903410903030ba6000604c030102d228079042070182c0010140c0d29003142144640320281c552500d64601301078890005103480074419203282c0c82504080c001e080c1c800505081040304d90070305005108031141c1c09000e039002c01c0000c20303100f5a401c40b8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 462210359 1250 462209109 462209119
    0x2130b0316080105030c190f0b0c071a1606090b1807080a1a0c13061707021609050c130909060c0203071709120d090501090801021312050c1005030708060d02 69
    0x842e5800c02c8403442c6c50540e200d047c841460400034402c000814543c000707125240301d25644e02c0360030820609001d00b41e0080180c02d030200d0001090b034545402110100b6100741e401d0480c00b0041d18140c0c0c09801900d4000e031009803803109100075000c1d0b22606c01917401031441100c02c41592028110b4440544160140000d030a12404402102c13009a00340c0d070080401030003034a42015095204800c0e40076800000020700c0d4207403e00c90102d010314030760741c100440340024110401844210504041d00b8001e9a039040c0d1150003050300c0c0d0314a181940e0170005540200d507143c50312030781014002c03c11b007017090394540e041110b405401e500202c01c54540d43d4010840e1b95282e0b6011440305d20580c03040c0c1140781c00ca04500401c4500d10000d220002d01440c03142d41e01800c443c50400010036040039500000182c1c0d1040002040851806480c1d004841c91010000c2125545041c45402d1450aa850941103c200740701030108503801801544569015200d0101c0b81e1164030a0210100300903030000d400c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 462211609 1250 462210359 462210373
    0x106060e06030a0207050607050d06050d0f062c06090709020306091816080c0a060503070504050409080f030403050304060f0501050f19051c0b010902250602130b031608010503 77
    0x207040c001c004540c8800052400342c642001640c0d010b1038801c0848110000410200d5441c06200044c007824000340001c941d0b51074000200d4442c4141145080401401956280341251964070b0010040e010010319561003889005200950b41e11041d00300d80000f07050040200216818070b841c801c7da8010070700500040c81c690781c1c55090b554101c0b045c1e051420f4510440f4000f9298184804914002e407000c28040e00082c3c0c5001c042c40381c0710203950842d10901c0014010400342681c0801542c0803940221000b184809460a00c034a040c4911071220904180c000200414103400000071401a84250000c001841c00780c2071110880300f0170f00032558000c00c1590700e0710962500c0840a1400c20440d00102c000302c0c2d60750009959140d00d460448a220402034454082c00000c0d4401801000009415842c02200c628121008041081c605500d80038210120003800300702e606451821084a60384100152100e03409003058004070707440b07850413612403800035505106444e80742c103d500c054010405 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 462212859 1250 462211609 462211637
    0x150b0909070306090204090b0418053301090c0206010803070210030908091009090b0409170a12060b03160216060302030604020f030103320d210f060f050102010606 72
    0x800340003038085401c00d0746894001c111845070b88010070082102082c00200d8102034400e220907106581960700360b044a4030000704c0450760104070b010510103144e500b41040820b0800c1e21fa020b088940000c1e00ca821007000200d400f040036403064440c10034640845941e6070740e4440d05a900d1280ea000290000c400c6810720300c03201e00981010000720b2281142c2030030840d02e10045143d119516000ea40006c0c0702c1d00d400c10603001c45220300705003d04252418440c1180b2500e41a001021402c3c0c4004150790000f05284061f120f8000d0a024000b01c00c0d05011641c1c4e03480140302130ba001503c001440e4000120000e030402d000044004103848041c2000741d00d50304d000402c1c0e00942005225941042e020000d007403080f01d60b035004602070340c0b0455840d01d1a90140909900384290b130712412480141034a902c03403c6101c00104400c00644629080141e18000400103441c07910120242400700d0401e00c40c1d00c6d691010390010019102002024540d440d0344900480c01d980310b038801c10012030301740e03480840 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 462214109 1250 462212859 462212869
    0xb040305030a0f0c081c05150a0b0c03070209180c041b03050a0b040c080103060605030304031e0204060905040f050f0106050a0b090d080a0c05190206030601080a1b090603150b09 78
    0x950805400c090300001c0c5907840745c4040d617121089202038031800d040a00425081482119080000c0b4440c0f1040401603a020512400c40b0b4081c00419210101e6541e0b40301d001001229003140c0d0240c1035240a0601050b1101400c0c0303110b00d4400176020340184a1580e061601c107108d000c180e044e0004440d801c0607181503004000c040c040250154640714662119142d601800200c07284036651014158910b050072800c95050b9088148039400c00c00c41000840d003101c50b03400a11100c1d8844c2c0940d0640f07880003030000c002070750104c10254102030400c014010466207421100d030040c02503522842c000f0681c1c41c2240e0305070041661104102105008803c1e014003c0d01e250322000e0220543e04d03e15803191105070300100301c45c100003240c0309003074000c028051081c025209590041480b00c0c0000e035002070031501005161904016001000038585100e541020340c118841c0c07040c80f01c05a51040c0028007a1200e405508003190070584900c900140c10f80c501c4040702d094110300c42c10000c1410400c2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 462215359 1250 462214109 462214127
    0x41517060a090b04022103040b0901110d090b0d1e0f140123010302070602030109150905100b0d1e02090418110409031418040b030c010806061c05040803040c0b040305030a 75
    0x1100741c5c00d001b5400120300800c0000308003800010a1441c1c4501014000402c003411518039a108c60700148a40e2501070341000ca1003050720300e0400c0b0f45485103440d88170b41000f002e200307504040c460000c81c08c0c1c41303060510f54003481121450500600102c074410782c8102c259102880750000e0250a1110504c0118030054141074041051401502d0b0403d05d072134400c2070741c2080c0c0040c1e25913030741d604200744043d01e00d904a1000b4205a00244030500e40b40143c41085c0f01280b155800708180003c0034040c2e21020350010441241d00b07503580c4614900444000000d4101c078021501480c90413000c5690550741c0004441900e9114031460b02802141080c440a044d45800440601880240100c071500081000c0c181062120000401180801040005861030101c2c024001e0300000256104c81e41c0c0603c00c540d000c1016280d4507954007500d1911401c4010080c40d00c031000f4039100621080285420046004502815180003400e889828401680c0b2842c4001041984100905580c940c001c1080b4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 462216609 1250 462215359 462215389
    0x20c06040b0a02070f2108040302030d0c0509060307030911180a090201020f0604050a02030111160f080903070608040b0109110d09030905120303090616021b041517060a090b0402 78
    0x140c205a040d0343c0710707500a807100e00112540075010290080410000d4880a41242e4507d4400741504003a00e001c0d44a10a680b9151641505c031020211010f00980032694419405000550342c1e1a06031002401804524811907150101242c2c064162a000440c821146c01c03074480000b00e900d92032000c41c028540c4d00c200b2415401f884a68134008203040c05402d116a0198001d04a229403901c105800c5441741e4500250310350f000c2c0003505c1102140725601101c5030780075803c85d480340c00c5800c01c0300d810b0181c045130b0f03603062083d07040100d441c03075000030b006000340e1040364103428990f2503007c1c0390190341000501c00400403062101b00d40408444e084108072902908043c41c603103441d64040380c01e201d00c41c0030380b850319480001807059035001081070075030200c40400c24085500035030000070f480e00c0ba0480e08030368116568241c6e003016a01d9602540301c0342c8003410003524070303543c5070079100c542803068901e14500e010700310004082d01c1d505d00882650f1544603500c1520355640b41e080080080000030b107 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 462217859 1250 462216609 462216611
    0xb0a0e010b010e270915131101050a200109260901120908161505090c041e0207050c100c080412060e01090804140612150105360103020c06040b0a 64
    0x20b81c091035004650b416005e44c80f100050222500a14080c1e0000180540304202d4500b103001e102001c502030354001c80c0e136000d0919040b81d032190101011201040c590894a100905142c2c601c3c117099015404491001d204130b1006040a03104103104040e00c03000320441e407914500b0410740c00d103984030324003110b40301102c1400000d0f060020303201c003505a003186160a01041144e0075400900c04032004040c1048540c800a10251400d00000c2d03494404281c070703c901480e00e43c002e108441c10690300c4032804041c6020210349039000b50902c160740e07882c0b81c00001e004940302c8098241d294130412140d60400e4020719030610307281c0f030813082180d00385410206845d0590b80d005400c0c030280d402c2c02001980360288481945075418482c1c9004804400c8112500c43d080030400704840c26910740070a40e001461060264214442d5401030310030b880b41c0411003900300c0c030841c03c8545000c2c03085081c07816209803801c8103200300301c1800150308a00c07035031040240302e034041000940041d4420039615480b16403054 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 462219109 1250 462217859 462217909
    0x2060f010915090e1609020c1e0a0b13020a0614033d050a060c02130207051c0504180c0e09091e010509060619030b070c0f0b0a0e010b010e 61
    0x440469507204000c90080d006020506410109640880c01410030008214238000900d80714642da01c0355000d80a11110022030099180d0354140001c684554104118502d40e103854540d0610010342c168080348a21825800403901c03c0c807a244c118544941c018046103980c4410401e2f2089118424041100552141e41d1001c01083e1240c0d080c070007000410000101418801000b03805c1103190403240801100103280005030f41d03423424860184010990042e81d4241d0b60400f41e0521681c1d1100c50401c1200345003160242d80d00200520845c1c41040e40341400705d03101e4699000f9154895400000035054a000c41c207640b400c0c0794526080300d0000111444501c07240f0307641704044007548a07484140d54880411013000030034000607501404c1115099000b40101d01810800103040c04041c02415034200040e020502555801d030745a07400004440c4000781e10325050300030703a50881e00c801d50740c0c1c20b000340c1d55207449050291080c031101c142c40d0030340d1300e09400b402e0000e1174104040003281e001c4120 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 462220359 1250 462219109 462219119
    0x5041a0c0313080610080c060a0c21050a09080d12150e0703062c0c0a0c0f06020903240a1a120109050d17010627060f0e0102060f010915 60
    0x150640000c001020141c40645080513031654002c02e6907100b080c1c10303009a4410046561860300f228031407000c0d0302b880040740d003090914010344607201191141850208a600d41460f03046000341842c241159105040c0580321000c1503107603852030400401140500705419809015070300038450303580c900850300c82c03090754944240f500e0150030f0307518030003280d40c2d25014410080b034540d018108540d00a07003422464036103040002121001031005000f05000705032a14540e1040e40010300050700652549900140d42c00c0c610000d60045540c28840e1013180b491850b10500401601c0c03d04100311540c4820396110788005010701614400c3c140100180348240304c6030fa40708500000c9821400000140a500b28905503180a659040c0f5400b07202910f00b41d07821002601050a054412601d0f02c01d14022444c10300584140d1002c91080b0410318000000c100654000880300a01c0c0c0303e070343e8404812403504010f90319007105a034450003020384100144a48081c03508100711850141c00b4560030290f0310 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 462221609 1250 462220359 462220387
    0x30e06010315060e010510032a200f1002030714070b150a030f08070201122409090803010302040515060f0309070f0e06093c0705041a0c03 61
    0x340c01c100ca402001079507021030040d80d4810750010304a06685031200b94142800151411000380d42c1008064891000040e003003521229200700e82d40c000724095041c4201c2c0c0d00039103041c03880300d4001010301403540c00343c42d41440000c000c5540d000c5880581461442160341ca0040d40c401402d03841400b0519480f014200c0c0860000c1a000703018004074001c40c00e1501e034660f2002d41c80c802c0c81d4030400c51008140b0100c1e0700f40c0b140e040155070016190f0340d14180c1e031006079020900407101351041c81c58203020314212101c004d04070f8003025443d008071002c5500c1c3d00c81a801c4400301040501200c0c01800140b0040c00d140e44610380005c403450620150f440b10600160305036100c405d4880780510007206104281c041004540003803c60f44421001203070404258280e403a0006118921902c090404035107403651b80c000c20213100e0305400200100302c0b0146044030040034190400c103c0c006442c0c0020340e15030300c00c0c2c040d5000e44404164000c0d100004e03101c4034015030007403e070340c0d0084c0c0400c2100707000340041c0d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 462222859 1250 462221609 462221611
    0x10061805160e1927110d0203040501060b04030311070501091206051e180c01080c0319090204020c0705091003050a0209180102030a0519091113060503010603060506090907060801090507030e06 84
    0x400e400d643c240400e0361104c195516a009068100b5050161000401280c102940c98600f0409001030b22661103040c040e016101c00da00040700c12000041c00700038168443c0311040744039501d204403000d041d41c81c03004440c0d007880c074810600c81c85003240c18000001c040350005a088900300c4820254007050068903045404c0913600b2103c0c035480c0c12094800304000384408070001400742402046850440b004000c58800148041040304030681c413034a0182c241d6201d008919000f030411910341420342441079807603c2502941d0b10400810740011040d42c08404a5401d40780c2c01005800b040105509000312494093304520100e55615000724180109102441c03286001d03c0e004582401c03c068245a04c0400e56079a40c1c82d941044400300c041000303460300c80408901030311500f5402001c1050707400140b240e50005540b44d400c3c25000400c2c41282c3e0403042c01501c084807020010b480b08500e09699582a00c120700102d5001d40040113028010350100d580000306050224005000130301682c28440 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 462224109 1250 462222859 462222869
    0xc03060709180b102604151416080714030f070e040c0f14090d05010b0102010b10091404020d0e06040512070201140f070510061805160e19 61
    0x40c6031000b00324500318186000070300840001d00300010700b0700001260705060740c1a070000900c10007060400b0640b500d5152170004540ea010024140e051500e03105c0200f41e8103e581d18040307801c0c2241700c500001030f5540c107030180b480188400130080404c1016a00701e0001009081070007001070022001d150f40100851003001070194048031132603c04001b502001a07448064051490310b0300c2c600b54140c0050040c682c080b400d060885030922618800041881072203181d6030040300e04c45400082103015000b0704400207090f00240100340807030702032065407004180b143c4001130329250204142c5410303004c6503170202c1e00540094030b001d013440e420000350742103102c540c941e90b80b0410030481840002d1100794a4003442d000a6482c003002500020a80c000240c00c1d204c12003c0069a44103002050041350398250b8040c080d034640b0141d205100c3d0081c5268030610614501004020102c400c29104007441104550a0407079105071124040320305128208015400020f410f0943c8208141c0020790030040c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 462225359 1250 462224109 462224117
    0x702070e0a02130e06090f220f021c260714030a020106062f010e0a121412280609060609120b01030b09030d110301060215090303010501110c030607 65
    0xb1600a43c681d500500f10b41c800780c1c0c1814203005100c455603544550a4120000e0301c04240151a4442086100080c00141001c034448500130303070303003003001000d80c6591681c022603070036481c05c215641d214449005400c4c002c0810083d481d80303184512580440c0f51507068090340803414500c856441c008550f401e40c031a8220381e440401c0c08a40c42d0b07824007508018280600c2c003044c0280d81c451000f4001840c20703a141c07519000c08404480d61030025030001c040c0c2e800342d000700e82e0242000d00301040c01200981040c1c000800020040c0581300e440300031140300b405800c1403c1000e958045466849480c11310b51040d6800400c00c0c1c01c0d005400b203010b040084d0050303150018480c0c5c40c0440141054132960303c85507800105800480c045080a1419411030380c01c504540750590701d201d04c1d90700718401c12440c8500985824048100880701c81d01a50583d4071640803556011081c0d52040e1181c0000c444284041e0b10130801440035510135001129204809411207200c82203140009050140c1259910001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 462226609 1250 462225359 462225367
    0x30e070f080d14090d05030d06260a0f020d1509060e0c0a030b041101050706060605030f2512060902270d0c050f06070b160206090c180702070e0a02 65
    0x600c10901421420650909010400303c040500c420f00c00d0155440191044900c040c0c55002c3c00402d0049405800018504014460316852003031030244125218540b500046424142c40f440c0c00501c41014580011030340100d15256401c11222050600f403c5a25100e4039013405001d0545000d4040ca15108040104d0390a040080740e0349403d80415900c2c1c414007000350300300045045844a503070855040b0180c04603003500040107840398821030800400041c80e01c0d00000f407481c1c0c0f11010b140607680002200b156a20b688051184a010840380440030f010020080740754103001d1990540280d183c070602169036980da2070504104d0300880c2a120704983c03103845000e1181d042d08221450301d02d003110804134a440644a604015085000e05400f078905001c003480d050341e0340d005694005e41e01205190b1a071525402031216029200c03074400140c03086d4000f245402c8404580c03420343c49005003624030281c450404020209078043d01040c10f6004101000c00c20a21a440303540c031032035a0360009661 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 462227859 1250 462226609 462226619
    0x5040c0503010c14040b090402040812071b080d0809010b101706040c0503010603090f0804090b0108060901050f04090c15090e0f1006030f14011d010801020f030412030e070f 76
    0x9403051841c2400420013240b1028501942040c2078401390740c030b80c81907076442e0465200031a000340700e00d4204011a1007510a450440700d0340710000e050443c41195104013503000e08001c800c0c12400c078065148035400907040f0f07000c0030f4428008142c1c807071111800800d082002d0300c01301c1e002d0101c60040c4800688400700c6018221210002c0726003011054404214050407004001c29500040c06240300f01a1201c041c0c0047c00100c0f02450107682d0014051030741c2d83e603900d401600070040c450b40940030403000c030000f540d01d140c40048141203500203020f5801c0241d2030300030440103200101e001c4400c00c40f415404a00b002c4039004030844550300c1d485113a141420007140c051000c100800c001e070030b10090810080c0180c52006402d040358201d00f000304078003c011001e4005007000201c645c48001c40e20000080a4401d80700021704160140707061032441c0d032030b03074a000d0030303803203445140000d04004002080000d081414640d07c8007416250015112031041c0aa0341405101e511002a0180f08002489 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 462229109 1250 462227859 462227861
    0xc09010e01170a140c0309060f04031e121505031c03020d020a03020333010f03140c1902070305030a2609031314030a12050913020406140313060c03020d05040c050301 73
    0x5d00260350103c054114503008100c99070769000100b480d42130b03100b0310001c1001c0502803002402c00c00e00c09120408004944600181513808000d40c0d02d03c200d08103001d0a0182506902800c151180034001e01201008812100910b4200ca80e941c410194204917a0f0518074061000e07180c0d01000380e40159403400c00303248400019110070464064440c41401d424545110b0b56240c508416082c201280c0b50347e4060070a900500d860403c42c08400d00010412400e140010002c240d60150501c1506180703510040c04c9070b840426010041499100f04000c802c0f481c01561380c64a00504440003980c6140768060384003000c042607030160080d62020914980c9404280d0f51a005002d00141d0700c030a9041c440002540e50008240c05060280d0034010070044611600c210b0b10010400740000211600d000128030003980103114480024001d602c1501040019004a074000c0b001007244c10b41903980380c0c45007002422400ca02c82d05040e03081041c040c0c00700e0306008082c403a5000c3c06c2400c84540c60042454 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 462230215 1106 462229109 462229111
    0xc080904020a09080d022a0a0f0603050618281506021f0e06010b0c0715110705090c1210080303090a05150c09010e01170a14 55
    0x180d11030350440c90382d800300c5030884101e48017400319030002c903200e608034179210380e0542c0c6480c07011920100030b55030b840d50392070002c003106c00f010356074540da04020019900c0340021a072074004008092401c1c3c0503090a481c4001180f01541c034000800c60503e8110041c54984014138094010b0800144c1e8003544801d03076110f003003207042511290042d6580c0c200d45071540c1342c0d0030b05030600300005480c0d00a1160b2000d06100401203a4209007615450740c0101c18940d1a03442820350014500552090881440d015a210404540241610b442c1802e109030001400b80c00c0c244140200514614100c41d07403c8030150040d106900c07541c83c40381b0f000d8107a9001c5070a40c4000310500580c82c0b4046140f00c0720342e100c1c10407980000d4400301d002101d40d60407107101c2c04000301400404c10950059118090b48501494840c0790036020070454060b103841030f50074011880c0d0314460300e04c0514040c010300d = true := by decide +kernel

theorem cover : BRFrame.Cov 462050359 462230215 := by
  have h0 := BRFrame.cov_init 462050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 462050359 ≤ n) (h2 : n < 462230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
