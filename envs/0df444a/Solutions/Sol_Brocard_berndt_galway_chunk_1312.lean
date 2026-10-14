-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1312
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:18:59.841156+00:00
-- url     : https://prove2.me/submissions/a3c6d06d-d19c-428f-a376-02d59f0c740f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 235791366 ≤ n < 235971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 235792616 1250 235791366 235791371
    0x90f180809091012020f060c0d0c062009040507020f0d0f090608190b03070f09060311060a081f09020d05061509010e0103110c0303090a030f030b09060d171c 69
    0xc1d01c0d05020b5415901504c405030340ca03034032044c520340a00082000751038250317801160400c240c481008003082480c1511010f5524220500c90b1803829001355200742c00d40d1140a0b0106100394131200d0300740141c0e00350001c1a90009101c1d96259012450300402d801c16001c3ea01540c0704242c500c80d07008902c05018071054403110b800b030340da0b110115a0340a0840708a0542d000364036101a1082840c0c00424001000070100c0d09150744801030880c0883c0164041c02805540390001c00401030303104c00103081b802e82111580c0c01c0540e40c440150019200402d03078400700314061032520000380000f0b40c14010700315140046403a08030810044004120503110980b0406821000300b11010641382100c2192106944002c2e81200480054028161180380c1000c2c0c518107200300b940f01d4034100080c40c4610600d00040202c0f1881e030402404140c4030315030717241c03c06040c400c0c03100090b01c0d0f0303529050704080d00382c410851104541c107118800b2040d4444201415400042c8002c20201801642e0707038410411404 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 235793866 1250 235792616 235792621
    0x703080a090602211005060307050d060b191209080306150f0304140f0715050901090302060a020a0b1e0103110102011e05100605071e0515010e100b0c07090f18080909 73
    0x28801e405903d00c86c456111f9020400100d00e984904083d20001c440d40c0d10214101d41c44841190150308000035480d202c50100312211000c0d03500a6501c64000d0010340c0410125078203842c1d1190b58400100b050740030700c3c03c0000e4840000c004804958000300b5803842240c817402c040c03401d00381c83c001341040f02d040e511030402590307518407000c01d000048640d0700c0c003440324010a03924182c82c2d58010b140164140a5541400405a1a540001d0042144590207814001c0c420701d4200d00c0102c02500c8060320403100f00280e400311211180080c10341c3d420030655442485000c0c0100d01520400111144030711507003807509884282030b00005d01401c030401203804001d4994100700c03101d0040201c064683c58020740c120000207909105013105501903000d90301034165032004100025001c1e807040d4401c514003410400700400565a80005d40030704912189009a120035043e920419802010715090391141c0c88116000c01c1d60040a01c003d2010404d0201340301c038103091545810111400380a030305403600 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 235795116 1250 235793866 235793881
    0x50c0709060f0501031419060e0103062a05090402130504150807080a08070b040f0512090108240f0609120c0f01080105150304081b030306010210020408030703080a09060221 76
    0x506e4204240844150300658803000001954400a000d0009055681801140049144000394041e5005070b10218001030354108603c00c03280b2005002e144000e50480100300e19a0200864140c1c8004607005030303c0700c240181030351201c08543d0009502070b243c02032449905580591820441c0c0404043d1441e10395201e02c143d8070b5104c043c0d4002c0007c1020001000054a40f4646c80d4220b401084c0d07400e0314551550302d00740f800c0c402c065603c0c0e044001050741c080540e4841c0c102c56000601c4a441c02080c0700304c1c43d41b00340d00425050030503c108030081f440030441c0c4448080d1040d501004080740c4501381640059500d0f41104000720340038041203542c5000950003551428101c52000d050b14000b160b17602010b121540001e4800c603035601c401c21a90b1041200c9001c60765105802c003028590307034100440003a00d460309400c41042c4090040c07104001c0042c01100b9125040d0705420162407642c1d404603190001c20b1805030060405202240c07103207100d40c5070140300300da0b42e100c4c4080c10500d071202d80 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 235796366 1250 235795116 235795121
    0x1305010f020a0504180b0303220503030412080904090618020103151d07020a02030106032306150d02061c02030103170903060c2104150c0504050a030201030c050c0709060f050103 78
    0x605a000710f042000200842c0c0b881c00424505076000d58000102c1c0c09500d4002400c40e445900d00000c80002040820b01129481c07000c680200001c0717005500e8a850301c0c0c00480600318541c00034105803804290301806496641001860740d42c030184c00c00980444000799401c640c68000700760300080c0351520054548003540c175114159115581074005040821614030400c810017007518003140950114000142c90900440700a544100d2043c5004003104051040a00414120200550010060040e11455450001403010059580c0100d0324024008a4450301c2407034000d03000440306d81e420402c08506680698140c921a0919003811140710300c2420083c0100c051881c0d00d50040c034041404410380740c0040c40e6000921500626807002425a61013828040b1010342e4420401034413600900030611a420300b49600d803c249007060b0a06011032032121990000906150f640c64611881900440544216803c110207da03180b90703c402260000d00201d2062a001c0d9500000100d070660190 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 235797616 1250 235796366 235796377
    0xf1005040e030f0c03040b0c060f0a02031512070314150627070c06050a0c020606010215011203031e0204050310020a12090215070308091510030f060609051305010f02 73
    0x21401c08082c42d142600302d034401003941d1302500c0100f200184a14009002e08501d00b500f001800c080d1401c2c1c10601310382c2d00b0090414907018810000c1080d071010ba04801e40510307000fa00c00d24620441200500e2030010309401c0a4102e20110170361643d0703a400052100741c05650f9001503803154036810705000344222604c011201e6030200e003100b00c0d80b000d070303e40c002c60f4000d42500d4568545001500d6090864800740d885a0207a901c6580b912220f43d01082880c1e00b0032002e10007040c1c1c1e501c40400600c61803e060103006c82c81c62194001006140c401c2e00002018280d4110078405074115188800c0254420b00c0348034004d0041303030000e400f00403081c030075141030034241d8484c00183c250b15648103008140c2200d0480c1e03c01000c29450418a0181c000f8043c03441c480c0e1680340301c504050b950145400c94030103121420200040422a00e440070008a000301ea90004176403014048030b00c1e240029004940004c00401d140c041084082080f03043c6524125015400070000c150f0000e4026003a03200c0c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 235798866 1250 235797616 235797641
    0x1f050409110a0f0b0703030b0d0f030e01020d11190f05030c07030c0e040c120212160504060b07051f06080619050702070503070510030b04150815090c040f0902090f100504 75
    0x1d00681d000b00303012303401c10310004000500903490310b00951740b8064040050131054001549000315080c082d40c040100c40e0810314a800c00002c0581f1040c0c2d115034502c90b80000a419501d4a02130300100690045840303400d0b5802000d8a4641c4c20008900d5942d000720302c0143c560402401d070010302c0c00000a00c05024036041114141002d081404840b504442010304a8018400d00403603840d44609202404011400c580c1a0600a203003104000580f1170300e0300a400c0b507a800304240d10000d0000a41c0540f84001c00094209084001c86040010100b541c03103180705014403001c110803002c3c0c044900c85802001c00b001c1044d038440000899480300140501c6030558403000060115103840d0b804a03404140a10300898080c040c10080390030741c0d40c601d1130350703172503908510b410700030300005000c1d01444002402524159107001340049a45034107007450140155641d44040d0030300da900303401c02c0c40115005441e09c142401c001a4076440e4103011104444a030002c100049240d142500548010140f1f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 235800116 1250 235798866 235798889
    0xf0915150b09010906080c160c050a090e0703061d03040602070923040212030f0c07061b120302070c050d03080405010f060b07020910051f080a02070b1f050409110a0f 73
    0x24501c080e21201409440e04078400d000340302300800f100d8001c01c01f44200d44503811140c04145001c05000d1804400d030880b40c4410f050080300001c1400004041080304e80065011484a00610700b210000507a500000600c3c0030014000c1040340c2c0004040040340c8142e0410002e2b213454410b42c401801e41d4a040c1046240100c0101c1c01500d01800612440100d407400c0d240b41c2091030fa00c406d030562051070309810304d400c500070400546400640c8a00000b082c0a0001c5417082696144c811144400f200e410038540e008c9078090234403440844200242001500241e2071b041541405030058600f25004c03030300340d070030303c400602026080c0c0103031011200c5000940c0d050034882d07401c1001e0324100070030303100081589590008041c2d0341d0360794404004101e00411105104110300080aa00000f844805854010071980c0001981c4811040e40503039200c805104021903e0b04038201c04515520980d44942016141d00c24850020f030100e41c100c02c22140b03080a183d550507079140955040c4120205840c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 235801366 1250 235800116 235800119
    0x309030706080124120e0604050c030105011508091204080a0c050a15030b1f05040f080105101203020705030d030605040b09011208070303140106090603050907050604090f0915150b090109 82
    0x259122425050071380b1814100300c000c01141d440d80445030080440c03502948000140814480144100e404081059009000d958100000d40796001e0140040c1c3c0100224072001540a002c1844404941800d041e03c2d01c1c1d036103590380001380c1c0c0c56080748010345100c0c1007105c002a040c5000034076101242e80002c090f6140c0a4211000e0b8010300030b076010180c0090b0900c0a10005c041518a40414030304036841d40e54449080c41041c1420490030b8020071000c1c1e240405014006002e00344240c111003001142094241051500300c0c188123855201d0740e010310443c7c074800c81c2c041d0583c10000039290103a400700701503603e140820008180078814101104200c4c521030000c00e09500007888028028207001c51495080095943c04400c240d0128001a403101018440c660707050188540140e0b00c0c200400469080c440000e055224620900ca00035948907051019404c140c0c000da00d0651b04038121032840f0442a4030100940070784454044c88250903c80454030242c01c4003910402c41040c0e5030108800d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 235802616 1250 235801366 235801409
    0x6010e190b0f0d0204080114070c020d110d060501090219020105150d08040803030106020307060605010804051c0e06040906150f0c0f11120f240f0601031b0203090307060801 76
    0x6070b00072050b11141d098100034a40e0048440c2c0000c10090500c280002408400782102003c0b03d2000b524450030020725450242c0542c1c0c8044201c0000c903000480e1900242d4444006004480601b00040c07000303080200010380100c00d136014051888040300310420f48040000304a080300e204961040c2082c0900100b01ca0740d041503110141c0041c4160812490076071036240540c41c5820036805800144d00024686042102d54050b00004040038241410141043da55481e110110254003988654101c881d0485507813003001c800c0701141014048982d85c68480210101420060207907a03070181d03032522402d035507a101d220045001d007017503500c90590701030707580e030760f40c00034a01c03503c26201c034101c5600342000b95982010f0b00c41d6110112004203110300c8a11041414000103105241c1e1410014000100d00058a400e0321f51010742d110043c40d86580f4500140d00400c0c030702c00c4441c81900032500283e09140c001000b8070030b00340120301311007410f5541d001c21140b5802c24003032180020a1444c01c00040d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 235803866 1250 235802616 235802639
    0x3170a060f090207020609030a0b01030c1a0a110102040f0e010906060206090a0809040b0a141e1c06090b010806010608160e1c060e16090c08040b10030506040b06010e19 74
    0x1130920003480540340000400000345803485242007070b01c184101074010400c00c600d0241c00c100410003e90803010496540ca2506450700401205006001d101030b01c0c40a80c2e00c0039030444015240b02e0f103400400d1a1920000304030081c0c00d0041640040c9080d101244031400065654490040300340201713207040c0b4035030790202d00b40c004513102504640c4038080808940c0d80c0800c0a40540080501c15481c1e2030701c80d0070004c502c005178548003855402240400c50b180c81c1c2c80e060450b030711041100800ca1034080c3c94440d0060190320800b0b00000000b4001251038940451127504031421550b904030320f81c0b0783c024061154950500d008000c13800d680000032450400f03502c03104489075803080c01c001e031300029210301d010b403001c8030070416894000081424410a041c40c0301c2e00074084500040080011800300508a08000762028000c6000c1c100040c0c0e40d840c0f19800403014540c00070a0712001d00341490400024031058912502060b00209407482c80c1c10300408840b41201c41c41019084ea40c60001888403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 235805116 1250 235803866 235803877
    0x30c110a020916090e0115180b031807080a1b14010203091e040e030405011b0b0103021507120c0c0e07020a1425050f0603150103020f0705010903170a060f0902 70
    0x14854000030005d103450750b82407010700a0548056a4201c250b00c079400800c10744100300d0324890501c1e181b43c01d1101030710740300a4a40c001c400114000003469042e092902c1c3c0310460740328450600c1204020410000420100180041c1c0801210385094880042252100e5032070b0141d03006a000f0701410a003450211f030328400700d0a003092403003869040440402c066910488602000380d200140403c900d580c40840680c03425000246060401616990a82d0212040c0b001034426554500001034400d0140221040b0984c80080190845803e0f240513207a01a500c80030b070341d030b070000420005040080b055000d02c02d00304c43e4080c200403503075945c170340d291500d14100c040014447d1515000c0c5003401503040c02d0b2a0400704010708070391440c01040143c40082e0881306c50040c8414002e01c014034442c00d42030f15030b01600342800b60f01d0b01510200c1d00854000c0030005401d17582046048014140c00c0400c41e1084e00248034804020742e50491043d05850161081d50700080e0b00410030810100154003808 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 235806366 1250 235805116 235805161
    0x705091011010c020d120209010c021306050d060506190e0f091f0e1c0203070f080706050a05060312030c09010c1721010f050105040308031e07030c110a0209 69
    0x180c41c820000d0400c0d0031511088000d10140c1e201c3c8140388915038000c2e209014a0716010025440c290305800006e20a602d1008002e004004403c04918210415045400034003006030a814540c00a4144a00a0070742030b84c04d41c1c042e2084000f80c1e101444049032007020344044c0103c81200749c40d078070000d142024009094a240740900d04240c3d200408071054400d100da5000c00110741d421800c00c1c0305041a000444140000d003015890b180c003603401201740c420720382d00000c0201c3c00540c18284114035128100c1d00515651a100070004a8002a1701082c01030380203900304c030b0110f003d0720340c1c6045a11080d03c24610180b8103000c004611340c410700c10802031a01c2413215810001e01c01401c2d80a9400020803a0516404481c8100c1e1064048001a0060001604200300030385040006007441c40f45000246c01954000001180c00e1900300311a08c090401c492013000034500410010002d00e4a0400800050802103008480d130000140c0104c0242d00200040103680b10103664605038a000782140 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 235807616 1250 235806366 235806377
    0x1030b040f140303011206050105040c0c030c170a030e010507021216020102010e0a0804031b0b270a17070b03150105070f0501020327010c0807120b040e03071a07050910 74
    0x4000d5100103101a50007480d01001a4a01b40c42d07070319118007501d4050f0000360140380f40100c41036071594032010328005180c050806081004540c00c0c201c241c400320711444500320900007400e4060742c2d1b05510085d1541c524100802864030780d1a42280c59401c1c2c1e0503055000c0d101844960000d410b60350030112032610500001038680c01443c1001c2c04d0449140060b11510310118081050100110700d543d403000d001c0d44030910047c00c003221032806009810b400160100c802d140581401210758800340e0700c5200400361404240c1d03d2050b0b9640d0751a4400c50f400d14003c1d5540018903040e15010749005146400c10000f42c0300c101401101d0b0f9420030b030701c191101c22084042d0000f00e1070a10096010300000b1b0303240d451a06490b0400105140e400e400181a40c0c0340414106506500c0015103400100a2801480c12202c0f07010364400b51000302d8140307a02500d0004c000c00040d40000040100c03502c00c10b50101045046114144814002c0b0744001c04240200308004482c64501c824014068143c2000b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 235808866 1250 235807616 235807643
    0x102070315141f0506120c031806090105090706050702030319020109170306031504020105180105090a080102040f050d03210f0501060c051005100e090f031c0f0501030b040f 76
    0x2d0541a64241c070401240c607458490320304071031086901500605015101945000c2c8107803091094100000c1c04a062000088007140e4107400c0440200c161003584021920141004845640203150a4422107140d00c1030b601c001944902075019a0301d980d40040c0238500309070607003a51180e03055400ec0c050f800c6550ba202a0400190305e0301030b142015010b41c840c10340328581a0249407801c040707400e24421041c1c0c00707070400005070303031142c2185c6090443c1038042071b0005180005861a000d003120392680206410000b150f000c505502403c111107a1201c0003403065516403d0015907026190090005007504551201030788203050103004610002c1000940044004156400c45200b0b801c00400250201e9051003444010011340840c40c08880c81008141400d00300006100c100307100f00300003480c2400c00248840002d105a48001c80c41c2e00540790390340300769007400c00c8034112646040709903484d003541c501c091034161150a040c0da07841501a02d0035112a01e44289140c60303600c08844c3c0c0c080a00301d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 235810116 1250 235808866 235808891
    0x909090c0a030221031605010f15090209030a05010c0201091a01050102030f0c2b2718021c05010807060c051e0f4612120c2003090102070315 62
    0x400488941c455502241291b614115007541c4c070501481c122a0b080041e5000c410802d4010039040b20310140005903914482d0020078140b44100c80701070455480c2a07500030b11280c064004a408500c140e200e59501c2006102280e02e0380c00078060640103a1003402040c280c812120001d101e0241c0b000c2c200d4641f8002c100414000c00c01e0000c0c074600405451030304010050300012100440e44441400900031440101034102500f4284138070000000700c1c07010702c00682c1d0b450f0304803145805032001c0c1c000c0d080941941790024000c20322502050f80f040080008089110740c0d04ca04280d9071000140c900300400303070980301e03696041580076609030040c0c4001d140c409408000b03801e101072105c101c1c1001d00d041107603001102140885015400507000c9007000074041150b5580c4a0998481c40c4040441000c0e0380803200741100004c08000e5a00e070101c030300c3c26690040c56020380d40b80d003420540e0b034001000e25500d0712406107001c5c842c05070b44030807024000610f00400002c42c1c102400c6000881811854 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 235811366 1250 235810116 235810123
    0x160f091502030409050901052505040e01080c010906050c060112111f02010606050702060403020904082a100603032f01020a09030c0e060108041707170909090c0a030221 74
    0x80e582001d40d100090402c1155030b98019940d0020360303140204201c0c50500050035040040d1000703592401d040101810103e80620152000b83c810b43c403240d4107641e120407210799101c141485c030b180881c00c00c500c00646d0910410455241040c05400f6104036460040d505801c815400c50442d0b17105000400c400c8680c80b40b415a15403d8a0540c1201410100316806407c480f103540001c030400404102d0385c005a100e0104a4088942c151440c036031698980c03c050229002c0d140d07a0036005480b41d00100325042c00c10400c42161030310305040d2403d011038038001c031017218958400100407420540000c12119149500d0910106a0081500d401d0084000342422071f0b000318251404214003a5042c41030207114800d040144c0a8521112018100a00060206007000304000c002031a0281d012002d101074206454102d40d00503050304a00c0005810105e4540144c00c502e80542c0141c00026080c407000101c44142000250000000d6411602405903441c12001140b6581d401c1c81c1320a2544041003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 235812616 1250 235811366 235811399
    0x1180e120a02150f01120b1f0806090d180302130e010e010e10020a080c130b0f180f10111509070512010b03060c0a110d110c0108160f09 60
    0x40c2d020302101c50018403001c0003000003a11025042c40307110010b10524030007103c0490b10a4000c600400180d0fa040c291400300301da80400040c0e080136003140041c030751100195250160100e1400d94460f0f00350320000b11407102c000c282d1141c0c9005860300c00c10141c03c080303500700d52074001d241c8003207080020003800900f500c2c0003942210046c0e5440e80c80385810070040c41420301ca454107140c2546418107440e0010500c4002520050342e4082c0014211003092807c1007803801050b203844000d845181002d00d000180d0410b001c2d505c40c1d2400e0050045072407602000841010b0030041551704640c9100804861090081c1c60301c081900c50001024040c82d80043ca16104204200042100d1810842480002c005600300e90403c3ea0410242c00c0340c59501050381070703022540c0b00c40b40341c540903401d5084903400082030608015000326070f490000300e07038440c0b11030204280c400304448140400900444000004680701000c0709001c1300550342d0148500203034201e6044900d031102041e91104072180c27615145 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 235813866 1250 235812616 235812637
    0x110604120c110a0b0a0306140f12030415030c0e030109120f0e04090620031003020f0d1b060e0f0102120c0102040f0b210903030402120715090504060e01180e12 70
    0x11605000c4586c0c50302844024080c031300c0c00380c01008600004105509680344d030081c41044001e0022040c00400c0094030014191066000340d0120020400fa004050100b161030000300301000115243c101405a8000c042d48514409036045403120b080b66591100031070542008106d9010104c0340e5035174051140403070b006040c0000c500d8911a8141c944800070f880c501d00056081c0f082244829100d0f08200480b0303010755000b40ea9100080010303180c070550000c01807a00308000064408807440b584500143d0361281c0f12103020140d5042000400c0d0061417030b81e40103a0291102c0316502d42c2901c00750000000300c0300054249501e4090152032032910b03130045080b05002056031900708000720a60a500f01e9444904001424860390058880c400144042e000304030302e4003540d0800c9020440c0302c0081880d0741100d075141c0c0140f00000e010020328440d203441340d42454000705149003aa103442d07040341c0042042000180302d40c82080d018141c03505c2c185101d809892220081c6000c140f0080002c00134 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 235815116 1250 235813866 235813889
    0x927030d1e06050306070804030201090b0f100f0b0a0c0c030b01060c0c0b0415030203060a08071e0819030c0f06021206041803020d030906200406110604120c110a 71
    0x4800c0d5841c900762800c107201c854114149002000203071404103105410040610b003c1140e65074504090780500f1040d240101280f03c407004008981b00c04c0c0744843e0048140c1c08142099598584a8860000850155410010003080062350342805400941c00c52485105c40411950b5292181c45402c1006da0210000c038401d00e000d2003c0007201807100c0003426010a100d42840e00f400304140103402c82609900504d80d002020910079a11044904010005003040b60052034650003070050462940c0004007204440b1383e0b000c1019107001c80d4a0b01d280d541d80b1101e80341030034591400c42d00c040d02d10a055503080c0d5120020390201e581d5000510182101605000c0142030841c1403004507200d08013142303800030407040700c18000307a404120496101003616002c5091105c0b0b082290003441480d5088400000107112100c18081d841d018008031001a222058801d60b0204115128101258000c2c440381c070401540c5c080d0380c000d030350b0b100050b40030340011501c4100040c0030480014040d04480d54140 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 235816366 1250 235815116 235815131
    0x61406090c0a0206041502070507030302010204081006050d03180803031f17060c0306060c0a1101030e0a03091e0905100e011202060d05060d050610060912020927030d 73
    0x521039032040d000600900c40919140b410318000b034980b60b015000030a41c2d205001c0000c0b02c1c40181c5c05030384182e60000143c980c02650781c503010b07000754414410903009000d0684140d0215450f032048100b04d03800503000c1000d88400781c3c0c0880d030700d880040100354135152020000c40c10203402c102039446500c0002d2503c28000a10402c0c11240720240d0048400d8004042c5418503024045405c40d04442074040d00c80c0c0ba519103000265160055150b40c07002072280854190502190912604110900303880030071502015100c401e8a94901480c00303004200e10712801c0100c51410601d601d01c0c120155038505071203484c1e04c0524140d5000ba2892902c24000380b43c14480311072446401801000d090041030011038080c1e002c40c400e40600d1891443c0c09654100044098440030207007402c01c0c0d401000d644840c40c0c00802c03641c50801c18081c1d000020380342c0300042040941500f05001c441c0d00201480c9003642c92004038040c18101034500d035000c0c01d069555103408002000904640c400092001c036102 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 235817616 1250 235816366 235816369
    0x2060106020c10021b010201021605060a0b0411070b15180403030c031a0402090d02031905120403020d1e0804090207060e030a05070b1b070b0108060a0b060d0b0a03061406 75
    0x5925144400e03c03511006000000c01e43c2c001440744101c0e414001d801a001041c200141d0083c0110141e80c01c82248c036009250030888041581849511030030307420480000300e40705100855100d410100303040301080101201040d101030070b03507910a5800c4c00d2010f814800e600403c042080348494400100e40500030300c01015018091189284c0107454200030309107846c4902a480c0544883d0540a9580041c0c810031948903000c0d41c05a10703070098102e078514118a018501d801c400d44409444034090828440e0035081450200c400b140d40084c03000142c0c44080d21818042e5180e9850060068690744000f000035036088003070b100411000c000180c556a15003400425189a0100184250070801c009603545800105441045811558295031a60b50850001701101e00c1941203200040100301c0790108403000c45954180c401403015281e080d2503950324102518680701040342e00c04420301c41445510b2007907010409085008004451241c2e4a40b580c44c11150b6006111001044020030018907 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 235818866 1250 235817616 235817623
    0x203070e04091e021801081f0203010b090112021c0209010905010806030d031d01020309010c0e0f0931050d140720040e1506031915050a021204030206010602 69
    0x25100c09480c1401024000d030740d80c8004001c4591594888006412641c06544800c0d1121101c40705610030000956185c1018650340c1264000c007401200d04015001c4074460b042c0252070480d004103031302504045200c0010340d64104100b01403810182d007440320500d0403c0944100a240468040c010b990300b481078001807542031b10341c004605010380380c0240001918005000c0840303003c0ea240c0015036504482407106010803050048840d58004018409802810350000d540f0300610344461240803124414821034040ba1055940e111030301d9800901d485080300d4644031149484c6100b50155125801804940071a117581900c403039000403000d580b5590031010418112107020310f201e00b00304041d600c650200c002d20182401c8482d06c080c004c00d054540360003020308811440151903c41411244004140400b01e41c00c030304ca03203c1d840c42a42c20003200d000c004500d58211601403429002e020980001c0c1c80044c01d41c609165013040300b900c501d00c005030300e140618400ea002d070415500d4100000e26 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 235820116 1250 235818866 235818887
    0x103182301140a0e011514040510050907030c1b0303020d0f02030402211207061a040e100203040f0f14210306011107051210050108070305030f070804050310020307 72
    0x116a0b1408180c1c0742440d4030303a6815580002d05003800304074122014030301405482c45181c02c103580c2000d004040f4a0003020405042e5004094808200079943d0a80b084d107000a244a69901300c0c1c8200e000c80c100a11030f41141d05c0c4c40b00719003000b4480c250340c609a030f000c0c00003500c0b082d00041c0e80400c5420035180c1c81d0040d00e102041441083d421410950001141d6000d25002e40ca00303c0c4003100415011001808821400b18104011948a5610303081ca6006013260388132042884148010903245441c007803042c0641c210360100189201058072464400a51004e4011349103041801c04200c0026148055088150b100300589514034640e00340075840d03e4502c541c019005883c2c0c50300120a01c00312010b070784c2d1203c230074a80310060541c014003042c24042203030031140c0c01c44009150a40d15110016202008501d08641048036070790302d0b00b61646924035400010202e420401450500b0041c1714040e200940c0100681450181d442c0000707440d010320805001d004580200030880c9154103d280c1d0324 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 235821366 1250 235820116 235820183
    0x14010b070512030c041e240f090f0b0d021201030503130b070b27161d09030307030b030715020c1005031b031b040806060306060d08030a0b010318 64
    0x341103040005004d0024010303401904500d0881290381c80d4464014104a0024000d86200d003500001d41d502c034217036a0f51101d0f40c40d4080b0310090800403605d0703c01d07600b1034110360010180b129554140282000e00360f11001240c55001c1d0240140480c6601100d052030007144140c1c0110360700c1ca40c03103a8100103010340ea803094001420510681c0d002c2084007203840e60090902c25220404540d203204a41c054401201418891154500e09002031126103054020352702504000c8003e07080200825180540459400c0c2003038009201080015029810400d8004801015aa80103403581030700ba9001903a81030140060307120521001c5141042d203002000130117145442480c1d4035003480c4a01301d1030b0001010050200000000514901000803042e24050785041c40c0341d43e80d5a1031003003980d140029076146101e40221b01c0822201d00d01003400401041c0d00c0318900742180c0c1c1c2c13085c0d804000d00c44d085809040c0f40d2140b25141d01655030220714000c161240030600084038003005000b00400d0544c9004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 235822616 1250 235821366 235821403
    0x70317030709150206060607061116061a01020a0f0302011d010603030f0f0e090c1b03030603060a141308070b0a0f05070f0210051506070f03020f06150603060414010b0705 75
    0x240d034459010688030746c4290260b40c5995911154a440d000402070808210652900452003600508030100c20985241c007038402804428410b010500c0b40306040710203240582d101100600002d4841c00710958034a009000004815003c480d10500d1000d01c001c00c40d44a95543c2c00a00403d5002400703090f118206182041c1e40124002c03010340320302c3e5000e01540c410000400020703e06802c0b80102c0356210305506c298000e0015540301c072692a0410340710715100303014100024560344098810034a2a602c603a841540381c0d144c000035018241102d0800360f4203000100200320104014600c07141c01f41001c00c40029401300d421511000301c481c00b030038100c10401ca503c4011240d80e40017401c219010851000061542c559542048004070945006900040040f50207400d1005075a09046072074004e800b5505480c5411003195200c102c11a00e1141c2c4042a011001c43c5003013083c05154000710252002039800038034844030120243c26448055165000101781c4c0410a06000e4244c030b42e480c08169 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 235823866 1250 235822616 235822649
    0x90b04120906090905180d110601081615090e040308061021021c060303020d090e010503030304080309010b090412020f16090c120903050711090601080117070317030709 74
    0x414074a03884c4144010306071070b4808140d00c250b80f10040454480380c481104e04407800f00d80003911400d82210074100c07902504d800003550280124044c2c100030301c0351240799125030070300c5440500ca1002090410030000108404603003d00e0b19800a4040c031b00a460360a400c2c60f0510404c0203118a0100d03c2d400c0004050110321170956030aa000d0700c022030450056160b140d040300076a05110a213042041203030502c10000145600410030524910a540e50900d0a980383c11943d242008280311b6607405600400001307020640b040040d5412803441400410303403400030000a200000140c0d010f40b004180310101d0f034100d0350100a1040041100030180914400003401444981154400c54480070748650714128018400e1201641d4241610410451200b0608008003d500001d908460590b80f400c00d060407483d158070940c0c0f00d0390701650b425130507a09012926000340e410a1141c0321500c14188007100051375204d141e11001c00b10001c040e200d184c414001459500550b0242d00c0d55200c0501 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 235825116 1250 235823866 235823879
    0xc060a0b0418110f01020a0804120606050d030207090203041a0907090c0f0801050409031719150b0a030c090b0a0e030c0409030206040803040c150206060102010e0309010e01080405010b04090b041209 87
    0x18003c1014400c440c4482c2c440e045900607824012110350040001030700103000704005018221455045000b214108441c58884040c000400302c040c40c09030150340100c02c100300a4216400640e4014800d6000405410031075441c4e1100d0030b03082d01e403401c0640182c1414460303030f1094815401400d003186000e001c3c4003036250024244001c180110703802661241c640a040c14028070a2007500e010103d00d1180f2450440c1041c00000d52102801d0a0741c1d003801d0b03000b241070131703c51385040c203643028801014602265150260028451000044188454920300107504007511000d0b0168908545a0700c030401c110310201424a50790043c03c40c46a4035121184011035400500c3c41d0f40a90300040c070f01d503a52581d05000c0010589031f032082482c100018500506540d000c6406130050304203030000d0092a0085002c0f949030b004100c5900d001030f800b11418103056114401041c3c03c00d02500c0001351001415000c50207070391100c5c00c152419044042070008000c0c4040f01c4142d0b540c40f03481c018400d6400c111 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 235826366 1250 235825116 235825133
    0x120c010504050d060b100503040b0f2809080f04051908030301030f11030304060915080103030828020a020601030c0e010312111504050708071e1a0c060a0b0418 70
    0x2c0c66000780007840d4507a08102c060743c0000c0711018014843c00789180d038031800814030b07402100e084405034054804150f0401000c62550300460500d40060f40024166640da4051682e4210048425840d043c0440111382c01c4c5e03004200301c0c00d80302e08103030350b0310700740000e101200d00d440c8403140051000840800140c1c5000c030589056a90106c10440340362407070304040750300c1d08201c1e1315294103010025001a0164011400c60308030755140c90640ba9590440c00c054919401c00d11000c1d01250b0000002400b1032000e40c01c45c2d844c14109400c150020032800c0315074007244c000c180d0071005603002900500034081da100b44c00700180540d0003444010760441d51594041d506003e844024804460100c10824400f888009000f100d4103e51030a145404d043c00c41d9501840d10408201e40200340011816580032030001842c1284017403071207070701e901e402c1d603c44011125003007140080d9404d00c520a0034040c14481e0a001d801c08007400b00b580180d0300204400c80b20800030080480c0303055014040002c0122 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 235827616 1250 235826366 235826369
    0x9011a0310020702180a090b01050f030d1b05060a0b28090207020406080a0b0103150606081330030f090f0212070b070311150705030a02030406020d0903020309120c010504 75
    0x900700981c0f500060f10200c0c10000307008505080540c042070030010007011030f91015411038012260205e071640e03140305000001841c588481d806800c00e41180000034000c2e0058183c22011506081304c18150352606801c100c1c0645401c0740064945031050503503d0001c12044070030740740c02e001d203400d01d4803a010381000c8407151141c110190b8001c281d50040d5900c0782e0101c00103110700000e031504001145429190780209020403980300c003104c0341d0452050014441c1c0d00c00d548480c0c44440b626202c084040415400d1844100c94401c2084808200141035012496070905246002e07445002044006020b9a5100c0c0003400018509100080410000760300303490200c0d0140c50355000023503200c04582c200030003504030360b001d01c00000707000b0105680041203001c2c006424050310fa4a017034600050f0a850016120200041c00900c00f10300384a00c1c40d401107400c07500c40c2200502d0701d0400b462140176914403039000c0d000340e0008200e00985042100e514450385002e08040d00d01a505000060441d0140317 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 235828866 1250 235827616 235827643
    0x50301180b010e0d06050601140c0a022e0804030801050619050309010e0f0706030e0604030905152802100524030c19031a01030b150d0f050609011a03 66
    0x664101c030340c569000390044005070b000940342d00b8840340c903800e0500c0a010284c074100e00240101c000107105441c4034044e18981007000700901010355640d000c00414540e0300164a0324258030f04004520b058854102c10031882654a440525103450704014060000591285028034010007446000908085040b591390100d810030b03540745c1d2550803500303006141c0c00c040e540b5184030300b424078800320b0800240c036011201955018411491411006610342c1c00035140200171507503240040c0240e203021104401c1022521203010706000c00000003094811180384907250682509012800203541032100d03244c48804600103005508007034120b110001c100008500e0000d20a02c0140c00300c0d41e00b07200b2081020002000c0304d0103602c0c0b007500e200424006210841f5080c0c0c04a610000280c000001d150480e60030008000450350f90026451580d1048a40103901075404011580010041c5140c40c4506001324002c0c0346600c1d05555207400c580405580030b070040307480910b4406550b000030300c40403408031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 235830116 1250 235828866 235828871
    0x142a09011223070809011503050601210605130b060108070804120302120f012d0501051321060b010c26270f0105090d14030405060c03130605030118 65
    0x200d100d0b49070040794018500e68030101000140400700e6400303103a6030301400b0030340c0003000a03640001010181c1d001c10f2100901541004004015100301d20b4020703e0000e200c02e91200f41e0022a640b50f00803904101c1340c0004010b03010380d04009200b041500164415404e00306503a403800c0c4420060408040207200401c01202c41c1c151000041c070075010f070b0b28a03140500c000a4981840060110443d81c24029007503801c540a850070510340ca1000f80745100803000c901c00c1281400d10004403425070202c5802d03d1400c03075001c000514069000010441c0e10b440c1182c511750b030440ba01d8203200395140e041c8070303a04124208a47c800402c214149000c0b544005046d007500100340000100000c0c00b640d00c08403d0049101d031108400c0e803d0449100c520b90007150070001401e440801900c89004601c030b459003040d01c2c0e0220800240d0070040c200074003001d00c01100d00b4566182e0010f450360741b02c0c500ca60300380d4002081c03c04248418881c410b01401942c20f0103810340d0304180400620000b400c204680098 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 235831366 1250 235830116 235830131
    0x60c0309030712110109111302030c0a05070611030c12060406050609060313060608161a04051309050d05090a0e06030c0108130206040b04061106091c03142a090112 72
    0xf40204150901310074108000d0200d40180e0415099601071500b038140500350442181e49880400e04c04c8901c6001464140d900305103010004950315045418211000c0342d0307a450303032500c00303150300040c520901c008c18007581e5400c44d12543c20307038090001c2c000f58003603400e005040c0000e96561044e10041d08059035000e4586d9208148924030800740c1c0d502030301d1107150003004a030f400c0b0007195802070301551100702d0468680d00c50040110181440a0034540202407105025074600034a10200c10f114051001c18803100710707222241080f0032034940d00d000c034400154000b000e0511030904801001175201c1400c00c1d00d0f250000c030362030341410030b20703241080b000d076000441540207200400c13601031700035021a480319150703040c0760240d500c14000c070300100d008401103031070b410400601d2520a10f0003d0190101411190402d10055a80e00c200c40074951100d1031a01141c10300711a00c1e1040308003103480800c80210040c034146495030441c402c0c5c1d40c0c800400041043c0d90300301104084400d0040000180345 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 235832616 1250 235831366 235831403
    0x606090103060302100e100801080604030c02120f0d090806190b03030409090602030f01080a1104051009090f030315062307050a0f020a1e140a08070305070602060c03090307 76
    0x2007602d0382000354445040c1c401c08400c643d2180b408402ca4906035056401121049801e0390010001d100d960010b500800c00500005e101e0712506603100e102134860b0b803008007640480b0381001d10a51600c08a5888401805100d5601100000051080d6030240189040c10080c0c61548821100040c2d030854540848004076142003040360028002814104050100791034070034041d50080e640380c0d05011000e40046119a0b000c41e28119669200b400700c0b1038070022400b80700c054a001850781e0b0078504496000078910b1214010700180e184540000c1c1d40e040e855150140450b24007800108003280309003803d0041c107401c44400ca419882000c41603080070a19070309803030340b4400c0140090907402500d00a0b1304001844505140440c400c4401e0642c0e151a8206200c01d41070441c40701c108208600c80402014503007900c0a820b884005d0040c01226461301e1130036203020016441164140e00000c000c1000e41d9040c01400d8100c200030800301d195040c090034060b500c5c09083e50113803542e850600c21a000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 235833866 1250 235832616 235832621
    0xc05060c161401090213141609170a0c0602063304060b030f0601030b01140c241e1b0c1608030a02070503030a230c060f06030f150606090103 62
    0x1d103503000c202102c400e444429201c2c042c00301c00c031049000303921800106051134035501511390780108038454003070b603655501080404038404400035007e10400c0c003000702e03800c0c8141c20101a143c00090003040032442514000402520070b5020004641000c0c01f846100c06210802000c0107205461881c2d5808400062820740b103184818180e01601d0b003000001c21001c2c0d100514402c5948891030711160b40d5403801034081d40c04001166001840c6581c511001e0000c1c2c0005e001a09108000c40d6480c2d5013442ca01940c1440894101948e5007541c0c0401018a00c01c6002000411250103d003002d41010b0307240b5800380c500400340f00358150003c80e031000c404d00c0400c00c491a4000500341445895170722081642c481c1d101c03015000040c015202d0115103800e00000316a075003005c50b5074080200c445101c003030024550341d0100c0c0078885000c1040c11008803081200030700030200000e551040d030500c030003050301c2c0c50424122008940c101c0000d8820402c40c1c1c903100c683c4042c0075581281e07100ba050004900 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 235835116 1250 235833866 235833907
    0x105060a030e010f0c0e040c090b0711030105040809030d090303055406160204021308030708090f010c05100b0f03010f0204030b070c080d0207170d050709060c05060c 73
    0x2c250301c0c0c07102c540c008980075002064480303480c1c1c032440c1e00700c0342040070b001c1560940d90030140400c030302c00020014241410010034120f40152071580104208400003800e6580984040e07440d000c010038414070a10301841000840c4400307040c81e81d119451a54094068015042e000b00c02c80c02840c00d1010451020030003055550302d49c03403c07402d12024418401c0c140507040303420781021080384081e4909402c3c01c0c002c645200303c0d00500b809076921288d0130480603511000d4001c2d2106030f100700010350328000304080c1903803a108994094581c107081f0240039003034101c0e00600e4100014000b654001c280046a80c1c80f2001640201048000402c80811000c0d11f041c6107040c4c0540c40e00d02030b072104030040d90140055a20902c1800d0841e11141000c41da01c2081c1440a4806101000300c2e0324400c1040c0d0080c0441e07442550904621060420180200d412008400050940707410401c1200e640c00b0400724040c165078184501552001c2d00c43c2e0380c0d10400180180e1401b00b00003000154880540b0043c02c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 235836366 1250 235835116 235835141
    0xd0f151a210c0d0e070e0a0204080309060903010e1006091112070f03060503070e1b0307020d08041e1101020f0105090304030f080408031306090803070f02010804110a090b01120605090105060a03 85
    0x4240a10034651640c0c0d100d051151241d5240c0f0b040201f4003200f1355000b00d0f0101c1324442c005600b414500401c2007016401582c1c0c0c02d43c10740d07884006003800401401101804100c81500203000b501d0309039074505a5030b038040a40d40415042000030002210003c000c0d4109095103054100b044035244140c2c01003005812080d07061190030400a54007940ca00c0c414480c0300c1e00503150b460780c40e180700104840d000c180c030403c0158100401c80e1100502c105060350303000b8010364803501c11824000c2c0341c145c05c120081099032030700d1a00d41042210758040204049043d2003500800140c50994003a5403680603e02006248000421400702400080c0c0c064501a103419030a5a543d0002100c050b09403000b244900d4001c41c0000c42c00042811011094a03035460308070b040e9640380702da00da0044801c004000e10484410f41c41e40142c1120f40c90340280500541307401c64000815440360b500150a008844d081e4000c01402d1090034000d5440d440f400c181102c000b0743d00e80f500c8480500054014080505096 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 235837616 1250 235836366 235836371
    0xc01090204020316090e070806060304150903030902180106120b01110d0e030d0206190c030e0d05040801110304080708070528030906110606060d0f151a210c0d 70
    0x8040100701d130b1100001000e80352038641c0e040d940c810042e11040c00c12100070003c100c40d00005010f03402c0040046502ca0b2042d10740040302c50307041c035801084891001c81980001d030b03500340c20011802e0100c0114016412941002200d40c9405402400f035900118007041640d2038800c0380070141d0160700c0c01800103071104261841081c0d085030080004400c0880c5c2c40c428030400c030420144c00d0022a409008990110410804607011242d903070180c0020362440c0c08040d0f5840b281c202c1c0000c14045c3c6225041103556003035035280791801c02403d60382d001c2155000c49008000b403100181c0b0800840c0c98803544015070300c0e204d01041c2812401c1005200703003080350842081d085915010000042c0c844144243c0742c003a09581c441030102c400d0413404c07104841c0c0b03620401c0030030a43c0c5011405011100041000451503940175039030801610248a41400f1822031084140541c1c0601c948420100107810001c03402c1040b4286101b0080781c20501d18101c02c400200841d007034000354001c4404010210505 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 235838866 1250 235837616 235837621
    0x20a09060f171b01200111070506011a0d090f020607030309050606040606050403020f0604050909070302030607080c0a0c021908010204050a120f03121103040b04020306180a020105030a0207120c051902060a050c010902040203 98
    0x410540350320141c4211343ea8000c0c1c8002084c0040001c50b045090cc20f1000e10605010a64007014018042a41c059030002005503994005036151802008030611030b50300403d005603185002e07460040b010301001c0c801e50400340e00740055a44001690204d83d0105e4070700615540b0031001c2003403803050350803068000e8a2130007006580300f40011210105c070f100307504581c03560ba24042d0440b6180b00070355002c07050100070087d09584a20608a040307140d07000030480315400e421455101d81400e0240d0180c03090380d4020a00f0070591a05030700c414014011583c1c1016660619a119071220101c02801028400c0c05074410040310b0f1298021b101c5010840e10b4a5581c0c24a070411b4919004200c41c124464030076800011072015108680d0803008118500030480e5440f0341d401503030f440d000140039030071540d0309000b0036011400c00c4103c1085021141c840001a5615003802030078102242010104440c003011003100507140c100481d0402c022614065440301809405140900381041c00603511a001005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 235840116 1250 235838866 235838891
    0xd0207170a02150606090f27130b01080609060106050a05070606120203100e101109100908120a020c0103020d02090301060f050a0e0c070303020304020a09060f171b012001 75
    0x400b80c3d41d0980107410400143d84034401c22159109003c80d141d0041d48004040c07505003030040011a010608009030341900c3c65800311104042c00c200d558825500d00d99614034248030039100d0b2039014044800190416140c401c0f8030035076400e0180700b4581003000c0014001060b51150040c1ca0710a0780c00300c03041c080e841e9140051a14142c034050180d1007405080f00382e200c40c001911810f0705d901003207000380c0405803107000c4000c0240080a03c1d50722070701c4200458401030741e0b00380c2003001040c443c1e160700001c6410903111901d850740d0603058040c3e542040010120503500012011061802460056070b51492090360a0180c02000d903c01e8241d0300308000462011001038200040d00e80968414290690710100042264800e446103001c0500801030103000c00e110350011540320340003030130600c000ba07500c41c1d440045411944c40100c2c0110135050038002811005403401c04070061300300a0002d62400c0c00c84c2e4519070b41c0c80c4101414002e500071949260414103907869540c0c084c0f030000f000603080c0400d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 235841366 1250 235840116 235840123
    0x3040209041e03120f020702010905100e040504120f0c0f0f14030723071a0a05040f030503090102010b0a051c0303110a02030d0f0905100f020d1a01090608010501050d0207170a02 78
    0x1c0f4040e003424100300f5252091700c024403c0ea21b0440e016959004c00300d00c0c1005025400b0100b4050300d007000340302c0701c125042d51a58050140514855080210702c1c0c0030800b0010649290458814200103101c1d1002010981714402005595013000c8900e0f0409024601007000074040b5031060411b02000c00e4000c18880b450300300c00107000002050070078043c41c00c0e020703035111201800f54a810380d084407503500402030203c0180007400c0700c0342000740c41c00380c643c1220a090101940110341e241d000040444555034280a0200c008074141e404208441c1860002a90461142009003590481000d0181854400c0e000003009944d100d994507600e6550031002500d03644650040301c0d2460514047c01c1035001c040c400c0e034004541202c06400c401c02d50014410190141c41d0205000320340a0011043e02d0485101c0d40d4041e01c1e030742244605600d0100000f410407501640500c00f888080001005182d821004648040380340c2000140e5808403854840c02b4444621410404400081202d038070345074001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 235842616 1250 235841366 235841387
    0x70c080a0e0414180d020a0b1801060b181c060b0310020c010b0a0e01060912050a0b0109050105040e010504050d050903010204150804020111010b0d0201030e0109060c090f060201090803040209041e03 87
    0x5407580c2100102403c4c800d030741d030801010805c016442841c00300007107441141d1a80d0800d541c03615100e5260654102a42034440c1c940000e051401d0029001070a24202120030700510029034082ca410b0410100ba05281c0ba0080c0002d40403075106d0350143c0003035070284a59408001180f00131519030020030b1206000b0302c80046e04a014400c0144081048030307200003640c1c1207500e159500d00c805400e0442c0c1403403002c1e0009044071644280040c4c2030001d03003603550701c602800241400040b00c0d071400d81040103513100655000c07601e900d04414040410750100e2044404500750034001e0b554807506011030300a01c9554004cc020400707850314018020307400455503005a000740d0382c15032801000b00d1641d00300c4049240c003a0340050241c64280041d402074201280b1001e003000005a900c215440d80c0069900c40c86501c000250080340900200300e03123910a6024041c140700800c2511050b645070b003043e10024001900c40c0c40c4010004042028122003030503607aa40748000c40300c1003068503010340300705441c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 235843866 1250 235842616 235842631
    0x305072127200d05060c12060d150b1305040b06030f0f0703020d02010309051006050111010c050d0e010e071d0714030a1a101206050603070c080a0e0414 67
    0x1011504580d000d145510000100c1d0001042c481e011000404912400c0c00c0001994101980d40031001c0403520a00685219205200c4100d6907400c0d170400d01030555074010031061013900d00c40028801310f8402100c1003500c0750b092900103103070a9500000340101301c4035011034000f1820036080208000242404500841d01075003210f01d0011030b0700240e81c48500c81e15001d03486500c085005c2001d45004605591420300606000603159031a072981400d0900c078540c003000e0301d83c0b140003c212550380080c0c860007000c0c5880082114110030f12008145100325585d04203210707221010722000c04020341c410300300440c0134011076854070b603250528100803414169600c3c440c207000e030001c0e4a55029005401c411049004001e29550714103440c0b80081c25291000007021103031040003603294a506003061000d45a41e110000070b00891100e080030b030707611038120038000c03c000e1060102d19600402e00446050b8001c003400c0c1c0300d445021003200c001118248a5600604140000d1070111550066034012482d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 235845116 1250 235843866 235843901
    0xa050d0632041b111e060c09010e060c012003010b09010302070c0b03010f230d0b04030201062303060a11030105060d090804181803120e0c060c070806010609050d020103050721 77
    0x85c42840426007003c44141007405401c480e00084256801c0801400c0303504050403c40754600403000810015000304510303a103640c0d174030082e00d10304104c001507018400340c0080c001440e540c1800c184007a40d000720020316041c9a000b25100c0c0c1002070003da40c9d005401c5100f07802d03480f5a5034000d01403060015102c5c09152008d084c01024070b0160045010400000250807510f104040759607c0c04040c00090080e0115561b420b0003188089110300740320404031b810208014020010700405007458800752004021514010700d90707800407010003d07241141c508490302a1121070444403030300a0000301c03500600f05980058041141544001a90142d5031000382c100320603840c031006400281c00401380580812410010003081e0552a0800fa8444410300300b9610710440c4600402c000740c00102003012030b0b030045002440441000c0010740d00511080c071f4560f6241d03203080d02240b025481ca0b48040c0c109500e80340010403503070044500c0541003910f0000341b0496041003917030300d00a10740143c2e481c59018 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 235846366 1250 235845116 235845133
    0x6040806070f1d030d080601050912060105100207030203060c16050f0706030b0301020327010e1f05130807020105180d03090311030a2301110a050d0632041b11 70
    0x954200c00d58980e09004e0010160381170200e07030035076400100402517070420400700000141c9894070071446459482c840000d150369414042000040200342e04031908561100104202582c1d0004074030780c0100030040d0156442891020b907204041c92010064010b01c10051014000d030000103070201100e080e994100244031020041601740e102c152800602c41100ca43d00f18442c041151612015510a0000140c2d246985404505041c012840841c502080440701c4600e0001e502074070340d0000d80d003425001608550f0303840740000e00821001904000021400e81031400000840080a0304024920031104d031841c0f40040260f2403d02040701d06072a298440d19070350600140072a01c00e580302c2003a034000851140365019623204523298000d5592100d04a200704e210340001000c0c0c02e891030b0703242d0b540c81d440d00c01501d0035107a00342e0282c0328010800c00e008041106c050074413041074081c4104e407031031003a040b0b00040141c41c0003092295842c4410380c0e0151501d411050000074644400161030629 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 235847616 1250 235846366 235846397
    0x103050601170d180f030b040c120302071e0f120c08031c09020d0209130507120206030a090c15030f14100e041b03060c08130206090f06040806070f 65
    0x2075025205061036803041c5600903405000d4601d81e1940d070705184d280c0398566601c00d0604101003113984159144c0e01400d0510041c0101048000043c00501c00c4d01041c640e01550000e40d16022440303035650100d40d01032a20490701c06d0031003810003031514503041c41d4100e072105400b1000350b9601c1d0049401c00a450300000b0841342c04801e444a15080400781007030603600840b20409441005401ca034006640206c4c04010398407541c000303025415800010320140c1e4986041490f00744c0700c0e0000341d403a490030b5100e000180e8901c01104c3c2e204401c81c0c0d01180c030003510700c0d0810010556800059090a01d0258010255410741c4140d107071041800d0244410796101030100e001600944414803500b00814040c0f040e660300411803038016200da11801804488007820101554880e00100e50380d81e154907003650b90070b9100032400e402521582d40401140380c184d0010b2140c0c4904244203019906030f81160300d96079114015a4004c000307410035602c1c940340c0914000c00b03030045c020880d0040761040400c850300 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 235848866 1250 235847616 235847639
    0xf0f4808120d0e0105010608100905010b0a0516020904080306031011120912031f06020c011d01030e031206040e03130e0a020405060a030b03010f14010902070f0803040b0103050601 79
    0x8550300c0d40e015140c044011441c2020075030180040b1141540c40e00c90841c0303218030900c07400d402007940782d07186079150400c903481e080c0c030885a83c0000005030a10300107020391454501101c0304141c42d13003025541e5031103409250361340d041310b03e8010394131240d101c0c00c100512034010000e42c4512000c4003520990080c02106200311b5a50400d41c80c0c3c000014440d600341801500c01407a0043c241d0300403141400007145c00f80425920440d0301c101d030742041c5410101c3c0b8520122000c4050b0689001800d0800030460008007601c480d1407550300c140103005400c02c010f90082d4444a010500a0140ca9545009500700c0c4529801903c14500591400010380d00ba50008030a55402c900a1140b40a41d00e03d0444a0744054201508240b0b1665080200007850f50380c1200505071110103881c00315120030620201401c486501a00031802070406038504030413082481d0305410b481480302d0051301c0d0302e4242030036081d01124503402481e0035000004e010a01c54443c0115040b28425000c0f01d8290303032200c0c5042c01 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 235850116 1250 235848866 235848869
    0x8061009050a0b030a050c04270f0c05030a2f030c0d110301060905180a051c031d0105040b010f060903150b04140a050108010c05090f010e041505010206130f0f48 71
    0x1004c615031881c4000180ca2032b0600c0c20705401060100c0b407098860303001a041c0f0304840011501b61b803c001040c0850780105c2044918002090326000b000f003412804a0344480644840341c4c4560390b07046a2a0030804030682400c12864054001c0004d184c803410650010300d03040d20514802c45d440500b0410b40000010070018443d07205001d0a1a80380a0014024201c0b00102e0b89044c0358450143d002c03004e24091440351005c07040400426142800d0900c4448d000040c0c10890411005000c180030007600074040c0011242e0141c604800f40c88044034074001040302d45034040d4450b0410051130b0f442404041c005024a005040400007643e880b13141d14200c0e00c0d4440c504010070024041446140381900031402c050f041070601021951403000064211030710b140d002100c2040c4c2035028401c030f5038104242a0321024107010b9090f1805d05403500180142c03c000001d11441400201c0d404215103651001d42c900d02040240c04a0308046240d2861004c01011307603e01180881141d0310100c02c0030174140b0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 235851366 1250 235850116 235850171
    0x501060c11040c0e090c120421030e0c060a05090d06091e110d02010c020306091c0c0c0e071e0905011205060f04020c030f03090c0a08061009050a0b030a050c04 70
    0x18407a0105003402013010300108043d541c0c6c402446400010030075110024400d52042c0180699500328a81c4401003000d501c0040081526101c80c0c000039813000140c44159100450300a82c94890620003154580704003c90300e604805a05060410480b058000c13201481c410a568078440d0344100c000045a5006c1001404081704203c6241c1541001400e1303c030882c0c0103240004d55140d1540102c0d01e0304205513100d1800c0d51084103040c0304400b80c0407074040c1003502450071508aa940d51100b60018500b03014020380d80b02c4441c041750b901402616005030f02920b82c1d0702007000c588070100162104900384641c501083e0380010302407100038103100d024411300009000d00062440c0c1410b0000a4000000c0b07002544020021014100d1007400a548a094000001d050554490040c0003144041e030b0701041280e400b52041c810703403621070364046e01644c5a03c54005101d94411154401800344080381c1d94142c0a205002014800003003840e500000d002e0341d0600058000e03852000ca840e0001c1d6041 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 235852616 1250 235851366 235851377
    0x108010c111b0409120e09011401080a18050604030203070318060c1713032607020913050a02090c0c070803090102030412020a080111030a0e010209010912030306090501060c11040c 79
    0x70002d4103400c0c04803800b00785024000146a80d4a680d82c000780640c080320100c04a82034412008a901d000000715014040f520451141c0031440c40010b82440740180a401301e07103445810215100440d000001a10758101c41180d90038145410081e480358030250007540000c00d00040100070b011a00d231410100c03401130707549400c00c59554031000004203141c06860500f0030104418032080075270001c41400b541c0154105000c8501e0180c2e0f0603081441c019400e41a81f409000c1140940e9452020550058201c1d081000c12065490485d04041c0d0400c030003540296414144021107980c140078055442d070314003c90301d070b0340d461b40349083d900d02403480c40c5070050b44200b2043c09000c03e00d0f0040c17480e1a1010700800340440c0c9602c4050f017962451105d420101501004201c00d820b81401038110a021400086142525001c0002c0c402d001c107000e64009070480702081401c0610070307403000000b4282e80504000c2540c42e0000140030010101e41070362013461049151040345014420841043e2558a41 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 235853866 1250 235852616 235852633
    0x11060a1115010e18150709050102060a0c0e090c040315090506060118140301060b04060503220f06050619060801170111040e071803050303010608010e070804020108100f08060108010c11 81
    0x30500e80c59131071140c0043c01540302c50605412125941805070340c440d01e03980c0d41241008002890513000910304201d10307080c124402241504403d10403800380055035210810784e111082c41043e4451648020150700c000d02e98180056440e502681100d07100700c05590958840400445000c01c1c050320807445202c5049082202da508411010b1140001500100300300740c0d00c440150840e0002d030b00c1140800c50020410500d9a840a111742c1c100a620343d401d00004110344034144001c400170402480d01340d82c0c1e00880ca01c0d54540042c254800c100300e400307419041d16410020b11010003071080c00c10f408150b201c2d400f1101c1040c0200300c0e99140101109041c0f5250240301d0907261805007840052241c60a02034620340b25140010000c1d6000341c0c0155500e501d4070754001d2421405900040d8850511400d100e000c0e0381c040e03600d9401c6502480c0101040e2204070341003c01c40c0d04d40d0701c80b110b00c9105c1c6000181c4a480401c0050496442d03400030440c41c2d82003003040c1e9010b84040c41c150744540199a8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 235855116 1250 235853866 235853881
    0x3040201140d15080106060207080706021903051213030e030c091f050a0f1404020c0a0201030b040204090c030905010e1c0f0203071203090606080c0d02090411060a1115010e 76
    0x15118420068501096150600682d070060401d01d030002d00180c1d468a0051207da45c04000c81d1009040c810001c0c22042d1511400075100c608103607442400fa511035200344117042c0704009840d000c9040c0c1c0341080c810708281e05003401d0302a80c924100d0102d10388450154603842d020500c20803d0402401e607071015036445c0364071018140010360000c212844100041801e4a4407010300014000c405180c03c0d070b4908000c007200300c0c0b094007450341c3e03c00d80c0100a550071042000c6010403035a58203003004039541e5210300000d0041d004079088006843d141c40b101c820103640c950801400a802030001304545810b840e11191075a4885055600c0c14042800c0310002d58401d1901d200e420b0b081c4d205a03810030041d9650310101e80903c5007440002a198104401440710074400c4a00421805006085035414580400e00640361604082d110310101400502849000305071503408400060810769502c55004014096140c40138805007a80314800c844818840070b800c555041c2e0790100c5c22080241c1e035600 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 235856366 1250 235855116 235855157
    0x3050c0d020304260406030b060a09090e0705100513090b03070b0c0a080a0801050f0a030b1b0c07030f0c0909030e060a030e0f0f0f060c0301150c0821090303040201 72
    0x1807048a00c0a22440c000080e6011812503610b1083c0804415175502e290007401420b4540510319988103d90810001b61000c4d003010700760084034020348001c02d6003120004a20306107881940019000503600407005082a4441e000300b0310700c0d600d409156400c3d501c514035002150070300030301140c16034030624050145c80300316009444415a07210484565a01d0381d80c6450751a04241d10580100341d06400504c0705181c1850540d00001c015601c00c001c851441d180c0c00ca0750003015041c07041010048500c82d03010003949086030381047c42c0c28211046d00e6583c1c81c0c81c01c403141c20308806440c08400d8003170101c0c60003000c0c000c040300c40741c0655506240300340041c2048020b6014401040502d9913039000c590b8001410b026a0721544496800390501c2071016a0007814107010403242081d68200c00100700310107100c1020790703054550b03046460b04080541007041d112403100303501c080c1070f114012501c0c10072040f403039610298181034120400c2964848085040d039a000688000f8041080c100c05c40442c01c0059 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 235857616 1250 235856366 235856371
    0x1e020a1d0d020609190b19181401020a240b0d03020d120603020907030b0f01052505030c100905010b09040b0a0f0b100c1b050616050c1309060c03050c0d0203 69
    0x8244540d4100d800344150900d4080d42e0000046da17001182140b548240440105024201070403d0b10200004d26102820700c1c540d4029111000c2c3c2c1c681c0961400d900c00c00070340402a500400b100074510041c00b440713102110310703d00414500d050004045d92424580420410720794560000d10801c04140340c10340c0c0144500802c01d62055844400001590758600103a01480750343e1400266405008140982e13501c28405803814010200000c840144c406031001c507401c481080315a500c400280307041800c600c00c0d00e0b008001c92013a001007444215075a1301082405110308001c1011035120403d010010720101c8020b8130680703500700040c0301d446913a0000b14141c2c020260005410308a403000440079410b4051280014040b00c0071f81042080701e1103140131043c81400d081e80402d20340400035030070b44036040d441c0583c030042d1a210f4003044020400c140580e88000c0103408400091441000104008581a0740e09401c1400c80000700d07010f4428a40a641c00911071443c042d1b01501c408040d5002 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 235858866 1250 235857616 235857619
    0x70806010b0a0c17030703050a0b0d0f06020d020703111009030f03020304051203130318080a0f290a0c170c130e0106090e09030f0901121e020a1d0d020609 68
    0x107002c07070540020508942134243e640000499522402c0400b00201100c800814a140051400d06149680d6a40400c0c501d03003560302c0b404000700600d10340b030480d010b03002f1078159542150000c41e40e04101900f01441d41d110007002070458040300c44205850040d110f6084024000c2916042d211042610039001980c2c0103000704110350000864a10040d000c3d8811694409041c1c04040404101036000068443c1d00255411141009081a010f036440354440c60000301188485a4000c0410004000603e00710b0364011421088860b01d145041d040e020464504040c5494030000c0701300c0c01d0194440600d00c805940415443d5915950000c031980e01c40701046021800440c0300040007141c1e00c064ce4064012681c940b03c460b440c00c01824482c07440544a13140d140c00a024000032070408206543c03207241c0929085100000303c000b080010010701000e40712403000400c24000c4081c054004014540c4a03554075620302c07035120b404103103030703400050381580c00715044440401501d80031001d08401d490 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 235860116 1250 235858866 235858877
    0x10e04030c120203090a0f0f060c03090801050f010303030507081b03280903030b06040b0901030221040605060f03161a090307030f02100c020f0d0302030f120108060702070806010b0a 80
    0xc0c07502c40301d20101e052100340005900010340c8640c00d050110b55180200040300d040c030811800e000d842c414050300707802401c042090000b1a1010f25104d00d4030a03005000c140001c20403070400241020011809000580c0400c0c140004030b10300d20b10804906210700800048802010190300b0304101d0740d800940082d084071034640f110440c2e172094400400c8005c00c0b00c0740c00602c0449500d005420380f140816018401c00003030000700032101002d000c641c0300740402d10f8016038695441e695080e414008000c800302c020713804020041080196806140604c00813074039440d43c8080d01c0d0030140d50b03134a042d0124031002070040041080400450001100c01c0b800c00c201410002070710040707450000d441d8400d66107050390380080c40c20350800c07000040a9640a140c00c070030121668011580a810855401d40079550a00411341814400c2c4280d40c0e50a0607407140c03696408541070f481c00440028003801140d80140400b14000c2e900018000088841c01e00c041e00c607607841e080d042d408039000085080c06010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 235861366 1250 235860116 235860137
    0x90d060e030c012304050706080717040302010c08180a170910020607090b131e081e013c060b070327050a090b0402070f05060105150909010e0403 64
    0x3101400a80780e01081a4000580d01e0503440301107108000c8400111420580300d4144004075101041010130b885903420844010f407500c0c0c200b02d940903440b0002182a0081e10140420141c1c1034109110a184aa9410a10303441e034621032003000908184018243c0e0068038400c000604d403d501c1e1034a01e03600749a10741005003100101e41c3c400082d803000070040e0441400c000100b070b00038000201401c104070b03086050002c800680148280c20340940244004551800f03086220080807201c040c4c44401c00f550481000da00b020a00304204c105154860350800b400c580c4104e84004488062410b440d415240d0b80c0107001844844041905040044645500010501c1101b400003803550900c01d40d41c0c2e414140c1d0709890b1005442c4100d440b40d015000c90441000241d484160785400e90781e09800c00a011803c2c2c500060080c415503100803c2c6510300301d6854107001c00403070024100c4005680c2000351180a42c098086445000c1c01c19a2122440c0c00611040e85a481ca4942c1f1520a082090206 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 235862616 1250 235861366 235861391
    0x1080a0f0e070b0c0d023c120a0906050c03030103231902010e04050411060c160315050714030a0903030e010509070f05010207030321060b0408030c01060e010b090d06 73
    0x40016041419140030010350f4101c0b000080014441c2c070b550a10262050210001c50601c4928101400c1c2182c2c47e10b032003040c000000b03441201c0c00520710503030480d69190a0030350280d140750410340340d00d4003213074000c0c0001940900407011620841803940140d032850b0308560301d1900f013035900c455004842014004801559404104200f0b2110800005c7c5001c02c071a880014041404149240c0c02241800c00780320002d9045240d020a003142201d9168482c0075045c2c20514008000405940d10004000000140324030000a89505001110140200d03501c1388010768030118003008224100c4810000905001640e82c80381c0300b607500c24030b00070956038010441182551002d640c400401d40107407200300640764604040c03070300416082c006008141e01d1070f00d01030414200c1c0591210f000740b8402403100d12003040d6100034060009241e0710f5845540700d26415a0303a4000c580300b25519803070050003055048195003002d0480703955020403442c00b91408103000c41d4102070b10046451903100d0300b040120 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 235863866 1250 235862616 235862623
    0x2a080409020d1b0807030902010210060303090806010b0309100b011205040b0f0601020118020402160209040506010e07030b10030c03060e090f1902100f050c060109021c0b01080a0f0e 80
    0x8001950016842c0c1d4418608002258500308030100154240d54540c00030540140c0403983c0300d140c81c1400503a1900900051341080b048020184003580380040c04800c141c0c0002441e0161200101101c0081ea280e80506070b07548821386e00c200090f031060b10614826000c0c0d401c05440c000341803425070000d0845a40c68029103505650840d0000064000c100c20080c03160441a440f4509200a0082400560600d0382c01c070010000070b0b0155400145800e543d400619403e60001d502a00703142a615040c01c0c45511400c080c010340d048855000d01064440e03129025001021500030450308100001d00350580040565113400000c0c140c660f0000540e52a454856501ca80886c0340500081d600e00c40105007040c06d40407409900030070b050b0031800940c81d81c2e9410103100c0303250305100c41112042401611580500f4001441612805c0d001181b1442c0e15000b5000d00b5568040540001c100c00240030290365401101074006544100001c45030a60b0390054110382d541054001403071455000d210b401c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 235865116 1250 235863866 235863869
    0xc140a020a080d06080d0905012a08030f040308091204050607030e0d03020f07060201110d2304050a02010f0813030318050114010503070f1a0f0903030a030509120a2a0804 75
    0x280b0613510181001200000d104000c03080640b403800441e01d47c14500068100841011075914421800511900240021414421071604642560384900d07180001c260141c10454044000444c601d0200d4501e0400144948a4095032540141071900b00400d1011075000024103404200c00f20b514107079a525100e10300410b56000c1d034047c10380d070505100d4103883c01581d54804011a0702d03180c0409a1040c4000c1626a050180d80c40800e95205003034004030b400c024540c40e402c02c0b0194005000c10800000f4080c01064802c0e2910060b44a034850199002e41c41112101c0880c01040c0000000a203e6844805000c0c241c00612905502686489007100d030f45140c40c0c1014214200103100d1071604012080082206240c03a88040e820f106000c0400d61080c103071006120404160162045002001d4035141c0c00c0c05811251503000841c0c0c01009020180c0700a0418011003010902c0b44000c4800c48290102d0b82c1c0303611465990000c3c10070701618801400b1014100c0094a0700c0008200c20300820 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 235866366 1250 235865116 235865137
    0x9010e0a05041e201603030207120306090f02181002070f0e10050d021e01090302060f180102011112090307020909061006091406090f032e0c140a020a08 67
    0xa0052010708140c41c01c982c980d80f4103000e040361340142d050103181031804460140c0c000ca0340f03d50410202d403034103501038095408000c10714120031071200340c4282e1546c040c50031140d0698060040036211a10343e4101d200c0d05045800310200c20581d6180c44c107160443c095a0381030f91040303410280e510040070b2145000364000c94068076124040c4204403010b0031031030015007021a191148140640d00051404104610594190b01090314150450f80540840780085401500aa5440e40b120507440043e51044888035425142821210002d5105204130543c0c2c0d55551401450f200a03c1124401000018258041c1d4481000417900588680d0101800356802e00010b1405090800480507000700c150401010040c4050b8200f008503003103611180059419581da41e40e0b0745440c008505080b150b207e88541520620b001c028428541141410f08603182403032441c00d0181420f17000c1c0c00d6800d035103805400244e0075640121840e8441009122080d21801213501c8203410740da981c0f0b06c0d6000301d9200b1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 235867616 1250 235866366 235866401
    0x280f0218090a1b050d020d110409081b010902060414130e010516080906010b090609030714011808100506030a0b09060601080a09030807030c030f020c1b030607020309010e0a0504 78
    0x6008000c0000c80c01d45200c3d140d0603200f40031030706050104400041c80034000e48101d030303065002e50510070100060090f9000203401031164003001c0c24401130541c00690b043c002d10004800b20400040184079481030154002c0406140c580b600141c14003000030752010550002d5440380034004d0307084600c81e10a80d10342c0c800c0003180d2860903427072070303154072401200481c00d103c81d1004001480c4004110345040d1400807482c41d4490b1018000708106028240708190944214007000c10030124400b00c1c00341c80c42d4240c1c1c4070000701010040b041580c07034562040035000d0f030221200c5d00c120803958015991040e400350450744030442584400c400b0b40c000780d44004080d000b072000d00242f540c0c01480642d01c500440401c3c490034440f9036000344082001402c02c0300b050f035909460203e5900c80d4005a5450380009825900c0350b20642201e40c80301d4161240f680b180002801000d424100410120700c0741009401460402c032084006481d40d28030290101d0703015012000100d180d685034425400c008481c54542c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 235868866 1250 235867616 235867633
    0x303040b01030b01050303070803040609060e100f0c050a0203040905040321020a02010c030b310e03090306010f08060a0903030612060f0b240f07080a11280f021809 72
    0x400f10441030b04130b2070207608100a20700205004504803600030381c1c050303400904000c180c10045d00512510b4812400c5000e80705c0c422142041c9904130031014a1842d5007003225004500c0c040d00c40d8450180304101680040c4420407418040d9802150b11500a080a042c0d9090007078400c5400e203c0c140000300c115502103024174603250309100d5020306104a060800004e51070400040094000b4019114100c1e003005000541509000c2a0510043e4000051188904118059840f60420300c2541e00910402000103880d120702c5500c901200c440381c003d4491902d03540c80c514040c0c18481030507024103482d401d0008810105184903549075015040c0050b01c80c811040c0742080e05d04640b443c9100301001c1d06a40c104c1440808030243c400d00d00e04202d50b50300d0408001e00858000c448000d88910340c00b04800f0051034000300c4148101c5944800d5070280f808511000300b590101c000c40046103040300749440000340403600c6018000e030008040100940b4803848402c0d801d0070444160740f0a400c080e60 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 235870116 1250 235868866 235868873
    0x6030318060e010507060914030309010e0c06040e0708070306030515070f0804110111010914010912090303090b0307180311040b030c0f090c070605040c23030c0f03030c0303040b0103 80
    0x2981405030409251080382c210092000030510302403110060905607485505004000c280f030a4080c1062448090700e40300d281c072408680c020501c40000c10028020000400f0951501c84221825070f1103000e8620101d86458a0807208410001d043c101450740e02ca6020012510410101550001100740c0300381e1071600300e00c004c14100003c4400024005a00c05109c00551881c8078041c41840038a81604e044164480300d0b030242a8554015140d045100001045208107401401e069401201400b0f03200c05444030803140f00d400c0d0f01c40900000d00380c0b1000c3c048001c1d00703c011a000b02c1c60749010242248203648c48030210a40380e00485061905a83d528003a00b418010100800400c4010740003140a400100d000e001021a150740310315250300002c0c01841c02081601d8080341c010034100301525141c60000203a00759400789010000c0510a0259a07030808070a8040c0c030740c4050040d00340005228144403413010020081a41030205016101e070700b0b801000614402e60281d088170159514505 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 235871366 1250 235870116 235870157
    0x3020c160b13090b0d02040f110708030702120c060135060108010b0d1a0a090c0e0601031404030c02010804031e0c02120c030d0c05070306020f0702010915020d031d01060303 76
    0x910907040a130400c0342906941d0f8800b03da0307084190701902d0200b180340b044402a4024800d02961441d181c202141a20500ca0440d01652140a25408651040c0c00c0e980400c5142d00411084541640c8403400500900d640e02e180c050440302050004030f20308540e40322210aa0460514a00d001e03804180100b1142c4000d02441e01d19045c2515568100074840d1100585004000c002500380c4c00d101000c07544594035944400301c40c0e5000000310b03034025140d0b11101c0b82c11005484840c0002d042c06110740d080f00f1128401401103616448009100c140c560040d500c408005109405100d251300b00c03122081c2d0104140703404000a43e907030300c48400442c41000b06000075061807401c254048142d900040e00c0c00151642844401d04200c0f0801e103540c9052487c124085d00b00919050012039103010f1043c40c400030300700080c402d898104c031041d03d900c4803400124042d0039280040e40042d21203080907000c5c0d03001c1e01d1071002659240c501c66680c1d0328450709554040e881140006c40c03180c0d0400b580720104 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 235872616 1250 235871366 235871369
    0x409090b0403031109060f09030c03030c340302010e0103110c07080f032a0a050a0b070e191802040306050721020408030307030e0c130506120109050d03020c160b13 72
    0x182c131801e0900a01c940413a60034040c0f400e550030b0801c80040c41c814680d400708200c1c6a15500141180ea40b02e982668942d120045440301c1b41c010841c0c203036134030f00e22520340d0101c1c03600c00090b1907885020b1303142d50011604d00d1030a440241c18959680100c0e4034600400c5c1c01044d14604a9000b0500540341c8400a03283c101003e00206041d0005c2c80000740c02c04104080e0002003070f41c4241200c03902d0540e000301c4d00b0318103940001002e0b840303818400402c10440c005254802e05a54440d40c01903c20601840b044882290380414400e0282105211041c01c507000500204074a040040c1019101e69070003003100c200381c0e541008529501c01400d441003001c0c601010442e88042e0950606142682d09a52800050900030600d500c030356100c076001d2402c000381c0e120340e20000c0c800c0c80c01c108503600190040900f03a480e240224440d200780842e0500c14041e40c1c843e5a80071000341008855004118001e41140c48401200d0140560304d0214411246c802c8018040f44400d0a070341d2440b5200104844259 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 235873866 1250 235872616 235872641
    0x10f05060f180102100c02011b020a110112091704051f020a1e051e0106060203090a0e060a0510080a1401030206030f0a0204080d091403210c030409090b040303 70
    0xc01001288a1400c0203460031003a09440e020402e0300b007032006034144070701e008800608a20306543daa40711641500001307011412004d211070107003e5104100d88800c20307114060140304c2074644d821101d5126040000481070485c0e4002480103283c0e669405809008a2846d0b078018003003014445880d01081032811200d0b00034401c4001920024084e445402d25103000e444080700100341d55041284c22161080d00340e1140c03d480d0b402800045650a400c1035140c2c16606610b021400f2400e1800041240c21658004040341140f0303242803e40e40071403c0007401d1a400c041031031400142034485014a600d103841c29140c0c0545d501c4e0001074141103510140da5003d81c0701d400d10040025071a0807007101e0b00000c00407004c40c00b1380d0742c10003d04080d1090790300655a5125a040e9112000e500403205015a81032008083c0360300b050401305641c80d0200041c4010794451030902d00181c1d01d0300002030404510074001d43e42045e40d2824407a0455102d00c03016210030100700104010182d040c480c1d40e800741720 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 235875116 1250 235873866 235873879
    0x80f16090504020315130812150402180d02190b030711030909060d03031416140a140c011506050403050f0604030e0d020d05062a04030305073305010f05 67
    0x142030f00003c0e900c0200c41880c409502c1503101180c04601612610300e43c054001e40400e6a034075004005007805001103031440380d1102e401d10442d24510300350003211544040c4542200c9031500160400c0131006030391100b2039000c3d00840b5200002ea82d0b44440300000c1422498254032450400006840d5034089503c3c400550410050724100d40d0301ca62000750000e07015034001d00304950b03902d4242d0040c01d0081ea00100320741000100b00003600b40d110503000310310040e5180071429100711245a8113000d09d4000d140810014181528121040b00240812140607800803414488503500a4000001c9400000010700001400c1c020300008020030f0792000d114100a0029180545005100031491a105c500c0b0b0206800da003415940c2c1c100406000d65084000c3c0d030030b1400c0524034414280c8003080743c28600000100d045981c158034105803021617030036842e00da2030a9540d58032031100903051800d5452410710480da40b01c40e00c15603a0b4942c06914507880018403941080c04064050b01640c3c4130364410003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 235876366 1250 235875116 235875121
    0xe16060203030106270f051c050616090902040f050406080a02150c0a05071d130302030a0807050f070501140a020f040b0a0201020f0c0307020907080702030307080a06080f160905 78
    0x10380c008101ca046030301d1454140c0c0d90b840c9611800600c0702c1c05580700c001c0da0700038000200f01c86062440d040210b0354221110030074141d81d00b1000e4401c0c88844000b403c980c0000000681440c0900c4005e0110340c014a800c003c00d6440e41e09900898205801000c1c446d08281c6007800715050600c180c201610341400180300380e100d40d500284085040ba02411307101880407546514003c4108000640544d100c016541203130340b40d42d9070700400380c03c0d10b128002078001440400c1000300071000c0b8092294055010350715054580106a50710200a4100300070803000f00100341d00b845501001d4000140b00708004030b5081108541300000200180c89191494810080c540100c0e14620880f02100d0443c1403c50712100300f080107900a000b4034030805206040010b402c44406008401018014030860317500403503480f0b07181c080322001021120035001d41e10420109005038064000d480e0310413000140410400d0329117031524207200d040c4442040c641e2241c0804220f20040208c104040d05440030100301d0752 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 235877616 1250 235876366 235876379
    0x1f0905180f07030905190b040b0619170307060603050a12090605180a150908060708070e09060f190825060804030207030b0c090f01030b1e0d05010e010e16 68
    0x24015040000f0706a8801100081020170b0048140180a000c3c61481464040c208451503220440d4100c0e004100e00c000256503140800f680e240c810072400d610540c0301c0c18085130340504480324440300c1c03261005203c0c4800090485c05548040d5119901074007000780f00386801c0ca1a16200030740358003440480401031003820380c01815a0b86a9401441c1500303000602c201080e80b41245400110700c41000558294003141c00004007801c0f80d0302c10003261510786c3c509a0888551805403610400620811011056498000285a00400300030520560030803414009401a040702240d842c020039400400c01406a090051100101c80c0d0a900c80c1528640c05040c2459541e502070320091059030320100d030606100b0441400519407044000030103050040074859281c1100004a104000c6141d4110311540310303000720b101100c0003409030020900380f2004803140048625035280c102189034103d1020680c24041d904006a07003000004504403146025400c241c0498004604502225010080c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 235878866 1250 235877616 235877641
    0x40f080d0209042a050f04031e020a0602010b090a1e09061a0301060803072901182306150904050a0c0e0303070b04030f1e030c02010b0d0b06040b1f090518 68
    0x1c104c4c940c42c285a0f0340b890000c0900640c041c5070070140001248121004c59600d850248851550088a444840c03a5a5034001c901765080c01c850035811103500ea010032050320300303504030441980d600c441d40c07001c422138181c090007241c07404042039030300c10b484200d1102548150702c005021110f06500a1048606100906650b80705214000b0300c414104410449480c1d803d0141e500c40a620303043c15503295948003101206c0043c2d0b0040d8015082c50941c0c03888000480c502c0e40e071044004044010443d40c0e0b000b003005400e07108201d00d04034101c010085050030380d48902c03030140300b44e51480d0f00250941c1039940043c117828081045034001e034820040d4101058080040d00e502a41c5460035544211780c40031304403045080d0700c070b0b0b140850188407842920240c154102e2420703419503600810001c50341004000f00810b080102038090350b5801301042d41d500346038109a072900009041101e440c1031450b1000e0100c0c6111002d4000144840c1c000c1c4044d29014503424940320310030003141090304204040441 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 235880116 1250 235878866 235878941
    0x2090402090c07022806050a020c0d08090411030f010501020102040501080c0702181e0f1006030f0209150c010509030703080f06130e0c0102010f020f0a08040f080d020904 75
    0x458007003a80010158290802168a12640038191103110b40c040c051005d400d081c00309856402c1e01010350007040c1d0520800070b59402000760703801030050801100500c07142400c04a029200302008103e150015210741c01002c14450180001e01e680f0314001524031942c1806801c0b807070440e40104030400c00da0303904c1075a5980091141100540d03c54040c400140311000c1c50740130480c05d00a010400c403004030311648250031013208840764800c1d59601d43c50707440c0c000e001310b5a840c0d01001020090041c0c5100b40d1022081e0080e0b0a4010700c0c00e916000024224080744070140a8a10000f62100d100c2c82d0a000b01c41c0c00c10700001c004c4d0b00f44420742e50090003010380144010a144080e90001e00b0070f60f0f030098071044500b4902000c1240400d002502c940350020000880d000d5030806201943c0305005208407000c1c5e1002003c3e40e41061a0880100e40082c1c0191054880c00c2c0b03040580c4011594a0006164176050104016540c81c0b0070000c0c4015a010840e081d6800c030391030b41e0071600700d001054a550 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 235881366 1250 235880116 235880119
    0x1204030503090910120b06040b09010501120f02040e180f070b0403020907020a0b040506012310080612031204060b0118030209060103180b07090b030915250206040303060b040302090402 81
    0x2505070b0348079002c003002011994491680d03605e000841e401409a1610000e00900d400d407410b200b180002c0b03050104600e401c1c840c00340010011080450181c109078005081e40e005c0300e1003d0700d0540d480d07500c00d01900b01580c042d94001400300300126821000c11250701e0215118018080d403e1404a40d0101c03405140300190154410b800080c090520074800f0240413a4000f820025909060420a50f252000d01070b081c8001d915599800510903200001003410070002d1401070342c281c21000403200075070040c289a8020000c6010099515014006000c00f2a0350000311a000e00d400d080c01002d589801480904ec850f56280c541070100c40e10021000792034040c2c5610100c1c1c0c6034080100e004040303c5105014000c4000c4036101000b4903104124007039480d540d115201c02d03844030414036540c8030540c1e80d1760441c1c4c02001c00040350a51740c0c1c18264881c45441210001b0122094840d00d0400e2080403500160000d00400c820107406200e2803004d8007103180d2040c00c2905550200b07a1044002d0f0000c3d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 235882616 1250 235881366 235881379
    0x41d06460b03100905061503030f07170301061d06070f060c0212130e1501021504050313150305010b04121e02061603030506030606150d15080f120403050309 69
    0x4000100c4aa00500e40c028005000c031000d803907101064000620404004449500614001c100001c460180e040740d0310000034003940c545800d404040301690301035034088604140304410301e6458641c20014500801150f01c4502410b0308003036801c0d540070401404544110014008180410b5a480040507940d5010900042925550302d00b40e207081d0901c5800321600000003108040448040742c2441154003e03c8240303125210720b02d0309070503020a850401d0042c1d000007540c910300704000300c1640d04140644183c0740b4090804d8070134072a09101d6000000c0302d00074522810121581846440e0040075010402801d160038038980c040b80e13000d500805171088050600550001e802a1048504194010180b0b5552502c035000c04400c40480e5205501203841c042c00035185080114040c1e00c2400001c1259000c0c0715a103480c64803a070001404500e030956a802c01e204107000c142021009860a180203203154541c0810f941c0c90030240b0540040202030a10003040000d40000603500044001c9621 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 235883866 1250 235882616 235882741
    0xc02010503180304090b01021b0105070b100317040302010224011e0b0a17070305160c0f0f06061701021c0c05120a020d06080c0f0f041d06 61
    0x101c400d070100c441802c0c00d071400009400503003084554003071b03002c42e0420b0302501c48200c1c94401c10f84020368100d0155001c01e0b410000140060a407408a0b94060a800048100c10381c49841c2c0c20f0105e00180c03444e0745032090004003841990780411000603443d001c0070070351120405442c400c0c1422401032080040e02c2019055060400007400d4440014021200c0f480351107031801e2500501864042c04c2c0c10425074020008200e00b2482401905e1246420562440940b80c13000d2040301c5903500100c00b80c40f605400146800040d81150454240e940113010208009080c0005c1c16400f03081100740b030810360310410419030403100386103403d10440a440780005440c1c10a400c00e42c0e8900c500c099040009001004104001d1043c0c3c0c0030708590706a58a08100351526600160369031030900038003a038000c0c40346480c1c800b50300d0040320781201450050004102c11840c0d0b02000d1000b1507509594141f83c22120420000c010a422004e42d20594403101412040040c01ca080040320303842451880a1f100011 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 235885116 1250 235883866 235883881
    0x303020d0b06191d1305010e0c03010f0506090607020405090120090307051c02060c0706120204050105070b19020d0b0910030209011e030b131109010605040909050c04021207030e0d0c02010503 84
    0x143c51803040d002e400311102a91417200c41d801058240070342c5001c006000d01080d402c0c404002075038141c940c40d024420040c0e04090402110350010814254098010031014005032100c1c010140100301c90f0300042110b00e81410b144ae80841d10109201502005100c113072240c0e5000203040e403c0320b5081d00d08010785856599100b14110300c0354006900420005205816000000b0b8900d00311105551091690382c03c03125004c0603441540b0440d0300044c4184490800301d00710503449500001c1c1c0007103102c00c2403882560302040c3d230071515607698401e99030005004142040b02d00d00303510515105d480e00b512800d43c1d0019a5448040c0a0961216008004c10922405000c07001e0081e58014a06108504e4004204000e4049403201140d07060340110510a290500a0549040e10040d843d418201420410250018602c2c07590642d85031040106191654507144028180201302e9840c6800502c1c0128001d002e071060f100c554900c60340245696524a40e000c040000e181d0b50900e8900d0b80c81d240d885 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 235886366 1250 235885116 235885157
    0x21c0605040302070e060102120415020a020a08011a040e03030f0705070b0a2715020a020a0c0603152702030c130b040f1d0105100c06020301030303020d0b0619 70
    0x1440104458a8102844249a00003d4480443e6040c909800035581ca02d4012600d440d4402000444148148000d0101e025104144c02c501c1d55030f48112014150f06400181000840c0d5002c400aa5920601c58688150201408001c0b010907035040c004031040d8100b00c0d41d64480180640950f0b4040408030760b0b82840340f42214601c0b80c01c02400c00c43c074204079480300f000304100090400c000c48840540240314401e215600c4010760440c2c1d03031111a0010070a190081d6110310700320b00840c025000c00c071002a8500030f0a1000d02101c0d0380010341c0300010f103102c0d00105455041144201040400a048a104150a4658040c45540242e2a51100422a0001d005580407a80c052000c5c0501060418054019008652100645104444da0784d40000005910b40002a00740d0b101c0600600c16818450a0040c0c040d10b1440c0c034018410580d12154200d80017a04102c0020f5000070303403003404405074054500ca0a504403171140c0b602580c0d4100d81103841c1c8a20740002803000060303141d40100c100c80c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 235887616 1250 235886366 235886419
    0x519110703060e060709090c3e01140705160f0f06141605130b071703090a02010210020a230d060914090c060307050705030906040902071a0606040302 66
    0x81401d0040c00c9010000740c1e00c413041101c0d400b0000d01950000540400b150007a031044070b10b10f40750000c140d001005052030701c1c044a02d4003a4412000d01e00b4a990100000e44500310000800c00000c00141801e034903111488098005010080140541c3e10036000707164400c01003036800340508034529a02d1a106208240395500500a42e1401d60341801003800c0c440254400c081030004682200d000207002e80302801402c010300b00110340c05d401400f10702038030b0006214190150700d900b058035101c4882600e15600859402003281c002041480031543c0403c40c6c0b84180306003440540c00d0000d0034a00402da01c9c19000343c0d115a50124480c00b0305025021b04550300130605000c24440182c40d801190702030a201c510442c2c43c44050000100401303804500d00d5506a4000c20051a40c3c4620000b181c06070400b0505558074002042100103d0391464001c5c00144080b0710050b0300c4248070300306103142c0b00583e4001e8904030803001c10041c5568880c001c032400d60368120340c1e44000c401000340041c01c80109 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 235888866 1250 235887616 235887623
    0x5070315030b040c051e09091e070303090b041a13081204050f040504020102030331031e090e0c1c0c08010806100302180402032d0c010519110703 64
    0x10103404024000d850b02030620440c0200e010741d024941d5481401010021413a810748a4902c0e01e82401c4245002c9400c990030007039002c1280c1300f070912948070014414000180c80800d070f1081d1030401c201030304491980003d14070001c44504203803510140c4504142003004440103103000060418a0203008101d100c0078040c03400464820100700e44018000390710900800f4414103d200701031b03e480c506805840d110b00d81c1a4055419500c40890801505500e4107652095044050900490003050f00900742002e000340e44141c048542030340b1526600c00f00080d003908015800c0d00030b00c00c21001e0176000741c0106074658070300d554045200b840701d1460129480f40e00d41504003c0040c6c002030340940c20a068070210002d89035185c4581080c1204034000b4440203401c520010150080803030429461584180090107440070b9020000340b561050804240301071884c40b81145080c404003007041100d071152400c0c2021403628041c42d0307205c030050b03601c00151400c1005008102840120a119110045a2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 235890116 1250 235888866 235888901
    0x3140103020f030a14060a0e0106080307030c08040b0d1d0606150c03070501060b0405030d2a1a0406051617010b0304030e0307181103040f020f0619020a12020a15050703 74
    0x3134010700c10703246c010550700500d0030b50608042c031048400612448003201c95200056180650598054032214000d072001c1e6400c50083c80005500d8411400400b243d210032800003900280358078030a003000c41c4240400001c1d5106004002c8039459095210310341041940e0110380311204000d9603841c5208451000744694200388001540000e403001031b006913801241991501c8604071800c50ba0030007128800414030319415a240d18803110b50040c010700600955592100081d400c1c4049088d4000703036030407208155500b04001d002040c00081c00742c42d00f01d41c9407a0090061150341c50283c81d0041c002c1e036849503000800b10f0200b40c0583c03000c0f800c03000041c007035800d9280c0c2d480343e020009425041c28101b40c1d0500c0e03178661032024072000320b80c0305a41c030a48200002c0004e40a102074040070000c0280c00c941c1c20040300c0701d07580f80311014600b05242c9900816011440346084600305070511552029503000040c1040054001000c5266240d0f81c076100080a60b0b0b944003c4000c0d2409031291250801d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 235891366 1250 235890116 235890143
    0xc08090a030c0503071203050a0305060d080a0e0909010c091404200c010e01020a14070c21021c020f010804031b03110c010c05030a05070f02090a020909010603140103020f030a 77
    0x81c2d540c400d0700071a0300803410b0312100c60341c40d810902002d0100a00034000350007007242000803800307640310980051011b00000360b035400c540e40c0d4000a600c000c01c0720380480c4801ca1555030524141080b1540b0134520300007444042081540a08210840d000c0c1040782400202030070035a80b21503000c50038030308201c21807140840e440310200b19107503c446d1000200d542054000060000b050080f5104100140d03190a051440503481040d250000901100e003c00d0511000800c0d4083e84140860307900425005408601c0074410081c1001e0003d41004100f6001c0c03040b42c0140c1c0c2c4421354030219040a003001e4417956075500e000c0740c40c10b0389429050540315451141505040e488002c00c010154440115001943c040005440d0250f02c41c0e07000704140e00c00c01042200343d210b1000350942c9445030722110140b980c1d9600090740b00c6802c980c440050f56010810344180d15040039150300608190030200404030345e00b0b00403000f0000c140006409400e036803800f40100d44042000c205195000700c40050242c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 235892616 1250 235891366 235891373
    0x10311070b1f06020c121507090602160f14060c01020c0615030a0b0a02131701020a080f101a07060903031d03090d0b0603030c07030303020405090114030303070c08090a03 75
    0x40c0e2090390044000d01c0c00c1200c100c02c09140e000c0c81015107510350010500d030083d00041245001621542d640c44d405a40d640450088148460700d00412403a00c0300744100e420150024070b0240d440552030181c9040c00010040514054070410680b10304a010f503107602c0350b110110781a8800c3d0343c0c000d00503600c00149001e603028045041070045038101400346d00311031020200750b0740352084040034044218280c042207581700c1707590040032954403284440c000c0780c0d61154201b1030710807600d8081c119650005010052030740d2082d54076030300000d031064000301814040d02c01400f01c00a070003140200c0242803030440008001c0d00c207840c1402c0d40807500b480042e10a2800402070b1040c101456800e07040401c10390f0ba0a0000f0090f15007051000c0e18881d100c0c1c401d42c90351101280041d00782034050004002c0d014070181c0c2800610f000d50301035180035964901d418240484248164000c0c3c03000c0f100b2411602e8955800320841c4d0708042d803840c003401d07040c0c3c0f14107281c07100703110f411096540100340760000800c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 235893866 1250 235892616 235892633
    0x31a04060501091e0b0f0a06020604050106061b14070308030a0e010b0405161b0b1e0105010203160b060f060d0c0212070f02010804050313030804170c0609060901031107 74
    0x4512601041c88641d80e00c1c041c10b010f4a820050032140707165002003840507090039920081c2c5202d801000c4041c1d198120000c2244042d00da000ba1005070000c20411081c0b000c24040d0700014411031604030480c0890f0b540015081480d0705005105055880403108101810001e410107143c000c41d1040d40d81c05d01e110580010441110030039a154280702c1c0c0841c0921b031920801c0d12581406001c250300240020302190040d030482218090f41c0d0103000c010b000b1807803130203e80d4810080100307140c19010110305c0c60f0f120444c05074003190442d4010482d280d00340130041048003c1640c4820002025250800001c58401804020b40c1d04090042600c55500287d5001401c0d20354098013520b6040e84002500303001032003040809810205503004801c01944910026a80180607000b542d003440e04a0dc845015030201c1da00c15541240042018400780d440d4030002d0160780405070042091510030300100742e01c0d000e140d140d58811807002c075250301e040e4003d030081852240c08402195885841740380c031684 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 235895116 1250 235893866 235893871
    0x6150801060f03090308130203030c190c090b03030901030509010f1b1803080f0922020304030e10020a0602090a033008010f090c0c0803040f2f0603040309031a 70
    0x28003610640b59596000348243d44000d0307015038070003c16641d0400c004c401100e03589012070300340c0700c10850041540010300403021515032180040303005040c9401c0400030a20580c1145080c0d61514a1131a45d603a80041142ca1448083c28045010365400400500400005a40c4c440c840d0030b204034408655440401820350401644960860f40c410001c44030b00b5409601000740300d450104400421150760401030701d03c40b8002040148403094802500c4003685001034204000d94021003400105604503c0b09460204107440007943c010148000954132101400007418595000880000c00e4a4000402015580003040d44071300707803442040b0391181803001c3c01c6004c4d50140c0e04941c07034040d4890700c01d1030b048440002c0c81e02041403e11003440c000b002c00c10340c51001e000e1443d01440001d84a01d0185104030300036014070104e40600e09100e0000d8a01c14000c0e1a600225150100003c000314a500030804003510055101da84500c1d061f50848002c0c0c0014000c48091152802c031400c40007805031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 235896366 1250 235895116 235895129
    0x3060403090f230d0501060b070b0402100c05061501180b03010807090c170606040906030f12022409030c06010b0a02011b0c030518150a02121e03070306150801 70
    0x50300c0d80e995100d00103001d83c640326400d415500031904540503290408100c640d4034014030000400c0390781c900c20303011150302450303040314011142001c010039450200101c4402c0c01a030700f491001c0402c44c1d5226a180c1d00001c051200704404092940c1e0140d2142c0305c02d14040c0c244008580491740c031000c204286400c00d01c6018501c2c4150b6a0201d0f007801c4a004686015103180c0326200062900c2e4280300c1d05020042c1860340100c800e2000049070000340c064900103500900401d070071020300c0c0c1001c5800702003445000066502240700440e80101c44010b04901015401d03601d001c3d03484894185081d4440c01809800900c140000850509900f000904241c60640c008015030070600720f80c40f5000c5501440704000c540d110100d40b010034068402480f00c0080300d500e20446202c05800907410902800000107101408640d802c141030301004401400c8030302d03030031a50601403c5c1418600c020003400f006040b0302404000318031300074020342207080a003c01414072241c03003c21080c020040d100911406e07 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 235897616 1250 235896366 235896389
    0x1c2712020901050a0803031914010306020406030e0703081b010204030b09010e06010e0105010504090e0309130b0f0d0b070302070f060504030f0e090702061503120c0a0c1d0a090609020306040309 85
    0x20f81443c0c40c5000d031085a2200f4082c43c11540c030081103070b1450010550656400d62a280c1c40080074a60101d024040c0d441140d0041c0c9550405900800722010303c03221903c6a80315010038030110380f400307013541c5516061903a410014040d42c10414064001c0d54001400f80d032010042c0010888190410b01e05035202504581050303a131101c000349035520a10605000c150108001d10a1104541003a8619241c0740216803503c0d50a002083c5004c29060312070307100700e58803082902217240003403020006080c200c1c1c2d14050440a41c48904001e003020780040c042c907500040c15010042d050484007007694026101304a40c1c138050078090b00001c1e08000c1000000d090f41e190005620f44054200c0c05482240c0c000c2c1420742c1c5241c94112204403020406a143c03207032081092000e0020b030000c02410a144000d08030705203c84c0391001c6041040e03040000c605440d90b0410035141c0d800686030f540481c0c40400410011864100040100b40000000e9014064032040005050f080f03002d000c11103a00380b405 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 235898866 1250 235897616 235897619
    0xe01110d200f191b051501050f0a050618190312080f040b040203100e01060503010606020d05030f042105090114090d0b0a020f0a0c141c2712020901 65
    0x1980d40c5845408103801400b00d040c04201c3c0400ca41c2044072148001c0e6062100e0511010354600403071035604401100e0a601402c0e4070b440d1491060f02d0140184019550f21508140c8080042e40d0249a4055140110f4000c103500c4442a4100212414800d005e003407061042d420141d841c82070010380c001a164150144100100c01c0e1089000501c100c12144801c81c69494039600d00c40d074010068000d907418407803c100c4150403603992086080350080c440001804515100074075007540c00d6980200150b421001121401942160403264850807036841c0040c00d030b543e441c040301140001c41c0340b41c0f8041c920208000c030042d0001d00410102c0c50980352030005c5040100e58a00d14400c010119402c0500000060009045025020340104c50008058180700450245c4556600a00ca11000043e1041c0f0040c00b44544090f90b2560306000d5800b802007041e4002005407100e112182410803c002d64000440008503e5820030710217204a51304e40b1201d585154829005000c00b000360702c201c208500 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 235900116 1250 235898866 235898921
    0xa0e3c060612040b07020a06020d020d1b02150a0e100207061503120f14220b0a1b0302010e01141b03100302190e04080d1b0e040e01110d 60
    0x180c484910725004900c2d12591280d81c1d41e16280f001815440551056010000c00200c1c180003400c400400c2d15801a01c0303c580720980e8040d1200d501100000101140c00c010003145e01040040c0e50014084000103503071100f0300e100e401008519a404c0d0179000e5801800c02070381d840d4005140240c004e1009000031911052031624600c0b980c4401010b10454254a013030040c041c0c140040d4080c058204001038868140c3c8004081d44903280c0348200c04490216002d05216580b101d40107420720031041400d1204c6502c0103071840414406420900d100c021400040500c00d401020500c80d042000340440300000c02c4040110000740c90941d0b4200d0440040c40171400c0f44010359229041e40403290540600d16000d20074030011800b032040d11441c400c0d1001c00c01e0b540c20000d031030140c0d204030302031750380e54086e405020200d4118145c1400007041d400640070000f0340c403182040b05c024080781d00050302205401c40c580106801c41e8000c02085001c44d01c1d92440392a0340c40503400c3c85c91812900c560b0303508074a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 235901366 1250 235900116 235900129
    0x305030403031428030204270507080403123309050c1303020d020a0e01150219031e091a07050f0c030d1b081605010b040b0a0e3c06 58
    0x1802c41c0030390303680701c405060100590b040c0810003120350b04006160903294810461064240907a04041030940004e4500c2072641d4071426502030043e245c0303cbc04034107103540e004081507128407100a8a680300c40c144d4004d03d0303500c4065141405186418400c41d892414058446100c620500708943d02c0c050000d452110030b4001c4031300f1080c0d0224103d098905513400c200d18132002e000140e07084540041e002c00c0800300005202d0103020a44c1d001002c98800282c020328041345022811a2050040d05810000381c00c400700d0500311140c11003500200822400c21680519240d018198040070340750070303101c0c0690032002420302600800507614604869a401541c5a0244181c9901076001400340e03c1c07440d110720307003038918401150001a404105500c643e031040d0000b90501c0e08126915040d1000c00c0381c00d201d4400265400d0703805000d07810040c4c0000c3c00040c80382c402d5903030307403150b40c00040e9a02040940c0080f005c0884020520040c08602104c18188010f03803131410344541c10008650742e40343c880c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 235902616 1250 235901366 235901377
    0x9060603130308090a060c180b04050d060b0d0b01060c0b060a03030207060c0510020301030c2303070603020703051201140109090203062b050105071110050f042a03050304030314 78
    0x254460756280032554216003031180103000b00418019200450000340c560b002d00307881c00600341d883c150f81c00e05085020361035454940c003031400d5003010041000707030b84c544900200442e07810600c0042d107502c0e10008100d545c003d411000f0700407500c038000850300a801080ea001001d001c1e072500000390b070343e60041c84582aa1400003801580c0240f00400c4403d209524010550748500140c0300f2140300f22005100b40d80007a002201d45004000741440b013903050301055001c0c2c00040128040200d00e0902013904e4002e80d000d020101500000c070300c4245402101210301803a03502c488a0510343e5601c0740c04054114a941007400942100313000983c100d10750007528011000100340604c600d400d082c51140b200c101d81c040c0d844100c1101d12043c08a0020710a03a40f1402c010340701e44a40c0e0102d060751030300700110007030241c00d41440c00c41030296410303203840032551096024060040b62414880a202d01103101403130240d460203118400b008100010002e042140e1080d10740741c500b18007000c81c15542d400361 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 235903866 1250 235902616 235902631
    0x70602010c1b120903051005010501030f02070b0a2d02070209090601060f0c020414070e010212130530160e070c060903090506040f031e2120060609060603 68
    0x104a141001c00c800303101083c1c60150a0a1070b905040e44ca0303a07407500304040090b5000750643d544004001558141c0038103a440c1c40004421894010159a441c054540180c00714200c1c658805803409540d040d83d164014088a08401c0c41b4541e81d40c100840182d1f01c404412401102c1c80400314401e040300182c5079050350360b03136103840c4080c82d600c10044070a11014181aa4880e80300c0040141c503c5840a00502426040d40c4109010740e000d0001ba29044c0445c0001e2514031040000c2e40009500c0300e041c00a42d6002c9503008803400005840c101907413661100e4943d00115401d00c0680078800042140100300210f004441f0280d4604c8006000c800455030b11000c941801841c50000e50b55501484600d446410510040d50301d85020403801d410580001a134000c0406080c003e110300980c08002c44200c0e01c0c144402e240c1c3c1580d0f11508841001919040e000c4000b0428a1a5000c4c8085810f0302d0401020301122484000405176505e0703099884900520001c0003044040c20300b401203e104881 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 235905116 1250 235903866 235903907
    0x1d0a0c0902030103330c0806010e19050105030907030606080a0314070809040207060608011803030608031e070f020415031a0f060f010c140303010e070e0a05040c030f060305070602010c 81
    0x5c103030400c4008070fa10f01410010b0b00050a451082424240b103a41a188183c3e66203030090b142ca200007403c08140040d0031031140403c1981a103501d60008a014160340084c42d000b034403034807031000f00c0703180c031f1240e400040c1440c3c14a040030034243c030700090f05101c60f4004e0340d40749520b901910540809104003400030348441c0040000c41d0039401e185c2c0040003c0740c819900010500d544189903821034a001d06040f8500e8880c1001805055050090070050040d08002d1440c1c1410074010050f400b1503c40c048601407004918141440840350390311660030340191052141c00c0905103207038290a8140002c850380d40c51400c03510b00d40d01c800310034a4400d10401103140f10688503001009150320b51707128014100f140c4811030300001f42c8442e0b83d0b1b41001401000454403075041448005168200504100c10011300d45640c40c076a0780d81c10000400c44e5415600010005d01d41d18003100680394174613038050341d5404c11000204210300013459004513171007a03008018100600720100d82c42c60080c5890b004610 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 235906366 1250 235905116 235905143
    0x30c0d02061f0506180d0c0618050d140a0b07030501090c0f02070b0c0102040314030c062809030306150c0210031109090705072027040b07031d0a0c0902030103 70
    0x280b440003011710050304904c07014010850300c005a100c0c80b0401040303500c0c03012807030104402d0b0340002146929907650a544602642404007098682e4031040c0050021500480d48108042c010301003a506590060701c4440320345407820001d800f0784800e204401002e0302d401e4000407007030b01c100003c031404281c650107445494507180188145d50030441900c01a550300700400000240050000b56010044001440d220074030308007420304008000b080b0070188240ea0b5581700100c61440482049600940c00000e08403040341003c0300140981e030030071840700c00504a0000b8007600f00c0c0400040b14401c891406006280c080e04a0a1307644111142801d030000b071105204070710b031201c0c11036480415458402d05024603511910494102000d001100b032003070303078860401c81c02c0403540300d0009030300742e01300450001c020384a500445e01c00074409000490f042d40428405c91290300f040134410101445826071210046c40540c83e41805407003100ca4143c074a5000131880d00c00c3c029030307040b250002004e40d07994 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 235907616 1250 235906366 235906369
    0x121e03050412031118030c0a03030314060604180905010213140907020115031514040f1208160804020307050603091b10140a03140c0304020f0409120e0102030903030c0d02061f05 78
    0x81c1703a5000c0055060060410010740c5231070700c2c204000150301954001c1002491101c8034640014090f001a01030107040009120841082d0b18200c1da03900070f05e800140e02c0d8541e04280b802809940100312001081c0c2400107030300391172075680342039401049071484025228004180c1c02c0320384039a24413004004c010010004240c00d01c0301041c43d03042505012802080800d01c11003d40001c40e02120200031211408080c0000054100f5400c04d01d400c002c0c82d20f0401a502d0008024850544801c03c128000000c003191000c4c8091401050045c04154590500041660f1240000f0700d1030011016402d0942903a46050b40c0740c5050f040c40707030b243d4440c01902181e064099034040f01c012814192034401d1201440307407000c0014403070020148041d45a040c0b900c10056450b544000080c8541e0034400d48501140405510014a40c224100020b04030500d2005038290300446034003d6240c0404a0516400840400d6030711900d44c456095039081d5a400810081d0b490f40e4003042900d95080e0389042c0b00c00e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 235908866 1250 235907616 235907647
    0x11a1005070204090b07050a110601030804050d080904110c010e010b0612041a07051309020a0806040b0111160e130c0b0a09091b0311070f121e030504120311 69
    0x41c0c00a800401c1444407038548080003642a5646d00004a0020303401d00442d501035040000040c0c0c10001e40f105502d03648135144180601d0091038070408440c1010070410a04808540c200c2d18081c00034007040702869204451078000803d4284c55500303080c031006480e8010701c1100a4410000d0140f410303d400c14444121079500144122030200141d03604ca02d100074480b201c01c0c400c0b0700301c0c1d0301c0b0703603440c01900ea01070901d11b0039078080c111450051014801d0a038010f80040d900c1700054070b0004030407152900403070b80c640e001110b1601a000c0c030200c280040d04501003040948034401400b0b942c544410109411190000c04003521116203054244a0341c4050001466641c0709440c0060f0300d940c464081c00100d0f042c1040314075444540300307001c0002d29090300645c080b0a40d801d42e91803d02075591108000c0490703011005004085401c841c0a0807030190148054000c01c100241c3c0c1d60300700c4c2c00700290003000700f0384090700e003141c1001d0810681031190181c0c590300d0314044080e50401c0d1501480c00c84 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 235910116 1250 235908866 235908877
    0x902040302011b11120313090501180905071203080405150105100e0d21020106080106180e070e040507060207050d030c110112020a180b07020a03150204090617011a1005 74
    0x44c692554050002d555030f83d8040c0f28460001280519900c20740416010b040c80720030350225242c01e00300f0004203c01d83c0c95042840b80c0350030030300010038814800e1400034102240c61700400c584074806400d946c145944008920301c80c520940864840d0403210342c40410100003480b4035075001c0351000c0700c549524450020a50f40803070160003207180381c1503030707860b220381c240c0c0334100a040c00750400342d451190b903090240c0070003011000e000b00b11007400d000c140d00441c84ca81d059801c52540b01c00140643c0481000040020030219040901500b02490125151411481400014850810007140d146000e040300003c17154180c590485064640d9582840260940001d506208425401c01c85a01a42c0001d02c100c02096541c030105265240204407180071541010341038620030710507000140c6403503040c04240c07900070180111582c810070442c0d010788180d0300700414080c101100090440b02d90140d0364610703000306e0002d100c841160542d0200c5035500d050750907403101c8002854011140900c00520 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 235911366 1250 235910116 235910123
    0x1051905040515181501051b0703060c09080c130f0e0f060a0e160b0919060302030f010b0304150c0e0315040507050a0312140702030607020a0b010902040302011b 71
    0xa48440c0c0d540c0c0050300b02c40301110100c6402d446a000112145000d958031000081040b401d044203003840465200107018030345209040c0140000d5003a00b8070b1040344456006003058045892103a102e1505030040c21180c180c00011407a00c1030045020100480d5010442c0b00c0030306094404c00300b03900340f00081e142074403902040507a1a2900c26083d01d040c00007000441138a001003005003000c1d62208100c0d07100c0c1c48801d0180e0418002c81640040d010052411a100c2c0310320030b91107030032260001d469403030280385c11300c09051510000a44603805802940c030404248901e0f60881e80c3c1d40e00804e07050311044500605021512004440503442a03001280702d017190304c0c024050302100d202003480c1603c40062109154824800c22041040411606015000540380741c0c02c0f0607d160b41d149035641c0822114030038880c1290140b842019481c00b981e0b813085d0020304603010350410b80350194807403485200c281c488075881000401d8130b0342c15000325400c482d0b045c1e445034551000685140740701140d051084 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 235912616 1250 235911366 235911409
    0x140a050904060302030a060e0d1b020904380601030c02210f070b04060605010f051902030f0a0509010801080309030a080f040806010b0301063b0d08030109090c080a0b0105 75
    0x1c005030320701b0405064031381d100300c5d00054500840540d042c03602c04841024420003620301c140700c400d0301700c103400c00391425030640366044591218500811034003034241d80c2a05e01a03115100454850340001210f140c0c2c011030300d02c1e00e5071707495080c011810b131001c1c00080805640642d0601d50070700c03010800214810760000301c81d410030b00f140d03040c00082e511620b01030f51807025240074801030050900c075050003440f003420000e08000341c400d8007030550b0040c2d010003002000120442c104050082c001c9036034062a0101903580c4030842c1a0103000f42d00a0010a0f0004148100100341d208001003182c4030480c004005042c0b8294035621645c0320380c082c0c8048129007409100014188000304140c034007802101d040716440c0c1d81880f50043c224407807650703400800300b00d40b0402d5500d8102c1144515401601c111880705107030500003c46c01751480f00f8402400d131710002000240d500ca20b85d00100001d4483d42c0da603010300f640c594815650b4104804007405c1440c12400411040c0780485401e058003d080061 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 235913866 1250 235912616 235912619
    0xe0a030c08280509180609040b040312020d1407020604051002091c0605040203061e010b0c0a020a0603150506040807050108060d0506010305010c1209050705010806120601030f060507140a05090406 86
    0x7542c0420b00300a04080810700210310456076150030300c00080f00c5050080070216078503000300028590703000900050100c8a2041c0031406241c410b100c044c0301d00050231400c2d99603c0c00c44604000030300240c001007200001c0c1d40040783d1020b101045940c00303550418000d001141a42410070000d40c0100a0744c3c0d4041e80b0a60620b02105500c0255000d89004000024a91419005060809070000c1008184810b03045101900b02c0c540200c060542c0c0d0300254190316154403c0c40341d85460704c0700030007941c0b11012810000e41186e0542040c180d501e055007104000c1c0da915424000540203900078403586400152007403096500c100d07201580180002c0502c411007045407605810071500380c20640303071a51a45020074580d5000720f2003022116660804000c8007202e0746600c0d450f4080f40c06183d04124440002c5034042e0780c0c82c0180140c06005105a45503541e591602840300841608100c400509020004000600a01ca1103201002c40c0c12820300d00101c00c0d1044909610500c02c079903000341c5d180e10 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 235915116 1250 235913866 235913917
    0x121150e100608090a03021c0302090402070c05030d0201090506240904060c02060115120c110d020c100f080117030403080d0b01030b0306090703020d1401021207030e0a030c08 77
    0x21024094500070850405060a100009003d404010001d45007a4040031054001903400115a0f2161170104000c1e00170301c40c45d00003100070384140c0c0c0500c1c4d0302030b0001c43c028003802801011082103c108030111808a010315200380d0907100300e40f10241c01c580241c80081e40c804e1500710f4450b0089044903151200b060480300240c200001038905842c0c2c0390381ea00e140010242c04020703481c00740803800c070b285005281c0c0e490010508400d440c40c940300316880703400c548111800380d02c1c8140b0100340c0500340d07003001c105c00000a60303c0320001c603a01d106101d07842583c1e0080307024090724900c6503065900d56501d43c0c244404220100041940031010340b2080000001240e2044060110590710041c003288c1c0d91005000107043c0c8114160f0103200c0d40014050104d04080001c2200460f5410350f40885128041d00b0079083c2102e1540640d5460350000400303940105607281035074800c8a40f500d040014405c1e105040d07649401e4450001c001c541ca503104480419944400f40c05c4c00744461580e00300b503195022 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 235916366 1250 235915116 235915139
    0x70501090b180105010b030402090106050d111b0709111b0c041d0d020105090601050d031b03050301180203010506030109021606091103010f180201140c01090803010311012115 77
    0x440080d00d40b0001d401c4034405034070038011540140300d160855811030070181c0008444000611070201813040001d1440340035482504a850b115900c43c404903110000c107501070380041a04402803403e40075a00380491515014411310522890650101d428a000c04a19003205d441c405040d8401c1d100d040313003440c001d0745d890081e410f06109166000c68007a135000011840c0c00e5502c00350206590600b401c12242c04400111541100c0c000c450307003550000a420191450004010102940b41c190640c0d01c041c5904600258100c0d40b00000404120941001c04803c07800280900c66200364100010440410550003a02080d0003409845801112641d2080225002a18200c031072942d80e80014045d49002c0c424515000c1850302e00748104002ca10910681e8068510003d062080d21b907440d003460b5281c0c001303440e016644040200008845801c1c80c5007560070922044840c1900e5542c4892075511801c3c503240c1c0d0f802c000204000f10008001c0c3c0310054442101d1810490180c646c000a602c0e00342c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 235917616 1250 235916366 235916371
    0x30d0203010b090a0602061501030513060204090209011404030b04030c02060912010504050d02030a020a12020f070905220b04260d090b01051002030403061e0603060b0a0821070501090b 81
    0x1200a5440303c5010520161040a620000c10740d0410300070080d60700e1030045050702d440710900c3e00196543d100703024444907101580000e001a4408070b0f0109902c0000e5000302201c0030242c0301d0012410441120315103d101c4c500005085280003400300300004e00410302c0c500a184000e001a06015040c400305154400c0c002ea80540c03a174540045c8424014280300c0651016100e102030351410302a490003941c0d800c0c0d4040014895071030b4507104003841c0d10900084030401411001c1ea05040e0b55072174044060075040e44c109901510507003512011307541c44a05911311079448180c20036295a6503c9041c01948110351164035103180341491016441a034000b400a101301101c0000c80c4002030400c40d07a00c440c160041801010a40c0208086680000c252400c40c0e41c804401310f00c40c22818202001e080c181020109941e081503004030401546400003a03580c01c0a4507412035056903160491303500c0045540c8003072003011054268441d401c0120052801390701030030010545a00c1c66888040b0000c04 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 235918866 1250 235917616 235917629
    0xe0f04111305041a061b0f0615040606080a090c081204031109040b190902030115061d06180135150f04050a140703020309010c030504050a02090603030d020301 70
    0x1c1c034a141a66a2450700780542401e503410007080c807605040c40d40000ea003c00080c451000414038202d041017141c91645006e10300c3d01603c2d003200708104100d82d00c1c07100307542c5032403014104610700c80c0c181010f00c13070b8004a8800d5580c0c0c3c1c2700d076241c050610b030080c081810b0a50390886840000b1441120410824080d40c41208100c1e5590780b6509121507007188050109101d41412418000410700b0110000d03046500d0a620088030b00304e86a8180c000c3c20400002034255007483d00d0b61034504042c0b4900c900f291059261400103e8042d01ea01100f25880c14165610010610071901d81e000c0d07203c62002c42860605004034070f0702a00030b00c46c0003000102c810807039036994440c41180e05e2194403d10350300722040030010307030a0b00c000400003041410303492000e60249584200080401282d50402c40040c00c000080d1013040c142140010082e5008480d0404550700303003007aa01140e0f12a110389485260404042d00008941d58200b100d4507101400c0e0641c11700c014006000981002d20081d402000c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 235920116 1250 235918866 235918901
    0x1080705280e01020c060d0c1809061406090d110307030c0b0910020a051207111002011d0c030c1003110f0a0f140d0510120b091504120e0f04 62
    0x700060051400c1c070308428082c11904804803000b0346855400a50b484505039a4003c2000e80e43c00741c04860300b800c0b411400c104152000400038045049034408401d542001100e0b10001c0c1c10b080922500e4450b9810040c0c0021501d0310801c04030b50b800c1540f601d101001015501620780c0d944541480784103540000c100c41c80000b0f241c900382d02d082c61f4108050328450010303022812007501ca840c2c43e290090303035092041e08000f4009082050f14100da041840004000801e0083d0381100240204169860101000e1004007154824880061075040040c8000c0060541c54040400e218100800540d000185a10f40c0001d000d0021000e001e411092442c81840d915042a000c002302120891802001480400d00c05092020010411034144c1e182c0d861001c0b80c81c0c0c40c1d0300c0b0010358030301c290ba1001844101d882c81c100104030043d81c400d802005614121a8603000396a540c160001d01518014024035034503181414050050461021044009010039805084400814144c0700c1d81e9890044d46034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 235921366 1250 235920116 235920187
    0xf111c0c05100309030522050a0305060a24050f03010209270a02031303030c090306020d14010503030f07030807021603060e010c0e1309150908040503100209030c01080705 75
    0x401c0200440b00785403900d011301100d421501d010740307280b1402d081d9a594840e018861094980e103120641c00810700909400a9285c1d40d0416030b869241c11385800300c030603050030401c07180503610390707501d4001c2c1142c0e910384810070345003600700800c4000504845415540030310440003070b07948844c031441c10804143c880c0c1c00310b601d0300100c0c45140c900050461194034414014420b1140b400e000d0030000c1507050800180246445e10140d4400c81c241c2d200510032800064062400b107a2034201c0d01110b84841203181e1141d0300d81e01010313100c1c0101043e0300c28050040c083c603008284038195481e04a20680103582060324268840c9280b240f06800a50380c2030b85070030303040388041d0003440340c1c46141846103050100e4010460000d04900c03090b202809400c0d49034401501880051015112605a01c00c01000782ca0b0607481d10f400c00f5041441041d11034065001e003080300803001c1c0225290540010050401480c28070015110141d01501c6401086418003800034107882d035a000c00c03035102d90542d540940a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 235922616 1250 235921366 235921369
    0x712031106090c1003021809040501021210050f0102030903060703090f05030a03020703090905040201020601050112140a0f06050102030f0913110a020c090108030c100509010905100b0102060f040f111c0c05 90
    0x1004e400c258004040c4100600783c0089247c25021684040131100c7c0d00e8903440c0c034144240640141c5990b179075030090007000d10580b02e41001112003155030568040f0440031110700107a07120302a49201c607806411590005003e00e101c0e502000c01c05200e4001c6904c40d001540359286107030082c1c4105800300b680024001c05060b04216108002c014041017030000d031801c0c0d40000d4480c003042c428981400800c02c412400c110094115800c03040b4135041040c1107261004c07601014101d066003d07414903142140108007944040201c2d02221050011546071204030b90034044c41101901102100650b03481110f07000142d20001005035190542c01401c4441e03c3c03000b007183c944010f80c03241015a00c100000740d500f01c2c011961b40808040104001110380d0f0307150056000d003414440040081c090341014840840c42d80d400361041c240c1c280c5c01c13a03610796506600d04022040988001d444064601c20302800a02202d960b1a4400300c054034070341c0100c00c0c08001c9000d1003480002228034549131081031010b0b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 235923866 1250 235922616 235922629
    0x30a1d01060519030321061a04050a060201060b031302190b03040213050106020a0201050d06050907050a0f05070206180a0b04151211070b1e0a06061b02030712031106090c 75
    0x24035886041940d5080c41c40d600580701500100350407440e03480207000e20140406c0ea81c41280104007407201e12316615003090300102560301a0080d20700c16504040046142c0c2d205104410540326500c0d407151a6440d004040008411801c404a9100901c4a04000700303440030042c1c0401481202129a242c0c140b610410525038030306641041c8840c500001007024950002e031684000c0e40a08200c4d07a41c0e41c03450000c40c05800c0302d402c06900490303414240418a82e02200610349070000b80e56010314400440e101b140c442c45001e00180d4003550030700135502d4910820355078a140c5d14005002000b025178800703c41d034058119a0085002c144072608045503640c20603100c0103c0c0618041c1007000c2c9001c058102c68a000d9203c2c0900650050740004002055031404500b00070111300c0d00c800346140807244403021701034074010800001c400001400d000c03084090221105030b0700801a01c03000f0f00303260016900c0c9070302d8074058041103241d00c42c2400045084c020341d401361507200e014140c000700c814180301c803 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 235925116 1250 235923866 235923889
    0x80a0b1b0d05180f0304063e0d110307080a0513060203040603060e01050d080a020327010e1801030305090a0909060f0c080f0408090607060e070321020c06030a1d010605 74
    0x944e802180032031141c103501108840540b611401d040c885807210f0b6504480080812005030364803030700d603692000d203c5e42d0329003840a00d95904044480d8403d10510880d51000a41c0c50510540d00621043c0c0c000341804003e8883d543d40341c5410703414081541c0240b01c101166505c6000940c000050a100717181e030500514018006500000311994540360115043e030101c003a000e0140003000c02d01804a510a004031141c180544c0311501d07402c0c3e03e80702c07900c180e103c1540b2a1800b1407814865034086050003000c02031812075042c510742d80c0368659102502c1c19480034100b940e0141c600200841c0b0401c0078407d1802241c05484005218018130b0501806c03100580350780c005000340e25013000081c4410440207903102d03038032482413510b0f0910200030032124010350034010801c80c14403448100d504400a10a801c407401842540a521a185204a07986503e80035001c016004038106030307540c0c10f02900540e00100051000644004407429204600761000c440da4150b9450f00c4e4100440c0c913100030000e0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 235926366 1250 235925116 235925161
    0x121915060806010b0c030403050a08040519050609090a0e1002130618182003090d081e04020a0902211014040506010315090b04050a06080a0b1b0d05 65
    0x200c1e003807484040c0c2e24101403113100c86030707040003945e507107000400e005030340007540d203c07007100d103110202e2620355502d401a0241c1401805010802c00700e8074800712040003101c002500700780c60150b44100380804c0c04001031410400c0b98a4441844001d4000c02c031054a0b0700c968080140c4070864040028106059540f14004103ca40d181d0100d511003614000c9040701c184280c900341c01d140398010280030307240c50361a40b8a4680700c1107811318903402450003540f01b0314030b800c00d981040740700080c10744d1060800d172602d0002d00c482003415005002e84c2014250414002041040c13003a50300c21024040c0c0e03010a40982d9100034042801868204610300700b900420201d6414020604045c890070040c2071014900748129120b10204910381d010fa4008412010b2034030b144e511050702c07800c00d08040d0190508840c0501c2c0b4040006d00d503031100c0d108110554442d14050b014120840c1c0b01c50100030f0024091161640c03d080340c041503213404070b0046c03400010600d804102c62402c0013030641001b40e00440074 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 235927616 1250 235926366 235926371
    0x16090e010e0a020306010e09120f04171501180e0607020d0f17070e010c1b051003050402090402010c03021203041a0c2a0c0406142b02040b121915 64
    0x180c0c0c0204100303047d654820740000003a503880541911704030050b10408444400000c1d42400c030101c80c40107006640751203092020701c0016a0405994207001030074100fa2952101c0103104d02c00750500000c2d489294280040b0351450659410350409000785d4a000140c0d200900d00645070f40c20aa24084801107420148520000a02c849942d107000800c0c410400000c030442d108268000d21401440a41000b54600341d40c240c06508540c0d94810700030b40d0311541d121003d16142c144280900c900c1250b010f401d0b030000e034481780c0c015a00a0710000080307065009940c1080e80d8900d40304040e45c86140121941000c0e02000680a244444060042c0340362400400400300145592014042d0820786414090300202060586505040d00b506580d43e000c0d04000300040c654041180400820104503032150220446016048440720701d150400c0d030720b10014107544050310f010b40c4480c25044010b040c40300e0b5100001061800c1c82c1d104c0c0c904c00d41c0f02c1d03180300c1d110044c0842c3c650f030062001d0404804 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 235928866 1250 235927616 235927633
    0x603020613091d0615011b0f1103030c0a0f03140d05040606050402190e120f0c040605011107031113050103050f0c0901050a03020d0807081c15030b0f0916090e010e 72
    0x31030304e60364001d10400c000c9540d8a102e04a59100c0d075480c8200700381144003001c603440507150081044440010642d001580f0b1641c1442610340030040310715100700e540040c110f0724610740da281c10064900d0803c1c0e05110611040b81110710155004041c210084c080004081c5482c0c81c08100302e0b8115000240541c1c81444408001c4580c40c0006280d0402d40c241000c001c0c0005000941d000a004001c0c40c003070040f0104180281070001e01002110801c88040c003102d611500115485031040c0f4041c60240c0c030201e0b0400100b44c800000c1e14010303c2c06400301d495a0f28503403c3c0740554600b80d004540301c0c0c2c000e95926210361300c280802000003038111030900c400d514200c00280c0b0301c20180030191051145020010421180c2070446d8102e66001080a880d6a07200e0303505541219003410051907a420550038880c000c1048014100340c036441000d07000240c6540d10400102a4000c200405502c01c2050300e180a0444600d0f80004080d480310100700e0b41c5603900301c4e07400e4907010b440240c2c950340103d80 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 235930116 1250 235928866 235928921
    0xf0d03050c03220203101508060403021c020111070b01031a01360e0a140f0d031e0f05012606070806010207091a10020309030703080c01060302061309 66
    0x4890f0802d0201034000044401c0301e0800032128640c400c000e43c03602c1140c00d0083d580c49607421100c1c54001c894210ba200d42d6807040110784803501210000c0040e044421010a014401ca8107c618452944000543d0030360040a00c1d656600c019003c2c3c0f00c2500b1580104200901840080941280a408607909516015614840d0103914036010f0082c00501c0c0e440c0c4844010300080d002c00c0d959a4402e0105141d01c062245e04d8900c807503010360301b403035448800e02c90700d50000890911200382c0781c0080000740d8240500b100104540626488005040c0d00d001c5442d11880c0510f11003802255400543c0b940340510706c0450078043c9841c242c034003404001c3c0f403001302001b0400b20360040040c00c0221160780c52a0040781002003076040086143e00e042590f150400c045200f03140410b100392030049aa059160084c4c2e524021071003080c0d41907004400601c009084000a407808060010003c91100e88950015101d9001403006c0180184c807030f0020032005d0858020082246404080200460720894 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 235931366 1250 235930116 235930141
    0x40306050c1303031103090d1a0708040305030109090807060c0906030c020109081e040b0d0504020f01032a0909111818011406190f02060a1a12070f03050f0d0305 71
    0x31001d014007040305032105c14040d050046400d080740040c00c503c1950124a07010b0f150451486405007801c8000b4001289540204075a0703020303d4054541c281981c1c40c0c54603e001401e80706000315035a03c0180311600c0019118040d20581d400d07903071218060207007400d40003002ca4090002c00030440e2704054078403001c80c204400f00c880800d44172074507440000c8481c120f11541d00c51b607805141081c0300094143c0c101c01295100501480c8200da5001c6001d1280c001101521003071486000710301400303a00803c071711003038401004862060b4149985001e5651036184200c070510740c50000b103c040040d01071031304901112098811b0000320740d00040c02d40b00d900c010102050502401c03003180e078526400360403a0f481c18160f0326030031028006208805103030540185044104c681a002502c01d02c004140d07058420301811444074840740214a203080c0f9141041004243e03d40c240c400d40c02140c00101e90310000301c1490014500920060055440e4400101d02d00815030680b2801c041c80c0500703014601c004403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 235932616 1250 235931366 235931369
    0x60a0f090b040e03070507150503013503030a0e070902031e040309030b0112060b030705060d0f20120c030105011d01020c041d0c040b090f070903051002040306050c13 73
    0x41000186481d101804900280500b82d40c014451101081001c2000703400220041625680c00c2c14032100800030707034140d0ba5408280140001c0030700700f41c0c600d0075001d190075124100d007441400e4121074020300c021031811035100b528420f403240d8450070724451009040018400410780070404501c0c40c035140381400c020125261440000421300c001140c02d05120b0300041001d0b5800030018070841d607660710440c40d00d80615404445c81c030300701040100240340c007080d150211100602041e1801c200c0f08241001421040028000b01d46c2e00c03c016038240069064000c2c81e181e040b100c2c15500c031030302c10303040324043c0c0d00a080141140c401c1005100313070790b80302052402906c842c2c1c080c40e01504a400050b800d00011103041508549041141e9042a181c03200b0303d00c48070252012ba581c0383d980181800140c64540c482c240c0c000030b80d2030104807040aa2010715030303c050f0a18040080b1910b0303550303090601410130100c08130300e40c0114040c0701780701491080300c0e000122403508600d0312645c20403c0d161013025 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 235933866 1250 235932616 235932629
    0x605010e0a060e160c14060f0f011403070510030207080f07030315080c060307050708030f06010e06070b0f13020a090504020901050f2206082e090b041203090b04060c08060a0f 77
    0x303810305d2808200811703000749000c400342c40545900d4503084035420088002115038034501d951041c0001074a130342848105041038005000703400058100420f00c040005451042000c00d03070708204030f0020130320a90203400c200712074000950b502c01160400034140d400032520f4096516030300760200244000040d040c203040b2801c1e20010707100d0b90345880594040c0a01c3d10f01900a030000420440d02c41a986441303486158240c1355840e00002030800c0c0170031401403440c01040e50008001080b4110030401d0402e034480300442d11210444440d60211381c0429180d80002c03401ca480350140700c11440c00c03000e1580505000d58a80129484d842c0006800d444c9040755185101d03a0500c449915070903d8001d4409007481000300d40300c5889803041054a41c0d031101d0032041403a49103845c07010031460b80c020118160f800c03400301100ea8580d40c50314201422003010391414180da41e03038444d0006005140d081c0c0b050340a5100050201003000c4040c00054008004911500703000d00148250340e1f64103148002d485d0f0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 235935116 1250 235933866 235933877
    0x10f05060604031e14060610020d020d0e0a09060e0414011b1d040c0c03030609061427040303060e0601020d0f1101090506090313060504050a140d0605010e0a060e16 72
    0x4c940c0740340c0482c5070030b200f40900710f503143c0801e01e4500140040c0050060806036408119041c0c5042d0490719003030640c0502e00160071418030404954401c041c8100000da0080c241000c459480301a54111100c9921001594400034104330610040c0084043e2080d0f41c0b00090102d1420b14001c405141048000308091210549000c140c500b640c1ca00703030140c4040a0800c00c00c0020107203002d444140903c008400003400c1c200042108480c0b0700074441195510804419030601001c20844081100e00a450f4490840b0724018820312190030034274001c82c00b0740c50018109080c100d9881d102d14000300582e055510240d491100700d54007000c200c000030801d1504030804040c40701d40501600e0701e890098103c0c8142d4043c040142000b2006000b604c01205907e001c80340d86200543e03850050340719455000c0c0780703444200034201100c0f01003400c0c95170052940e40480710f00e0303136184115102038200c140012191010001442030500c1500081c01c2c02d80260011b80c074015010b0f040400412005408015 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 235936366 1250 235935116 235935143
    0xf03070f030e060c0315010c0b070804020102030f031501030c05031e09010207020d060c1b0c06050a0e030610031b03020607080703020f0604060b0f060a1d030c0d03080108010f0506060403 82
    0x5110b54003490032003003a0429202542050340e820000741d0019146581e0341c80380c0c00046261580140d40b20400554009030840c2e1035500c05505a90724200240240c0c10341c0010002ca460003040c1c0d4004603c80c0700c40d885038480500d9520300060865074403848c1d180c03d0007020401d00501618a00e145aa0b4400101c0310180300d50b240304880d0701a00513008000d411814064800c010494540c01202e800c21702a038030500c00c42211030081e003800104840117000b1501792001800064418002403040190034103109810700e601c040130030f10f400d808451040c41c0a4180b0024410024200c0302107103126000315001ca0641c2c2190001445886010402400c1d584001100d204140c000c1c084842c810000c00180c03506464a42401005000d2440380c0d24811151030700740e620f06142c69405c0d20011840c0c0c0d0b031060706928411030035400e00e0135111a41c691610902144142a07a50b400300c20040340d1087c0c0e620100e95140100c80d900b9100d001051003103072820002003202940f1900700342c0d02265003040c240723481e40307 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 235937616 1250 235936366 235936397
    0x2303030f04090501050910030f14070f080303091203073c09141e01030e0705091e0a0509150a0209060331110103150801060806070210020f0307 63
    0x6104654015603100030100d000155880c950b84050304885080d10103070307080c0c0d5170403001980c0101c01d804000c04030034684103850086507090801451400b104002c55442030b859206200f1006121b60186170b06600003c10401001e5080c01a415810341c1202c803142181000e08029104446101303400410300202e56038400341c4241e03018040004216143c8e503c0179040b181400411151442c05620606402c0d20102a982e0402c14514070400c08500b00943d08800d1603001100500000350800500c0e11030041c0206482e82c80a034154000c41001c5151041405841d1203410022002403401d07040a2600040000c2e20704003107262026204114000e04141d56021100c000a0003142c10041d000320380402080540b01d1000845484018040281c1e04040248150300c094030706100401081d850382c0010b000007550081d004038a00b0240d1443d160320f090780fa10501402c4412640c8030050640c070000c1400341d00d036018042840041c0800324103501e030001003680071b0107900c0050445c100b04031a43d00c0c5c11119 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 235938866 1250 235937616 235937623
    0x1824030a060f05220c05010509032103091504080403020622030303020403020909030310090e030d020304061407050a0807140f0a0201090b06121203090c10090806060a2303 75
    0x2025403008041000c1040324503142d00811040f614640c1c0007070f0014140c1c0a400d003a4000c0494540e12810b06085a414a0700441d100d401c00100c2581502c112010f5013010500d800002c260307402d880044a482c1c1c54142c2e017070b602e080900b508150360740072140280004195610704890640b50142c54080c0c0e91000c1543e103e0362119018802503a282c4403e2010040550513001172040360b000312100c5d40b1680750036070065140d110030740d4a8845117a000000b0819141607412040c00b0400b10300c00d480c245100d2a1104c0166403040b10304840c02c5076216030584030210b0b41c41c5441e0708110300b40781583c20320808203c0900f015502510100c1809650b54660115062150440d07082e04a0a1080c0b51180b408070006800f030f000c140c2c8100d603884008030024059051040c60400c0101441d001003415030080106c40340c4c19440503048001034000d640c2141c1b05510744207a40b800d0580c0c84c0d030701c40000b58070b030034010b42c1820000391015108100c2d511080190b2029600f0a100d06c604060502c0a08802031000a18 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 235940116 1250 235938866 235938883
    0x2901050f0d050d05040306110903100e01020405030a14010f020c121305060f0a020c010509150304050304030803090a050f01090b070e1315080c040b03031c0b0402040306020306182403 80
    0x1180304a185000b8100c0d4044c000c2c000301c0348116000d204213061302028982071300039040c4242e010b51058031010030000494104600d001e481c80700051809860f400842d0811805040c1074525802c0444440701e10748091080a41c41e0031005811800c1c500c01ca4036070b42e02d0b10320380d40d141d0403c02d1020400d0140384441c3d24600c0c00520700180b003160745107000c03030043c0c0f4250002001400540560b0010080d1940101d040b030b019644020030003144c50181600010031600003400035610340c4002c0c000031000070103510040d80030b000d010000348000b050074030b0154501075480403030240300d034100304002c00010307051420305404c0072080c200030300c1061f481d0000c19503100e014866580d486003000040c1d410b22499a00b180d040d546190295481d450420041c402550000d00456405a00c200301c240c0742d0324002e1450581d00e0300520008608150b07400001401e07604035410590b00d1a0f4000144002c1c0c0c0b400030b501c1c10301c04200407d06500381c03500460003190441c941d0a400c00c80105209490b00340d0317805010560 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 235941366 1250 235940116 235940123
    0x30d05030c0421060b0103050903040612060b070303140106052a0f01090b1614030103080310080706030f060e0910110702030601080703020f01020601080c012001182901050f0d 77
    0x20000c03ca00070359888441100f80c3c0c1036506a2a0610201ea19403007802000d00c145454001949854a0b02d04200c600d0082034210115590b03480d10b01040103c404c00040040e13500075a0b02007507480c0c0381072030400307000c0060b40300070280705007045003140500b240403e1341048900e00e29000c046000d003007007050802140074071002282d440c0200550400006040700e0340542801c40320303803042240000b0241e8030003c0d001003089103428180010000148128021340c3c0c05044017070b00141540d903500045250200e95042a0042a00e07424501400c0e44a48a208010301000f034003900345042c1441c615850700c22800c801d9034400c2c0c507241b4110420080c03100300c0d281164042d04585880d81d42c3c03890fa546035411070004038860b09524100881941c4001100341c161001342c4041e190305c5451800540b02d41e030901043d48221115501d800344440405c0c0b05103524031004c8120250103140382d16003680105c0554031500c07170700c3d9040340c1011443c00c82e011a03141075480c00e5030154540314030500020070440310100c009 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 235942616 1250 235941366 235941389
    0xf0510051c1a010504180b0315040602250f02010c080f0403050f06011502190201021005040302010b1014070303050a1103010f06080a020405090f060117010b180906030d05030c04 78
    0x4100c01d000a5000b200e441000c6141d607840e000716240115400c1c843c521550000d0b200c080c1c1905c4070b694041d0300402c1d2545000301199810200100d00700303e0020100d9040c1c0308550f02081c42080d0000f10302c0201c4001507c0300b51500d50410541e40c10700604040303140a410002a02c40c032204200d00a021980c80301221500c2c207454507a00c1c9081e81d03440404c05244001e5006d90000095094050062881801c07881d80240c141800d000f11046140220380800703a04500c110f064902e0268402d205050103180213900102c0c00f54425418000c2c01e501c0f80702250100b11100340c1b00d00030342d8001e03c01d4ae400d265041c5800315980e1103043c48031024120010f07800049500010000503015003611142c001c684082d00d4a8042daa42e110b81401203002e640329868005804a002441c070002e0b4105140d4048014107050903010540001600401801d0304844510030380043e040341c074240001001000d820048801125034a002004039407940c54409840c000d006001c00800e50702004801a64003030881e44144 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 235943866 1250 235942616 235942657
    0x120602130f090f06083403120507060b01020c0105041a07080c160b0304020603060103020903030d050106110c030303360313030b090c0a0311240d150f051005 69
    0x2410050240f03490f1442054079001000400c60004141640a802c48060411043c2c0c5441c00e004044521a82d95022442c00540040700060140b00303106034841720340c0e035410380310070240c6401000c40301c05040c200c1c19980544221165603038440e0840301070b5891807010140c00414000962a28020000e00400384034004c105110a04400240900b003900154107820a0540d01c164a208070310050307030302a4003c0c07801c000040c2c60354000e070000d104004001d01200d00c0d0507481550001207801c213030000c80014815510500c82c03138504000c06001e80c50110051441d606201406000c001600baa0049410398455140b041070b41a210030341d60807004100c11350360740e404444081e100501150100b158081d80c000c020039132501000075459090100681030030900c6081d038071842d0348090211205584816100c00b030021701040246002c0c140c6185103040ea890782c034043c0f121001d49440e0f0f0161003d80318800000c00039224000c41c2034007250350554040707811080b1450300300c54610560b214400003c1e0008603 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 235945116 1250 235943866 235943879
    0x9051005090606010c0c06030507090e0a330302120a0f06020c07060f02060402090415060605180102030901141e220905060105092e0f020f0601120602130f 68
    0x2203032180301d01c102074540c1c954403640107403800301c809900a80400d400e480d007840040d010b03034031080e000810307424103900c5540c2da60b5002070403440c21200000b042c0d44503801c0441d40803074030b242906070a900c41c0144464250000c400602c4095910019129103054038040340302c0202404022289034001d103800314031400501702036020b5440601407907010321450300c0c00900240b0800b003400700c8000503406030400c6e0b2501e400700012403c01030300c00d8812807501c01108042c1001c6100321401040581c403115141d20740c01c10000b4a03003104809517810b5420030401605181e81c440584680e0360b10712011640c580394400f4000e5800c03c140d85104200076000264403800c500c100f548100c100504080700030801c1d444078a07000a480c1c050351201c0c04507000303002e420341da884d02e05108040441c0000d00000070481c3c892700c03d04510804000000481e1034240c03148000e42e03041c000c071142c916207070006000315450145002610742d07040002520060f40400c1420501e030001410200034100f00040e4844141c8848 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 235946366 1250 235945116 235945121
    0x804030b0f100b1303062d060509010e01030c060c08222112030903140d020301030312090c03030e010c051b010f021513080f030a02030a0c021902060a0201090510 71
    0x1c40c440c04000c00c4a2000a10044000c100c1c0c2d5246441307000302d0251403560b82d5410280500384258500c0c5105080d850341d420ba0131900d860f1103001240008a5070515190500c0602d1034103030040070849080d4001840030480c425583c004483c11807070224400b91a50a02200f14010407817221658072441c0811910703454100c2f4403c058401240c1524058080082c3c40340880881c60401441e042003100d15000d198044e0740460a01c60082c144581ca561100ca124426607001c1010f0f07108099000c401401071542c8090810b4030350003000c0c4104850949601e42d500051031920004080000c40c216580716a40b2403618040c0303066102040703a000350050a071a100440c0d5101c90340b40012101c203503801503684005040100610741416504003916a425070821100840c074042d50200001c100780c40c406080580150302c04e4800410050f10707810140102d50642d5080c4030210b0440d40810441c8503030b205003844100c0b0b402d5044410769680d44900c2020b9000d031241c02005130040c000c0c00d0003110401203d4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 235947616 1250 235946366 235946371
    0x7020723040605041e05060f030708030301240e06130b03090f19020108060d170d0207060c030908090d1704080c030105060a06050a080a0b0a030501090302060705090f0d0804030b0f 79
    0x301d03400e108590316031080c40304030b400e0121200f180c0120b1128813000d031001030740301a82116015000d041200101c202091411116501040c1158400001000703050312003c42610032405e0034030034105408103440010503040000714680c2c401c1d42c000629400040000c0311007002026145446622840c02d02c00c0a515240d840c0ba100c041c0d405660314640030b13600d1803500d520915505841e0225180c40e441c0034006108400c04044882d044002e0348001c08584000c00703400303200c1da10107000da41d0718000e02e005c030b044e20259a0304000b49810144440005121070082d2251820140c40c91801c46443c0d061807461001c00c01c502c40c540e004d0000c4c020404041c00301e40420940340a074001d000580712541448003070b845034416400065400c0c060307030f8110b0740329030074858021001c1300f03000c640160442c0000704039116aa1048400c2ea40d100840310405405100c000d41c800d0042c1003803030500b620342001c1104c861444218a114580c180318103010406486c081d20080c0d9001000e170616403134800314030155404103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 235948866 1250 235947616 235947619
    0x606021005061504060809010905010e0609070501080f062205070c0215031302010507290601030507030b09060f240702030f0d0e210a0b0a060602010e0c010807020723 73
    0x7804001805401c00f00341ca0641d40743c0525902d031030107103050740403174681e00c007c0c240908a540700c240510101c0c0302406000080d001420150519045c400c0b031091a11005d42d010070306214100f03080010001d03202040582c0481c0958400c0e15400ca00d2800d01c0300c404080c0f20ba280003505c0d21342070220340c1c0c5d84158005036007842603c0030180e01e658607010f06400d0100322a600b0004100004200043d403051016100c058415603050340c50710301500c480b415800240c2600389160720900c00b0044150b81c5400750b140c000403181810011010010003041e00540b004090f68000d004240b1500b90f84d454201c20300606207408074035010ba403217840c003035400e0f6076000f02c44c240d00c280301700481d00d030200802103584012442c00340ca40d904000041c000b4003502c1038403d82415100706940008440254040c412080c01501c900b605840e6071821444007002c54585410034803c40e0700d0030f00d184c4588000091080320707a00c02405c1914480d540c000c0200d01d00180c1e40c0060940188403000860304040509124484a00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 235950116 1250 235948866 235948871
    0xa2301140f01030b0a03020f01050d0212250c0b091203010801020901090e010f03061802041404031128060615030c020111030c180f040e03071b0617060406050406060210 74
    0x5001c00440c02d03074034070710700c0303140e001c1d0420748208014505a4004414520103060980c05d00c0c1c007505d40c1100300e80250b15038103c0010540c00308101302507510146440115070503500024500038403002000d0b0307004008010300c1d480c584804510809003c00000f40c00c6900071207220345d29070b11411918081d4011154040c0400ca00c000085508407040c00e910741a5104039403076244941c903540707a060103001e108480d0700c9039402d15920200580c41d01c0c0070305604024440030b54007181c2401c0c036000340300400c3c0e6800d03c80d040c0c105018140804404000c801c004070410030103021081402e040040040009900548106202c1e510000b0b2240d0940c04c10081001c032500200b005601c0c50b10351140500c001c0f00c0660070680e0402c40c07458882c98503c0030303142080c0041d1004019101e40008107084a0703001403201055880801e4030410803001031001c140100d804559039800ea45000c3e405400c0401e00740740c0d03070420340403072000980c2610345601602c001c010040050001c00d680f04400f940b1001c0b50142e09086a0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 235951366 1250 235950116 235950139
    0x1f090503070504020403150f060b0304110a0506090f010302031905090604120509060d02161e14030405092d07030903020c0306012403060b04080715020d05030a230114 73
    0x70f86032085e10300712604891040c6071031810205400c000e00682d0401c17a51503036505000704044c0c06440c0a0740c0300728852790701884048050f2003003052111075076001e5449480b00300f09840164442032030440500b9000e00380503890b600c488404581c002d500398021f40d2447d161108000c007504000031340ca40a580544044030080900305422038180c42442030700740d007015080296008494403a80100700c400840c10700c3c220324001c0c6a64400108400c050300424100c2c6203880e60302031005541d0040c01c1c1c0d0704020011860146020040307041048000c04d10300040802c0803488244916461444942034001000341200b0700d031090001c0c004281e00b00c010340047c429040140124140000c549040e10100c0b4071051000d030101ca6402d44100300000450101a111000040e28080d071201400141c000d800c0505040e50400c0d91030b030070f559171035180c1500b158020101c48024540043c1202d42114049002182101c0e0f565000184829201810404420403100000720721007107a02103a2400e030119400450328 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 235952616 1250 235951366 235951369
    0x20d052d0a020603090102070b0f0106090f050a030b27033406111b150f0f06040203040204020705030a0807110304030c0e061c030c11010921021f0905030705 69
    0x9000340845120340c000c10400002d498080701440d071015003480007620303002c0560356108180005465845c401d640c0940148101d58121691401420b1803600c0c12540038500000100d040146110144c40c209030000400e01228142c07048174401c0a210a0441e2090244880f1a030389070320818010903c1400307260025035400810501d064208c242c0e104e040d07040d825680716207004007801c61422100100401507810f444000400b01001c145025000d4109a180c0c03520034070405400130b0855582c468100c0411680344103041c002504000b00380c400503165652880460028400c3c2c132006401440b01094040308554000c8995224035002d5a030030358650b039880c00c1c2e207a8074055404000c11402580c40c05102d0421035154555200300002c0c003a00200140c0007e0380740100c0c582034164001140d0a1101d002d0100d80c280c10121400c4c203182c00100315150080c01e214810542142d694815550503004040d0741d40c074802900c0703820300f290205440c41400d8002070185411803084600a004103a800241d6 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 235953866 1250 235952616 235952683
    0x40501090b03061801020c0a0c0302090109020903030706020d02070c090f0e010c140706110a090303090b070c060f031d071404020313140307050d03060905090d1b030c020d05 76
    0x507003400b4005118903221868200e1558602d20906aa15907080c001d0303659141c4100310720500e81c0d018980c03495800f070840c014000801c2050f0060070466004200c480e01944000044600b01a040200141c0f83e8a04a502c00003a200d0803034068803003642900007060000309948101c6445048110030480c0030241c11701da40c261441d10800c0804910f4500b42d0007a1100502c2c02090f600d0320441d00041c1e00c204000000340c91307421000c03003c17000a4481c101801016000f0400c0d0000d01045088a400d044959850070000e074080e0044808004d49030020001c1c59000e600044950042284403100083c0107110b1581c0d50801c0b441072580002c014144204142410b00c201c038050712a040f0390302c03860348051320b271a41c40f03184030a00a025840304100110200d001404001040c0515507008940c4030320709008202034a01c003402040c103d0308180403004a0907080841d003102900382d564406200708917400c5c140c031908007172080a0b40200b60011004100180443c8040c1080540c00e0860000006c940c03c1250 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 235955116 1250 235953866 235953881
    0xa030507170702190f020409030509100c05060604020a0201020c01060b19030605090c030907080f15060105090907120f060e010e0c040b040315092a0602161505070215040504050109 79
    0x544c00c18003041c1c0303001d42656580c000c8a4000d85085001190f07640c04a0122340303801105900045001c25040311625014480c0144100c003483d021101c4100c6898082d15104042e0200384070366800500e102202c1e00130740640d6108140360008004103640d45841d04219030101c1112041c1d0b90f5803c0c6072050340c1d0700921500b41074800290160b1000e41c0c1e03440c0120015400588051f50300c0c0f040d60360004540e902041000f540b0b29180d409082d02560f80d455040341c0170405804541446428400141181c6951400503404804c624118644461500400009101075450914003505015000c20f44c100b080c00e200e4101c07404507402034019035810300b00b042c5038041c1c0d01842555040803c010000325008602200d001c0458030030008041280e695904811000d40e105003540d5410224002110701d1004076000c01003c603800549160b4101c00d459803036940c054018140003410b840c00c0c03100c01500c514251140c0b194050500009168444445403080d04a4494203219604000021510714003501650340d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 235956366 1250 235955116 235955131
    0x130606021002070203190c050f0603070e040f1b05030f1620031b160806090a02041d0604080d051e01091d070b04210c0302010c030909020a03050717 65
    0x880c1c90095a80e00c0040e501c208001c0e68140320b246030b9800b00f4050590b00000e058410541032940c58507200910900d9000440c80302d1080340280100290250401888480c03500101e800140704080015500010b00f2121050303802c80750701580038a00b8641080042d80298400441e90145a41d01c8910302c1c1c0c0c003042c1407454000140e40d2103202021080e01c4061044c0440c09400f501d042400140080c035030340000d003400c02402c2c0d20138004185006400c40340c900140c080c00001c3c10741ea2501c220101e580d51000c03031009026640d074210015804000c20030402992071290b0135580039042034148621143c0100c0300850015103000d0104030700716603e8101398680780030800d907003030a6860b000da40d500420460084c4281c1d512030316181c40d102c0c481070000c440540010b910701600c80d42020f20704118807040040c05089400a032282c1c10105204503601d00407030ba07091802ca490041d803481c084a4042403644603501903400070a80a04440c0c06030030052003518103607178001e480500c089000c07601d40001d48242 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 235957616 1250 235956366 235956373
    0x62c07080f0c01051305040c05040302010f02070e0c0a0e09090a03020d0c03080f07020c032e09081209030d09050a02181902030c0f0f1305032406011101090506010513060602 76
    0x50b400f54081c40103003060a2980074280c0d600c5a480011500303595040c1d50103400164006000c3c8219a0000c0006003582141e100a00c100f5040004c041d800c1000a0600948040040b41104055102d8040b10301d4103031001c0c1c4105550b00f002e400d11a510407a000d412405802255035101a4903c110003080d80300d60981c0e00d002d0350352110302c000e00c65421b0140181e0110f0145202c161050f44080045a80e0508009020030702c1025928406810b00c80c001c1c990626141450980004a980300c01900d881008025020b4102e4440441051440c07155000101c0004d061107004400d0100100d041803407a4000d4840c0260711280d00c039840c04138402140c11100c00c10100f41d00304a0003030180d01459000c14203241040c40c118150040000766001142075242511001550b0034142e2614040700000384420340080100017401c0d44404100f141600038101a240c139000000e281d6031207482840440008075000300a40c01207824242c1e100c00f000d01030039006031242504e001010020b0311450046604541c041d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 235958866 1250 235957616 235957633
    0x3120a06151409011b12090503010606050d0b0105040e01090b010201181203090813030507140f1e060702040204180b010f020d20060705040f090b010e010309062c07080f 74
    0x501d0250482c3d4000350401032015001550304c0c1208402d02d14090042e1050102c514284000509042c403942125000341d04120080041d0303900101a07a050000b46d50010510500c0c2200480d003038050350744603c988160441c00024000000d5000e0b50502c04281e00910041c9000c0381e0003d20403100030300042144521403403650040d4840c2d8062020035205849862804604206e0345040e0f01c40b0750010f86a5810084c010005820b01007510310113903009a9118030200c2c40400081c0b542c020420004200041050321806a507543e40111210140d0007081103448580310000100d45124070646040340314540356070b00f00198010030802000d80c0b107a030700510303503004802e00c1101d60032005100c540c241e00402030017035642d680a01283e071040b0000e94400b80c07101d02d86910800c141e06181c2c46a00f100b8a13060032006682d81c00080c2d810b1213003003801d021410354614580b210007400d64034054030b10456440c03403450f403d40849404002203440d000445414984420049440702744941003c55186d00c003184 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 235960116 1250 235958866 235958897
    0xc03040204091511040608090712200406270e0601090b040f0204060804030f540f0f0b07060c02030409060e0402040606030c0c020f060c03120a0615 65
    0x10b64402c0c1c0c460b0402e080c00300505034110f4191402100d0108500300d01240a002c056840b007105680242014000d01c0c0152405904000740c02e1400005000700c401800e4010120702c0b2140d221030845400781040160355901d20302d080214400f403000b4402169142040902d1030300c0d6000c2c5102541c060310282c07a1507460300d02000c2c0100030790310109400689446180003002c14a2000d00007e20703554440440300d01d884c0c68000d2000c0198520741c4140074244c0715414500202c4a40d41c5058001070266070f00c81d100800142040e000d00c1c40d400003103170785880b030102c148400b600c0c4168201d411a640ca00e418603111050808400c080e030041140300c0f80280041000700344a40c01c4621449160b0056901e0680c83d03061020688031a90001205d90f0594000d01c01181410b101e10700080c070007441d0802600d4243c0500401c15090307000040d1003402c54507405122962240210f4041107511000c42c0e9843c05458101c1902d04801c841c0748001c146402030000d4403081c800361803000b8000c1956204025141c1c0349 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 235961366 1250 235960116 235960121
    0x1060311030c13180f050c03070506070c060c08070f03020f010b061606020f12010e040314090906090910060906031109040201050a0305150d030e041a010903031d03120703080f0c03040204 82
    0x72184e40380400e010010400b242e012800d02ca1101d0081000e01100140e00060500d0b01c1c61b1035200341d01031101003140c4008101c1091341e00080d40c2d514640000c05480d00d0030503a40d41d020b0301d28003614840b0540d024100301a00040c90080e92a0020000e00141c0c18034402c01215000c6e01410150424901150710700250059000b01418400034500500341000003818410112090b00444c60203140103007880140740e0080480c5c0c6c0c84030045004540740050b4032010464800c0041c181e1401910114040b50444005001050368015014000c03c813240c0d8422a4401070012840140c50868880d404c1c02441e040c0204450f06c10b54060315043d2034107600ea00d040340200300003040082c840340302d400031100c00d965407001d07041e100e800380d540c0c0350280710030b8000c10007100c054220320242d00e08101034001c5143d8000d1800421a900f600b0700038070720190416000030107840c90421b03580c075000e10749504030760720081006884c4071130180d5509a03090381c80880e403143d4028182c6000724910400e000040052901d034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 235962616 1250 235961366 235961381
    0x8070b03090f010c050307020610050a260d170a050405031c060504050408041707030c06120207021002060f010611062403070e01090c020102030f060609031e01060311030c13 76
    0x100304980007984420300c2c9a0840703070b4507507440000a00c000103000401c2c0d0304124042d00210307003118101740d25143c400001c030502581d200d00140c00450010301070b01d419821100407404007250301500d503000c0e50190300514800f0100112071200340b8000c049510f240c524402c1a1149074450015494070121100205a0300070000745c0c03550207911002c01080c40d0b01c4d24021f0b04d008034440d6103416125424112015501d40d4603401004031a4001d00041010490700d102c10707402c0b6181410b02001c0d034004400c10102038807a656001c5c0d0070442d4076010420071a40010f01520498603030040543d26601d0780000c0303903440c1c1c05080c000d10b40d40c02100807030403000105c041d40c01141c4107400441514411000400c0c1804100d51151951195420040096880c0f0740900c3c2c080c030b0894070086203585050440391404400103041c050240e94040303584c40c004c3d00d040144680c80c29444503001030901607401d4450203030900340001c681454000280142905000504203001980141091400b6924203000d60082540 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 235963866 1250 235962616 235962631
    0x507050a060e031c050601091d040314040306090b041b08121b0d03050103021302120a09021c1b050f0609131e14010e040c03110f060d02070506010f08070b03 69
    0x820940c1c018202c0c3c182c800c04ca500950401052a01e40080050310300c4001d544a02c0c0500c2105018200c0b00341108034542c2c1c8654982040c0c062640c940200700c0e610b000325003004208500c0c00e40804280080e68403114030817485181d41c040c9038a401140e410110a00344281d02d032961207081c3d00004074000c07078045e019020340d05450380684a80381c05101c0c0703030084201d02400860b6540c4014000e504002130303442ca41b050b0608055240011070350016000880003001200682d80e102e84c000110360f50b07520500145460026540202d4005061002075032a9403040c0124607041500001502d00b0504004001130a0041169003004134030004c1c440b9241d5902c0050304010796813104444e00c1c60164141c040e01039461240001e100011803151510080e060300240c4210f5003100400000600c074400100a07242c1c415554900c40684401043c0352103009110554814004075900240110680c0038000e0300e030241c0308560039666201d08040c01c040d854001c41856030494030003401803020703004c004c43e0415007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 235965116 1250 235963866 235963873
    0x705030a0f0c1a0906070305090304050913060c0f0e09040b01050111010608010513030206010b0906160c030210111c0219171209070e0606070308070203120906160507050a060e 77
    0x10107503107107048201804010002501404103022500c1310801c1426804442401c0410240c1002c40501c2d0780c900130b52244a1203400d402000400a4150308010300c0d4096004070244120800c00b0310240112501a11500009440d1404c155041c40c095180c0d40c05160046d40307070044e903424030004561603910303102d00d0502c6648901000038005024421944113404518008070800183d2a0080c00c2010603402241e4590040c01511305c25540c401c111052091110000b144888031841c00e80c100c500c1581c0003a40c0825900740c0e00d91603582041c2c0c00703e8256642016200300315070100704c0c05a15404c0f0240706005074804410300c2004d401105049207881d002e50a482c49000d0703003203c1e8101c55842010540342d40c0c3c181005020044074200003d0014041110341c40c6402c0c0f800d9000300f0b81d140140a005801c0120240205240034028401c072441002c2c0c26034010711619004000540e1144161a2529000c00101c100445d0f00c0c880c030240c0e45010f1388a00903040d402000c1e112413026060709201d0140c10b00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 235966366 1250 235965116 235965137
    0x1206060c06110c0a03030e101b0e0307030615090c020a031d130203160806090403050d0908091905011202120a3308010501050f100819020408031e0705030a0f 69
    0x1c03010009104c4a82c80fa55012940d100e0203288541000c17007041c09448203500380317203481c0c8120203080c02c9104185254030b4402102000500080e02d0040700390310207003006103440d2240500081114000d8182c2e000b00700144600951000101c1e40c85042c1d010250010f4810030094210849080f0100207220008102c400e2803000034400204036030050340c5042d200d50105007088660754002141690225084500803400d207410745010b400e034810400180c180030b5135032120200b00009142940c01600700500303030410902840e540104000301c24001c4d140401c0c480c40c0a01c2001a450088400c100d240c6090346e00141c40d5000490041e05108070020504002d0b044a40c2e41082e681078020f0300c9115898200a046281500c3c1d203003100c0040c0c2203075005c0c580e444032101c41034403a44000c1200101c00e1801440c03c1e61051030200341000c0d0084d42c102910300000f80050120400006491541409907601048500340350503001c40f88512030740204641c205006041e1102c0c002e0080c2202e1070f0541c2020346484 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 235967616 1250 235966366 235966387
    0x15070f030e0304081f0e030a020703080a1b0b070315050a12060608240a1b0804030c1202010207140a0507031502040308042709031d01090f0305010b011206060c0611 72
    0x1d642c1204070303280c494a00300b00c00c0c0240c05c40d01880da40390000c840510300e040b03013004009481d078a99020241c07000c00c0001d10030785082d01c100100d600303001d500d00080b10350603c0da2900c0384d01e1a005a81c10f80000381404040d60043c2c032240680022a100141351ba41c00a24107100d2828060401c641500c01e641c0c0c131032001607484030134810300700b22004544200c3e000000003c901880f02ca00a022607004502d82104802a060300000d480880c4166040080b1180d42c0e03481c00b02c49054807640d004054020400d50540d50540540180031210300c5071103000c100ca04e440310700d543d60346910032001e0602c0c0c2c0112410004107051005c0c00501c20b110303440143c1340c203490342c90756a01c9034041d90003151845504005980d032003090748294003007443c0d41d4100744184803940d18000e1000740c06501d4140507404038001d05170503a00543e00180200294921101e10030707540c0c00c100b40206929404540800d02d2001c1d60710008000380320b882d00b81c1d1207036100e104039030000340c581000402c1c0b00d415481100104100e50390301e2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 235968866 1250 235967616 235967623
    0x50115210510150305010513020c1f0e010605031603030c05030d1109043210050d12090f0b0a051b16030c0929061606050915070f030e030408 62
    0x3038814014401040c0c0c540020450f00912140b0604201460400140030300d5441c1c15146c42840500c0e040941ca41e00300d21605414410300c00b90b42e8540713240c020b00010340003686821942000c0c44500080105e10b07a22010b06071202a01c49484010071076070042400028004e4000a840c64000ca040340c0c14424041c0030501212124585d0300e010880c04180c540341440d041c000d01841210003103200c2d80c1d00301617000b03030720304440c0b61210700780e00c20150b02c0001c10b24205007203035000a0030014414101413203141850700840c1ca1000154001030700381c210100710010b1040144040300c00d4a100d16261034030f099803c681e240c0250302c04101559100130b01641d400410000c890311110071000c148290b600d1854a030342480d4041d0300c103075017803400c040c12031070003004401c6045403c805001c802e40c81b200e08800080d04030b1040d11440c01c03415a800c1024000c3c840d5642c002c0f4841c849440480c0c00341440d44c041170358112400c544141c0080e84111808903903078443e030099106640e005044900f0036842d010824207 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 235970116 1250 235968866 235968871
    0x207060b0a1a07022e0c260306010c03030e0102220603020901020d0809070e041218141201090b010b0c0601140d24020d020a23040b03070e09070507020f0102010501152105 75
    0x24446d01d08040a0000005602c981440c03003040c1c1c003501d40c5418001419a020041c01b49040c058a00d040200b80760003600001221954440219525103941c101c0005400e40308081c4c540b00c10788041d0125149000c6e20882d040e0f240c058004000354500b105044440380c10062819200b03010700e1a0000c0c45081050f100750086118183c01c42d43c55501e54401420b0594841149013280b014003410010203e00b440200700c21141501c2030031a101c62000085e0241907511401040080b61310700001e441c800d2840900034502c0c1c40c50684110780d0382d808a0380c03542200d0003115070b4005405130012001074a440100b110201d21f6074060b0074001c80c200c98003c226044800c0c3d54910a8000070701e00013240d03100c0c002ea04201402c09c001110f00c502c14407003850600480c0103002642074000040f901d114050260042045e2000701410401d02d040b00300140145c010040c03c0380510400ca008000c42c3d070042c003600381a070711441c03070186003a41228011112031404400c00081000d80700380300c04407160540242803 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 235971223 1107 235970116 235970209
    0xb180904170c070807140111030703080a0902040f09080a140f190203071e1e0b060906060c01060e0711030708040e06130207060b0a1a0702 61
    0x1034a082802c4c4c0080005100c0c2c0400002c0d1000c1c9090350f0002d00d4001c3e6100c406a00801c040117950703000e4600d000f0081400d020000d41c030104c0310340c482015540010400706600015980100840e040034406035101c140001c0c5032104a41c202c0c103c005142080291203207031035508030030340c20103006104022003011218609a9440391082050302c40082d0801d40320064403080500340c9480380e00510342142c9520714400b03003100b100313680b000c1191a107800604800d46640c801301080403000c4018009507105500303000101c00000f092044101505e01805031003400e040c001d9014000107450607654944d07610800449000034910000e89003116031085100e006034072010300094070840e00f0850b91080c5813020030420700780b0840c1e4115000040055820610183c2c43e401001540e070040001188640c004010b48001810002c00013821401828a00f0302c1a40d4900c60314181a6407181c94103 = true := by decide +kernel

theorem cover : BRFrame.Cov 235791366 235971223 := by
  have h0 := BRFrame.cov_init 235791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 235791366 ≤ n) (h2 : n < 235971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
