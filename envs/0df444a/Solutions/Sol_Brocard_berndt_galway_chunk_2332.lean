-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2332
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:23:42.109022+00:00
-- url     : https://prove2.me/submissions/03ae1ce2-7d5b-4d50-8eac-a225881de3b2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 419244604 ≤ n < 419424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 419245854 1250 419244604 419244611
    0xf2e020708150606070f0218041506060c0209070e09090a0b0a050402010f030b1908011a010503040f060c12020a02030901030c030e030a030902040b04110a020d08130809030106170706030e01 83
    0x6060320070b8a2001d07a005081100c5107a038030b80692411010004042400035001583d02e07160503c0c03165680ca14a2046008400d2100c142e131204d02000f0480f070b02d50048102092006140c20050b040a021450703111501c0c0c2400b44038204000000365800c5000c450031071550b800400c1c270a00304944900101c1d00100350700d406204c2810141d0020b4280e86100d00c001c0105076540409131410703a642c0c0c080303601090001440c00410f41c0c4840c4510301130071034843d0ba0309203010040c605041e40c1d4400c0084a2140d9082030300d15540061071b0b5540d50103066016581c00802c41000500c55a16000f44003c003660300054004603556007940c0b0016060b15117820720035060610381075001d0351029010084a1500c0703002d240002d500c118501c009801082c80550b4035800502c3c0048840c0e800008900500c0d03c064681c08030b80c142c50303c0880c215048107080720840b44504140d03840c0c0000a4021000d03000401001f0b001055480d2568002146014025003e002035030101108208850700352080c42ca000520030007d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 419247104 1250 419245854 419245873
    0x5010b0f0a060302180405010f0503190305040b030901020c03180108090706022113060c0218061c06020c0d0801050a08011b0c020307150e18070e0f2e020708 69
    0x16070007801d148151020706070000b912400b8000500b00001c00f59100600400c070701d50311040b0341d00b402103440c06000d00903c101d24501c400150a0340421881c01d07407550f6000d142c00c1c24461400082c2d01301409019407590284400c0ea821241840506040715500c0c2803a038615038100d00050903248003074000101908400424000207502040500041424a0305185504c8252001d9921032168903802c1e500c0344a00741000c181160310215140740c060003120211038908004100c1503180c00150303003199000e5405c07003e1140c4d080e41071200d201350600400d4010701304a00e1600185c00c00380380380c0c021400142c40000600580c580011103c1c0a0003000c00204849064050244500480c440c1d020061050340100002155402c000c40000703028810804048bd440c035800140a0389100d0f4103c522400800180f100c0c2d081400c0709080c0302c1d000300d0b541c2c445444610780600c074140340c0c042e9409030800480b0040804176030020254001c40c6404865000e826051000c00900b00070b55500011482e4201e03d011 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 419248354 1250 419247104 419247109
    0x4110307171b070b0a0606081006030c1710050913151a03030c03090103110a021b12010e0304090f1b14070606170111040807090221040f05010b0f 64
    0x282811481d00200c884015141c00d0804040c040b0081c080c20012080002e0780c8080114901400303000f054028801e01a1075100c840a5070040c0c4201d864045512501100304000c1d4401c0c0c01094080b41c440c1800c007400b50b080f003440c0407012011602815490540b14042105003894a84d0f15800040c013114503560720055a00d02e1844c200c5031800880c071649030200c507041c0c041c410703034403c00100e00101100d41c1c0740000f01c0140d89941001e119207003c40d2500c0a00400141703c40100c40000c400d550103452031511b0310320003005041140703d48079001691b181c00804990002d208140341503134050b0085441e01e103040c004c40b0544035601c48d1401210700f450780103020403500c070a40391b0321441c0e00e080a0b20700030b12580d0383c4909030280d0075000d44964107200c40010440340f00014071098088100c024805400021025400d51145119500b81d5611400e4200b0051303680b54090314101c24400101c1c40020a90b9040103012001920b084d260001c0c1c40309490100b100902c41c10400705000c1d5403016810036a02c00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 419249604 1250 419248354 419248367
    0x32010b09070918050a0f181a010b190c020a120611070209060d0602070209010f061808030301120303060b031006170103030c020103090302010e0115061d03070b090a08100b04110307 79
    0x800c1010f00c0d4686000c030340d6040c2150002d09a01004c2c01c400c000c0c084058200c0e0182445400c41a85c083c50000711a2480350204404a8166044c4444003441e01c400c0340010188501c81c400d030002004101103c8000580c3c55a032803030f0040154603070040c0b6920303850400c0c00441d040c00403c82d24040d820000800181c0341c100001e0351018003218405c0c1c40c05100d00700f0401a1140d484002d5118000c9130012444880c4d0700c50b00000d5804595488902e000d01e00042c5c0002030362360044410b1640248010812201e0143e15442407078401d00e0041010741c0d6442140c0c240780c1080e5121801c26520b10802e00945520020b11001204070000441555245450141894501030707006410103031a891540c003894000d42006040c5810000200b004050b444503018032800e10780540800039200700800d020034580701c0034001e50440000c2c040c14900b846c11a0f0241c50f54070140120b034001d10144c00000c0e081a0600c1100340001b03a002000c12020104400c00c000c5407041d141c500303640c0d4014414400955880f69 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 419250854 1250 419249604 419249639
    0x30203040f1e152a020a020427080d0e150705030c071b030516050f060703230304020a0f03120e1906170708040302060432010b090709 59
    0x103195001c24620601400030102207032019006040503420b090791400e1a5011407100881101840102240044000b000400d0020003200503881b086040e005498658040c000c8808010840301607400c140e1000c4000100600065518080114270007541d8202030190b81c20850944024001c0c00070b24040a1242d1540600420b04202010001031080030040044540c6e1350341001e0000c1c00e184409204014110380f90000701c6407800741c070804110301405d441251060307840c001c098400c20b561901c00d20442d078100d104103804000c0300014080d00ba500d03480350020b0328040d050549a4074506401840040e40b10740e40614032442110104101056110090b120300f907504d0300e4030035140c001d00000680c05c0c1d9a25404031103c540d8005000650b142c0012004881c4201e8406c0c07070107142c0d2403036070540c0c1c1c4417000c49000e400b68001d08001000511000400313007241940a01c100031148000c4401c03c02806920782d45012030f07660303462000b603a260400e020b03603014182d0301c0d1100f00203040023400a010540c66 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 419252104 1250 419250854 419250863
    0x8011a0a15022107061119121d0601031208040b0c07031101050a060609080105010302010c1506081507081005010e01050c012714060c03060904060902120105070e01030203040f 77
    0x16007166032041d00c2404000d09041003a1000150f940e0182415410766005a00031a9002e207804007000e1460440401d80b02c0007076452140c50b28440341710109441040c5030002443e0381c50b641d40c3c3c490424080f040003090440f12031354001c02c6d0030b41c15407600002c62020026640240030500c820040000e0004007001d6100c6422103050707450f002603150558180c1002282804c06500346005c01007043d11542c0102c0440b00344c3e40e1402445c5666107a21400c80c0d000b8080a4000345070618004080b454140c00c94540c60511003001480ca0b5448016074181301c0500c0e4050b010401c0c507814800e103281c1c85090729070048804860750745030a20380742c0080d081d4800c0c1c10080e41441400300d03006018a400b0740c000c950350a4109242084c8c42d8200308040c120005500044aa0701042d00185100f601c1c00141e00748159008244070f80b42d03441c2e034020480f1010300107008484072519a036039680140c03181c08400c0c41c00c01c010300000c1040e041201000d4403007200d41c41030b00d04144c814003c00010503240c801080c142c07600b2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 419253354 1250 419252104 419252129
    0x609060c110c1f1808010c030606090e040f031403070e0112020a300e06090d081603090f08070f03030b01030e06041709030304170d0f120507110d050408011a0a 70
    0x828406890408020010103244c02c1040c01c0084c500300c0c1034010843c6000103590030040f90742c440e03c0070f0340e005015000302d0520345244800075000501201032006030501904004000024460001d40c0640c421141c45001030380c20a905102941c005000d42a042c245003410f41c180b80b481100101030310110440c0c031050501c680c000b00c0240d01c00c51020008007540581c01e101009065030600d80d29041560b10740c980d442541c1d1000b036902d1103461014001c048460101c00035841100007180504420001900c1d0310510741075810018015034000c0541d14494074812045001d1401d01408545a8000c484d0502d8200100d810000401046556019620590850104c42c01c540101c6040c010644010782510000901190710400807826410001e202021141c1c00002e04204031011020082a040801c002c03409400c0000701580020745c0c00b007080d1402001140d002c0441c0341c83c04120240210209030000342c1800515428000c000740d030020699296240d0303010401203855a600303441900c040c03004d03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 419254604 1250 419253354 419253409
    0xa090911150c1015050102061b131d070e0a05060417160b0417011b050c0111030a0911031902060c01090b100e061207090b0a030609060c110c 62
    0xa03041601d030342c440400300f2102c03e401807919090040142c003940048000742803100081c3c661000966902ca80c40d454260003840e5083c0340f503500c158001c0c00c5802005c0d241074001148134031291045115070041c40b0b01208141c00c19a002600301c142c0b6690083c058404040180810307110502282d08a400181c17070403011400340c032581c5050801905c1c0da240b40d4060310b9800290000c3d008064810f4514200d00151648610001c060883e401444140300320002c2000030300a89000c0c0024160b0000020004030702048581c424101c15801181d4500501c5e40d01c030014424880d091300d54083c145400e900070300c07803285000c03400c81c040c240e8a80001d106031030010325110251020342200c2d91aa51120700300c0311605255242c2d405841d4503005030745001e03040d2000901c05d440d110000248000030320001d0318590342848810005801c4100640340c21000c05880000003401a1007500300050103002d0000b01c0240120005110b9406007100428551100c60844040d42c0e1344044804060030068000c50400b1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 419255854 1250 419254604 419254639
    0xb19050f04060b0d0605010809010203090a02060a1815030c02070e011707120515061e13062315041d040c0e070305150607170d09080c07050a090911 65
    0x24064000004524020070410b119091341d80140703090341c60036210203280e55640f4070081c0c00c071700040301d40c24041c0e80722070700d40340c0503040500051580200303e203480045020507444006101c4140d81c05640d07442850503c004c0855803610030841c0c8480f0320b20142002500c0c00425421014040c0600c203602c4851050354a40704030204080c1d401030410b2400c8041c26011800d040b92a03540328130303c40e400c00088000040c444d1800d003401000801d50b41c1003200e019035211081c81100030300e8504101040e81e640c000802d01c035182119003505244540c255600c148050001d0085440c0305186501c110401817005002500308104002180004001c0194441d42d0740e003401110b60000d6400b0f0315400090310140545258540c2015218504403511901948100001d100c0303039104281020304404030306280300c4003e0b44c400c1e00420726800214008a4000d9141d2a4482c3c42d601294024800d41d1000300d0030001410080b5201c402002018400c001c1e150756612103420b061180945607100d000481c6005484a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 419257104 1250 419255854 419255861
    0x40c030b1014040f140c040f2c150d0f050d0e0d080a0504091103040512030601121802030708031801211e0f09060b1c030f0c120504090b19050f04 64
    0x805041c18103801c503041481d9a00055030160140207003640c141200804c040403410518542086030021460301c4027030044507c0321001010300604500c000c038400d0502642e44e07500e40054424040c8264016a1100e480c1051600c06001c007054103108142c102c01070607944003039070b034008240c22203580c0c0d5a03905080f03c129614884c03600410811407030080401c81002580001c5c5100f14030400403503185220294030340300d4230301080300c5403400601c10007005801ea000300d40140c0d9500c41c00701840c00410303000b50300280c1400c42c07540010005600100f0440369402103a01d0100704414217003070419000d826041040743e00c40e1001d040c100c446442d0184c40780210022415480e01c0d0039803800412811300601f0b190b2000e0451074806540643c20301d80510000d1800700700c003108409959401403410000d0790340c00e80f2000310402042084c8024020b8040110714501407101c11140142c1d2200c0d900d5091061074003c40c0c2e020010305000300c100c588141c61000140441c0002d4500417981c61015035030000000c0c026 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 419258354 1250 419257104 419257121
    0x42301081303031b03020a1214010b07050715031506030c020a02060f12040804140603010e1305070e041b17150613180b0612030307050f090306040c030b1014040f 71
    0x1d101181c0d13265807507075165000e003c00d9007a03039031040c01c841001c0103c6820fa50241448040c0b2008070401041440030f028002e140451040c002c1d03030589a5141c02d90000700c00b8a0213030001180c0c40b403949544e009880b85031603001d8131640c1001c01c907020107603400070368800f08030758001d001e071900090700c80001b0700440a0307908004041501429a14142c60f0008186c0c01c036100c2c00b50740c1075036881c50b40303200d203400c2c5c064a040e206d59111070a035a9580200c0d00207071500c085801e8404d40180f031303408203401c51003541441c410ba0141602c020f41da68801040401035400341c0c401481c85e9680c003070f1112102c40c085040c112150341c00c0702d9220b0710744900001640e000c804218120860f450142850b0510380b22029200706030307001b4003607940b060351032005210b01c040140b000304440f03820402c002001a40500c01410b40e6000750401c007030038248120040307441c104080c1c070700392400c95814000b00200a034445102e81d000d0508010082c1a80c5011400200810a9444c0c944202d440d80708140880d041e9501c42d514 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 419259604 1250 419258354 419258381
    0x19030e03061806280902220603171206010c020a05032a04050106050f0717071b090b030c0918060106050a080718180e07060504230108130303 62
    0x1c0c2007041007810503408003100b0541c1e9008400004100d6a9000503d1202401d0503041018052560405000425000d84100d80c0210324600c4551041010784840080d14000080020b4560940c01d003004039240070414501e04800c2000b16190b41c0711000c13a001d4000e1000e0915690810b014800070701040c4081c2c102c503406d88100d5426507ca0120100c0b501d4040038103e0301a92514401d0382400259402401100007040c0d0400030150041c0a0744024094070f402003010160301a9004141d0110b43c1c490001510032140c03100e200ca0840400c2c44558000303100e12081044284045400701c0e40300c0486151041c07088140c503000440007104108403d28024891094421660b100d41d03015200f40c024003200c0e4000b40e41e0500203503225009181d0002a40f1101280304000c80c07803d00749080d985d10160706140701a86a20354100c0e02002001000094541500c9140e03d55013810400030f500009100b9410494000f621030203a540d03040813000d41c12540d400318030880d100850905a001d002803601240 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 419260854 1250 419259604 419259613
    0xf030203041a0a02070618050c06130b04032a140613030210031512240b040c05031f0b030c03091513030e04090b070f030b06271219030e03 61
    0x3522500c3c130790040800c0c500c01c8500308081d04620350440305500c14940c0003000359110752041d5090b46441005030842c6502003019141c1b054a800b2070448a030015031007110316032041012628803624504e107503000d0b810540b40c03658400c1e1400b11300d014442c1c000b00089000e070303d0010301904560640b00b41c64010f990041c1c040b103684803103180020001c0010540d81e1841405806c004178806451210200403150001e926034050944090b803038a1520012002c11492542c80c4001180b075200c9004202c460401610780136180c1ca001e45e03840c1494080e12088001e5050404828050b0280d0341051300e03084040040c01d90341b242d40300245146030626262102802002203020800b00240c2c074800100503508c030f946e0303070b204030780001c402d0000303590a050008000510503400034460a00c103003101d4880564510380800d000c088140407170955440110030300f07441c40a10510344800b43c500e10040342c02d41429200d0420030074203000d85c185c40d4401c040740b00c031080d00c8003000d20041c5880303140c10f01c031000c01c000c0a98 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 419262104 1250 419260854 419260861
    0x603100e010b180f06011b0305031510030501091113031401020f07060207020f040e0c090603070906030510110405060301090f021201090e0115050a03031b050d050a110c010f030203041a 81
    0xc2c501244200c507503e4084e00c40000041480d44224019402c8984200d03400c800c0c006c981e83c003070350345400041c10085d8a01c00c03a580080b29a80c2c0c03182c220b014003181d8078001415410004c0f1001914440740000c00900c0d420010b85410796480d00c2a403040380d80004014240803660148207000e84a00030080e102050081410014810254006c1000c503200b1a85012070600e4032080c48140e034480d15404036580c10401140e401c500308001120b9008d20010141e03070009807036402e0386003180c0d1180c100360380321381c04a03186015803902d510030b0049019080c00d10034200751900700001c0091205004400e045a00d8884d07400c1448401d130150f6480c0380c0600302103680d968440104a00400b03042c001440e8075801c1541c00c401c00484002d650058440140100402d0f40c11910250b46103903102580410081c95000c000300440c4050040c40d1080c41c0c00d07034803181c0d41c280c6c40070000c103010f20203841561607804c0051400810ba8010103803001e403404509000d0384039540d60a01c00c04034000014075008488482042 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 419263354 1250 419262104 419262139
    0x607030b01021002070c08031c0509010603030801090b0102102c0307260f070f0308070c02030d0c0809060a02070503100203011d1f0e0105010908010203060f120f07030308041403030603100e010b 85
    0x443c0402d603c9ca0b40c20821551800503007402d07038209100c09404a8810b00c018802c2d4000c9800581d9016818012102c0c040c98140703000085603011401c014610701141c1c0c000c103141d0424030101440c0d148160003907052050b192102850041e002d4000b4030086800000651040c91003002e036400030394240e8031a502e40900741011042000c010360218006001c8000064405018149502c20190040c005111a01c0074030010b892901480300d05a443c15001d20000742143d81c2e100040820f002ca60b4054400e692602e0240f51420000c01041d40c4824014001801024400c0048000010f17004060710740c01d46807034001100d05003444841000c03003001c0384008103000030026060780c12184281e80d80101281d0701c00d0540d00701d0105071016a4400343c8118904080d103030480441d10101d01603030548440716500f4692900c4c3c880c6070740c011030110381b04808000c01d006403024141003513210500510715500e0580c0009445209102e5000b44d060f540d043d107031840d25403d601403410000c015115030740303ca120005 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 419264604 1250 419263354 419263387
    0xf060c03070e030d020c060904060308130f060c0f0f02060f0304060c110a030207030b180d020d03110304030206061003110c0304030606080d08010927080c0607030b01021002070c0803 80
    0x2003070800320710020040c542e40d0030002903920080b401640907013801d201000c2000919030006002a9005844a0000c400b044503d0000d1905405607010148950310300b906110300d41d5401e42c030440c14840c14080400100b8282500c10340d09a60120201003542200d20010f6800c0c05400c0130841060000300070030040001c0ea80c0120080070240d142e02c0d0801c1002e03004a941d800c8002001030050b04580c008000241e40c42110680120401c1000c40d03140a010880501e4088510b91031001a844840241c00c80d82c0c05228800d0485201100c86103185005d880180d0307210300144c03655014400c0c0c4c104d031500c018072a42c441c0d0001d64200b0b60165031045c0c030708421643c83d08503010540300c4520b413940c000f900040024203100310500545072640260300e810b411400409103610441a11f5000074500c0444820b02c07041046501d10440440c1d44a00034040310a2a059001307040d001072602d407141d85840c0e6a00062003208182c045200980da1341503501d07115980d81b0040e8042c100b580300101e04aa40d02880030b0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 419265854 1250 419264604 419264611
    0xc0b0a093206010605040308030c190801150905150306011107090618020a0816050409020708070b09060c0d0b060702100206090f070b1c180606050f011403070305090f060c03 76
    0xc01a1604400c40300034507403201d8080c4904130104108100405c001103070f0317a0245500c00304a400d00c03400d06082c07445111242401503c03103070008207424018003918440c10502540001245041d0700c1d61f41c10000400d903001d030000e0382070600040c08000503109078482e00e2000f030069240c0003601d203810381d29294140644128050389041d021010043c208215880c8290780140a0341c1d0fa508039244ca0787c241120b60b11019104010400c50100004240e4100034002414594401c90794155a130f6100d0416150844c000f0740108142e400c030400f8020810011002c0c1d40c51041c500300002040c1c10440c0001d041482410340094000c08610070000c1410303004501c40d849840c4450645494454010500e502ca06a500903a4806a024000d40302c203c6002201e88101c07540c0700e400050b00a10700712980421210070035080b40c3c03040c0c4898051000d401c0c2100d528443c80ca0a08190300f0034041c1c100b044506001c010800070400d0703035540024006590800400c401103004034107580182c144900c0c010201d0707004a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 419267104 1250 419265854 419265923
    0x11090a080607260610020304080f0304140d0c0302010e0a050901120605060d120807030f140601181202040509010207080403030e09010501140a03050702070f17100b010c0b0a09 77
    0x40c41c1c0683d82e80d404881c2000c4042500030907143d643c001c10014610503c551a4003140700604c00401e9540c0100020107180002030005c5450794070340f49030004102d00104256006074860743c00c050000304c0c1203640205999090905039030550401c0045040c90403950321a95110800c0000001c07520101840c80e04003e029038070600003565171409000007451038690003004850a000c52003025445110000c1e0041d840e803501050015001e42e00f00242c5078800c0f6a83c8080b6664000e02816681000201c100703181070740c92070b10500d0b02d0140160360007d0710400c064001d0740c5500024810003429412903245961003200c01c2d40300d03612814000d10500440d845240a414090000f088a40c0642883d0b8000c015000c2090310700071ba0014100d0280c0005020303601948611f800108444052038203543c0546005400c00044640f980e081318901000020141103491500043e81c1c250f903400301e50300c1d094681214088440d500c4550031240140071004020b03080600700390b00c140c403041c0440261240140607 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 419268354 1250 419267104 419267117
    0x5090c0409031832010c080403060b030c090c0d0b0303070501020a09140607080405041a0301051e1b0304231002031f05030c21030403060e0709020a05040911090a080607 74
    0x1e44c0c0c00f82c0c460f00a450904030308050300d1410104016200a0310a1000d14189803001985401d60351307048580c6c120307400840d542130716800c5c00c10241c20100500450702138125200607035400c00c029005901c2c0b1802a07040d00c01c0343c503120071400302e4504004491a859004000319541d1001b414000c1943c0100d018080e0a0003002000c02864038024040c1ca50480c1c20103071007454240703440704004c020141d92203c01f401d80d2b0020320302d416942c0c0a20401d03100d00450402e500180700c5559002d25540e070002c0141240e04134003040400e108124a06880d44250300800f281ca0700181e064550948410f8401c0480151180003041d50703844080741c005d50f004803030113030007004100104c00c80d500d031040b0075006003034050b403140000381c6d02c3d407130031a02c55800e07078072520310301105005a41003082c11584a074009550795600d0321403180141e0b50410100f00180142c52085041c48003030300000307080d4400c9100d0000480d40713035044c05524100c0d400071506003250040c4042520ba5540c86415220201111000003081d00f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 419269604 1250 419268354 419268359
    0x706140a02070201020d0516020904110102010c03051005010e03030f030106020a0c0e240d081204030908150601080a0e01240b0426070312020a1106040b070605090c04090318 76
    0x38903000740c07040c055058000e000340d940800800c030340542158801521301281d0030315640250310f03044002c40c040c5000b00810070499010700c0001e420760316580320000030549070000300082e184040c24880c095800901e002814509540000381c910b001e00d0300c501526001c0000001681a000a98468640c1c45248145c071555521040c000f40000115407042480c0725071484643d026a1140710242961030040c061150506240c40c1ea0540340c02002000f95026030480511050580250714007000380f102e240240700480801980007004480901214180922074011507a000501e0300514030024150008214a1481c0310503841c2000e0b45090314000d0208402c4049000174800d03048a050300d003100c40c035030030302c03141c1c0074000c5501005204103051500a90728044005681902c4200c001902507000700090005410607510092507828075502c40d070000c110030000501c1941c143da040c0c580010700081c655030341d80c190b03505010825a0740380c0c3c0186066002410143c0120b02034841d080b003145220040354 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 419270854 1250 419269604 419269621
    0x110c0a02130501060e010c0602130803070204050105060301081009050309090c09041103060114180a1e06020a0f02010804030e190320030a080f120c04060f08071d0a0b070614 76
    0x700d00b8091000014017a074010340c0035500079130300301c030140384140390040c900f880d418410440844240c101544a4000050080c2980303010b0180c00e02401e0704460140c81c2d545001c2800d5914261540354400b0261210f07022030a020041c426140580005810405c1030300c0c2480742c0c00c010707900040c0c02c24411440c0484e1001d11440d05003c0e00d1140406844524144c81140c14520207504551079034003400398400840211038550424032001454000a41d80ca00000d000d400c60003d00380e40c00c0304045500040464012a558402100e040c0e130302820302d05490b84880c181100c43c070745d01416481d0824640310b824206450300851010072203000e01c25002802d50000e0b40800d41c80003800410303034154040180d2001007030a03031000301242111014090310308a5844d0191210307160448155565150101c0d08006054112501a20300321441c54150640e1520907405440b4540c00f0103a4040028580311200150f1039a51400010b06a020382c0b540d1120580d26110000c1c03d00c0200f45030318001380710041801038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 419272104 1250 419270854 419270861
    0x12120c02090106050c0a0606151b0b06330a12050903041a190201090209011401120b1c050105062e18030f11011b08030109090204110c0a0213 62
    0x40d500801e00900350346811011140c0390080c95110006000701105d1380300065240c441da0b0024101c1820410500c2c282100150804101e41a1100c03203a042c1030410300040c261441055200604544a0300d609070080d840030340e0080d200e03041c0c0c242219451559000941e075200540700e00c009940d14039500c03407080313216a0240c0c1c4040c0d50101c0581d005000a00c01880b400000c0d4101c460480c0040d82444088039805402d075000605001c0036035501c000f18819810522802d5007d40b031421b0140000c110010002050244142e600d030768100e0382c44244500ba59110810700540c0c0031525002116280c0340d003440c600170401a946188184603038a40034002e14034880012a15440c03040340c000710030907150ba064896030040740030450950314102c00440040c04400e0203004845c00b0345403d41c0e03078440b01d0001502c0d606661110b401c0012036a0540f800050004084905492402401041881403480402c001c1c0200e03803030070710070a9808141b45a44090025540038042e000b1030b40c0d800c0c0c5d07195022280045 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 419273354 1250 419272104 419272127
    0x6080d0207230904150b09010e010603060b0f0307030f1b0306050301060e130311010b0d03030c1d0307060c0219080a0b130c09150504020a0504170d0c1e0203071212 72
    0x591803900080211740c09106030b507454002a4008140c03d19148000383c80b45409811042e2100303003030801409081d92500c02c6e0300160071440101498a008400d2101e40b030702000b00400101030f200c108460b002441e0760848200b404500180d003103400308202e0058050144c0e40a00c900940c600000090a11036803085540203074000103400441d40140d40781117882007007102d0001419034031510380c1c0405447d0000f85024050181c2d900141c1c210500000a0418041e40080e0100007944c4c07180c04019600458010304440030381c00c002c801002c8500c0032520b03100c070381b20002d0000c4181450001e08500003050420751303a885030560300441c0c1c1d039007580c481440c0001c142c080c280c0070004400b4400e8220580c45401c41d600c1300e8244802803507448001506980c404a035140000b00041400c10900780384403400f50012860b080540388524040c1001005805032040103401c0b00c04e5008044c07a454540c0c108590015005000d07180c0c0103882e8179420b520130750319010440b1581004080106440e1091340d40e41e03107 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 419274604 1250 419273354 419273359
    0x1a06040605041211030624010906020303160311041e0b0f030406050a0e25080f1b0d1502040f0501050c0714030f100614010c050705060d06080d020723 66
    0x8141c18076000e1050007030201c4089a941c013a01c40c06628039542000154840e5200e2845008030030b11701019501ca1180c581001414001c081c041402840d4012094907800600400840284144c19074101c02400900c034940da0402400a004124000004000d00d0303822010010340000d9070340c83c203410303060344504440400110800d02c046000207481d9003015801c01c0b01448040340a8a215007a103080003e88100c00403c50b59102c1e50081500f0746000c198010403015000d4600390850b1405c060f01c0d100445140c1e0a40e03003128a18035950355440702e0b43c1c1c0039641c02801441e0a44010075084000390300c1401002019140c5070b00004040d8450b0003102c60b00340d41030740a0010b01b850000100c1c41d194034480d80d503030305009032000071a10102c100071440e2044e00100000c11414600138a0b00c1c134010104013414100310b001c13403440001c00c100180c401c046030407da540d9569404980c3d20f580043c0416006100c89001c1d01d490002101c0d80000e80034140d403411000360344941000f00131061060130900c20300c3e4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 419275854 1250 419274604 419274607
    0x7020307060b0f1e040b10020c241204050111040b07020909242406041413050c03060411041d100f03030215070302041202090619091a06040605 63
    0x2000110160440c0203030b00005416507180c4003c40c00003c040e009511032071440c80070071444004aa152600950812000544980810000c9080004d45440c114840030740601800412428903054842002015070702101440340c680036112140c602e000c00a4406980942c20451048140600101203408a03000103160600c1c1041c582d01707005034000300401c7c01403107005030728101042c1d4400c020001107403048084584000d00d040600b03505250055030900b2029680440307040a240c0358141124142c8007641601c07d02d240080c0c0021f440300f071082d000c01c0c52040c01c0606014083d01c026000d140501000c403001e101c6d2a440e0002c400f40c0c4d00580c81800c0d40b01c0044214198070340800307005550410041c400310003141307440f605000a00c03800c56100700c00603448040542d07414009002c2c000e4009555290641c941840d1100018408809550191007048444c1c0414110740d108044000380350140302200f050140c1d80c042d050000c0081d25825034414018100c0a001450800708035000c0c0c54031500e443c0d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 419277104 1250 419275854 419275867
    0x50708010b0904150510020d091e03140c10080a0b010c0c0b090402070c030f02091810020f0c010903020d02070803040f170f15011a090901090b190f08070e070203 71
    0x1002034054004000541c1341c0c40e42000c2042e4980711608120419150010020441c0e10a00104205519480061090444294098010300d05c2030104101c981000c0241646010034008504087c040c91840e540110300d000a0014160070107201031103808680e80800510307c0c100015170301c100e000300c0000d054484034601032180360a40c01c00381a4135a8017400040c100030165444404041c01c40d0010744029850b00c840d0021407412801040d840500e82c440b1290425682c980a60740d48803615800e64000d80201e80c6030b2528403141c0540e40d03564074200090219106900307002e5110144400d81c003005000c2c042c40812401800001c660481d40f80d0078140340289d10380340300020a144081080308c6c05010340218020503500c01c2001e8000303051070b0b900101d82545030510740392000c0c0700300000301000d410a01c46008260356060320503045039840000400c284601000142c95000f140b284114204480a808540341412010390010323191100b0459090742c0e1143e40e0904022801c9070f02d000140d0081140 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 419278354 1250 419277104 419277109
    0x9050a1401060503061806011710020d0b041409100b03061807120309050a0f030803150103110706060905060f0d11010c080d09060f020f1803030d02070b0406050708010b09 75
    0x4018440000d00000649962030300002414460146c60000000140c44603000b8000b000384421030041407403039420206404000000740d00c561640068070b10a0b61301051310320700c601c01a0030a4651082c018070400c141040c03440c0d18203a254064849000310b1046c5081c07032005140601c15054201002030040c0702c290b84000c0e401c40e2000e03540c41482c03214003d0820014900310f40b0132840411070711980b41c0c248520b0505061002c6c2d078401d030340310b234022501c418001c04c0420602003c0b690042100303090f00280740706000041c2c0241811907043c05454100151860500c100f030f07403040c8140c403440c40b0144840d4468000b04020300c0b1f078400041da80104014117602c0010650046021001418103003544201d120f81c90b0789a0507080f1500380c0c0b00407602c1700901c00800481c1d1080c0210990f42c004110704120a0400c0b4408602a4000c50904048600070740c1c8000e0b9800c006490140503c0942550b4403041c40c41d00c8100e0480c00d48007201c0ea81c6c01c0002190516001d040a103059882c2c901c0c030142481401c008 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 419279604 1250 419278354 419278373
    0xb030406021605070602060c040303050d05060120030a0206100f0611100c08040302190803160912050a0209100303080402060f09091f0e060604062001020d0f06060309050a 75
    0x400c440c555401c104051107050008000c0d8416802840038000340c41c9801d0010341400402400c0001d0550700300414000030b41c004c0e05450104802c80800a07080e1b8810300165100e0214851040318451400d01960000800100078100142c40d0b5080c1c5095480d504c50501c0c60b112103010b80304620b02e5045040c01000c2c4140c0300c81507041e00c1c0314211030038805014404001c40b64031800d8040080e070090704100a1517010000c541704002803148c44d00344c108036074907841c096010141c00821600d104000c4014050301c40c001c010090140000c1d0e409002290749071195031a41040801c078018410300f00062a817084101484040f650582c43c0d020840d43d841d030800000c0c0d0310030202103460803014000340c2504d03158250310300c1c4104c0864854019480b14180b8101080240d0b900c8503900032701040411105444040c260b80403a4418207004901202800020114000340029a0501c2d0300c086803444505100350000701400100450030041203488480860503076a80742400fa01590101c21090000b40d03001c81c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 419280854 1250 419279604 419279611
    0x9050403020a1b051e03070905070908030c07080f161514070b010e090307240207080a0e040606140a11030c0a030302072a030807210c0c0503160b03 65
    0x1068942d10901035a40d410030303500c0d0300090030568201e6802801039081280e903611030140c1c0b00900d8000540601c000a650f84607900500300b80944420124090501030420389000e130403201c1c01c1d80e0311040e008044aa40300f84031302c2100e240e84a22000255030500104008000d50214995040740b981011041c00b0164000885c15080284802010724855501d60140000c83d01c41d81c4441c07000e51600b8903254100720007070410105500108922000034491307504d030404114103032a41030002c03e8a544018004d00500a01404440b40042c1c80340190b54800d040010303403402207902304400790b00c13568119802e02c43e92032a03040488041200307060480c01103414403050f803203a001301ca10b0803520a503503600349240301104401080e004a052420007048070b00740c01c00701e0944070760340125588039a0b141d11600204d22025100810011b220414440042c2d8113120040100d070300c616018000343c2004190b03952210059480c410b0242002ca891f1802141c1003d43c1410552000485410284d024442d6031025 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 419282104 1250 419280854 419280857
    0x402180601050d02040e0708100b2b060602060f01150e1c0501060620010203090723030607080601020f07140609013c0507050607030b03250603060611030409050403 72
    0x20f00880f1a90b55140c0010809000291581c820600300340c00043c0613113001406d80c0880280b100350070300410340100c041e20b840315412150981d00c0ea0154454820700c0c240c2d40d1494511605008001c100a030700003503000d000380c502c04803502440e0381c1c0e10b120400c01542c1d1038418002a034100181441032410419290350540b0382d2a4081440207559201403c6450640c04500030401c410850320b08c0a00000c00004c14191400080d03196107043c40788030707807074144a01850070040300341c0140c1088503101c1084040d00420180c100c0e543c609148402820443e41101c916006110746c1007072229a003404900c0808880107241c04407a048000000c12415800400307405041206c480b00821464112600f244058402c64551450701ca03280c0607d082040303002020601844810043c1c5400644006286d030383c8440345280000b011080040000d0800c0c1d000425a44034102c0814a00c0c2460103440d003801c210756442c0c80400200d981d8803401d5429130701582401c901900180001c000b9941035400881d44180b00b03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 419283354 1250 419282104 419282107
    0x1005010c020105090909070801060915150c050a050c13420f0602190302071406040905090f0f16151106010f06260406090302010216050609060f040218060105 69
    0x181004105d803950102d50f02c000da5030245204109014003886980d002d0b00c40102d05010180300500030854910f018400e19401e2032040008001691040c207a012001360b21805544454043e81000783c0c1d00c240101120344510107030821360224490300d12070310640400a550343d90041161501c0b40040da0301034084070318407403442c8c12400c1c00040c0d1082d0041c05440c02201c80000142025002032401c4c111042c00c6510680b0100d400020980000303c0004654400104007051260407003c81d60b01c0c0569840800c02508100500c000c00001040c10125a1800800c60b600c032004032140c699101201c65003007a81201e0504240540c03086203800070701c108000c0c141030207030020a901a904e40642648401c0c1402d19a034424400e80341d11a000c10400c0003c03101c2c0c030712000c0e102ca002100507000501300a00302580c070000c6d0070826000390141c4841e2000d9201c2c4200300f0f00a8184140c0ba4002102d204410b4000e07034000803031003101d0f0803c00e40111b8010703102001c440b201a11303803c20858080c1c203441c14403a0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 419284604 1250 419283354 419283367
    0x110306030604020127061d0307290f190e061e0315030d09180b1e120303070306090609020703021207051504030f0314090d030f020d05090304030203060f1005010c020105 74
    0x822020302801054240d03070316040e1118464018887c13100801707400e84a900150010482034240d5081005008007600c442c1c1000a6030422280351440340703482c84482000c02141080300a081d05114825000c61521130745200c4004104015442c402d01d0b0030200309a020f10b00d0540480340805c059035005003103069101e5898070000010380380c040c10441140006418840601000c150b2180c3d1060b1a000d80c0d105200034861400000c0c00c1c4c02440800d02800d0180040d890302c0703552031569000040c001242501d59a0521800050282c812070240c410366034100b400010740c803141031080b1441c940d0507501070a25a0450380390106140d0100324240d8061249182e044a0584a42c05250003180300c1c0d220921119072004c030140c141d5400e1a1209c203064074a80410507107000100342441c0b070340d92038640069440d501c2c076082c00082c007401520b4004940762204000c1c96200000c010001c0d00d008030112040750b03031140d210700c5103600d0031100080c0d580b0307104e00100080e50040061000302d0744141407103401c050 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 419285854 1250 419284604 419284667
    0xb0f040603050619090c05010c020402070614010f0806010807170a0803010603050703050702011527020705011d1204050603180604030806100212071202070b0c0a061103060306040201 80
    0x401941050b0342a82100302031005505081c6401400c22198000503c1268665182c0204600c0a0312456050000700d0110703404541d515411100d42ea940900304210410422000381e110314001d014002d01c1007042040030a100d000000e84a04840302c00e002461001d0030b004100080040081c44544c051141d010740c01e0004e020100918060841c946d00011140740080004042da0400342087c0156403401010504c0e601c00445100243c0303a0000c00702e101e8074140960001c0c40c84104645499852011800008001040d00701e107600202d112083e0110130b0402450325140d117070040071030780700e0801040300b00881d0810750061548060031080020482005941c241d041013000c96007200020340c142c0c1002083e28000700c0031204061944010041100480e10380401d5210f00400a0103c40c041c3c01d01c01c602d984200140005008158841034541d083e50740c17141d680d400300380030446880b403c02070b004c40d691000c007003928401ca100500402d21522507400545181e0080c69019038203512001d013486500 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 419287104 1250 419285854 419285861
    0x1020c030604050a0209150d02040b01020c03070b120a0b22110a050d05010608092d0a050703060c05070c03030302132403050915060909100515010e030106030203100b0f04 75
    0x10383c0910b000e80704c620620720400c0141140207004c4041c282c100c210000198980b261540e100d940c3c1598005440c0f03080c000145d2810344040c420035414800c0c0d8038041f942084000c05401e03040317107505000803140c842c14114001d0315039491400d40c02c90001c511050a51856030324212000650100c00103420501c8810404140d00c0500410007040b00041c1121545540c1d108103801001e030303403506041c01e042080e242038681c0496181c01c0c00c5100c81c1d81448441d20794078031b05841d1900c1070314200d0f102201d02c0d180541e1130f010702d84001d0b034980c3c4c5030091588241d4000c1045030308041d0f010080b000d0342415503070143d00035001100300c1c140e41155120040780101241c81d0072642518a4002c0ea41c03000620003004040c0e0360010071240e8550052a54075160000c0003000c1a0400d004903000b005075502c4c03800d01445c100c0c99000350600035043c601405010554554030251260080e40c0320428181000240350907a01c461100940560100c000c0c07a115200039801404200001400044424828400681034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 419288354 1250 419287104 419287111
    0x40f091a1309081c05092e2a0f030504030e0409050c04060608071704050607031d060901061802041410020f01020a1e050307091a0f040e090d0c0f030c11031014240f01020c0306 77
    0x141060001c008c046150043c1092900c855a4641030040f89880c5e60001c0c140c00c0080941400f41b500e03101401c041180a01590501c100042c001704001940c40700020414003054031250003040321b00304905c441d580c1c00107c0e58403480d0048001e01260300e402c681100249040101c10980c00d41c28503c2908c2941c060100c10300941d2090008507081c3c0c1070200c41080100c4000d44480407170301c1000200300b0b445810301c03201c400700411100c19a088141e40700c01da08064103045065415440041c02080d0641c00c4005081110915401003520600c03e10007500c2c00d1000b59490000b00b01c04550030800000d001c0c111607900c00b2801141c0b41400c1c400d20009071560401d8100c0340304c410a400401140700010091880804803501d0030700710340883c0c0e490b400f0a4004100c0081c080141c00d10140e02800382110b40d8042e07060010301114005c641e2142101d005004003201051b40e04c0e00207000c1081d071000803004481d84c100d0756490314600440174003007041000c060440c00b810350140003804041682e05101c680e10 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 419289604 1250 419288354 419288411
    0x8070507050f0f0d181701061d0109051305100903031b052203081602040605060f0307140a1704020a080a08040f091a1309081c05092e 59
    0x2601c500700301c01d00d030420201d80c0321350082140ba40c0540b001040350200c8a42110403175050b020b007207401c110341c0300d01414103900012909038140240051a5800e481c440341241c85c0d12500b00300a4071081c45003400b070544400042c1050b0b00100ca41031080c82c0743e03442096010b2080c03c0004524100c1e001d460304c0c480c007842c14940840c0c00402d0795030380c0130a00c6038a010941d410111394640141560f444005070300500d901541d08542d240d21440031900d49900c21406010000e110b40d440d001d622b8a0754281d41d10440315500011350180060500329051401d49aa90354182c4078401401d1040d14103804586c4002c10690384441c180301e00065400c410b0090301070841c060008991340b18240164410b900105501200d18a031500030340044101d980c00c10301901c4442214050311070180452001c0c05081180740142003c480020007140504000e0b80159004000140600c240d41d146207803c0e45a007241c580c80302038920a101075003040105901d0051802101003000200594141c10958030504500e24511 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 419290854 1250 419289604 419289613
    0x50c0a0c090e060f010f0b13050a0306020d0e060103030813051f1410050904061d2e020408060103020f120d09181a06160f110111030a0c020108070507050f 68
    0x260b10440610400b80d00c00300380345480c020b030351520101c0d0f082c40d6010b02c45e9008034a03011074072506565810000074010f0800600311594181c41c0e0929200039441100008815850a00343d50103501000c5803240c102c81c1c268640d01842c0e691100c44582c0f00c48082d004680c907008400440548811807059101408556440047e4400440d41c1c0c4d0015a14081c2c40c1d9114800c02e0403040149a40c1c10808036030265000402042d10788824807500159800f001a00d071080c001e40d0f17002802c902401400c0c4a00c41c0090810341c103d0f0030f03000c81c0e0b0012071055006001450300800014000b50814640344003400001405124900c1100030a0341c1c24982821020750020b42180c0b02045060715000103210304511079038082042d1107042000c2034808803400d1680e13004003004a07003811050403440c100c00029400005000c0d102125203030010380840c45042c528081800e201d414501c1c09030000a5440e24800350311505030100c5c00b42c005580d0094018031001c10840d04000a0b00015424082d000000c0280001031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 419292104 1250 419290854 419290871
    0x1020f040b1806070b04030c33061a07020d03050417070806011505160809060a18090605090a0f090f08070203100c02280c1e0504050f07050c0a0c09 65
    0x1045100c18100b6841401c00b0310891020440c8860031035042985410600c00402c1e080c41c08a81c01e1003801c034584216900d036014002c00d00091482c04800d02280841040200c2e11640c24410074168681442507495082c4910001800d0000d400441507000741485400c25540e2026010081c01049030a40c00b03030082c2d40c00300114242088032034054440c960398410640c8180c00001c1071401540005048001a42100e00500a24001701c50308100080d084941c1da0314140c00c007601032031054011141c982c09071100003a00c00d0042c131842042d5039004080d04400d8503211100c101610800741406d00307065440400c41d000480d1110200030b40e0340300703011464a40c1c1003401018100301420707400c00459814200740203030195010401821340c04001c20609160403c8480341d0400c0801d900f00180b06984401c07003c64104090181d00840b00c1c090044d05000d59114028442601c600b0f680644c0c0c40178122021a6001d401000035080b040e0b00c20702124420000703030300c1340c9a43c910a54000a4030996a0810 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 419293354 1250 419292104 419292127
    0x14120111190f0c020f04050714030a02210105060a050a140403141605100f03090503310308120402120604030806120712060213170610140108070f0201020f040b 70
    0x8600798092030414103e0f400b101d0300401c4001c0c200000d9944241c2e44c9000050038036010b90040320052031910326240d268608007280c5402940031254140c0c08203035511031200c9060b07100081e06e042e500c000e44454102200c2c2181038680c1d4014501d01000d2000044101e4000c4010b200540001c40c0904280320300ca03054899181e0808226082d6004040000345013401251a00303c40c18400c0c100398a00003224002c1d0040440007032803c0c00008080e07010014814002181c0706500041800007030340406d00264600a440f40b01d010315200040c02c0301410310040f0000c80e070b10301c0c4581d0b2090000c0d00c00300d0b08502c42c0d01d5840c1030a4044500320082524401440003c4c148089050f00601d1020300821659091144142c051400c801009001a40005005c0700c00c07a000c40742c0317000401c80d01d0400700c07220710707000b964a88950045500f440c030700207001c000051810031000741c0d2001350b8040c0c4404d9907607114004119020103040880e5001e40d9001c209440c1c480c0728001c0104001c01f005181942ca503114804c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 419294604 1250 419293354 419293367
    0x309032d06091e0a020f010807050708070f06050c030405070e0c04240f170402040b1908030c01140105010c0308070201021b010b0406090c09060e1c0b060306060301061412011119 78
    0x94001130b07108140203001070700e0b01e1550320510b00e824203006080703954038141140c080c41000ca0041841070080340c0780c0100004d42c640300803041e11481d0140000d944000f9001050300080f00c0140c402d0f07000d0319042002446040c166901b280716a01060f207429141d06014200840200f03c41d8000d17010440e60540040d848103c1c41c45108040c0740c410300c05885a452014400009000a48500c1c0c0d100c10380c5403103903190303142940000c2c0d00181c800c80301a070700d00c0ca0603125041656950303165400c0c0010001c0012000c14043e058450507152021724140a88080328036900c010140380640d0f42c20880c0484580400340d0f824900f50061002003007003c040b50038403040c0c50301d540c0040729441c101441c090401c0e8101806005480700d074940305400a080d0400070390700b403085400480c420450840303081c0c00d021608860340e205030030660403583e440e01d4903028142240c1c0302c1e2040c00038110400105146030320f000080c21054080341d100214500d00c801c1d191500c9544207442c41c10010000b1540034400725004035 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 419295854 1250 419294604 419294653
    0x8030c0a17060102031b160e09010b09061503040f060e160e010f050d06090b010e180706121d15040203101401090b03010e060703021b0309032d0609 65
    0x30740c54545050000010390f0720700841c40240d42c0920007454100400d00700b08848070300c401c04c030f5403100b4155030740f2614400030060a40b0300100550030646802002c1c02e049680501030240a84440644601d00307200c00b0031504040d0080310440c001049810204900f4081c0721032041640d00505444900c0340c49000c01080c0c654050100740b95154010440c5860418420301103034420384c1c000400791072900d004401040242001040d00700c3d1000049034441c035120750648a080c49401550208543e01c800300d80c0c07021244034082c0020340742161a0300300c11058211210059032000d500000007210100ca83c00c0c041d1142c00c0c500390120450400c025490100104540f4030141e460800c0303843d1111007100f0300d00d1014001c02003c1a00c03240c2808084d02d09620100342e503040300382625000d0403c040010040c2d0301c81d946020401c105825070909980000c003c032602c200c0000d00820768803500a050407080c2e000000d101070108101003181400900511003e44a00104c0029185400c04502407400c0381d40321a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 419297104 1250 419295854 419295887
    0x20d0b04230c0a1205031e1902010216031211070807110d0506040f0c091e06050625060902060703020d031409060f040c0801091b05090606040905060a0308030c0a 71
    0x1010b400d040d0320381c0c460503816180c2031922030607595036900b403d624600c900c0045420707000549200f101030031020340180c40c1221000c0d000040151100c80704900381c1c01440121302d82e049100ca1100300081c024240b980700400000008114801c0e007041d134000030b8100c2d590685001c40001680c03010003c4c418081c80da038000483e18005007103515190700b44ea0700300c0280002d0042450aa1842c207000c1c041075440300404668000340030700c4440005007480001810401800d90303080c400c01082c0c0d490300700f00f81e590b0004520716002526007002143e0440b1455401c00340c0c0d86650b142e941d8030160303d4400c01001c1c07d9001e90020b01140000d03070001030031510075007404003020480c5400e008005801086094000c841007800c42110b440e18204525401800e1740500172540c617040c00d0000300101e43c00603043d01141c1c20030301d4100650311f00c14450341000817207196620840400c0240030360103880d4855508101c01034030900100303440380c1e0f592100f40c1c0141c400c80c03090500802ca400c002c0342d103e04a116168400c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 419298354 1250 419297104 419297113
    0x30c11070f03020a0e010b12070509130e0f010509150406020706060e0717060f060306040609060f0e090d08010b071103010c0512090a0201050d020c012319060b0702010804020d0b0423 80
    0x1040d40301e0740c0a01548007401c1c0a100c031003010580e501d1040003a5040010018200641c8044100d0010b0037002c40c0660319a4900a203403820b030300b80e0418400c2c18032403440341c000f9150070040e1080310361001c1c1c0c0040c8100c500c181d082c00080081100c51140d0b80142007000d8088841d42815440035103055587c071040c40f10680000d04110b0709495481c011550450306840490303c80e201c03a00024003410447c1c000d04000c0e0302d00280010100b446540d0303581124102081c60190ba01c03421a02072b1125100d550610100c0c800303100411401c0341c2c820040a40c0e0b8041c0400b14071055000000030b0941c0c03007035000e02001442c04a0300400b200074841c000340d04030319007000500d200d5a40d540068500c1c00b03402d4580f9529035020882540c5c42200b0740003407800800f82c04080d41942e40e68100319215500907243c0d104403e02400784d40522215502c60542540c1ca090103850601c101e80e401100e140300010b10403600001050600c00000301e0b0b5441c02c900551089000300060102c1c200b21050801c4410b4401e5001c3c5d00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 419299604 1250 419298354 419298359
    0x4032102071a07050903060a05010603150302030c06070305040803040f090e0c090c030a020403151d060f011511010c020f0f0d080114040e031308010b01050415030c11070f03020a0e01 80
    0x140e80d034124941c12403000d0300c510ba070356104020fa80b14090ba075540b6405004840030000c4082039640194140c030986e44042000000c0e0040703410040c0c0d958000250141d000d0701d0581e60924112000e40003185c03286c0307000e40c90152640c0d4450b003146c1055225001489440038180901c00c80b40c01040401d00a400c0102000d01c03403440042c4000d54042d010b040c9546000000c40d10403000317034040750080c41c1c206000405d000851520240204484e040f9494000300f1051440c01d5001d01096550003003000d070480c84d0459082204004101f000011014203000c4082c0c01c074500780070207019808840600303801078030343c42881052550503c8010b0390560015041022181041508070340e50038152000300210356507000b405070106008004e141c07021180c071302c0040381e00c0034013005240f202c10035641000020700000303400301c00644444c00f45014583c0f689a4000c026414141701e07070311134000480700d07141c02c20150501c407055a040217080e80001d410407001201c00c0c0217606005003001c008015001c000d03403c5e5031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 419300854 1250 419299604 419299613
    0xe06030c09190812091c0320160e0703051f09021e042706060e0906010306050a181d1c0203120a05240303160c0e0403210207 55
    0x105800724a4461001c2c00450342034201d040c28944041d00d222001c0320328982401d0300718421070300304040d107a00ca55880401e03440c100301c490002c08461641900c42c2e2414840c13022000039a810b415000c08080c1c881c0b040050380c0f0040c0ca8180800501c3e0700c2c0c2c1c21240c030303041240f0000e054400c010b24400d071803c58801501c00c1103119008010071581d41c04801a01c4841c0301c0d00c0740454510b50780b6080107a0b40c0104020030101151820410b6100400100503c8807050a81d03030001d03a29144901d00200b5148605c1c0d2100b03040c02d9149650201052500080341358458002950a541d80d03080700e804240180020441401d007841008010251555200740509030700418990f41c08a80d502110300d001d83c00070700099940204141c49500c801007002944c2403808140c3d000080004940c250302c101400010000841c800706682c9011441c06800b85240c004e18440812610003000001c17241203502d610f001909604440200703000350f12955031400340303215402c14021015828940d070307201c45204200020029 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 419302104 1250 419300854 419300857
    0x3060702010b030615010c0501240f0501020d1202070b010e07030e0a050307020607081c020904052a0a02070503030d06150f021b1215100b041d0901090c0f0302010e06030c 75
    0x30700c048841c48210b20540c5c0048402c02c03005400100150b0a003030010040d001e00429000c10303448140e0f081d80d0002c1c2c7e41d94400c0c1520909200f0140036070000c0c138840750101c0c8a40c54081d40c04030b9401015182003102e5a6607441040c0c268070155152840c50140403180d035040c0500d01d11480c2c00b000a000d501e000c1c2d101c0031344034404c03414002e201e000c00140800030880d298041c0c8258003400d80a01c000d0b1076034005a00b0107580f0210100344901d1034000012010075184268403004c030407a002c000a040310341e83c0c118a02e40d00481c006c6d801d52164510004856030104000c10300c4044140e408501e00f031500313170104804200c40c580720041c800900740c1c20b0340c000d9000804500700c88202c0e0800141c142004c002c03984160041c810901d06000b225001308036002c80384507030b074040c81602c041e00f040d040e5290164161806180206070b400c0450b4048000751010940c0015000031000c0c000051180c410ba4506108460f694000e02506816072820400d40d03070404c6040d410b002050b03a01601e1450814500b00c4036 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 419303354 1250 419302104 419302111
    0x102070206121f080a12092108130909120c080f030417120f01090c020a030c05070504020724020a09090c0e030607022d0304030f08070b100503060702010b0306 70
    0x4141440000500b10f01d075112403502e03180100c03103404510644032801291100144101540c809821200a80d01140f2902d107020031500c0300400f940c0c40100140c0d4032003244005a109541442041c05842d00c4514000315040090564040c0020755620390b1400103000c94109a000b818441005510804140ca0008a6415042102c5050390700e65a62604011000c08200caa40c2101004138406c1981c3c0c00d00d0078041e008103002207083c1d8135a0390741e40d220010f0350380e401190700c016040302030000002401980c002003010710440907101d015484030b010504a802c00d8005032008401c554029078010189022040c04400381e08055103403c038200400ba00c103502c148160b070100c2c0d07074030650040c50f54414010b49500e5440141954454204004000c1d56107000360b59800341001602d04601003189011031511201400e50302442c02c02d80303987c9030030940da140800243d5041c2410048100000c0d21071881c18410200980e980c54094100750900d40740240040100c0c056a00d004602c001c0341c0e8000584075030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 419304604 1250 419303354 419303377
    0x1014070509090c0c0111180a03051207110409030905010f032c011b0f02010b060c0a030f05040906030506153f0105010305060105090619060302070606150305180102070206 75
    0x202c0d031a1a4090a120311518071041402d5107080802c00344442c110000f41900c05400100007620000c4004202d1541907a1200502c01e41c8401466003060750b10001628009026421803c404440070001c04c0680e84501c1307045000446040d410702030f541c1c102103042c00c0100c041c5070401c482145180c01010000030080310121140b800481e03106400c109410080c1c21039144414441c0308050750201428121007000344401650a01031444036900b0007100f070350307240582d1b0001401415a03549059a01c403144c0380a00b03040240c1044040390000c3d05000e600c00445c8150001c1c403807480c00c2d120050060203048042031003a04003001d101e030700707030b514440e1000c100041185c01c02300e81e42d2110303135a45203209201080c81d403542010b00000a000020400c1070480e08284d410000d1075803036004011450096403d4000c5e1480c4059050080704d10030f901070000c035842444006541502d4114682500c0d800001e90f40c0002c0c0c84804002c8160881da070024400f8010500035401c0088980c0002c81d00c0c0500084100c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 419305854 1250 419304604 419304619
    0x80a020d0c0b0d0b360601090f12051c0f12060f0306090501050601020309030322381606150b131d01060e2205091014070509 55
    0xc0510801400540003841c4182085580b004007941001c09800c880a813107108507030001d80300c400140400007282c61203d100d5071070305814051261a680c4104042e14003810443c0144000c2007119901c1c2030030018103102e400001070740c3c940d8603001c1e2a181490880d01e80301d42890013030840982c0c005107004901d601d541402d403848801042820000c04c80c3c0e0741700900401e05110000180801c0760722211920380590000d20055a68800580e0b0342c2c81500c00b2107415620801100749a101c0d508441d48104400500f000034907a910b428603060340e10803500c11801c003648459944071110b080d191b1819002d000b800d4031803e0140c01003014030850b00c8080c01501c607503110001242ca84d494560803d0241c10755408850712041031440c2400c2d140281e015034030600d40303260b07043c241041c0e05040d02c0d4121441a507079500b400d8044403e1101004500c911942888980300803c2d42070300300c90182e80d03c1040b480c0010728809030601040700945003605080d034000c02c1500103000c002ca0f0701c03004803183c0e90000e03076204 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 419307104 1250 419305854 419305879
    0x1f0b090a0f0e011b0201051e061003090204050408120609040203070b091c0c031515051201090525090204150315120c0614270604170303040605070207080a02 69
    0x14010b40b0751041011040d510f0214540b00c410340240d00c218041201c3d42c0208510355070301300080682c0480c2201e010f041500b500000e0031a18010011046600750b42c03038085403003581d6601060507540203642c01c44200201068102c1041294501d843e03100320300f01d6091500e820907070042500d03202d4602814070440f000044281c00364860007030b903003c00c00748842c004600d6221418401d0500d1210301046590000302c0745c10002422640c0205c1b04491300071542511510315002c200850904e154130002c00701e541b98400392002c1f640a01040310041e400c0c00d643d20400100000c410380c90746064205000052040c030040c031a46100c42d941c024071500c0c3e4200000c03503103a10b50300a9810b8159511444000001d01c2e4400308005e40c410101c82203a4042c0c070b600b2a0340c40131441c5a2418081c007900c02540150601c2002070400501d0014070303c514000c0e00f014a05074807540003803850541c1307038034000169200005110400c051480350742c1e4021072074409092000c0c20702d060151100c40001d8080c2c461110341110 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 419308354 1250 419307104 419307131
    0x92407020a0507030c170304030c090504062304060e0f0304031707050a03030e06100311040902130603060207020f030d081b040e010602010b0111070b070204020c01060909051f0b090a 80
    0x504240d0342e000302c201d501c4203503240381003200b2103014000e29410304e10390b010713510200794000140c605803540151404a5541450700003002400000e005545845d11180c2c0c80c0d81030541c0c4403a42203000c101c40f5102d02c2e540f4260a2202c1540e80a01d00c1012541c02400070004021011056400f505d5100800740c0c207074000140c0840c03103409039400c00f90150245401035800c041c0c00d64044004070800d0400d9a8440d03036200b5549040e1402880080d14030800300c59151030368903280d44904600e9100030010041411210354200480d000b03500100c8140d54001a1403095103054500c007104244210014080d0300180e40005003031400140425400890b203000c0d1410312011a07041c1c4026002c0080310201c02e40e59000001d003e010030200140c0403d510215512032040081001380c1561300e81100d0b940380070202c4c0d080c031001b54850704150f080d0f5560340101040c41d201c24020341082e00c4c00343c801455a0400d05c0c8200440706442c180400115203010805400d0346c81c0c01011950088500c500060600030040340c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 419309604 1250 419308354 419308363
    0x1060f1d0301020f0f1909031a070201111b01050f010b0906031b031e0601080f2a03040b01051318020105071a0723040819081e03060909240702 63
    0x92075107076581c4c0401c1505032901d4410207005035020090000210701500e4400b990981c1c4140000b81c140d0200c00b4004290304080d139070080e00003003c2d01c000511680c200d60360103125000441031288900303080d4022000b1240074042c1c2034000d0388034070340e90545e5450846225070301c2c03140c10a424020b0782e02200040307000607d2103006e906000240e910341da9034a04071110801048005030300621003130203100801c10552080603140d115003c610b40918507916101502503888011100521f0012050035100b40e295202c1c4020354002e51140e020034030554140010414489802201c80b180d951408985025000c485090410340a8080c20055a00d03851400c100b9091202e84020b6000c4040c84414024016480191001d14002c02000d0090350404e5481a1a0301d204070f12504900382c0c0010040511880e00078000702a441c4078104080c80c0003076421504222121660160700c0a01e4040200b009070305281c1d84c40f035070100501d005404890150f450040141025107281c58001d0000c20000307036030500801 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 419310854 1250 419309604 419309617
    0x1401030c1403040c0f1508040303110408100204171203042d1a06040212010b0307030e0d0207030203010b09010b03240616050c0301090308070320070501021201060f1d030102 76
    0x981280c0e0b910303240c14450199410780c4541a51911030b80c00004110380780740d00d001e1a10b1256a12442c0039110b81e241200a81421044610813500c100310028291504012403041c0070703070000c1d015880e646410b43c43c000714040010b9108403a0407030340703205141d07115440c110f03507006502c031040c4d40c05c140038080c520101c01e0180343c0c2c040000c4400107a00c8280306030183c03981140d070400400314a0541c0c8490500c01170b800794403d454040381010005104649203000559030100007450002a07405000b20414030b0300b4500078247c4d0150b0840740c401c1c82036040a0003001540c100070303280c1043c194500803110790103200c020700d202c40c00c2200218140c52a1866850365800f254010941500c440002440362a030080026080303c1a12500302c020481c1e05042c05100319003a01529042c1450341d0303c0c001600a0b115411107ca400c3d00c80360117030380d2540300c104060003405005400040e100c90b95807070b0002c001107060304050180320201e05410301c641e910100aaa00100844040040904440c08640680150f8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 419312104 1250 419310854 419310887
    0x7050409060b0a0618030f150914060606030f06010c0302120415030e0f06010605071415010e0a11091c0f080c070f030210050a0c14010c090f1401030c 66
    0x40c4a02040c002182c001050929049500c0d0704056600c103419110310158400b112102070000104001060280413007405a40c091010140007681101c02070085072500c1008072500384140101c074120180c1042181e90002c41601c0b4140f03541070002201100c2c0340300a1007641003045407074900342014400d1120605410710543c002c0c0d02d964031800c0b4015140640039458002030f00c1d240700f00c0c2e0035000016503000d1100350341d4003408a99090003000c0f1803070341c0580026a00c00e515a01c0352072030044d00700701c2c1c00300503000da0f2200040d55061514015510001500e0200b0190510408104159020307017150420380302100c0081d40c02d107009003100c0505000d480041c1c0024280404102840740150080c10f82c0801c0c03c1c299400c140d110301841c0c140b114140800b941220304104203020950044000f41340b4403015042160342149290740308030700b540a0824401d400e0351074499880800e608191928040c15026000711038450030240c58869a440082a450406444031182200c5d140111594804600e11 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 419313354 1250 419312104 419312111
    0x1d03031e0903092724011e030b01110d030207060b0306090705010f030f020c033601030b040608010e0c010207050f0306160306120309030b0a1406041508011a0a061e080702070504 78
    0xc4c04601c1c245043c2000f882175410002d0054041e175610450b8400000d42200b03000c803404010b207901c101e00030030302400540d040c851500c0490040b201c0c10010710382510040c0d079003d603507030441e490610709035500c9080c40c4d070280c1d001205000c5105004149541074038001c1c6060340702d00c4040202280940103440d0100d034918800640ca44041d10f0210081181d0017520a686460f0708003600c02c0600780350003007400d0551004201084a5942c8243c000f5000800b006002240c03040e1100b455500711848240c80c1c40081d400b8121140041d40c040c0403600080404507828554007052a01103074035540300600c035040148400b60700c0d55945000703501c01005400d000104250081087c0b9010f0011082d41c0402d554105038039002944001c03847c003d040c1d0201e0701060f41e280c1500c07602d05200150030564841c4400400d100e0020524240900c50f051041c038200340703610b00c2b00e003802003800084072141e0007402c100039a640100701203075a2143c448890351074614183c0116562030008074200409504055402801d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 419314604 1250 419313354 419313361
    0x1c020d060909020a0e04031713120c0c09060f09090503120c0a08010f050a050d03090b27040b06120403032004060e0406060f0f02011d03031e09030927 66
    0x140c940c00306219074401d4444c0c0820640384c007a90000420101c0d001000603041003512280400255003240d08906000c44129805901e50389810006600604480001e6110142c2c01d0034070065401100042c80f40103810022075040c070041070040c00d40ea0003500380658961400c102002000c2088a0f440c01585481032a01c3c1080d00085510342e0050081701e0008003003600208100070614020411500001c01c492805464070041c000e1114000000303034213010351403400281039050076005081258a0044144408885401c01022400c6441c5024011031600f100c1400076143c0c401103818920700303180c66400690b100d01e03040713010f80302c410240524620052003807440c3d2200b1802400c2a00c205840d204d0904c3c4e02c0c00c06000452f2840e10601d0b00140069800c0043c0c01d000d107011407a4060030744004143c82c185084040e80b00c0300691480e003196400002045800290307030032403070500c0380000b20012003421f0203504160380340190030015204030400001d80100814042c00b612001c204041703182e0040c80c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 419315854 1250 419314604 419314619
    0xc02030a12080c0901090311040e0607020d090b120103081c060306150e04021008070201021b0c03010b1e04020325020a06050702070302060409151206020c1905031c020d06 75
    0x240011241d901040c02c0300007103141c10000000ba01c1e018581a501c1007001c078075545642c07804842d100c0f034050304207a9038a0f0030841c400041c041c061180586800400b070540748080e004000140c180e1007840c0d030407002e012116442e01c05d00c03641411030382c0200d101d03503c4030b12480020003105420410640c0c90b030700c1d00800000700503550300400c41d0f10110010b085a43c0e5911101f410704200121002917002c2040104040054051580b0980101440c4001403c00f0803c40c0e62102854a40d00c6810055010700800070181c81c090007550307060b6806507030100d1235000300440c030b82102e000c081c2450703c51074008c400120350200d40c90394482c64005d4903180e4040c020003890041d4440e01c8a0005864043c1003030005075041380000b4094003103035400b0300502e241a2800010400800c041e2003c040c80d00b00d40940040e83c01211203801044078010040140d80701500b5070000d180c01c0141e16103441d45444d010710500850000b009955080002002d60308801c0b505400f810020721070760b070262000914016005c203d46 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 419317104 1250 419315854 419315873
    0x9050616030815130c0306050d0803061002010204060906110c040c110705040c1d040912020708010509010b150309070f0b04090509151f0b041401120e060114010c02030a 74
    0x503000c0e8696411688499503a8507081d035480b0400f641012840311000311592030f81c0d03c0b000c01440c003481c0001c1e01ca81c0314000104520204070050340c40302d001000f0b224452910031246010020240001c42c54246880e02c050910340d52031280005000e0403c0124802d10340620000310300b0580108200142a008030001c0c0400350120400403051080d00300100c0c00b81840d110386500c140094590003071051520a0480041495944264225444143c1100040c10310441418566440c1d0041c00741107090031340c2a03003102c40c0246207200780d81c10861501c82c1078680e84105036940c6407001c50b0075945d030f40b41100c035468040e00703501c26184191080c8001a1643c6038102500588018038002c2c02542c403440c812903610071144c2e000301e00b81170000d40801c5183c180012040d8607440d403a20a2001d0755a6030390105c90a41080e400b0700b1010f09442005400f42d81d10000c0380f461144c0d00c5008020101c24201c0445d0358650500600c924000807107100c11250380940111400e8a900504803454443c0916002515 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 419318354 1250 419317104 419317147
    0x7240906141503010603082208060702010e0f06060d0303051e0a0b030d170f0403140c03090a12031e0207091805070e090a080d0209031009050d09080309040c090506 72
    0x510045400e20b0469181c103003d10300480707402c000d54505220580c1c5004504019002040011042c01100015581800e204061181c0301d2900005072010160109504244002140300d44580110041014558402415020300754041c0b5001855940c0d80d14809800e0000138140c0c411401d00c1800c0003207005682e080000710301000c0d0140c0f03d181003115000d640319180d000d00c064a41d203d42c000210703c101c0c120585e9a10501a00c0d10103003590710032051110642c49025401c580f80c000040d00d01c1503007024400d0034014104802650141512500c000300900706500390041e00310240e0010050b020310800044019212500e42004924000311100c010100c041d602114540518800000c02d200f008410612940264014081032901560b07500541c2d40b0030f08000074882e03400e101d20071803601c04001c00000c064600c20001484a42420401e10f4985548070100c00c0000340170301404003c030040252602a4802e49010400c1000301c0781c01d851140441c1c00031034002201003400c040d13035078580541c4a907 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 419319604 1250 419318354 419318371
    0x306020901091e1a090904020411070b0c03040b010b0a050921070902070507120323070c0909060e16030f051002071a10060e06070c030606090609110724090614 70
    0x491903c000b80d0903139409408411684070011100040240c24641c001e0340c0441000e4040d149404000d545180d51001d059840d0301e07503180c0201c100f00c100312544e400c81c1c0c05443c05281c050f041c8004260000c210b40310380510b29006184006800e1075041013021030168021b900030a45401c1074803096140001e411180f03059aa601c03810800148040d034507030000000c030360580d0f07440c2002001070401502c0100d2021080c155050200a00741c00b203244605810090641c88902240c106a90b041420941e5182c10480d02d007a004014007040135220f076403400341102d91055803100c4141e01824800d041a070180f1003924164000100175081100789501c02134401e9407424541940d441d0740d030703200c00c0710001d5001b010081200404442c03414901a03000e0f08446215118181c412626aa40d010594089038800742215466060912050080b405400304c6030301600104c504003003641d154581900d040c941c0c1c09884107500144200c103800c40360802036169811000038480440c0f482d96800d01c0300411160a035 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 419320854 1250 419319604 419319629
    0x6090618060c0c01020709151205102a09051e06070b100302010801080601030f23070e07030c1701030605061203190e01180b030c09090138040306020901091e 69
    0x400004501c14024000091554108e220b810b04032811010300003032a041d111481005902e5140c542d150140d501440d01900341880c49800036840064600010900d440611a00c1503040c400d60311600c0031941da0074209040e140e900c5500101150a80c45100405001c03640050104004810f690b400c41044910030399603c1079580e1f81e041c2440d21004d00b800010100090b007200d68001c42d55500185d40c008108440040b10b160748407215601e8980340b0b510941d200003180003040ac2c0340d505803142e0741d12142d0710305000c02d001c05101040381020301c0500004020581d10030200d1855298014041c138144905400c0302d540c0c0d41010070900011421100c6040002e04044d00b5951355441032406080b410007182008401a0602c3d82c01769441d08000e044ca500c00d002400b00f81501d03510198014001c2c074100307848400321440650716252102405000d8920a600b0000c8501442a030b8000c6404880d0003510046e1103480f8007004850000d45a0300601c2c0800c2c2c0208034034002c6441584400448201c00f9100c1d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 419322104 1250 419320854 419320859
    0x1522051219150b060d0507020606010f050702092206050108190503071205090d03080f0106050a1706010903060608060a0f0e07170f01050106020a0606080c06090618060c0c010207 78
    0x66900d03004101c5184002441c00740010019900c10780c0c02151540c40ca50201d44031074580d02080290300300c0c1984844060b12a401d2045171074050008540100c07003803811546030307105a00c01620510031134000a0082500030000b400286030300290362000d446010202a4803955810050054032081c0607001450244103111916044002d00031050254400091b40c240a00382d00c3d0411262030801254060181c10006180075541d401c0841400d244039449001d02c509081c0e00040910743e058022909100040010200c140e8000b454140c1c89100034440400310b075146401240d4030006540020662400d001c0085003580b0b01040300c51151200e00803c0102034640d00d849001e076105070503000b0071a00040b00600c8044240810400190040012240e004224454480c00c4070b000341d00600c0141c108101e0002000310f98098900105008330003041c0c01d0b150303000028664030840444502c6040000713000c802900384031450303219042d4004e104644a80c40d064810f919080c00400180c010302551002 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 419323354 1250 419322104 419322139
    0x40618050d050d08090303130b09250e090a03140c1c0309053d11040609050a0b040e0105010507050a060911180411011b05011a041415152205 62
    0x1500e21403404000040305101850300c1d00e16814070007800c2c1c0ad1450103403040d10444001d14490481e000242890b02e0a002c614241030382200300400b030000304542e000300000340c0219501116101460400701101681d420f141c18030035142184a840d10704a10007924051042030340c03d50701440020380a5000d4595080f41405c40301c031180d0301c1c00341015100403900f80805140d1a4556404203002e03044200003180401c4400c8501903810540c085000610f15400c18089070030701200d800002c2808010440c1824100fa846441a210502899041001c04100201800b1007040460081c80c0c001408005211260901c0c258404504108600540c0d068400c0c0c1c00c001c0c06041c00e0b41c4100d40007481a168116104c00440300c0c520711288803c16454030b8140c0501040e03080c40740e0385030f6803480140040e41c000741406100c00e544440c00e42d465040b11480c00c20440748078242c40c2e0f41c90131604840c1c22555400d81003800c0e41c540520f01481e80b481c40803102c40c1440702500410041654000c40b16400d80342e00c0d040c3c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 419324604 1250 419323354 419323357
    0x90a0806280203060d0803070c0b09030702120303190c0e0d030801060806010207240c17091c260c030c01091403030c16051903020105151203040618050d050d080903 72
    0x12011781194841d034010f4049644071011310303000202272a00c00103000b40c2d92248811014192000d94058000244140451500e44910800216414003131401d6240c101c0040e120400c1001140c00500c0d200c04c01195000c0c4a1021107543c110000e21101c0982d0450a0003044180e090266401007580ca1010412540c0001050803c46042c20b1900c0c058000341080d40c0e440049001c0c001e001d00070443c0c910b50000c1d0140e0b0500c401031401e01d00d019100d003807090030007003031140b0780d00c10080c8586000100c40c003103008414406061004101005641c400c4540a40050700c40d581c28403405010120341c3c10583c0c3d01c103400600e1030074050300c1c2d50399044112140e07480c0c5912080d9103072003c0314020003129085112207001d60100741d01030001c0e50404883d142070508064100c5c24114010303556481081103140c5400704104600100303441d0400854984041180d9900c114010b540500842e041c1010402d81c1a6003c140540009840c540e0480ad291034115500c6550120080201d03540b0400200c02040020 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 419325854 1250 419324604 419324611
    0x20102070b1605072702090f0d0f03080705120c0702031c090f0b0c07171c030522050705150d0905071d070c02040c02011503030521010e0c090a0806280203 68
    0x1142c03c5c0c140700041d4290009500c086501e980105240301804090342d1600c5420791800e00a06001032030020615004041450003007100781131040030300050f1131301010986203e80c00241e04902d50b64134099400020328080212140b004010710009030401500e9110700782c2d008450b040ca003403440207038039108180d24a000748a0f41c40c81541c84030b0300030011920400b01c03803803840341040217032041d01c0003907030000c810307068012004404280c0381d000703221607440c40107440520001102c0b200b03688107441e655915211051071040a00c6203061102c0f04d400c561601d41107506446801404203c1c41d0402c3c5802034544d1880c2c401c81c1407a41e03034950b00280c81c403131590605126034019a03d8804045066003000001d0001e4100e00f821596501005130419100c1d05108001d50700a4603015201d9510850758070074a07200c0707540d1400d44420203004102440301d40310290341014542e54015158107030b03800490316030f00f6036610060180c8640424058509070f0901940058015540350300c1203200c0c0c90700520b080e0b10040c5c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 419327104 1250 419325854 419325899
    0x527030f090103092f09090c090106142701020d0507030206010608040f05160f05060901020c040e030f0d0903030506100c021e0303180f030106030c090207020102070b160507 76
    0x4121104203507102c0c1c2e11070f0300c0349481003400c1d000301c044c2641100c05c07412401c5070030300c100707415401001601e2800c40c1c82e40e580b000e01d00005113440002140800e003140c5041c400d81c0207000c0c01c02801503003004041c0580e000f0240040b40824203074103220b211030542c101c8080c0203002d8007034100350710581d921800c115000c40e500342c0c0080c4101d910380312080301d80b403e000307109603281303001c2c402c000c80010000e005404044520b0707002c1c180e4890808140c0f001840305035215a200340c1040048000ea42d80202d81c3c140c0054040798002400440314000d1400c0d44604480c102e21000d0001d0301d4102c0551036800384039058025034040141ea51741c0e605003c102032203525040701080722424210014640540841032008001440280026003500420303e9a044201c00c200503c1c1009801c001038140420b2818144004900034804c0c14030359229200d01241c40e003d005e0915400090300c07010359000300548401400070b80d40b0170741d031203901c0600c202c907100c418441281e1900038000c0c0007030741d4420b5082599408005 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 419328354 1250 419327104 419327107
    0x504110306031b0d0c2c011a030402060c0604030917031309050702150c0a02011103010b16170d05060405070e03030307120b10050403030210050411041e0527030f 71
    0x101041c0c034840701181c203140c2d442400c40b110f10001804405c003200041c580703c100b100d00410344140c130006180c40700742c084140e40940801006a2101074103150340a50589400541ea5102c40c000b00344188100201602c451007140240020140e0050901045418945400e2403005460174015224880d17048103d8402c07084050134002d20f41641c0c030458000e142401102c00d040710a42da03441903140d044403856410400824074580c015028002d80081741e4040c403003140b42d58104400c801c2c00d400340d4548050303460707a50304001d810001003400404101c6100ea00503900c0b1075101c2c4004015060883e13045002c1d50030040072030720340380c0510000d214550f0028041c0d415940c0e0304400300d52001c03220601e80310301501c070980c040003a110780401005800155551036070b141d0842c01c0280c0750006118101c11050300e01400c100c0410060802c00b104c0c408100ca01040c440b4220700d202c20850311039800e04992a00d48030900082c6134040348940c0ca640302c0390304c00385024465a46843d84900481c001481d55200 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 419329604 1250 419328354 419328373
    0x809240a0f030b040e07140a0f0e0601110712120f0807110a02040608010e07050d030507080f122806050108131a07030e070e07020a14070816050411030603 68
    0x42803100d00c100d0a624001440209030000a02607510000000c1c1e400d421880301441f4816100048801ca00c600f510074030603c41c640030300d0f8014502c5600c40c1c24440302d00000407840302e81c4100407460080c22000111440701ba100c1e1b640c1c0002a5180404440503601402c06424150091005c2d51003c20b90361075011407541c40d04001d03152000d507402104036034020401030500680d40c511601c40a03050000c0000ac40107120315200d4944081600054444c0d07038646ea0440010741d20000701c03940c003075110403001d4407001c208880e00ca89028201d001d07911624440104072290080f260b0b030140ca64213a1664850180f00c0044090450700280034007030000d1300350b0340060710200b010500a5100c6100707403244080522141030041c0b0010060390658000b0780c440201290800c800c1211102405520260900a00f00301d10082d58071007183e80c000740b241c10300c0d07a6041c0d081d96060013524000c01c0988103a80310184600000c4400e28418000c2500c9103181100344042c03c0c0c80007050381d2041001130014210800c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 419330854 1250 419329604 419329607
    0x3050f070c02120a0302011d06010308041a07020904080a0f140d090515010617071409010807170a06031a100b0f0d060b07020306070c03080a0e15040809240a 69
    0x6403101da041c0c0c1c101402c0784110441d034604024110700d40b8025030000840c0020b0109062440680d4015100298081f030010300c04210920100d800320b8170781ca034103001400187c015820b01400341250295001c002c038030420080c802d103040240080705080e40c51040420010006590410045096000c0500144650352204596070f100044003801581240d4a080c2c42c42120340e54500244c1020000902c207012240d0349603010b0b482c1c035803c074500e41000d0050380c000c11b90b903081d44d0280802103410000c40c40b021810701405071020503107029140b1207200340f41c94480c465001800591004850044020301303030110720004100702d21300a050f08105050907038075180d03002d805c54101c050f4541040314100000d80400c0668810380e0700500c0c00010782074544155004240c20003070024130a105201c111144034002a0340040c10560003041080f0010360038a08006051428150b82c4842c204820288240014000264050031001000b1502130311000b103100a00703010301207848003060f4010024064080c240d03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 419332104 1250 419330854 419330867
    0x60f09100501112119020601051516020d0b1014030304030f0804170c040c020c0906060d090204140406110a0807030b0103021c0606031104081c021c18050103050f07 72
    0x5000e042c045811031002011602d0980c50001ca1805003020001035008640b04021448817648002e070025110641c500404a010340c82145001c401c0510002011301c1ca010500484010042d00901800d007a044035181045240700b068840000034141c1d04c40020b0203403414100300c400260068091400c0a1940d600e6000c042c126890841c0d040c10140000709154920718084860084800d00400c80985503034284000c84640112200840d0854242001d6036200c2d07402a41e08801c0540307589544039442c0f104c440081020340390003035016081096910144191200c01e600850240d40208041c1d41d25401c05039540c8614400600414203440c000380810707000303a206685a420604016240000321204040e0070703800c0503443c80341c00e6030321242032026541c140324070000c8245600040d0300d4181004201d03503132600441154140d8103d0382a2101015100b0b10081e40e0000800e940401c0320001d0701070143c4501d82006403454143c240b04000030742c07580310f8021280262549501e0700b07221346600d00d00303e414 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 419333354 1250 419332104 419332127
    0x17330a090c020a021c1b12150f390804060e0a1707060b01021b091e0c03040b07050a0e0405060a0e0702030c0708010b1f030e0a0308060f09100501 64
    0x194040c43c00c1c0c140250311290308149003103080c45915514104140740036116401c54012407402d5151920081c0071014010741140d10580e0400382d14651945030440d0500680070290b000c0c1c0d18a41401c0804103a40000311a0601403089040101c500c80c02d8100d0070070381c29801c0a180790001d00e88101041c04911554020000126071005507150341041d41c80342d40c00c20003140c0c0a00d44501c2d0008403d01400103a01c207690456000b440a8011004400e480062420360a01d0f0b040c410460440480d4185140411140b501c03203260080000f2481d0007809018030303800c200ea095810302c14100029010520500844111440c5903c0342504681010144402014010240ea0b01722201d440c01050751480c004141d07109403295802141d44a19003100d00e42011615840b00341d603a070402c0242896981c7c1c200112041c0250503139480442d0080100445c06004d0114100c00b840c040d081c540000d0503072000586104031410b80b04080c10700050002d20015010403126520305501440c8103000c25031060582042 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 419334604 1250 419333354 419333357
    0xc0b030f0c1308060c0705010b090103031e1101050c1c050606040317091e0a050105090306070806031e160e15060f12010f03120203181017330a090c 65
    0x840c585603c406031501000b540c000110328804101002000800d0141820800c0281d400c1c1130325503d1550060311002c40f10003000d0020641d1845070203803d1080003d0400c03c142a4000d125600309200045840d601c464400c3c9051a001003d003d0b00d11114002c00d40181409003042e46018030f56100d085d602440c40742c201780200d800300501c0005695850300c10480074a4030b034010708008100307001c04c03451140590049041c41030611011030990b8002c14a40d501100da814a811250358000000b410f0050f40312003040e184000c01a000d18580c40003640c15060741e41c2c440544056603c40c0c2041c24060011034484842d40b942c460b94251904215000c0d080340541060b02c0780c10f002c8111128040d145090300101062840303c1c00400610410a2103481c034010a03001031231070300b10080d030b0616218410b0710f9810300880701c103242104228400c0507402101c0d141d081942c1114240300000010100200e40308400c003401e8035545102d01c0c0400d445500782080010f191040c5035181c1020b82020b06a6105000d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 419335854 1250 419334604 419334637
    0x100501020f1f020708210609011a0d020711060d1b08150d0c120b1e07050706050408040b0301031b091104060c0602090405160f02070e040f140304080106030c0b030f0c 73
    0x404001d85800c844401b105910b00004661804074107112103884144c0c042e50f90200013000c508030036a9140f0450314086001800503a54406031b003841840c01070007009441e0071220020700c81020307036806e6001000c2c000d0191050504000c484808a91400c0180c444203205111105000070615010150107819403240f0120890103a451080b5007110307240c940c1c2602d6001022007000825000480800100c20001c500200313a0300700341c0350040a074010f040c0c00516040e41ca201140500c4503070816580140603d080d000c1d9a0740c0c5030700d003d60020554240b000704007180303c5000306070304070310b401411b07400015001400d0415240400c2103e14800c84002514880c0e030070401e8161030b46480c0600740c4640b400044010304855103000040c0b107a11740800000c03c40d00440024484d11045038065908150000c8002c01c4284842c1004a03c3c0c16015100e1801807000140000d94040103400c0241264000d01e03208094940c0d03564518941d100803a44283c25400d08070020b110826001c01a0820a03800e61000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 419337104 1250 419335854 419335867
    0xe071103040803040603060e041a040302010b0415090e0606130f0f0e06010602062203080c1303051e031201051207030f03030515040b09150612100501020f1f020708 72
    0x60441c0e10540007000c1d82c1d000010140005a018012207000b411007000c00c441d00d2420743c40f00d202010709034061107200131105d404541418400d40000544100007001000741b4400010583e12a1440c0e204201c14642400300d00400c03027001141e0744d880344c0006801600ea100c0c90440c0d1400400409000c00590740d51085000c07102100c5114180003030401c0d0000309819410460701a181c0740700103000308041c0c24002c2d0018400016541080259541800d0445d181d03260f01c1403410403400b40303480c0c1920f002c0b880030b000002c4c0400011600c41c0d024141490821001c0c02181303003034036449240e0691024401d294010446410400c00c5041000e940000360307907805843c0e6880d02d21403200c41e282a00001e03100e005001d0007a40e040c100b0760066004480c20814684101c001c030708141801000e02d40c0c03224040d0480350650f00c42d00c0c01c9854884405201500314605084d80c0410107115004003401485910742c040688940040d65003a50484200e41c2c0c421200b20360584d0b03002c0c1d031080c0422142c54a050000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 419338354 1250 419337104 419337137
    0x18090114010905010e13150f1e09030306050d050703020f010504030206030a1a0d0f0f080d0204061101050601081b210109050a1b050702040e0c03030a0807031a0a0e07 73
    0x1d0103409145804a01545003d1131390320080d00192280c500118246849000900a03c0e1040003038030040d100400d850f0503003010000145003540d0f059404100007600280214415880107032007901c00d440c02c000b0035071038070180320006569401c000c00795404000c00340b0151604480042d1002c1051401034039007512a03020440b150000c0e9454130000c0d0b00c3d0060306c6c10424101d10a06a51042034807083c6c40d15059440f80004540040d1002d005212140074000a02c40c030f03541102c3c048000d4002c150b50f9203035103103001445250214420140f551820011400c11b40c89030114600a0510400807800d13480789000c0c107040c660142209030071103803403030740d0741c22403041032200d9980205480500044c0b07500d0b0220f80001941c01c0b052201098401182d803120610350808140c41c0d42c140c05403030001d0400c0101c00b103e890318076007103209a0b240c4408202d1880c48ac1c0e0007500309109110b2960f013808400c40c0e01c0c407100010b217940c0c4165a401201f114090160100b1024455480100303450704000c4280000304 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 419339604 1250 419338354 419338391
    0xb090c0a1806120b01141f18080102160501050a020408060f0c071a06101e05070c030b0109021b0d05041505160308160509090612070806240906180901 66
    0xc003220764013205001080030303c011040c250100041921140c0002c0807001c190a40d0b0000074492906003e4420303071500d468041c9035540000f40068100071940c0b107020710300c20724000e154000125215820580064641c080c0c5000741d13021114105c1c000c2400f038a460f04400140003006102000c0701d41c00307200103004516004076041d22007224040506046c01c0142c14802080c004003008800c0c480d4010b484000e01084440c420044a902d280c041d485210724541210b8803a0315038406054160707030714008503d40d15283d0082051206201c12017140540031060300b6145c036000c80b400d00c045032060008000622000981180050140c0303001450310308070284040d02450b002c14190006410300c4c04214041c5841c0140c841070020300c2c00d015041c2180240044c902c4503000385000d0084c40355503400d43c61110300f040500f01420490064403840d280054807100600260031441c044014030844600030381c14508201401003c014081140c462201ca070002c6400d80c3c05403942d401991780e100380042c13102c1c0700d65 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 419340854 1250 419339604 419339639
    0x20121050a020d0b04020c0706030e0f0f010203010f050a0f0501200a05060f090102072a08030a180603050f06010309050705040c0e10080f0106080408250b090c0a1806 73
    0x300010703207440400c3c00030001c89000a81c80c60085204004460040400060481c02c0b2201840e01080d00d41c11072500a0501c0340707402510b8001d00c661100908a080d06402540c166444007c1a03850140e9500c10040b00c4c0c26284141600410061340500855104201c8100b103210410803045241030600803052a0007202c0c032040e281a0440d405104012415402e070071b410103070302d01c000d40c2008166120366045240c0401c0c04e90781107040781155950070721040c102400910110064039114040c0440141c0982020940040700404894003c281340c0e000c3e20405024414903072180c00d640d030780c5200550007005100015141445150781c0020307180d645001d52004040f1681c0e900c9980204503081c02480b0042d12005c1080c45a800e0400c00000c2034418114110b419901d08180940c0315420075181c0c51040040f2122050060301c0c8444c03058121041c440030306c0380f1645860042e5a12401041d1b20b03400301c886003540c0071022101c20442481104a03044400030588400900302c3d40d1212165001c0b0020b1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 419342104 1250 419340854 419340871
    0x30712020412080706060e010503151503010203091501061d041515020a0c090507021906180305040e2401030e030408010c03200307020604030c0f02030d0914060f0702012105 76
    0xd01d0390400c14031b8018032006001031030001d40e281d41032000207070710345000a1481110860b00800100c289002c081082802da1002d002150789080c26040c50383c40c0d000148400801c0c211050000a0903486820050444031014500b41101c0041c5e0701000090b119122400240b0240205d01164994a84a40c1000071045030020000b8140038a8034040109081e40620481c520746020000404c0d004208900300c00d0440c90040210502498024020305403080c900791490040c210f86010113411600610a480d1045100e000581c3c806030b010401c1000c5030b03800b0307d103100c1c0e030f080c81c54240d4040c1d0020700414410310140c07401c003615222440e08490000411000290722050010429014000840080c1c05071010351451441c194401968070301f0064001020001204c50040034170400200d60440103500805650542085120060101c101400744600c0b03100c1444408095240070b404489001802035050342c141003191b001507801500410f0803100c0d11102d9440030440110034440c0703922900e0709 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 419343354 1250 419342104 419342107
    0x1260709050307080c090103030503071119110d05070605090a03140a0c053f010906150603061214120c030c06010f0321050904180212030a0503071202041208 69
    0x400c0200761404a490313104200c07980080d00341c0ca07199140c1a1751941542c0d05410259501d8031004011282c0d40c41150007912140103280c18040b840640d150700c240c0236800f408140c401c3c09176820410103074007010080100107503c00c0b5010480701c1d0084025160300507001b8214606141c0c0d94950007031640010301c1c203500603001820240d041020074640407028180c02c0d100801c02d644100c00007800d40350418800d41c1007508810b002c0500842084014600445070030003400310340c51900d40600034110061021a200200010115440344644605000c40b10f2000d031045008509132140400500c041746041103034051010803a150707415000040401105100c000c50b44c400869000b6400c00106801144806c5003001041000c250000c0030031400d610b90341c01c9883c000b850000b05403241d100f011140ca40060800c142038103410120071241c1c0d034484c025151120141c81c0484442e03120312910311a58081072040c030104032410300c240410107450031445030051030aa192603140c044850240c0049403074040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 419344604 1250 419343354 419343359
    0x40b04021f090302030d11030f090d4107050603040204020d06060816021504121116030c050603040206070b1f0b070516150e0f0a090912080c030601260709 68
    0x80402003055051880c0c40c003000c4041c1f00010390fa17207a1080e079005901c0d0920104020115581c2d0325540000c281d0300039940340e0f90001403031101038207159168148400d04400344081070641c3c00c000102d4062921200502442414842080110f4002910a0741c2066080c0080c20509402c0d01c41c20000e022552944020340c60048510905070784840c90450440d00f00111340c200360040f141803160400d0740701c02c85452558040c04100c1e440140c41a03600007038820410415681040d40d88500f0075a409000441c00054840090001c144801d640094005900f0012903012400c21500140c005840b604410000d0340900b200b580d040010b5049142e480d500000d403101080020029005845440c011a8110904d003e4030340c00c1d41c07405d07440044103000c03156030140e1040d9541400c80c80406402403800300745503256502d40d0300810086004844007551800c55040003401070486500c1003400c05a282d00c5c40d46e4020045030039060700130b1498840001d4411420100d6422100d013031051080381e072003803441407 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 419345854 1250 419344604 419344609
    0x3160e040e0715020a030807050a020102070b0c1e031b0c030f0f030a0506030c0d03121409100c02030f090d080c0f06090c010912060e0a0203030d0b010f09080303040b04021f090302 79
    0x1100c214070300f81994000300c40c810009400c4600c8030362090b15410402d40303031050034600740c1c064404c10300000c2407000b4036810448804200406800303244646590500c4120300d0002861081c8400e9a03492078040e011800f54040154017401007480004441c20341e130608a200060143c940c00c00e81d01d84642402c04010041c00c0c07a0309201e8640c0c082c03011402000b03445401008198444810007015007000f185035644040404150400c2c01c0305040303100003500b24688000903039102e02140c0d0380444201d00780980d01c1160303032001003550316070300002d00700318503180390a01040b205180300c000465401c4014440ca100ca914240130040380360090348047c014515007404542e083c01c0024030b4040c140320026400740a03104414105264203035100c0400505101c41d030401618007040444000d5140c8400146002c8416031900401c4020000780c8500824082d0340d182550804014062180c0660048c00081c0100b44400c020365041030010b41180c200790b004a4400d40c0034150349030f0741c401240e14058208110b0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 419347104 1250 419345854 419345879
    0x20c1503040b10060e15091011010f02040b030114010314040b06090907120b040c03020306010305070e060d2d0204111e03100512073c030803160e040e07 67
    0xb03200190702c60303a07092038006056010079140646c091451400643c81e81c51951045850002004040d0020b4280c0341c0c900038190010100d503400741d0f500300031205c2d400d00180d000fa030302940e8a03120307994156800c002110381141030800d81a8101070b1140c00718582400e055003400c1c0900d002d0300b87c00780180b40c590284050008050141802d80d4000c2508204641010702e201207500e601044e40c074081d88480c00e0980310019190400f940c5402124000400c2010016200d800c032040c100c501c40301917480c941041060f0344051806041c90706000c030729440b100038280e80c000001c0040c0b1400700590642c6d0300440c048490f402c041c0f45450500003045129020fa041030b504007030300300418092440c40c240c604880c0314940c40c403400c1e0050040c1c001c80c40c4c0d0100c0600802d809011800004079450b01070140c0f42c4060320307200c145d4000030f21420213102e190030b00050111050380e800c03e20451642c0c96031040c140d0000044050902040140c42ca42c008550700c80c095003465808440c01401d500c0d00b0241c00c2c4800 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 419348354 1250 419347104 419347111
    0x15032310110a231c06050307090c0207080c0906060714060a0c12020301030c0306090309230906030a050601140f04150305060c07110f130207060624120c020c1503040b 73
    0x843c4015156000c030b66000d0101c542c1001d401c1450b906164000078044040c11968001035814000d03840d01103148805a4041d58028107264200d0b1541c650722291903450311300340e0481d070703820a00b44000190316042c21402403620610410389003c0d0035051000c0c250a114044c0c0d403284005032200091405158080c074000d401d094400c10861071540742d50742e00355043c1c07002d00c401405a511036003160203050180c1854001020504907180000000c488500c1c4800c0c0203200309846082a03001185003800c1c0064034040e09588070000f0940703a4241000c3c030000b00d1040d1450343d4000b1803a0340010032a207680c010f004240c0024440148190b04504c0c100c1d00340100200240703486202484000041918454003000b05541034403460004401100442c9000c1c002c8050f143c0c41d5800010107404120349580141c0c122110301d001101407500c0208001c024030280c08c0c0c84800a004440c105150000da0b500948412810f801202c1481c081c0340003003a81d003001507042c3c1c00705400200812041c40140d00f40180d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 419349604 1250 419348354 419348387
    0x50906040201032412020d1203020304050d0306060f080901060b16050c2407050309091e01060f09090e03190906180608070815090a090615032310110a 66
    0x2102c911401d0b00f100b004524482e40d4002c0d05c0640c510029907c500b04030780003444d0400b111f240300e40e00c1417002070040e5105480488452007004440342046119100d50390079650305075a60845042080c000b180c6410300900945400c0d540d42a0002c1d43c102440d00034502a5030381c0c1030a2501020508140b4244000242d005024400510f40d11b40c900c0d0403a0003d0000881480602c1d440b078006060013451030041002e001e41000d480c00038041e03240c400c0c42c400414a100036010404030b03a02c2e00c4c412280700d42280d1310140802d122400034010011640c11904e10302e00701100301c9081080103000c2e00082c12101904e01c003c03400c9030300180103031a886a0a10000c007a40101509201e00e0080e009050440c020014810881c1640c00b040500d4002203044d40e889200518021050801c1c2e0001c000a240c0403600701e44071481c1c0100780680c0c01c900640365049940000201d010f444d1900c4580f003980c1c0c003800b0310341550300034885620a00c1007c0d00c2243c8100c0035502a8030344a1000981c050044c4901d11403055 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 419350854 1250 419349604 419349641
    0x62b0f0e0105131e0c08010c0504140a0b18030307080f04060f0c150c1110150e1e04050a050f160e090c0f040b03030301080303071e020309010c0f020405090604020103 73
    0x40c003240813402c4000144490040d8003101c00d00e9800c0005002c0d000e41c11102c565420096544c10096120700680b054400c030b406140320340988002080901055445818802003052100d0708040b030f030070741303c500030b000020b000d4901d80407203540c03911495440040d0b111105c00b4041020310641d40d00c052480302c950001d00f4004001449616200c02c190190711820303404544524043c589a482200d2440e2000c8108007201d800380b4a40070380744040c158a45080400041d03048001484010850340c407800b40c96007031071071600f10740c0703030507117606e96850061040c1c809128011000e000100c0c05c002080d00000400080e142d145507414004e082c0c0075140d13202660441062040c40a10240858402075140e4101d65140f507041e082404900508603540d005c644c5408007000006041038040300071441004e11b65554820404950200c044c181358402e1068010381c8244804001540241c001003030550250800700c141c01c81550014064075401c0f6858022030b0080002d0004550b058043c1c800115001080350 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 419352104 1250 419350854 419350891
    0x90228080712080724091401060f0b0901021501120c0b0702211f02180102011b0807090e0114031612080319061e0b09062b0f0e0105 58
    0x2202d4803a0041d4003901410f800522070040051691103aa80b01890800c000b03040f090000c0c0f050010003043c401031b254003c407a195131042c41d00600c00c00d029030f03501c01c0791100741d5400c1403011200b80d000390599905500c00d682203000310200d414100342c020700784680d02038120703811071030a0003040380c0c185d00c0f03079050309403d010141c0180d40301000c0310340800c0b65880000c41d4403031504d0710b2445c0c5140e081080120814403003c0000c400c4454005003900b1521048007000c440800004900301c5481f00030300981902c00080e502e80d0180f080200381c0c1c02541c070f494105042c1d5202c10b401600040b007a40000600149101954802d003801e10800400e240e05901c0131140c189040c0301541d1111240300c0c01411408000001401034100401c60322405014010401c031030342d19070400c2001420341c0c910002910f198190006044407140d1304562032400e02414140c10f0242c0c410010754500e582003040680e58143c82c05440f17804109104650072051001d2001c203041020054041c02c562001d0b1610f1648050005030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 419353354 1250 419352104 419352119
    0xc04080d09060c0b07020c04050a1a03030304080304080d150611011a0f0d03020a0606030f150501060212070303091502041a090603220506010e010e090f0601050f040902280807 77
    0x41203290002454404c07907540c2c220132406d007803a024031280e0003407400c4140224001280d0001d107a4141c000f00c3c103c2542a040c080640c1d07070208403001407251008000007000201c2c0f00c405002034a83c0303060007154140040c0c069504521590300300e4400920451000385201c0400d0240030103010040f15940c910302c51340e07004182e0404602505501075940401c14504061003084180400d6800c11020051240c403440c100300410580d160030b83d00b032000882d507030b4940c40c0b680c442c8a040700c600c0c0d0018a908500d09454220903000058281c05047d40d91003110b000c10b54410607400180010716005035100d0410022856400400782540180042407058900030f032980000c4031340044d528810b013043c0e0100800d0708942e02e500201e00a02c00e0190301300006201d602e0340501c1d8103940c0d0300c59040c00300fa515805d04a503100280d05003010b042d40800010071440c1014890072002d0f00c0013a201141180340c5801140c00c42d411541071421004207880301d402c0c02002d08180d2000341c00d160014240f200d150010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 419354604 1250 419353354 419353367
    0x30e16031b2c0606070f0507030203072102011421010905090309060f070602040510020a061d06040210050f1303050d030605030318031c03020904050708090a030809010b090c04080d0906 81
    0xc100d4111080200801c03104d07600ca0080d035017915800400e81004084600c0c0c4180c8132110340c801280203120325480410405d026a114501c40c00c40303d0003440203130340b2a03001119080361000c95804171400c2040440042c540381e42841240ca0310595411800f9450a00c0070382c100c03800100009503681041c0110101a514881111030701040700d101180c82e801c090070080000d10444d03001d598007a20380400c2d030842c0e54011a416016601502c0d0800144048641c1a00304400004030020a80c110070006001850441c1c0d611600da440d500d0006d04004007041d546c5201e0b4032684000c045501713030440c208200b00040107004407448030703460284002e03458900440d036240219444103040e04001d90000c4400c0c0c8040002140d4896070b94100d46185044010290080d407103411402d0040307060100045078070303010b00b00260294032080c0042180c002d15440c1160310042c06440c01602c3c1d500d0301d018203c03079650102e00a02030141c0e0791180b41d440340341c158010303d0008003500c807005004043d6420080300c0d40000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 419355854 1250 419354604 419354669
    0x11010e03030a030b120f0609060a09020d0206210a0e06060415060f0e090103111c050c011202070203011b09090c0207050111031615060b040312030e16031b 68
    0x3d022a02d001e1040010344414085020002c151040c3c440700b05584000203031041c00340b60502c0036510a40c03200000c02c030668100ba00040d4000048481850044c10500020549400b42010450b001c40304a50302621401058071400361042d265142921081d409120b06508104121010460506001484130200d61244500d80601134036940605405006010b6080c0541d4014020031a96842c0c1c03500040380000401903900070003100c4042c540d0001500c1d0040d4420340c0290040c9041c2900100440e90241c95136044040e440d020b00000c001628240191900a48038103000714080c1e5514600600111096114084a600b414035500c0c03015000300d1242d041e01c1d020320b400f542d204164892145944140d50050300841034030004042403165014900c1c1804c0c011034000d00415658090740d41d1603010381d01005d801200302d070407071511450107a8405442649140191000c4600145900081c0c094913230003603a100d4014034006210305012a1764101401c405400c1c4000c0c80e030211000ca00410300d61 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 419357104 1250 419355854 419355857
    0xd02120c030c0d0b0f130f12110331080109060504020f0117010302060904140f04020310020f09191208070c0e07020303060411040803040902130f030f060216060c0c11010e03030a 78
    0x1040072410468140c600c0081d0315802156131f020a5aa07807420380448070310032040346d0003c1e2040c4028481c05c4004011071b1403e00e12103800c802c001c02d01d080082c00010108405401c803141003c0c0000d0700c034200b805070f07021980c01040b00046900c0c06005201200c016003c08a04000c030070260207a00b061429401c0d411341e0b8040c0c82c8151200d0380400814011b101a2401c44001405401041034a40081d01c000c0e20881c4250141e80403280c248500c031050b4000e00e401c4114191050003042c1141c100b00c00c3c84000c8a0510442004056540c030742c0050b21500d0950aa03050440003c2070300038424490300c00001000f100b41d105680e480d007084002d48030302024054500c21341d00c130401400301c61404000e1710301406054051b01c0da215030310f80501e0000c0d03202286c140248210040001045080e0b101c07007c0072603810002c40292000d280e030f10300c0020b500841d201800e00c05e83e03440703650210710f46100b401c0c4c001c60079842d01c402d10705090034102c10364518440941d0400644001410300e5440c007001751440305985 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 419358354 1250 419357104 419357131
    0x3040f03140c0118030b0406092a0503010c05040501120605100f03050c0708040e040c150c020108100b070f0602070b0a141311010e010311030906040b0106030606050a0e0d02120c030c0d0b 82
    0xb41d19124000d0803c0c28400303404080307164010440320010304050b248008ad8106d91140e40d0741d944050500780c80c68494008003045c41400104a1540107480c1281c269403030700300c0022881e4840780083e0421550725212400900707440d41c000b40907038240c411a90044103442000e030402842c1d6541c034050344994007a4200c10090314012900f0040c50b8028000a00000400710f00c03c0c01e120f60004000d01200c50040c0c2c00985000c020a04880c03c64400400341c0d180c0c0d04106241c601152641406100740640880f03d490307080051902060380070700c0182c00780b01102004102020305103454a40b810f07001e030400c10303a031842c0c0345c000300000d22540d03403500d00c80400e00f0f0440301520b1035030047c2c001340881d2290380f0254000000300104c60710041800d902c11446041a1000e42c1d8940200702d0403605140242408680100039034020140030740501c4455400040118039852040c0e40411a44020901d00c5000c6500c42c050b001d48070703d028480e1400b44403055803016001500790311009100040a41581840305c1d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 419359604 1250 419358354 419358361
    0xf0603020906130e09010b0105270109090c05071401150303111603111f080106050d02161104050702031204020d080c190302120a0c031103040f03140c0118030b 70
    0x10b50074241d900c210441c2d1490f071103495489245002d82001104da0700b541d9481c0500b0502c15601440c00d40d42d4440d2102d1803400d01407032405807400580c03080d5484a0602906041c00141035065000c2c44041c80329075951962542940c0c50031103600000801c0460032641069036142c0b01c17459409990040b203405180411200901003552410540e0b07095542c41149903909010041c01360324a00c41c1c09016098400c0d402c5100e5000042426004100c08100000e07003100040200b24464405000074408030712005260010391078179100c8090807030700c08603520304095011a00614061084941c4094140055442c00d091300b810084c0702e0b140240700034481d418645000e002c2c0265542a500f01841a0040f0341d070b0581c0e1500f20f21000346070220110014451030f00358074400c00c5854103030f03441c0350740039251820403003c1c0e070fa01602c0001001076080143e21080c0000100c900c103162030400203501030034080150150070129175003024488440c06040c0540d051040d0540c000c0d5602c0300d42100d8110031880c01544 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 419360854 1250 419359604 419359609
    0xa0b03060f011202070f110a12030305190504030e010210020a051605070803070f050708010204060e042d0606111c05030a0b0607082505060a09020d05060115080c040f06030209 77
    0x3c03e4007003494429440483c02c030080000c00c82400e039105004200600b6001c40303c00c10048607203c2070154010980c1550003240000f0f0003504400d8000c1101c1408600900401035507404440341203070142c000494401703004410356014007448581060005065140c1240c066000d070603885440808806100c400455005020081c03182c94058034001041d80d0756805542003100800100c007001b950140261070001928400500c2141c088844649640b00d25048440800c8010078202441504140d40e111152004051043e030050300c0c01880140060910706100c401480e404a5036203a203121780c0b0528119880082c070103000803072010107140c4541d480c3c0d40d180c0700c240500501801300b0740000f804900307c4104080310f0080c101d01024004030070035510103d074149140070010100139003a50400c101084400d50281c004880d01c41c0094503a140801030340da00c507483c08409900052540c1c0c3d042001c041f05640c0407011076086011840d149081c503040c014040f09503201d610609080c50390010701f00c00307140c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 419362104 1250 419360854 419360867
    0x4150f05010c080c030f1b06010302030606010c020619050d180b0406150b040f030201030f150e100806090c03061305070e131203060e180606090c0c030a020d08060a0b03060f01 77
    0x48440c1025242c441690b151018016000224461f4640c490410810120000001d08074100c0e80c000300103284503101d081c0107440c102c80ca02010b82c2c11440402c4000d940498005011071082c0c0c40d03541300c1c0d99401d009050a001c85203071151038851044117101c0e400103d00100c82c030b103421070b401190018038144000b04555440c000f03544410140440801c0002d0b00d1000740c8500c20481e8000e8a0130b000c1c80c044660003002301d40b2414540c2c0c01100c5941c00610000000811041d800200c200c000c462103070705c032010305141070800c41c0c02e50340551010b810503015080522145070801d0032a0348140d40307840d03503644842c2c940c0f041d801408440009a0b00003549000c4001022130215001304d40704450080110005002e003206000e0f241c9070000c03071400319000c1d41c0d050b4000b0390b90441e00030150405440304800c1012603c00600100e03400ea00a2114500b603800c01c1c0018084425103400419448024003405814044014550f500c5a181d0b00810442c0c01c1c191000c50f9030200048401e009692102d0300142e412 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 419363354 1250 419362104 419362117
    0x507060b0a0e0f060a090b030a03030b0622090b030c1807020a14160b160b0606130b040612020a052d0c070e06150a081e04060203010504150f05010c08 66
    0x100030320083c4034080724580070070b030b00810301a20510340d015202c04001055401c1040d0090b0140d0180f01c2d0f40340840d00c281c0c0250b07625003006012900e0502c030800842c1c101c803c501e080d046860181502082460490702c00c0c4800c014040e400340c8a84855040000c000078504070050701481e03003940005808034400e2201000b079551140310308000e8005454442d540d1582c00c110307603005035190f1101283c500b075040d041e5120402c1e1308070320f518a8041603a072203240c207401a056a070040c0051241042081c0f010305040050a110302d01075490780e00e0000000c000314090700e00e16150364410400044041d0f44807049a802c81c1214220201505403120250381e000c207203200b40c529101d4080344190030250007141000440c0e16040c5c0c040300b251240803c00c00f14501c00e00310f003005120b003003020405050040c03c61070345c4465034108078030340b000321a0744662900004035001c40d0f0003580040140b103240703000d104000031100701d10710b0709200c14100500c90001c00da03035000b21410b0103440404501006140e4044412 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 419364604 1250 419363354 419363369
    0xd0b040e0d200109030305070f031401170114040305130e01050f090402012006090d05040e01031209120609120e09011a0c010609060317030f070f0909090317010503030a0507060b0a 79
    0x2410361820020020401628600c0c0016200104000702c2440b80c0078200b0b841c40380c1c3d07040d032500e0b0b407911370381020f81040700301e50300c131207540320b5484075002c41038203104500c180d010341c8a1980c2d826a00c40154012116508220600c0042c0c03001849180c4810300722408214080e03a019405488500040e24403540c0c3d00004a00601189401170301440003048103402a40344104940c09010900f07026507417030259014040d00003603003100404c003040300c800e20a2070304102420301800039a1103080f403210002009000340c9078a5190f132074507006c100600c442c4902c5641180f4140c1c1403840c8034400030703150880610032520340d400c1c818400c40f9a0f020b1102100d004400410007042441e43d91114075010345603610081c0c44555801d006121011611021a4400c42c03c00c40e221095580c0e1007070554040c902d65082030708122607840c0c04542c9502c0d9200703030702402d4029282e030040c8410100450a0011050300803c3c003a4006003c50240780e40c10005454806030701131300100d184000c40c404a40044500d41c840e10 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 419365854 1250 419364604 419364611
    0x12030f020a031d0703020112050411060a0816050301080d123c0c090303110307021e0907020f070504020313050a0c06081303090b2109030d0b040e0d2001 67
    0x781c1141d015401030600d40300d240f801000c0c644026030a9a03c0c0d0394603210203400704030000340480d180c0d8000c1d48902c1e8042c0c440d03c0c0f15012140024007094036134005c944004003050424052008110380103c00c89180c40191034845d15641c1001c910988a1a26298881c244085500c0520b03840f01160805100c82c4850060024100840503805910800194141404540e81c4010262140890254040300c0881c0c0d00c80b040c0750b07465941c0c22071702d60b440c1d000c2c0501c1e140801d000540060f0380d071680403600c1115038500c1c1d20101000a0800401a001400000c15548803c10501014002103085002c42d00215001600e03540d51080d0035140d0300b0000300050240c0100d90340c04040024001c1e001e0300341c0301c55581c1d0090320b954001148603420800900034000c40e202e220100402d00c5442e000f4800301005042282404100300003c01c25080159403000d4a03410218100f880342d8190f2003a1140b03228211804c1c0210700300310f500e16403280504800c0300200035000c1d8104a042e1010060f2142400e540c00081 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 419367104 1250 419365854 419365867
    0x204021e22272912030403111c0f0b0a0e0a0c090f090204140702150c040e0c22061103210c0c03030109060306062403020c0f0f0d02010501080f070312030f02 69
    0x2541c60404200030310b0701c105a441c2c4003030135814002003543c0640340d010b130100945a00c04420001d09600340f5038070080d40c2c4024005000010303002c3c0300e109141032250044030900c0c107002c46010195075269403640b01c240d1046064002260601404a08031a1000000900107030840c1d02d0002030071155001940060034075481135020361103001c05512038140d039400d50300079944c82141800d440d0001d8400303201c0c44005100a004021121548540125000740d02c20f00c0c0100801c4031440c0700303950742b4911050340303400710702004001d41005082c6012190746000d5841d02d6488140403150518021041e480102c90000169100b18001d00310383c8400c00c40000c4a48035a51140d6010141900d80022101301d814002c0004035422000415200c864225055014507100003400700d000b5000841102914421803000d848208010702201c00b6508290307028010403009800042d0965a041e4440700c11503200e209112200310300480e860064071340c0700c07103c0821800c0001049000d08441908904c08a10000c0c10 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 419368354 1250 419367104 419367161
    0x4150c17091516090512070b30070801141804081e09150f030723040b0c120304020d081e0f090a05011404030f0204021e2227 55
    0x841e40d014000d41c4c4003248103885000380119039000c20911200c4d98401e500901480803008060026080d486071880d48040502e08400447d00c50b010b120926084070006010106510188070741c0500340036a03081c20203003c607c02081010347c1c00c1503a42e0140000102280401c02800b0841d4400c5851300f000380e400c40c0c000d0301d809102d80d11030f1502c030380704420900402d8640300c400e1003a560400c0c0c400c402c480c00c3d40c0e20314105840040401c98401441e140e842c440e8035041800001030809400740e4601c40e615011001c04440c40c1c06016030407034150760424010400140e40301c08510340070b25804000280c903004c4070655040c04c01c007980d000c03040000300840c130b00203100400406800380010841d407100c0c1507036a0314010350742c2e039405400303000c80c80004010034030200d000100a048043d1019200503e01903000b000d0001d402920303543c550170410700240c03940c660455000d0140031040800200e281140c07070b005010304480602c038018840c5480c92120980351800f1540070310440c0205154000301e6544030440c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 419369604 1250 419368354 419368381
    0x50f0f0f03041523220c0605040521030405150c0d03050603151005060a0513030318080c01081303181503200901030e1009060504150c170915 62
    0x440f083c80d14010f00c4011800400f1507040700d12044030820302468996150701d45d4a010015510f4400d03040d1310f8102c40c00101084c0082000705019a1400e40303a40c24901041410ba284140d00100b0088100038030b409402c004c400c60381140c1c030031141801240c1003052800c065010f1ba0200501d54001c17041544022038140e0000ea120307200480944440241015041c40080000c0d5172060100c44c03040c40902040c1400307801000509a1820294184041029a070441d82559041207000079441c2c0314905184074025100f03c060130481000e0718600c0500c0300004d0000780d000b007101c040c10f80701614140c1494001d101c10b200c91180d44500d4112243c0380c0e80c001c0c05d51100740440da8000303480c1c54540c0020602810b0308040d21044140c02a1900002000460280000c070b00241310500410070655111081c910480042d148180b40104040c605420b020102c00d08200007242100d04003c20300d0169540210740503501d10015010081c5070300d80309000c0740740c02d110045c1c00c4449042c000a019501c1c03200e04 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 419370854 1250 419369604 419369633
    0xa0f03081e03100e070c05071509150e0915040e010b130c020712061d0d030f02040e1801110f07060e070f030605041b0b090a050f01050f0f0f0304 64
    0x404107200110361070150503503200488405504040c21942071104c02e02c02c1200c150401098501200400e0945e00c0300c03400c00029601000743c201d0b243c26030700303001900b02d260319000301071101e0140e1021009070b901402e1811458401442241800d0000d600600f8a42c1188440700010303108015a0001d090802d000348000368005104413001003403500c5054290041c202c16411642c042c01101e49408113100140701048000c503a000d071520805040c80d004034003501c202c49092001000031800150021341250070440b84190b07068010001803040000c280207603070300320300351420002a07421140d00c2c0500420740d00400d0b00e0b080e0000a840d403d807018840160902e6409a08104032101c0040043c9a8039546440b6220840003498010030100f0100d81c00581d10078042c4c43c940030b0400046c51224418001038000c000031400101e00c50300c5505021590002400c42510a0a4030a40d80c0b030018082e40103582d207040e503030140081d480a407100340a003a03664030007065142c9901c034180380c030386a100b606e03102 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 419372104 1250 419370854 419370877
    0x14030415021506040614011d091311010203270307030830070806060703050c011401091a030709180203030301060302040816051806031905030307020709061802090a0f0308 75
    0xc04902c00703160601c17900d421100e000d00a4504111100010344174034004000701102201582d5269206450340f0405a1144104040b20f4035801c0c410710701002c119020710348d00c0d411540244903079500c0c00440d010790700c0d81c000308010020034400d102e40000c1c81d004090300000d0207210f003c83c051085900404890031450440f900716403c0c1b100300070616401e030700200c648070001450030f07011071b2140c10000014071405020f8030b0403d16143e010a01e40e402e656251080c8480030404c040104041c00a502c5417544060703c050824a00030800d000091741c5e0404c0c1e01490407055074444001705809a003078444400164050280c9480b580e44000c0540250043d208415480c0502642001d00c013810903101400d40b803006201d01d035a100c110070a03501c0100010300280c2c0521901000200580003200c40044d46c61040d40203642e640740107640242861501e602850070f450824005111050740381040002010349d86a0050b100d484200005003014040d0340722a00c0c0d03003c110f0010007130050700001826424110f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 419373354 1250 419372104 419372143
    0xf090651010201020f04031e0507030b011412060601050c01020c070b0309071e2601020705063304230a0c02061e0406110d0e030403020f0303030906041403041502 71
    0x3400010781c03e078814003411044682c002c1206000060000281340310720a500d00c4070500126650b560070345002c1d200d40058a4540d03034030b8010442d0580801101142034010360310800c031201912440c5075595030150016046c4000072a4030341012500754195089420400700300d90196540e803281d920254030948201041d8080c5e841d000ca070b0030780d248002503904482c00350714040319440c2601c1000c620a0158000c0d030010740c030302c00c02c0240700e03000d001a10070305008074007a14490805026920701d1600c0d0002c41c1c014840b8101096103522694610041146002d403004101d20001c0e4821840c4030081e0058400c0f0450102d092052141c9694050b09442c2119022501d240c4c0741c0120300130303006402c8003020844c0320581c40000c00044041c0c10220440716100c0c64141030140360000e0b9025205080c8841d082a400481c0400552a0200038640c0c00300e0103801031851424407070041d58407158014809001d081c01d180201d05c8542e07041044a004041d0083d00d00a8031003039043c02921b95440c190070b066540d02c13 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 419374604 1250 419373354 419373511
    0x305060306010603050c2d0c1014011503110c01090c06030c050f0a0c0f080412020906060f0306210706050304050610050f04200309150f0906 62
    0x85c400c95004018410302c690500f03000100c0d180400403141c00f400203850381c0c1d050800c0302d0700c00180130b8008000c04078081c040720040c20141c00100d603216004813848005c03010040041d100c2528180a44140b5031070042580000e80900c00c4080c032620306520515885c0c0780000e002e2107507142c1e05030107451003980c00b880701034200801141c0740c0c051240c0400c0034142c00c00020019902820700c02c2d4415104411100b0388161075143c40c9502c4d0403aa00010301d140940d011002145489101c450341720000720785080c01c22109140b03c260600005240902405202a11041142d11022810740414885080701d00380f540740c0c0350082c0a0707081950121024822400403c1442000f09031138029114040c00b02e1603c1d007070401c01c200103000c0d00c00341c2c2c40208100d01004000c55001000451289030080001c00d4628003404051a080c10028540d4000d0070410301801121302011800b190012040210401d00004c0500b00102c880c0494241a042205104500d101c1400310580d280d42d0165400c83c8100040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 419375854 1250 419374604 419374607
    0xa09030c021c02031c020714012102180301090503030106050c030f04030f0308010603090203060402190906240f050d110c031602100f05030c0309011803030f0f02070f031d1003050603060106 83
    0x880071a103007005038014800500084846003023803107001070149040070700c0380c0390742d0100c03554840540480c3d0540b079000074450441c030702c0c030404803162600c0c01e5000300710302111600c456403203000c180105010480001040c182410f01001514590145039205982c1c1e82d90f00e02c1d15001003c1e14140883c08527008200006171140a4400c50490640160107030040355030341d40c2081403401d11b954032080c070748241060101d02225107200d1040138181741c4416120007540c00080c010304140201c250820004039182d07141400f684003054441d203018201011415101d50851400d09000340c0c000c1d141d45120210300f05050310515401c260b803a90090b10008000c3e080c8000482d00c0c07000700024440860303020008500400d0580000310b50102c82d402c000100700c0340310744802050302d960f4001030700040d46452100d100740340d403885080c03510307004034a00b1032401c56260754403900d44540da02c000c0c0034046c0c0001c881084000564150942c5100181780030b4529002c0c00c8003400070807041c5e41c2280244140c000108015 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 419377104 1250 419375854 419375893
    0x130b0a0207050604030f03021b030d060e01060f05090109050907120b01020316140a1703070e0d0210030209151c0b030606010e0909120a030c0216030b0a09030c021c0203 74
    0x219009000f4052503a280d072000e41c0c02c0b800c000da60070308040e42085030440c2040c6207100311403905180d401440d074900c8290341890030364401d9000401d19900c00d00041141c00c0e04501ca404030051310b400d00540320103001c0010f981007601e5500c2075810001c0001081551030b84039401001a8000680410076104074074012680d9000d554041c120980c4440e04c42d201048810604000586692041b160b0b08046640c0e400c1c065403809527002501407011051041198114100020800c0c054030b0200c1d001d00700c1d400051098103000404824140d000419840c95200d40200520b003102d4041034035510400d51030340940b5121507141440d840d5180000c203444600e80031035120b0050405075a060ba06500c102d04010042d00c02408042c0301e40308030f603220000149414054a040c02003610f00143c0d01280c40c00c044d0808000294a800d200c0402006100080301e2010898021150b81030005a0202c1031801f59101c000402012754010400c00000d450071440c02d148c4000603109030203603011028840e800f41041d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 419378354 1250 419377104 419377117
    0x2a0a020306063c120604031e0318200114030610090e0f040606153e031305060c0307110414130c0f030804230306130b0a02 54
    0x1904444003245076454542c402d5103e2202c07940b43d1101c03010365100c80c03001d20f642e085254480d0782d00c8250709a00914004a080c0c081802c004040c2c846031a203940d00500e03070303980180d211707001c420280e1500307204030311a61008d0401824808042c3e1001c1c03150070003410401103198490500659040c8814495124405040750b4003a03c9c0c4442d401c1d6103401d410002d40640c80d4400c041003001c114000034036500041e080301d01445000c510f445041c14581080d20545d0000e41140c2810302c4854022403d05078480c404100a4001402d4441261080202105600c0032030300601a00c00c3d122465101c03a5001100611203420700c0381c50110340c965502c2c1406100d01417116034100ca50000e208100103c0d0b0541c01c0406601e200400000d040303480000032a41c4e8000c1038841c003281044085c01e50b010006402d1850011b0805041c55030521840c40e940d40d0900c2c4220300510041c0003094808248030120104900ba9072000107094502918001000e040e01010350380701550901c09050100c1d030b044c41540b00b00e0380c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 419379604 1250 419378354 419378359
    0x6091c050702040c020f07030602120705030f160e0a240206040206070b13020405150907020c2107080d020303150a0e060f0d06110c120901080402150d022a0a02 70
    0xc01c500c6800b0080100b04411414082d4000ca149011190f001440310a001d18858140161502c6074640030802000c401041202442804c0051280000d0152030f02c640c4030030041000018088142800c8030128182c8000703540010070080c0108040e8026040d807180303000d0807001a4010078648104907610f02d000c0d84c029400050800c049400702e1400001c1590121148045072803c2d249036003c5002c56404807600c40e00f90b0000307800d04034240b6050900942010040c07000307250b48035603400011400724035400c81c65010621008a0788944100b405404000c1003802c00f601c8450301c0248000c0e459902c1110101eaa8040b800d082c00d01a150280c07400d03042e100c01d4507113031340c0c1547d40209000302c0d13002060403140c0c4011148120f000084240c05607a00c81c07035110104540300c6103d0079550b072411400030001d00c0700c0352042c0040030060342c2c04003109512507011a00e00d041d540352245098804e20840c21550501c9000250343d010300307a60150740d018a180c144440740b004080c00c0c1c100075141c082e0140002d5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 419380854 1250 419379604 419379607
    0x30703350a02040503060a0603050d1d0607060b090a06050a06080c0706050a18031d0909100209130207110f0103052806050310090b010e13201206091c05 67
    0x126404000c0c03001c0d405500040c0c0146096140c000192412104444030841d0a40f140001d104008081c00001c20b410841d09000351510604c000300e0f8506c01000125a001b240b0201c0c07031303000b4810180c00c00ea00030300c0b01500004c49810300c2c00c0850082d010038050345008541d020400500c09224140891142c892840860708050440d900c85028080141802c6020f40d101c140c41c0c80b400c0c134680900007980703219441d0420444c004030792824050700c0380e904c168400d01c540010049880c07004200c60040d100b0880005030b803451074900046050105000700c00c0c1a030302c0440c281040100b40e181e880d804a208540522600c000324004609403001100d611020000704048490001100c5180b203003455071494001c900f00b034503400403074503010348180601e006071f464040c2e2030240070900701c0681c050710005010102038903056141d4185207001030001441d9000d070300301154041c0c250044051962200400440425007000d940e560b5407401a16400e10a000f0030b01545c1945180c0101c50761101e40e181c4400303 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 419382104 1250 419380854 419380937
    0x906050a0e0f071403070801080d140412020312030a0b010e1e0d020109090c03020d0f060602070b030705040e01060c02040c08091b0a090528270c0302040e030703 71
    0x2c4801000580b080080c0405440e51408050504c0c010b148200015a68407080e50314202442e0700d003600d411a000f080c008041024004045840c3c00c88054a0011300002c21595452002c0b9217042d840209120036420040b042c4400148244c2240303014000c00d076101600c28013400d0400650101894031200c83ca054100b03240450f003084c40303003180d011740141091880030342d441c0210416200201030760000294009080c1c41c2030f01b650f104a15480e0402441046580d040400c042c3d528009400350700a4420080002403240d031068044401400141e250762180f5651200083d050f2020010100e104a0802d80c25002007803041444500c940d143d900284562112070050100b0400d2840480d41c21100b89040491100024080e542c0540400f0102d0400c3c440d40b490589101c5047c2c0c0d1840280b1800c25040d00c0059015140c40c144001a44100000300d04c0c95107424111051158002900981020b5049190310400b00c0a004001d00a4646010070801d02c40ba040c4040020048102008402d0554 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 419383354 1250 419382104 419382121
    0x616050d0e090a380301180309180906020d02030601030b0d0b070e01121d0609060408030f09100905030414040209030a06020f04030c08070f08010506011d0114040308040906050a0e 79
    0x210030b00302844001c144580000109448400240c00d8800d0307883c1e0400d0703c5400c81d040074810020030450091f001080340c0103942c0e004200644c544503041209803811300894868003d0b90000b00c40580c0100115980e140300e01e0380d84040e41040766100e0101740381001c030300b01c06d05101c01d000707842c2540051004d840f03a80f010380589104030524141810000c02091480c1925050b10440b1040c0809050300c50080030030300c8000740380c0800100303418046d8100c14144800500e224007540d4012421b41c56070036180e07507a058440d2400c4150064001001d0401d6007000038072a0101c001c20a0320300b400c1c020380b40540c0180a000582c0b0503101450741580c842c058500108034a64042d101443c8800c0041d0b1409a0740c0c2c4902001e40d9054001186a4008a4040043c0d21000b0204c00c02001350000a1100b407030280000b0703003401c440b89581c188010300c01d402c88120360321a90559202d413441400e60380c2c5036034880c02d00f841c0e9900039000c1c0f6a0310724989400413a01d0703e00400507a04036000d1404040c01a543c00b02c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 419384604 1250 419383354 419383361
    0x7090c0e0109051002150c030103050105070c050c0d030c081206010207050a0b030a090215040306020a030c0e030a030c020a15030504020f010203030408040b0f0d0f0c020106090b0105090d050c0616050d0e090a 91
    0x34540114002d03200c041030180010b203842401b410141c4901508d075411401c0080c2101c030007070300c800c041c01070710301195001034070109040b0a03000c42240c05660801c0d00d800c056640c203500c07040c010988240001c407564403100e80300751680500f00a90803540980e482c0c0050100001460141c02a02c0b0020310005c0d00c4009580c001c0003809101402d5800c000b100b211401b10340c0d40080e00200c03026038011810040d400d03858495151640020b00d4043c10205081c00480c2d201c0c1010240a82040844010b0760103544902e03403080010b1503030030320030300c094015110024024078040c0c4e02240704151030f90002141c1d42c07001098034062038008501501d41032034030601c560070780e210300d9201d0b107614020701442580c03001510460000c240e101c480405c01c452031400007400c40b902030b04054105440d006c071f12805a42c0c0041505d84031380e400d44000c4641c880d1810118034140044e45880d501180008102020203034907042105c60034405c404468502c0d031984400d03a801450885800c0c0c10505507400910784031306a81 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 419385854 1250 419384604 419384629
    0x7082a040204030503040806190506090a0b01021608150108030406050a180305010c05180904030e040f06091d15061f0c3005040506072306010807090c0e010905 70
    0x9000614090783d80c0e4034942150466130001d4400e801250800040c0c48087c03049c001c0e08503c0c1c503c1081940390010000b03020b0700c400740002c401c0b82d40d611402000c503402002850071202c1030b88102908a540e8039801652240c20102c080d00300c4c141000002001000042a241603c3e52a1a15800d00d0041c001c12a9500c101c403040b50700200c01180c002010403400e1242d80e451102c1d9031740b0540d0780c544100b800300c3c02c0000c0c080708601a0300b00300100004684c2c032219006003202e0848011907071400c40301080c80500f00e15045109403d2424a407002c0c2008002c4040282e1030022082c1d40b00f401402d0f000090a4904440d400e0300444103035200c0344c5001000940c203525011a04010102c10f44e5070320303072024031400d2582103981c1c00c0303148840c00c0f402801040803806110340ea1a05510b400d0900d00450319034060008028114801003120400c609604c2d10450102880c500450b0400d603580c440b03840d0380300405d109000500340303450008603480f441106041038002c8181c46901805140506000ca40c90b1600c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 419387104 1250 419385854 419385859
    0xf05030409050a0b0906010f020705040c1701080c0405130309030b060d0812060f0a0803180a03200f040614090406110f04050a0503160b0c15090d0207082a 68
    0x4010104070940700b0b108407030103007075403203400140310351a81c0512030f1101c0f024240e20f060058888078800407950001d403420568506540108258443d22000d070380b116030411092803074901500010484100009a1640c6020103c500f882181c8510b0644130080303107030200280010f450b089083c4042400710000e0b0340c01000191881078521020b440b080513603000300c4044040c00c00d401c0d080c808945015a80b0031480942200d000c950a0315101041d541c9124003000d216101404c01001c0e0050b96500d81410000c0d078105a49813002c01201d80c44c0c1030359045c440e000600c5112003009220fa02c0c1801d206680035a04030b4031140c0003c5003280c3c00c00c801420b0040049a07056100c031415603030015610040c02d003000c2100c01242d2030718240300c200003049201c1d800103030213036000d040d8404d107078070f000c031104030403182d03482c40d40b43d0b80d501c03a003031041e00300000e111401ea040744900c010300204803400195000800142e90030b0b40d050b55241c0a0554580c2c030b4243c40110fa4403010308036054a03036400c410540006000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 419388354 1250 419387104 419387107
    0x503030f07150218010f02070807120f0615090510051c11100c020102060a0e031b030c030a0e0915010206271905070603090c1202010c2003070b03130f0503 68
    0x10b4907407099030300c201018800f5001100b0140c090796040140f00318030f2103181c0050807045d8140f05900783e0300c044c41c0c804c0c0701c180342c1d004900c8414004a441c0340408d41d500a01d01b030040000c0304421403110910b5224024445140c070000600184ac45210300095442c01801d02d035070295280c032003c1d0070042c400307001d0754507091100c80d0101540e1a000720700c040000a031510800900140006030a100c00240310bc003005080c00c4c181c80b031000020080700e60a42c0b80b4050001c007010000095031450040340310500913884005120581030f90488881103050f10700319030340c615580e02c401114451240c1390b9002405a40302d0004605101046a510580f005458028807c00207000c92000d152044c40400d41420041c00011581482410f01024000c1e024070705040c400f1009565401d900c0444510542080040c800d038901d0440e0b114000521800d500010240035100f2050800c84a02018040c024440d1141c0200054000e10040507248120354110356090781d0802c0d034642012002806108030f425010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 419389604 1250 419388354 419388383
    0x702010902030607052b06150801030f12050c010f0501031e020a030204020d020903010515041503171b011d0c010e01090506130e092a10030f110a11160503030f07 71
    0x14521b290380c0e00b40b03042842c00300d03006141400d090322800a0030150b8040048803401440413070364080458030350f15404031000600078110700c011180382c024190251040c4d400c0c56440312030344c50b55400c95810307030307008200a2410303002c6562680c4004482c50b0f002500a0600e100401c0541351a46c094519039039003c20141c41c040f1000d00107400c40b60f04075213114001305d4800003030546003800c3c481c49159803000c5070b40307441131419516500c6003000d880844016480000464800d2008400540d018400d4120001d0141d500308007040a520002003403410441e1260520181c02ca45c4501440f242050068507203603807103800c03c0188105984195220740343e103001d89000140d4a600c05030164480c950100141c19000080158020a008030328007066107040030384c882e4140c030faa0340b0002c0c803c4070f01035080c0011480b401c00b040704040c1c1010104280116804100328589540000e008135105580b403003900c18005083d01542c0c400081406980d42543c4280017000300070740c40c84014005280180c070031191191 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 419390854 1250 419389604 419389657
    0x90603022503090801090812090a1502131203080f1f03030507050f030f04031a072c1002030a1b030c030c0503130b070501140c310b03070206070201090203060705 71
    0x43c511750f1b0841c0d8030302000840c0310240802c00302280d000b110900262080c0e07101611211145540003070b0440c001540000d11006540354498010002d0294141c202c00c1e00340b0a0401600322a801c6450680c100c1070200012241c07445880c0c05202514403004a0359030b5400d50714101c4098011343e0b4211894450035085041141040020300704400d40a82600d40c6d841c15854540c030b10002c0081c61400030002e01c01807001954005642d01e401244001000008050030980203004102d821003464000c030300c44140030045a40032008040c03090141e03c0d5807007412820f44103406100481e10004d00003e07050014031001a11821201030f0182c0104101d82c1003094000c03400c0107002d11035104500404002030b034401006820b0180c401802c04111041c4d02c03034905002d840c0c215100c0e009001c81c400141070461101f40d031041d078028410004080e56110b102d61503401c61070041c0d0007610030070003510a40000a044901c1402186030450b405805081e00e6159800d095410b500305504041c0004089602c150340c0b407 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 419392104 1250 419390854 419390861
    0x3091e051e07060207090b0d0303090219030b0a1a10050a02030f03070215010902030f010315180602040302010818030a080c0c0f07090f06080a140309030a0c0303090603022503090801 80
    0x14101030107002c01902d001006441c0401a502925401341000e805940c0e03644e03034031440c034459905170030b0100e03c0d000c0910005012481d0410b50919030401c010010050000f4024203610400003024200b112484024452141180d000d203c00e9122000b02c05214100c0d1080c03019101a60a60040b0390600c064400e40d111940c00842d60200140e0050030200805014083c1035801070042500462450a05000b202d0f001641400050880101103d148241c80110b074854030602001c0e485049410300540b8040019501900c8182c0c0010b5890000c140c08074100c6100142480302c4400461510031088800e031a10240280006081402880340e03c040e01c2080c4401119a001c4001500301c060401606508030382000b0405182d681c034050003440044030014400602d1601301d80c5520f4200214000b0702d1075841256081a054007410b4807150800c1216004141960300c82d440e030169007138540c14203d089004002d500a2008a034003402c03800700194030b03161203105020b441c0402c544c54490408070b003034 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 419393354 1250 419392104 419392153
    0xc01150303020a02090703110d0b0a090204030c030b0f0106051b011506020109120801060203091e120d030e1207110f03010203150a090b03030306060a0504030501090308061003091e05 80
    0x580c01508003c02140b0b0502c00031641b15105090030400300c881742400381d0a03809a4882410401d07922052241540e481c840110000c2c21134920540d40c86032680f420b503544e890b041c4001c80303e642100d03001c90b40c07401007000a00e0607240c50707655840c1000c07002c072507055000ca44a040f0100da9540c0d80d024056014a500c074520280c04a50008503601d011840c0c4240c8201a40c8070b078030308000703050700140319481e0f01000b1201482c1c0b0440d0000d61500d807503110700342d00070a031520f2a50300801c40706559071030400c041042080e0029540717041200d607003944540c680320640d1025106240ba0100b00b81e000150b2a0101e0350074840d07001d0b1002d0030008001d4082070882c0c2c810307642c00b00c03401d10703400c403200e081d141000307514000c2d01400320244107800410012070398078040070340310a10565002c40d0300410b42d84150240d0f00115040701c0280040e10842c2005440c0e41010303240c60740100003075004002a0b0740240540c0403020351100d44030162807510b220144880c0a140d6040740c840c0510382c41a481c4030740840c0310404 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 419394604 1250 419393354 419393357
    0xc030203030315011706091906090203010609030201091a0417010b040906020d0c0e091b130303050d2a0305270d080117030910170403030b1306080c060c01150303 71
    0xc00e000b403e0000d040590408140311109104004211080c0c940c036803038540110781e1a81040103080c0344000c0c1406411075070452800c442c4048000142c4690244000080324000c0c1c079000c00030b03601d45a54440d140040056180304040420082020b20300b41000d05000080300c0d40001141c01c503ca0003c1c00b59a4800300681d8050340101d81580508128414034200345d07507034240420075400103804282c1031030004140c1c0321500140b9144446204040081300c0803001e000030103002003901ca00e07010300f07140c01510304070003c44d06c0d04540c940f00d02e00c2c030120714410003452040741c40700c0741110204034003030034004003c042e88503029200c50700802c05d04000341042641050181114003280758004140e040143d1021025419484440c0d40410002c0210344c600c8200707481c030400b1100100d00c07d0703a4040c0414010240850f50b10204420700d80c1c03580c000d41031400c084584210b100c988220f00d0040c0c072481d006d0407505400441103201645850801028031170014000803a8061030852004040004e40c1e00540 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 419395854 1250 419394604 419394631
    0x90a06030606090b011205090f060403050a0207051e10030204170a1103011107060b0a1502030c10020a091e090203100e06010201140c0a030608010c02031305030105010e0c070c0302030303 82
    0x30080780c0d005a402522500c0c004200f141c04c1140000d04004000744041c0f14280e4410100300d13802010b2014046800801e800c440160505260082c020fa0101ea03262005008c2c10302d02140310700d004440284d5602c107450510080c4003030712040001105400204109140e400c120000310810280c81e915407140c40207014100b50182c2e4204200070954240e200f074403a0349803000d0040781410076011f032030299410000000d02c0c103841001142c1c0d2158a07400c0a00c44c0c1d60038042000665a0000041c00e0401140e025035041202d1a4074800aa00481000c0b0010409a15052142998401046100103d034002d00d5440540d2081500101d074004d81d142c0c20310a0340e4200034040390680480c9290410001c3c40204400c4002c0c002d140080b050181011600c010005201e800080c46a0820406844214005c01c210815407802075135940c841420400f1101e00c644001480d0715062040904807840005800d01980d0340c3c8808580a41c424082211254800d081c04001350f20100007441c8500003140c50380 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 419397104 1250 419395854 419395859
    0xf0f1f0c0e0a091a06030c03010b0309070e0c0d180c0b090301020d090302070302011d0a06110c18061504030b0c07050a080307020304061d0325081b2b020f0105040302090a06 76
    0x203010102130041e01c0c600a990030002d00003420305403003c582c119480d120f001901c039200e500d003041c100411a800300050705800c0080c8100302500301c0081031810103441e4100090020414117001101440002500324100414104007485194000307051030500100010300e450100032076002100d003456010b80c0160f000a80c14030865800c41001c103500c0504098039600c1d4002d1300c0018400d02810f004400401100b50760750042d00804000c5107842c140000c08001405182d6001d040d45140300300ca00a100d00c05860710501125140070454080e203810844c03002071343c1d40300b8541c0c100395803010301c0c102c03028070a00103240007180644003d0343c000d1250f035015503030b12840d042c00106199101c03948651030480c001c10004040d940042d148480788012010a8200110f80c2c40b00a4103120781e90002200b805842c1c102500001603040312030004600320356101e49580c841d1031000d17100d0071010f086028201c25501c3d12025141081d46501d1281e814504a45030544039408980c407041c0544500d04400d8440d03900313 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 419398354 1250 419397104 419397131
    0x30c0a091407020613121b051501120c0e07020a020d0c08060c1603080601031e02030a1d0a0321021207020f0d05071b050301020406020f0f1f0c0e0a09 66
    0x10b801504901c02008a424450306240003210580402000310040c6003a880c603007806040110304840794014025880c000c9070520701d0f190140300b101103003c2946440042480f00140700416002a027002c140c12045051811001c0c0700d541c054440801d61003103040c1c40d00160f4440301003048203031107083c040d0003962400ca42c644ca0310328050301440090f11305108483d0031191001c800310450341c1507d000c034101c3e1a07001c0182c00411041c148409084207400000700100710640046005100c0d045007003107030750020003e041c81000030041c00005908a021490b012900c919006625001c4450031081d107420460455802c07a84250160f0320864100340401240359014040c840580c80d059000d88149c5008060042c81803013030b404001c064040700000e100c000516110901d01038007025000710b41e00c64940c04d01a5843d110b68505600a1180419544101101059080080703408942407010a02031141300809020054485002c002c490076040920b40c2d6408000c10080c10303003180004005440520 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 419399604 1250 419398354 419398391
    0x100507060501140d11040e0f0703020a0e0c1e0d150620100c090803030108070f1406030114010302090a0b0d140f0703093905011106060609030c0a09 65
    0x602004550140c01e031490303844940301c8000c880e07844000441c0b400c3c0c0702c0e0000b030700030480d40c0311a080910038100ca0300ea2310072000070f07048252030003110141003442d0303030704607100da03504040700d000c134400d2000d021171031441190080211800c40d03092019405e0007180960350003142c0411800504c1800a50810068180c110100010580c1c55442101c08100343c641015620840c0000c0c040b031840c0d54148150070b280c070802c40400907240b4070055a68a503510161540e0322029402a40e0940f92040b4001505c02c2c030581041190f40ca01500240c02c60f0319210301c00d10a400d15152544c149078003003140d142e03581e60f01445500540400044a81c0f101544880702c01112980030310708a5400111041c4005a00800040e56000b1341614000c41c095030a0b2501208074411141c00091016201884501c0381c2400724515109014548086c0409549c034001111a0b08a01c41c1d00c0c52603401607400300c2c40c00d05018000300b000c2007002c2c081312003100c9624049588007001e41e114048260399500c02507501c108129 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 419400854 1250 419399604 419399609
    0xc0a0302091c2303070b06091e010906151704150b1c0b0c041208030a060e0c09031504080702090a020c031804050a060323120a050d0c0f14070f02100507060501 70
    0x4011170400b0001d83d00d13808000c1c0045c0c000345c8501381a0000800144000e014040a5031005108030401c0d40c1d60718000d80034081c140909400c80d00d000c00090407032841070200104600442000007919115516604115180e4121283c4400e450f0068991240c4a580400b401e0030807030f8880707000b15280c80c01c2040c1c0440d00906844001c40e000c0004015030703540040e41000807600540e030995242c40300400b541c01132006a018410040d100e0301048101220341015141c07810301913041d00c0103842d00c504018903000c4111001080c00006003d0440035050811006500607507002e40145013848009040c0d00c0c50f003281e506011010b4440545c04010f0400e80a841c3c0c1200d1180001d010060542d6101c0c17442c1d0030480016401540101d20354030748108100150b02c3e401c00c42110296496411507002412a8041c41c0c0c000032050034000c029545034801c1f01034003844082a503481c48110020100c10111b51b000c50000d4130080b000300f900c000545d5407040c024002c422103448240e40c50803030b840d1010940e00b05a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 419402104 1250 419400854 419400923
    0x60b060d0e1b011103071502091011150c0d0504030e061602040b030105090a030807030902100504080607020d14090f061201030203070b03061011012c0f01050c0a0302091c 75
    0x41340d101c030051400400d8465850b48100754544c0d9003000d8050303400034003449114681c422174502000ca030303031600280c2e1900c014501c403003501c8621404a0f03030108201c00c140e40141510300c1c1001400c03000d407038030380c02507410070b00c2440c2000c0c4040d420400a6000d822041d520304502c001415450700b1440c1ca4801e85405990a900a0090b0324107942c2050321600307805405400e02951500245449105e0340c40a400c0590082c80b5140c40e044d2107100802640040c024081135104200205060500001e0340042040e0969551004070384014428140c9400c503003956508069031a07003082441c3d480001401c0f03050b2145d0381c40c41507507155004151401c1a0356000b03c3c0711890070004d100305619850010101020b40741456070040a0380c4454a00401201c1c1c1e8494022400c40300d8101e099403424504182e0034400821101c49040f04103c481c03c9490540c1e003145040410410104018000e402505602c0c1c1c2c020032030b41601080311240c21803403c000c03100700c581002481200c2c1116001000820044412 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 419403354 1250 419402104 419402117
    0x2030f122502180414071202010f0318110d061107021507051009111804060f271103300906071122020d0c020f030304060b060d0e1b01 59
    0x35008500c400d12007801c0e03404258040f50001e0180b204e1080f0f80c440c10b0844104980009644929004040c480100c080380055000b50002c0c10051207401014105203200c1c07000342d585600b44e5a01d680b0340040c00079250304004015852000f16419204594040b1a030800751550794401c0d104000312924070202c0216503a01c14442d04010401c00102d52400329030240c4001102c0d451820441d918840000d4000e51015000d088420404400720809008510418040c001060140c041006464509509203100c06d011110f000d803024040b81c00e118100c2c01035a0030380c44141c043c804203092646035421116000d00016503682c4240a11410310101c1009c81c000a06000804c000103507075200709000a0008007150505400da542c81307440d44e034140140d0306000d8040ca0300e510100c130040e4210305550307240d8030b103400d20604115001044400c00510450b02a52030356942d641c4240040c040440002d402003000d00c0b450074940410b1040080c0c02c50140020140c00e0781801c8903420180b03103904180d040000c0d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 419404604 1250 419403354 419403427
    0xf060e1015080112060f020c0c0a090507020d18080d050304051c0905040e071e05040f202503081503010e1c020c0a1d0f0f06040902030f12 61
    0x24406081c60640700f04c105821985503290504102800d00d0b210800032803031000400e15001200081e00065201003650000c51041c4c1d62801c501c104e41040f91300c1d0002d80c008a8040084501c910401101e81b041c1c1d000924841d510782509606e08a019503039400451000400c0c002800010403c54176142c0154040c0007006040840003458031282d4030074070b0b02458031214084082e1354140003840251003508440701c44c1c010180d15000340c800e40c41c820703540100e181103180e2000c01d40714000c422059140020700c0b6613a079000f80f00b82d000c5074083c041c6035501080500442109041503800d031b0007020301076602d403c000e027002031a100454040e0804548a80e2600b8103501c1d45800200b420700e071105011030200c8102e28881170683c1025413529816501c03500808020603000140a1003040b643d05c0c080c402c034a59070762560784080841045d550010250b00180000e00c40d0300c0c041d08040001d910203010b45202c100000c2200e841e10f202e03ca1010900b074008124801d000c5c28014040585143c011310042c5040d2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 419405854 1250 419404604 419404607
    0x915031704081b1c0f0b28140402190e04050309010807020d02151b040914070503070e0f01050903031605060709030f060f02090a0306020301030b1e0a050a0f060e1015 73
    0x13900c8000d42955a06040d81c0414880c120445c007000640081c030320021b40c5007800860924041010307040c240345500401610701101d01c3e210701e2042403000040200c10b6100e0340c0070001038060000420f64841c0c4c5400003c070300b41086078100340c0503505c900011519400b1150024000c414014a0381e000c561120800501f0241e0010784900075041084d4104810f880b0f80018800341c00303450301480ca041d8000100000d00201e2a0302042c0c803800c410100c10f120b034881c2034040300c8900c004d9481c0000a04c9280d1040d00e1840c00540000c09210141400c1e071502d0103010201e804c540048070340140d91514000a1800d101082c400a85d01803003038030748120102c0c1127580e01e00241040b40c0c000361041d645e45c1004885000780ba411039111000c0204010f0050b542c1e407034080d01a5109003c121450380000000c1054a1301e0003459040004100c40303503000d039640b000e094800604000304003400d01900c4484800041103503106d242c01401c0008001c91162400cbc0c54069a2544280e01806800c22111100c0300780c80d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 419407104 1250 419405854 419405869
    0x112080a0f03020c0a11190509180c0a0909020406060f1b1707050d09061d040f29040e0c0f01321b0106030503040915031704081b 57
    0x24901814140181820704004400a004a04c1d00e28050310410b49070b207003400800e81a41184103000c8501c02c0d00006034102c0341d80f46072140c1c416542c0102404012600060b4200071048942420310100d41200c1030398800a058544264400400b1036070b503104203025420103025060140280d828840b40100d4142c0c03004018a03004a410202003c0d0001741104115040105a1000f82010030080e01c5a038541041e03030329422103c5003800800e00d103c0300045c403513000e4483c4540780000c804d44401c0d41c190103020311000c1d003040c003500924540e84004000045740c482e01144803902c0101704441c0c910010350140000c44144201c031004640c415001e03c20180c1c0c850285002d00103081c40e1000040e00086148050032450110070008220180d540c410714040b6a4044c0505400d00300401011301c0f41c4001050172180c007404094195042000304cc480e04483c5e40005e1058078615481207080f90783d94031210f051282c0c0c00e01882601c0c100290800c00e0000400c0f21030080c00c0740501200b090918000040e400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 419408354 1250 419407104 419407117
    0x70e04150e06040906090b010305061012030806060309100c0201060f050301090c0b0a0c0b0a0c030b0105030912090d02120312100f0501030f180f0309120507090906020f040e010509011208 82
    0x10f6443d44501801c02c202c80c2c200e84002a0303c8003440340c1a5031240b9100762aa0012101001888012680022400b00750200c1a144603059219030180d0780b90203082c070030b20f0350004080304054843e581e0011900e01c401d2040039040d03036060b03000058007403c00c1241b80c045030940c1d101c640300341e04041074003010490714519201241c201e0580c07155a900ba0381c4062792900c8007044041d1201c103d1a0810140c2c0c002a00720301d40d801c0165404003c0040501c4c01520359000558a801c029804225000b419590070030040100400080c003401c03000780c1c240c0c00150403000c0b10040a000b40c1000c0340c0c100c1e0603080c4490040d04003004070b040d0380005050072110000d80c3d1040c8241810161a40610740e401010303544403c0442441440050410913103060020000b410741e14118001262881c002842c15805036400b640c059102c03000d00340052511756088090500712405a035100d5017081008140c1c0004d200a00040c0703907840899040350700d400d04000b16507070140d0200d141840c0240341031001520b094100c484 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 419409604 1250 419408354 419408359
    0x509040b0406050604062304080a020108060301110f070b0f04080f030a02090901080123061e031603030815150d0906060302130b040e0c10110114070e04150e06 70
    0x16000942000200505050f91085820500000c0c0c041503d80c5c0c030400132000b001220001c4503100070b0f030b01d0410311184624801e132420354004004000c0190310641945030414801400850042e1820074240f076681d02010403440c22207000a95038080000305104141e00c014520b5540d0254641902d620102d0300c680303480c0160300030000000400c03118003541541d40e512000703800c580466071904a0035000380120580000b82c04200400700d95211a400c01c101c0c45114060003072550726400200080c1c4210034440450381c14000e08005c4101840d000e050100294002d5071000f0440c240510039440c069038401c507030fa005200c255446903143c281d1904440012030040e0b0b000919410034140400200b0003074200941c80080c1122034440359545410036152000c0440d000c01c07500400039182135076074031003025050300498155211044503000c0d650f0700c00a5403864001007035022101c145404c0703040c000c5031400c020511074a903105290038148034000b03004c0f4581c045589690b04000401c105034a00908051 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 419410854 1250 419409604 419409611
    0x105030903040e04060b030c040b012f0105041a01140306270a03020309031905100504030c060203040302160e0415020d0212010e010e060603041203020a031d06040b070f050904 77
    0xa0485108100b210010400c420309112541032920309400600b0140441900c20710070740c800f180b940e2500d03100702005040705131a804908100703040180e43e90350f04d80e0303448041640210395040c0300107003e0007081c1c441c0340714070b5400a03604040346003105400303410f800c51034540c5480391144000740c400003040c42c0c00140c0c0170243c010043d100100c4c4a1410303031155034000c0c2402112140700c20550000080c000f030310011420703280500e41680280010304140c1c10003420660107002d0f94041c01890fa0300160308a4002e1170031201d020907945401081c1e0f4820750f011001a032202000179004035004002c43c01810500410020501b484e0300c505150f1682d003465540c0392640004c80c480040700c6a8110b0300d904810f410000041d6070340788221300c850002482405000003804001032020315003c01100e02c100d030300121980071403810704000c500035008080c030b11050540c0c5665801030640c50509034060510319000400440c5440e02d45265000c1c0c01800070b40510188292400034186c003e42a02d04481302501c000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 419412104 1250 419410854 419410861
    0x90e010f140a06120512032e0f060f090e061801122001170c0c070e0105030f01020a0903060b0a12060504050c040e0d0c060204170304152609280201111209010503 71
    0x140c11604092301104100d114141d0080440960b0100500440f24040704560403283c1d206d038252a0502200d0412001488801d401c0c400c598081400a801441c00b925011384003170790300710184108030280c1043c2c40340c4441051000030440c04920031400c20444d00b800c6112001c0090010304000409030600e9580515580000c5100000409031070070344018808440e0320741d90f103030f00c0c0b00d00c030400c00e0051502901078480c107610042d5050003118108109603940000e040d2860302e0b128014035083c0e03402e6a1104004400003000040085030032030241c0a0400090141428581140381c00040042c55000c2d41c00c095203002040408550007298011604102e0343e000700c9071910100a1141d900104009148114001050301000000c0c10a55200003001c130690744240134147c0c5d01d02c5035200d01c0103201c00c0c4561846490a890038500b50031012030b60440310000300080050700b02c00b6205541c032060b00c0c40003141c24155070707001d0a000728500d1a40054140c407062800b50320748074401c00440c2810707c00000b012 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 419413354 1250 419412104 419412121
    0x30102040b0f160b0c18060a090b0a0201020405180a0b0910050103090f140708211e07020a03050d03060504021201090c020a12020c0405010b13090e010f140a0612051203 74
    0xd00ca280f5400301030200d540c548100170000c0d03070700482c8018490f401810782d07000160030040201c0303041a604da15101102c40c41c0901440300c0303500c034001d00c0c01155000d11002880d41c4822107410145010b0801d94041840d01040207801c03151080d202d40d02c901205001e03c039800c03030326540d400c058807420b1802103847d00300c500f007488800c5224040180b03403011500d442c1c0c00491010610b14150f4140f441a02c1841c9648498103c0c0312010301c41142440000f0054000c10a0180702c450070154035511155080036007039000500d01400503031081c0c440da008801d10307500c07850b41442030ba0040c0604803011401c001100c0407003001e00d0320500030907000350b42d94004600c8050080040d40381040e071150000ca100c0c001c40034000e480d02c605894090081381807100101d2443c034000240c1d10f0701c011009400389070340e16108038003020701201000c6035400e55941c0c042c2419820240a40482c400f650100e030906401c3c2080c0701005c95a15511484500e101c2094100c0000c001141085503610f80032441902d90719203504 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 419414604 1250 419413354 419413387
    0xf030507060b0f0d060e01090b090601080c1e04090f0602030709050f0a080303150d080307020c010f0e100804170a020c0a090203010f090b04022809050a060509220e100506030102040b0f 81
    0x1019040c049d00070700304000020000b980505030317440d20090318900f007500d109021801001211900c00004884110001402c04d135000c000e415008604000362910241c64038412030f0b006a039014001416404188224140242c2c0481c40c00b038146c07110018146001010744d00c901028004030042c04c680c0c054211250384a051128986400032071480d6240ad191001a5944a107450468007003100c911a00c41c61030f00032215414400300180c50f24041c8411000c0480305034a005000302d0301c0e2000005480c2d0b100c03000d60302030002032420782c000300f080390725a00c1008007100d810b5204040d014010001845580a4000c0d070604071020146c02040d40041080004c1c0070f4000d040789a0242000d00207a10a603000b07203801c07840900440c0d140c6d01411521501403000011060107510040760781005040300c01e040c0400f400ca0303d1500d0020001c1403440b542880003d441c14808420190303408030042c401040c0c0c0c00c1c814a50404401c4008600d05403034003140700800d0081803070b0034130b40c040d0100d07032a4070a485403c1f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 419415854 1250 419414604 419414621
    0x31c0209040b031207060510030f06020a110729040f1208090d0605040209060315190f0608070314031c020f130b180103060e0a09020d0f030507060b0f0d060e01 70
    0xf010303205000e91142d500c0c403158201c40400c2c1c0f400c0c2c2c10000404c071003400c4c5180c0e0070162501303c1018920504d05480700806540024800b00c104240d142000150800c14010f50b40640140c1c40f040030000410a4111515040645150070007181040704100303030908114400112340c0c14000c1d4241020803401c00251500602d4100c03038014504241c428204070300c03035100b40d00c5170b40b080320845000d4a03410240765588400d079003000045030050021641002d1456004180203840403c040b60703182c14100b603c816a4074030740c084103c541c4030100520820402d031521980c0d20099100840c20603200c031641001e07510341003c91074416540041c07195003840401048642c000e02c2e003071402038860350f141140c0c1c42c590300c00001c00e0020700d80c404c245032032584280507c504445d9000c120340c04a44604281e4030080443e888100c0e80300c0c510f0b06480b400215801400803070940252200754455015090040030f40305aa180e441c440c0180c514203003025a01c0120b078014071034020304006011540450142e00608104 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 419417104 1250 419415854 419415859
    0xf1e1005180d091715040318050613090506090708280216150e06153c09010503060a09140708070302150406050304080a0201020f1207030608031c0209040b 68
    0x491058001500030300d000003151400d410345003442200000807500d52882e285c0c10380401071500c0224010900c0351220544610460500f20030310b0355179a0024110303500c644104550050b800c01d04004070b59442c070a040c2d200c00180c640c03e400c2d10340b2000003804068000d21001c001c40950300c0c0505060480741005a10f421509000c6590740c1ca900c0c091030450500050481e0092000e00c03074401c0c407082d50b01a4641001d2441c0c000c0c0442e40300c0c0c01405050b0807079a40380300d402c0b01d8106010400042e605031304002c1c801144802a408584d070846481e844000207440e5406545480010070654800003075203540605c2c2d81a00182403221441c040324614200558503410b84100341d00490b40207800301d01c0700e0441c5c9c0301300e5400c171130340d2901020714480b4040d621400d404a0380a0002801241c0448001d0140c078200384001841d190011140e030310503411512504001000d10010011034039011700c541005800180f0040d41408080c1d151902c42d06080141c040020b500802d0095654030749401141404400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 419418354 1250 419417104 419417113
    0x705010b131a0102030406020d03051906120b1005010504050418021009051306050303030103150204031505010503100506030c01050d0b0d0b04031205150f19080f1e100518 75
    0x88441641c042c0000c0d0700c8480719501e605007241d800d90f00001c121070846040340c010b03003c600d003007250030342c0200341c000c1c1904101c05240c0842c0701540c42c10321504018001c0341070030400d903982504104152460041031400b80f5402642c091106070b800c0002d540407220100d60114040150034808030301c038100f05200a400c100740305188072040d5040404a4240c6206951102a004001c101001034520500c04c42d80c25410410042c0045000311503100210443c58001518142c1d40342d541030f00000b4021048500943d4420043c8600c4ca4203000d911188000f1020900c02c50408200090701c03410f0701c0800d03505010303002901024200231504a8201028003d001c042d07180258100001c1039a412501100000d90106841441d05054803905000c0c480c40080c540003012010244091ba0002c3d049483e448440c0202c18a505280ba00a480180ca045005003d20240c011102807a0049588a480149040481145a000000038640c0070b1115080010800741c43c1d0201943c450a510501d48030f09008 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 419419604 1250 419418354 419418379
    0x21206010609090e01021306180810231504020904060b0f03100807060c1502120405150603010207031d01200303040b0f0f0f150d03090e0a0203040b0c0705010b 70
    0x800150b090100c68200c00148100e1345540c082e10301700d10403515168070b984600d08050010302d10a003070181110180c45014003015403945119032524000b50020601a0f80f0303841112041c01000c42e1301d000071041d400040c421401e1030811550451802050540900c2e40814480c00d00c1da05c2c0d8004000030601a421145c3c1c6881240303081001d43e204441c04003009010890006140d0800211241113440a035a0381c070a40c500369460111224090782e1034107030280c09100500004214580d124081c600c104c00801c4805034070b05d208070140000074032440c460703481403005078007080d0000f001d44203142c11200c024844034815001030350703080b1011000c4203500e101b0803e8035240c00c0b070000044d80114024110b058059982c40314070041c3d54000c032521052041c0308008100c0c1d0104240c0c1c03140c0c1040107814035405090224011070240800c0d2034081c1c00295034610104082e504211030f0903000700903488250f10350714140d1519202c1c401c014204400c0c03001e0014050040c000d080d4000c2da03010100030030700d041024 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 419420854 1250 419419604 419419607
    0xa0b0604030b10080303040b18070e07020c030d021b12072106140103080a05090d1b03031206031a070203070f0c06081f151206060f20190212060106 65
    0x1030040f503401c1c080e41d2801c200410101c07800401d883c42583c2c800b900b020b0701d82e0340210a0350640403014400c007e5100c0c20b80080703440310724011405c0c49812260b004211300c01c1c40104041c0b400c10618517010941d04035100d10a10382e1441c060070701d0f010304192084103901d00121481c51500b001d55000051070903c0300c05001d841701c03a0900b4650303440c0c06800e043c043c100c4551280c0031841c02c2072000800c0746200b01b00d090b0a1501900241a1000303000b01121103050040d10344145a161141b00b1040b0003011580520406410081840b80820108410040c0d81d0465659100b00d4034100341e0100c20240c017000040490b48208200c0c1c203e1580800d134004c620450386400d5019070094000ca80200d41030a0000d80042e0605100c040d100b0000401345c5007441c54103401a00d050303000404c2904101d6071390710040441c0e0b0b5500071a4018055940c03900003446c41400014400d00700700c140700112070307020a402c4c001c0c0b250000d0141012403640e201c1e0000300b0024400900e204900083c9400ca030b001c1c0300000508036 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 419422104 1250 419420854 419420873
    0x20030304030f090b03040215070b0109020c0d0201090b041410020f0403140a0b0a051308030f060f180106080c07020325090b03030f0a1812020f10170a0b060403 70
    0x1184641c44012a00742c42040680307031801c3c907000b04a5600307030500c0042d0240c580581c081201c84440e070302c003d150500d603895800b00d241c1c00340c000340125600081c0500f100081000009508002d40c4000c020800b070076503c1a503901e401401c081c0c40f840c510f50b51010071800500034040341e0305c405501199107400032004180d880d04a84000c0d1500801402950307441c00c0045900c240f42944002d04070030342c0e038404034110f009050142201612940384104200043c110f04004d50180d04016650402403a1240c108004805070180032809551883d82413601401404c10079815607000d0700b03244025560b254140b200600030040c0196040c450841001003854041d60705032202c020010202c0121500c41411905035031000450b180c141c3e008003d5450781e0945075010f00a2410780b0302d80416019841c1e0000340c02c0d031440d604900000c00ca001100021481c000a81081c40d0340c003941c05144403030010303901401c00480c030b1000c04071a030301d00000540c0d103007640d034031000340d1047c01800d058440d503c2e810b10310503030b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 419423354 1250 419422104 419422111
    0xb0118110f13080d0e030d0806010813030e06210a0b0d0605150916020601170d0302070203010b120d02010506181501020f010f150f0e04020112090203032b09030207060f200303 77
    0x78003c001301f10b10b080340704500c060300c10f44060310f60540580705d103006241681284c00054040055211050200e03903900390080c02c1d240009101186060304260b442c09801601500808a251902e40048003036240c1008540c0141c0c4c0041c00055942e8a0b400d84001c51100c103d81d8681c441e100c4420030030500c0d031481410014a04681c00c0b00c01d140e80300d02044004a95090740d80c040c0f544891140403d4601c6500140310b414406000403800401c900041b5007003034504820081b150b0480402104d144c0c0d070910580b80c1c8040f0403190701280010701c03090382107842c4c00034028001d0104d0f9502d20350140c1e4000c0141d8410030900707100030088000010f03140300c001d0510b04101c01c03003040d500400080c1305103048209070503903441c854100c5440d11540d00654032005c031070f007075150181e841e8600c4101680d01030016001000303401041500d51184402800034070800f104c94110304605e03101c0c141c004281c0c0007600d031090b51201d040c05440d50318443d40c10368508240201c40242440650b0521491240c0400903600 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 419424460 1106 419423354 419423359
    0x40f0b030109030309021003090b1819051006060c08030a0e1212060109050103020c0c0609010203250c06080702060a0b06070b040b0118110f13080d0e 66
    0x255090810103a000c070b59030742c4802c0198202647d00134900c6d45c0920f0b0801040c6455583d0b1401c44001500c23100c146100f050010030b040d0020031510b4604040e041d440f03030725074903586441642c840940046180050a1030303000240507000b2061103d2940d84160b0160460349e50814800081c00c540f841e590380c0d445400c1c145038540d540100101080c182e40840302d11b00b4545200094109a0546c1c0510304152040201151004000c185c07280c40e004103d0b811503644122000407807444c01100c0307000c050300c80300703003c00180003035600c1d44400001d11031030585a0341c03559020103030b071075900c101c0d4a080075030000c40c00550724030425849103034a440c000b0a214242030840d114079021903422a41100c02c104100014004884910700100013004500c10601031a4045001042140601d006030f00500070041850301c000c40443e03800501908040f0101c440c0c040c01d80700000c6c850741c80c4280321070 = true := by decide +kernel

theorem cover : BRFrame.Cov 419244604 419424460 := by
  have h0 := BRFrame.cov_init 419244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 419244604 ≤ n) (h2 : n < 419424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
