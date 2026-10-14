-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1310
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:18:20.748347+00:00
-- url     : https://prove2.me/submissions/c6583ef0-ef3b-47f0-9ac2-9de900b37771

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 235431654 ≤ n < 235611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 235432904 1250 235431654 235431659
    0xb0604031514010b12010e06061210051302030108061512071203030f0c090603020f04050a1401031401060f0f032d050105030a1505150a030807030e060a051606020906040e01 76
    0x42d040600107030480003a04d04144804071000300300c01d2005044440b90000c030f40d656250203000c1134951081c948844030300407500d000c015003c140c211211085543c190303203500c0000e031101405c1089001c00e001e00402c58000b600420101c0742c910859913041d600003043d011003002592207841c901903a0744d100c1c80c071840c40e1580400c02d058052103586001c428072001440700718130842000f48002c005000320418554003185801c68403d04900741c03405070101800100d1000c0d03c8107241c942404080d40c2a80c000303820100011400c0040d58a558121509038441940c035401810058a650b11982d03005810196124a03800750000f111400341318900746181000ca12011341c032102d10607104160000707402944140080800195400c00441c460307003c403100010241c9880d100b148140c0c091101fa42d074440060340000c0180320300c510080039018401e482c0c0e8141e081110052080a0040b0742520020034001d01c01510300460006920b4042c611440005291101d681c0003d01d107a00190041c000ba07072400c0f00107 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 235434154 1250 235432904 235432931
    0x7180608010c050a0806010c0606050a0306240807030b040201050d060909060c02071d040618050d020706030c050306120709050c07020a091a060a020309150a020d1107090b06040315 79
    0xa101c18880b07103141c0645403070200d4801510409000e80403c0c1000803a281e42005d0140176071203070024080040c00744144503a00c0c10302d42c000d0454000c20f5010000d58440404d4900c2804807200121003814019220f070b1459910b4600c05401c004005a060010401189940320002c0c412040505200300c0009005041401d01504403003140b2a120300750750010009011580c80d8048403000c28907a20f06d40e126980d61450101c004c0d0103c800c03050740c040d49a80d0342004014000c2110040040c4079401c84500a03903412044040d502c00303204030301c04214104085151030400940076442c101c140c10490b5107540e03480400710211101210301e03202880001c03030000b003146445045140141200c200900142d182800610541640c1f21442e070b100d9480014540c1d9194024425245003850003003840520044882c502c60040d03001154880050181c0c0d030070048110b00804203c1821030034135000700700c1c003800c0070b6104000f0130310034048035482801480000001028580e41c105c040e0ba08220100c0d0b1b10006400c1e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 235435404 1250 235434154 235434161
    0x26010f06230a030305090f040905070f06080c070f030302162012030f091207150c020406060c1502090d0b01080304030c0509011a030a0914060108060c0a0e120718060801 74
    0x140c81d0302c6080907110410200b6800f00c00d481c00b075181100c2600e1144052000280285800d4030010240e018a041c001031100801780120101d5400382c840300c45c6903460035000001362013000401020042a0310070b4502007840f0394007818040c240b10b00d04d00c039002000e86505070351901d04a0420320b00403a04000101d1404c0a44071402002600401181003240d81d003e070760007601030014214010a04680d28405090082003034800825045a03680f55055010000500001c01001d082e4002c03810b01c1b0002036143e101d00441070b0340c150403500b580b000d500c03030000d080081d600c211140d0780e100054030042404101c00b52901802452080019030741d41e480c600e05048103000e554001c2c2d2040c0b02003001040395481030400307685120000d0038440e94942d10310700e6000040003400800360480c8103002c800031001200180300c0d07040e1603640301250866521304607003001c2807140300d5a20000070300c4e074100c40c5030900306500c1c60070a100c0342c6c82c16610030035120b0101c003107c110a20704e41c01e04075880743c6042041903820720 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 235436654 1250 235435404 235435469
    0x507230706120e0a0f0203070e15011403060603070305061311090a0602010b1c0303061205010e100b0f04150302180a06050a0b04031410020406020c0a0b0426010f06 72
    0x94144641d188a8248948813000c24001822903c0340700d109004645d01444454081c102200c40b000e514108480031a510000984140f03010403001c0100700c00309808001aa0310900008003410f10303560724038800310060440605440d1b041082c01c5001216020103010301d200d0068103800ca070351200441010003500c1d10f00c40e403000c03041d649016140c0321561034010b0146442041590741203d03408007864100c0040c071803984002101000d05101004100c0103420020300145100c00305c400b40102680824211588541c01507401507000f0046130090400d50030841030f580480c0714401c003c03a03a030b8021801d04400213001242500080c020400300d044540714540c060802035400500c41400e0019148481c842c5000150010009000107403500800700a910224960031909640311075403074102a54518203014042c0c483c0038500c0300400c41070040c8007642c0071118030110490100344414500c05118a0488070140c495498041d0703200d0060b100d0007080e0080841d2640e90307650112001841c00850b911030b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 235437904 1250 235436654 235436687
    0x30105010b0d0513030806060703020f0105010b03160e0f1c020402030408070c0e060306151c0b0108010c180504020f070c080601060e030327010221130803190507230706 74
    0x484000300f0307845500380f60310a1f010340b01c1a541e8829801d0982c6883e9046d01718100b258201710005c40c0d0201000051402103460403c0190700e10700c600c0042d03c10318000c414aa0304100c1c058818041e504d000c01504c100140c40b1400d02e449213248d60007113010b80e84221015901810001450010820140550b20050040c008095003504144001a803208405003c028101106041c0044c903640d8841c000c49000f41001e0360f0491f41040d81c901070718517000c24450404194a00940f540f10507001c1d000f1081d051305070044003200755040c2800c000c000d4201a0401035181030901c038100c000345000c50b6440c060902d13800200025071521000401081e00c442d10103000b40c01c18409403100007004c9103000104802c0481c490000004040101c0c540720381541d0181141c00c400e1020400440040f004080845840082c91401da4035020580d0380c07403107401d450681d18000d0381d03850031145d8441d4016007403861007040c5c9541e40030440540326049020b10017012401d500401c00c1004080e8210701844580d80c8039 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 235439154 1250 235437904 235437931
    0xa140301080d03091a0f06130605090a020c070f06020708010f0c0c0209040203031c020315060408070b0c0307020a0305152202060f1909060f170c07020d02030105010b0d05 75
    0x1020703821a219001c142c4528140b5455102c18410408103925030410590071814a110a19002c000702c403100d501603a2145c082c10710744800100751256030040700d09a940240281c0180e0302d0f141c9900c8025440301010703000c14025807002246e04c0648440300030081c0115801441c0c82c500380040542182c0c40d040301117581a240c44180910729400c4100105003980454050301141d17100d00205c3d0a41c03240d000c0301c00070300c11400b250003414034207176000d14090315045066004018180e030074842e1a100700e01444003d54043c100400c03051280000401504100d0030640303040a41550200d41070b10310325001180d240c0c0141c0360001600d034003007080507402204481c0403070346404003101c408188031160002070702400e0700103042d421100710751044600c0b02e0300c01c155940303140c803d41b007004055440e58041c0d40001591082950b00884c8110440c1c80300e4600b4039110452a00c2c0e01c0c0748040705510170641241c11090001408025a41c20700c40d6074000c1c401d000c103035942c400d035408401c0e00705d034801010407808049 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 235440404 1250 235439154 235439159
    0xd02210f091603020d0c08030d02040f0b0901050910030603051e0d0309110d020a050a081c0816030518070e0601140f040e0613110702010824090c0c070b0a140301 71
    0x200680c0402c200d0f034040d2601c0a015030581008201d02500e9006102d00e40300000ea1422070f444250b0081c8100d604181500d10b256460f100031184520410311503500040052150041c189030100381c142400e4940d09001502d6607a9a40d1141001d403c418a6003500c26482c1d0b410070480c00904c070134001052240750800654150303070340742013401030300451a81c0036139910141e0400b15101c0b40502406000b0003003c0840e041d0f600d007009030b5a1700207040041c50740b119905072001100d00410049000c0c52500c00b510051500e0402c0450060000802c43c0041c007800c80303c47c02c440b0700c0512920000d0304100d89030305054500326002400300209004160900788040002d0310400a01d40b041c0c1d0180c03a440c1031910000d4840c0300000d904070f01080114030941785088424034620300307080c00501240c1e20070789440704603030f841e00f041c444902d4100c08550401814080404120b15100c0702c0b403540a042d4464181c24880c6503c4038900d010401e40000c200c4800c0090041c01044d0400210701010078101c54144c070b15030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 235441654 1250 235440404 235440433
    0xe010206010603020c211315080a0b0a0b03070e1c0b190b030706020c100306030506041101030e010903180902040308041e0b03090a02010801050301110a050d02210f09 73
    0x220140b044200b010340c0412081c88108083c0b00d03020429103400301895620080e440d19121550101403140e200d0503442c6400900380403000c6d840c5450380c01c1c42d10341d481a5540d4030601d0b030141561038040381e030009120001048031140381016601a00c440d607100f0b192807080300103003d00c0708044040c000c001c1601d01d510030b00041d03100003a9940182c40c616222102c4501a0300840640150300076a40d050084210215500da4000f03148100c10744100d600160002e00f10000ba42114910701000e0110340214000401003a403401d03444150700c9042c0740004003508840e0006003101e2740c1c2c581c2180080d03140c040705080140304501e500090300741e4210840c40c0c030b46990360380c1216200744d00c52820a03401e11041110500c0c07850a0f280e0080c04c2c20791a2551320b01e40204565151540d0402c100d002c940da000010526040c140710b5900c01d03140d2001c1d5980b8111416032706031041c0c1c0014070749460700780e000c0000b210042880d4404800c1050072400c54449400e1410320300c00705801c014044120b035408241e0498008 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 235442904 1250 235441654 235441663
    0x60e070602070b092103030f091c0e0103090318090902121c110c0604240f0210020f0405030709050103021509030d110a0614090c0604050a05091305060c07020a05010e0102 75
    0x2107030510501102e40c0350403514503008517010f0200e800080308002d44c02d1030110030b01784101ca00c40141c0e000d6140580010321840921041140001c02e07180c6004019402070744401041c6010342172564000749800b40303902400d1190740184030708988a412600460412070741c2100504e14500103450f5041c0d400303075400c182503003e032890350400000c074100c81030380308060129440000c0003070210340c0d545440c2c980702300a48038a0088072400c50618022454003621a4409082410580d4046d00002c142e54484001a400c040b455007500030040000149658082110100812111401089540c03441c0108452804c0412030300b0f40a200c20019010340c1c0c0d50114070000c6080c0e130f50038461019005000c50a20f051500400103041c20310b80700110403017208038890301e8441c241c540d0407101200440d40900ca101d018500c00c240d005424004144101e14044804590000f0715150900c00a8003944800380740c80f5040d0b40a803501440010500254208402c2e80b0000d8403080c24414030111203500003e43d42c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 235444154 1250 235442904 235442917
    0x20c090f0606040801050903030708011202400504050705011b060c03020c01050405060f0603010207110409020301020f0301140103061a0d050a0b0a0618171e030403020d060e070602070b 81
    0x892110300081c096079604401d8401030a43c0030b000700100d1405200090b9a5801078031840045404080001018101d00c1d80b00356105601904401c5950060700c1c041d800c11541d19041d0b146c031409900c5003940c0c1403040000984480500002051500705810500e082c00031640009042210f00300451f040780003a002c0c082c04190b803043c0000745510b0487c00c101e00034002c0e200c5482c1d4650070030003440140301c0000343d954000c0034510021001504c2c0c42040608038071681000410009004c138010100d487c2070b92000484500182c005850212516426140395209170400002603c1303c003003110482d6410700c20710f005041040a501e6002e80f43c8105440360317005d41d070314050906440f01d00140103c0040c1e080210019400f5100b45001e03130715240050f0030341c040d030a0000642c65556a0001d1800054581240101113000140031440e1001a0751504050088500030b090301c001c000c000b00580783c0c1c14403c1e91143c0501000941d005042c2c4d0010700b8401d103540080210743c04003d06004040c1e6907800c6680 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 235445404 1250 235444154 235444171
    0x2c010603090f110607082106010f020a23163024020f041701180f0c0b0d23063a030201090507091103010504050c09100504090606020c09 60
    0x2e5810340f0380040c03880d115482c0003d006c0e100214a101d04100d50042c1188a07666040a8150030391755a401100c2d03501d03000c3d80100c0140e100c0a820b1010810015034403c51074940d1514a9580c10060401440c0080038500d0042d5940040d10400401d405007814800c44a50a0380a0705000204a042101d40c042c100000d007050007000300047e0b80c521a032401e0b1071040b00004065450340790b050280481908144100b074a0740f40c0c0e0b0b0644020103030f010321904615a05002c00203010212a8480600d00b070469001201c0c2c2250035200412421005005408c00400d10440414003682d07102e00400540d420040d880a580030301014850996a096064442c03a419104601c000c0c22417142d012401303000c42a2000d06a4007403588071800d01d036040d0042c0c0c0e4050b015004542c0825540c000050807034050341c030005c101c0700d01400140310a18041d0001500321042401060070300c81c00100080d050401c8051074004510001810402c208441c0994001480140081c101e000c11800106818190081ca81c19 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 235446654 1250 235445404 235445423
    0x7051c0201020d0f0e040c08090d110714033405010c2d06090609030e0901150e062203050f0708030712090807090501051504080a0b0405072c010603090f 67
    0xe4020744070310341c91782ca10340c1c000300188070b41442d052014007849425600d410b031074080c07051603a1030a03001d006034121100203000200f0303605103800c598030341ca844207040f02c0e42d2501a490030700703115007410b018400303030f0054000c0b0008080c1103426860700b00c0010707684220b050001c00030440700851004c40b078206400b2031804980012518104042a4004a2480080810f8034110104d000d100095004034842031080d101c450340d0400e09010080c03070b04003d2241c1c107198a502442a4201886408a40c1100c00080c05040c2000708a08140d511040c3c500c9480340c0d10304500e08100140441040110140d03140c03030340541074880c00d003810b4a80380d100e1500081c003200307520010345101510808031440200050015030310556220301d44400501428070419104020a8103180c0c01200884111421964828010305403082660786803840300e03000400c10349080c001d443c00000c2a5180e1051241e042594215900540d041501210885c1d00d044c0c01ca4410035140055a90000c0c030b5107425564225042110003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 235447904 1250 235446654 235446677
    0x606040507020c030717010c05160602090409020603010b090f090106090302010c0812091c02030901050301050409020f060c01140a05150d06150b040306050604050c040b090d0b0907051c0201020d 85
    0x59140a21003d5410703054072604000249031400e03880b4180300c00c04400000c3c8402181c860045a00780a107a0003000d0340e41d4108004000550700d0340c001c001010300500085000344050b00080c4031038100741c1c0090840d030b5000440040526007401e002d542000700321400764907541044001050f58119000090600010700a248184034010040e64400865004204440e1810000c040d488941c0a08038181400c0320a510031041030000c0300340d82c00010306035103040c116843d020400000c2d0055020503604000300760503003041130719144d000744201078a100001c504243d001e22224080c04004040f40406c2d8a02424482c0081221740c030b0424030401150007800010160030404003c0940030b00f4503e003211804c1e80012120010360207441241d0103090108500c1d42c44000b484169141100c99143c0c141080109002a01d4460007400400700042c2506070240050b58a0710381404040d00d0088655000520802007072801c1500b512060280b014203002001c03290b80083e40e50380d08060404140007003402d28 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 235449154 1250 235447904 235447907
    0x711101e020a020d18030b060105030711060a150e0112060902031005090601230d060f0b0a0b0306030f030a0f0f030b0d03030e070f0b0403021309021503060102100b030606040507 78
    0xa0000300004420210742d40c00300c1c00c0000e95241c034030060940c00720700e501300f0f1400c4405a101110080380d801c0303040c0060503600d03000110740329131005021005100b0b6421401c0d0710181c00300f1a09200d0100e16000003460a900c410090100a8507404992210711540040c03125440f8aa80b02501c40c0e80300301c0c08510b0354841c0c40000d00300072604003a0036825103030404002014200048080c12200c20180420000320f403070035a803540c41c41e40e95050341c2102110020400144e416481512049035190001603904401d200103513040c44268032485142e4000320a000f40b0340f07010b00c584006807440000551400c4916034020381140403420b08002884442c2c901010200c0c0681c000c0c1c0c81542c002085007513080c0725454050010000c4010b20740b140d200e000c401161050051540384283d4622403102d9060502d15030801009410400e1a04002515055103000503194407544040c003003035040f1016201e1170480c000901d041c1001d82e88005203428070404520701d45000c11210b030808410389010903030380d0780c3c00300 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 235450404 1250 235449154 235449191
    0x406080303040c03110f1e0a180501150503010303020d08100b040b070501050f070e0607083a02030f010b0a02120c030c06060d170a2304030506071110 66
    0x2000580c0000000c00003004854206901920f100740c885441c0b0220b60021301c8648000f1002c4960440c10742420b01c40740300724412150b0300140008185401300d580756041c41038024a4001a542c0ba02d445c2c2c0014400302c12041241c00c034211903403400501315851a20002d540b46616000c40d42032084c2d0304045110300d0703c040e084da4041c006104090f0b50300c07a50380540c1c030590351007048291005d501e8400812507600b50100300e28000c01003030b60303900c8800314448100405a800214202c1e01040200f000010707481c00040790300543c806000c80d501014a52440750f1400c03c1c15014145656481007081104280c40c03d444d66044d40c0d00c840302c4c103445481c894000d03482d00e206003048003111036001c15001900301001000b020300340e910a040c1c91294131b51806120b038400d0b003084020801c816050b01900b5003c0140c0c05002c00c8001803802c1403040041103840d8a815400c0540000d050f540000c040c01402010007500d500013010745080b150307101d901075105445e00070411105902e20b03215031696004444804 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 235451654 1250 235450404 235450409
    0x90510090b030708180f0d11010605040603110306070906050a030e03120103200f03100903021510030309080c030a020118090e0a1a151c061b08061c08090406 69
    0x3075020b0b030b40f0b040021025000c8101115480c41116002802c991191001301e44c3e444500c60920003441000c80a44059031840d03501220701f01550750311440000c095440340141c10055000b580034040102001e000e06040c41c0d4000c1402c0d00380026103d0820040ea072060071503505070030718600000c40c90500541182907100d030080c1c488084045100100a000f150386240d0788280d1103540081c40c0e17090782424004907404510056906801440780d07480e8601c19030b04010f41726842881558041a0300001c07080101005480b44400d000c02d4030003d0003007541000b035074805044c41000400d410450329000070358400301075000a0400442392500c81807188904124401361590600a0001c6013800440c81d90302c003154038007500c40c01d600180c1c0c082d0494800c210070f80245600501c900f84000303c0014094400308084880503952021040035012071140c0c46184012620b1034045c1818105840c8000d02e452405001240310f032030810350012140c131512030110340765a84903e0f12510f43da444c400007001880c17140e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 235452904 1250 235451654 235451669
    0x2150705010f06090b0d030903110303070f0303051012020609190b0a0309020307060c0206030420060d050f0115090e0901061e060305130803071b050712110405040309051009 76
    0x40c403007501114040d0020340a80d4444e01e4108014000c440404c00c2d141103c40c1c02601150382ca2405001080c500000008840d03006800c6a140205982e90b0b581180d040607000e07400250780c1c40c01d101010000400f014020706811060021940041e00001c04510800c1e00a51050100c030700001d40407100e1001540041403c818440d8448035401000303000b6100c4000100e129004048000c80c1180c0a0100c1c0080d1940141c2800e08564541d59650301182d900e90794001c3e6120248031510555a5070f10040c00c500740b280d580440e07941412a0f101842c4481078100c00c0c050300ca02c078421030400e54070040c00400c5170071100d030300c4215880c2c041141d80189515005428010040c0b440701d00034401011591003119015039040280d50f85042c3c280101820843c0000c04052081020402c0d8920400c3c01405682c02040c1c0c6010125007603450f1850315000d45e2003046413100b040c0d041d40603c00c10810050804070261420b0010740f902d83c1c0c00900e8200c0a000d03071841a0b541c001c000c418980305442010260240 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 235454154 1250 235452904 235452911
    0x180402030a09020418020315090303040f0302070f03150c2309040b030601091b0302030702030412030e1206101202090a090305130f0905060d02010c060f0f06170606060703020a0215070501 82
    0xe4008500d05d24032145030603030181c4540e00201c1c44040030b07031800d240703d503c40c00082e50075900c9aa80b1540303840d1500d41d0640451051000200d0703d0003810314140c2c01140300c0c4150207811004421a28282c829010f4000d00388580d000812005050300621903110307030003403410305e80e41c0d5850400203801044083e00881d014410a40041440310341c0707510108080d0050f00c0d0000074400e20003411803d07480308954440040c1c00a120030440000700742c010441c40e501c42e040141035802d0490105010b40e0441840030a6035100e48240a071003441080c10f403000d4640401011414881600401c025032005060f881d811a580c0003101e05240c07280068805004800c2000c40c1480c6d07072071903840b20304001801002c0310a40f5210126900d40b5241240e81743c4264180c42301030140019494400080141e00e98040c03005032102c401e200b00000354070440014003c403415980700000c855155513b000c0300144a240584d90400151000c03a4000600720f0455034116561040c03040c08400c04a0b0502600f0001071142d0708 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 235455404 1250 235454154 235454171
    0xb06180405030a0206010503060705040e0711030309010c1103120f0405071703040510050301150f021f02030f06091909080d0212040b0901110a1101060b0a020601030b0c180402030a090204 82
    0x1c000c0018840c1d210a0742c00c503034460341c940e4100b68440b80280c0702440881c0007048104104044804025130000039400c00c005c2c000c00702260141154801c48007082503954507030b03400d40202c2d01310b940340074407281c50801582080c41c6210040400a400780400d98856640e000090070440304100050180c008400d460240c1e5500d07030105a500c0d0014080c40303104030603050200842034810b20a483c100d8104d080c204020101162054460103511004041140503d000402604217032070748200d10840c86020040c5d981ca445520340302000d0014001911510280c002d01001242030300e000c0d004620502e800080780c04051800c041d0900ca842d2092010b84d0002c5000720b18800e4203e002882903006c0c070150500b55407094031040c01c8aa0090468032070610601170071814074411944400c4540c0b07a1030000804a89809020680c2d030440d03688000180c1c0404010700c2080305114110742c20508417401b240c240785a41c0d01c0304084c9500002010700603540800040d1142c07d4035000001c500f030300034200304403c81 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 235456654 1250 235455404 235455413
    0x90316030b10121104020c0c0907170a05070c02060d02040f0b07020108070c020603070e0d060f05010611120301150e042909010e04020108090a081315030b0108040b061804 75
    0xc4045444880b00d64001d40d001408a07070b2010501d8026a100800000c034224030310400c4029040000080110302c80d10303100b82400c1c0c40d02041c0e50f02802d06620f880003c00c10032041140c0f0000c004044061090070641031100480d000055400301603130403905680c0343c210f1411000300078000c0d1707840007040365041d14000035540050070082219038000e9030b40c81c0107561000030607035030f082403400000c0d000001000000c150604c1807050b12440300c802440b50b161080c454070340b40280d6039035103000c00001c3da5500040191036000180c480650b103846014040d422401e00d142c0000f4081403181a070842d030103080800100e17100d82940702012a00501c10405102503111020201c0b20441502d0840450070000c480c41e40341c0095091304803603040410803d980e07102d6004403492800604682040d2282c400b0450016070400701a10210320244205800c403807500c0b0b503180c440c0200082c0300c418035142c0318103602d059034803134012a8070681142e200c0c02c01d51202c2002c51918549011900e0803100c1c92010f110402 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 235457904 1250 235456654 235456673
    0xf180105041b05010203131809080c16060f0206010b03060d0203030a02010912030902031b0d08030f06010e04020c0c0d020114120f0c040815040203010b100f020f19060209031603 78
    0xb101040403000c0c0d075a0f01e51006903074900c60a00d6114640514403c00c0018040c000000800840305200109001d0042c0d81e541b04a82c024692841c2aa0080c440ca9591030740000c081c44001c045520306810030201004002c0c2d1918030601403103030341410020025045854030143c22003ea0760203030440c1c3d5070321000b410090081c19560012100f0300014082203030018400d000c2d0588480d002006003c00425030002e660001c0c00e0385010f10341080f5842101004180041c3c095446101d41001484d00f624012000600c003a440640c458844d48c0b040c025102c40403130001d07500d01c54800513038466024030218001603a000141d80542340c4c0440c0300042c035440e2100304100460091030b001c43c000d6080c1c1c0b01c2e140584058007031401454420360100a4202080c94141e5001d0b03089030001d000021000c5480c408aa1580461205032020496181414000d154100461410451070602070305c0d80d890b00d00024072001c040f101c1c001c0c2c0a950040740310816507409004400420880e0070000e00c0166a925120b1600c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 235459154 1250 235457904 235457933
    0x101215030516060801060203042c0f0921030406150e0c0d150e0c070809040203040f03020f0f120c01061e03140615061606050106200a0b0f18010504 65
    0x34032402841c002040c0f40904e180034103980b402e80140d402e150030140003002c06c500018500e8414201c3c0300d040a58010200d81c290f0180c64801c8804142c0e00c0c0c00342c005840c0c0054800250b545201041c06940e8600b000010307a074000364454008200789903010521903001c0c00e660000503c0d10000e40038048440039080042802140c501400d22084050002c0d826000041d40300340e01581d19804006407804182100408000b8814180c142c1040507410108007280c0007102c08039048d14000040300c2c14150100304805003209004000c1030711b0100d04420585400810307210107200140820a40c080180a41150014014400c8151800a0f119142620014141c4400d9811101c00c0d031280c1d50181703000c41d84920035442c1d0039012144070032030014009141d00c480d900e5180c08001c01e280300005003550081d64003c1c4090303a83c85a46034601e4070309003110b19458440750302039409845203000090003142041d9000b0803580080e01550382d414034501a4915070301110009500c1e1030108000c00c101d8180207800c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 235460404 1250 235459154 235459183
    0x5090102030a1103040f060b120109050a03080c03040507090234030e0a0305070608040c0306050a0b190e0105040203100e1609060f230c0718110301051012150305 71
    0x810031080200c01540c1300071360300501140342408105010640741d8000400407030380503040603206034025400380d0071210901e1040740d00f900404218024541d001e0300303184e00900c6000d0000e1640c02c042c4c1e50b403035940d41e0a00c00c0304035040d00403415a442c03c09882c1e103d85da0403680c00030001951002c100c00b4220482d1030300f040300440d40c04d03d9820941e050482d0b2040c00d07070b0313400300040140c24100303e000d8030403e400820450359141c2075440440000c8a82c09107500441c0b03441030104410350000100135002110aa138482c50030300092040003808030402d01e017070450b00281c2d4010380d291103000c107507201c00900750809806682400c052141c40400c0302c1070b440c1c0d1800d4a0366041e01d2591110340c1158001ba6141034030000132100d111080d00c809032140342c68404849040094078000140c85201e007089a1540091452030503200b401c40b44442da8081c20b2402c504605626181d503040600081c086510400c02900b08400342649040c22601580510320b5454480c0d210b403602c039501d141207030740c542502c0c0d1030f0301d03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 235461654 1250 235460404 235460411
    0xd020c100f020903101a130c120b0f04020d090c0303020a060509070e04080a09031b050a090e0a260304120e15271201090b0c251505090102030a 63
    0x8400181c500c25940b1414005014201110710218240c01515440305458045074030b10b03881c010140e4503012680e0040740e581201203410b2910035006002405d80036883c0400908014042c48180d940c03540100e0844411500140c444120581d018010851031074000c1031024804000b10030301d40c00041c18815644100802e1005559220720507807a8003040c801c00c154080184040f800044e82d0304c02900744100340e4940380300b03241e680c0e80300ea10381803207250421140001c280001303000c20308000424001800964800b40100ba080740001c0307030340786180d8502038000c0701381c4e04810f682c5101e640901c000e14189079000a8036400d05041051485103c0e2030100301003003010301704c15102e042050b00040e155a880c101d05062200815444101c900d03191142c44601c0051003500c0125a9503c2e07286454900344800001d00c1c1c05945400310001101401e540c072289010321040012a06540c1190209e01040b640e00c206000586000d80340d0070f590203042c00030b0034140000c018076030b03c056010314441e461550091 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 235462904 1250 235461654 235461671
    0x405060a0b0d0305030a02070b0a0c0f020f0303070f02120406050306040f05040b151201060b0403020a0e01081f0209030613061a03030912070e040503180109060c02010f03020d020c10 80
    0x1040321800041e59410044108414011034007070b8014540c000c020340000352520380705035540000c6840890b05004402e036142004400c40390700c9444200c00a03001d0004000e82c0440f2401150b032408010210400c000b02d9a0140c20b20038030034406001c01918140701b99413102c0c1c407060007a0640c0c00458066015034580f5003540c0f0000e045000f00c4d401103400c1910300640703450316905003490307d03071111000b071b04203031868516014a04240f10b100001d100c135042641d201c2d411481004541001c5034042411111040010322400c000810042403480b17881c515092402c55820018007e4040c1001e42941406071108000d0004280c0b0700301d0401c0780c800c02d0b042007441d00c0c0b00341c1c00c46064520143c0c40e4040e031040c8103400241c184005060200031112080b60710b1240e460070141a0414111001ca40307503040480c0c10701d183c22041105052099090034910a043d0801400a140c1c40b14502c010b4108218020300e440d40a0296040710015031954070295a900410a035003a520304d11001110401403406510 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 235464154 1250 235462904 235462921
    0xd0b041a0f0a050c070b06090a0e0a1505060409170310090c080406110414060f040e01081b010305010b070f2402070c080a0f0209191b08060306060603190e03040905040506 75
    0x855807855804903410755035403a8071040c003500e10001840b450842b40e44e500100d500b91001c0000030f0300d05220f5040d03001d02466208109081e10405070031540100e081c0018400026450608040f040914070625502d81e80d406500810004159212410040c6002c0860700c10660220044c0e102e180610414042c0d005c0005600010f8440da101d0038001148800d080f814a1400100a100304590b10000600306521094400d094403000e038001e5035a0751060507151030401c001d6902c4210183c0900702000158501008550315104e8040020040800c0044c04020014180c1410021800c903501040c2e5aaa0080da041d009602011003903036009030411000039141d038001803c65050f50711070101100c0240e1a420302c0040007010301a0404240c50b09082c4651160511501c0241a1032120000303940c8103895000d0094540900b0003402904404100860b54861404480e00036200c90b400a0106515141c03080c028042101060807502000500248401441d0021030003070b030041040d03d07040c1d11070403070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 235465404 1250 235464154 235464157
    0x9080d060510080108030d09050304091b140f0301122a0f0b091c0321020d0b06120705090d050307061a0904050703031404210b060102010b0d0b041a0f0a050c 69
    0x100d0520358010047e81441c580b0540040448910070f000f2a420607440b25141419200c10001c0400390090380c2c000c4d4105e03140d01031010f9141c10007000100340b0f000702881d030490b014801401780c1d681c0c500102c88030310204002860803c0968600b0306541300007144003244411030b1480361050b0010040b601e4070105042034040100c03044c5c05002407801c0403d000c502404498608060015404d000c80c01040480e0903900d54801300802d4103081e00140e6680548054200300c5400082460080314144183c40c1d41d100da044481d90012003030300780240c44801450000d01890000c9800408038040402e0f8441000f003544c10604048041260445c10100d4030705c10301050791f000f00e0b4082c0072980610b10070800310380281e4050014400306070f40c0914054590402c00f01694900213003603010082c01001070140070640c0480d0350818001d10090001c8452640000c00304003d4400c0a40468000c2010500308003000641040300181d940c2c8400c5503281032980c510714800c007101c200070181e0134640081d003004c10480 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 235466654 1250 235465404 235465409
    0x71e0302280b04050106170a1707050a0b06131409070819150b0406060c02091605121003050a051e030715020c0a0804080f070504051501050307020109080d0605100801 73
    0x31032000d00d511002c5541c4400b50041d15195a10800032130450b81d4040003201d20414200100181c2d190b0386040018151103035000c641521050207100c0000e0030205590411070340001c2d1100950319200d00241e03840c09410b880380c480303600d40000e08a8410782c40070b490344515820000d5607401607840d84100c1c2c44d2032010741ca15460207524140c220000e1a4814003c0844654150014950150001142c00c135041a04a640840d1300b0301c00c82c1007145844010164064011516106031804080d4040c04a020360410f900070601c1742800216408a000102030045820401301d582c100142c2c00e0094480c160713031207910500240b4803104120a0800012540c1a560002040b44808122044200250410081c1e840b1034012440b00380c011035075190180c8050840c2101a02c1003403140d000c41442c02d036840d407045001c0d904110801c09103460241200b414000207080c1103940e03980303070401240100b10560b0020012040816120341141e9158080010f8901c1502c180190788003e20781070343c8280007403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 235467904 1250 235466654 235466713
    0x5090301061e030309081612140601031a1e010612090218010f08010c05030c091f1107060212070b0c07170702040b01030b030606011d12031806040b041406071e0302 72
    0x221f40c2000264200022500002d000f5a00708240381c0c46110800c6c00c086003a80140c0c0c019185008041d1648540f9031041d42101e514803500003190100425a415000d05115440c180080c508454528000c6504000400360f401404170310303210b00d1a0b4082d043e40c1402c2c011100c0d05c1d400050007007124a4140725144400788141c440c141555584110389600e81e1211050f142c1084142c020b1119403601c11698500105030f40e00e0f100320320141c9a40300f80c87c10300160b02c40b0302194042d11104030b46000c00c00440303403009d803c42c684403510b640702c004606c0b8a101d286002412010003010b076202e220907000103440d40d0f500c2210188045001c520044041d01c00d41400298150040340105001e0b45c0280c560304000652004031000c41e000c0c48001034900c3c1d01461000995420000b078003201c0d440ca0900440c8820301c00c482460404c1c0c14808070b01c0d070902550041945824004007070780b826a545400391202941e2006c0111014031809c6030091003201c1700241100903203e000340f64018680401e9208000f202c18 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 235469154 1250 235467904 235467943
    0x207080307080304060e0109060506120c0d06021809010603021305010c08121005030307061a0306130311030d0e03090925080a0b060403050609100213050105090301061e03030908 78
    0x42c0c2c8940e800341e400504200c500b00c0d030300c4242e6010303501c00f030088c04102401120005641d02d003c20900c90140c031103101c41c04c8181c10a240c02c000b160758401c40310040a4000790016111040038011455140084c1d0341113a104030500000281d490f0706400400d03c0501034060325241d04d6440005440c15130344200024864002403264041c1e0405141500c0d5000d90f00c00441140e0560381e82c0400e0843e0320940c0c00ba0782d400d4544a0808080c0720900c00088690015070043c0214075080c04516104614400010100200320b07002c141440740c200199044007a00190030448004016404c0e0394035440610300d00d000c0c550290018032003264624010040600c1c501c0c5a0030024410b4504a44800008000e04145070780d400c1504803e4035900054005148039400411840c244080464271b060040c440c045c1c2c40c1401000295100032505440c0300494000f800c080352517051180009024086a4014042c0f540801030304030010080343c0c1d2114101d0717000b0b455007907115807030300c40b510380320680038010b242140c00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 235470404 1250 235469154 235469167
    0xf0504050d2d0f02010603080d020c06061e01081302180103050105130c0603020f070807060e1c090303081302030109111e03060103260d020702010f0c0302060f090f06090a03030b0102070803 83
    0x80e20100c500f84a1901c0001981a22030340c540d8260781003600000416540412840d44a010030040c55800c00c0c2c0460301a0401b84219100007140100c4034089030400520f80e0206400b000c085040d00d5405900030031450581200c50100884030303070f092105480a40c205004510b01d400b0300c051164030b064010105519003420814150302035807100150201c42501003060b00017094500c2c01820315548a081c02107500c0000317620303203890644091142602d51400788240c640c1c0e20f4202000c10f08403076040c10f0100c0d003a41da640d07441102aa00302c1c6d0207500340d401c240700c03070082282c1c3e4103002c0209107040320000d204103030440350309408001132010550540c1c8520018404189040f41140103e00f000b1190308000741d6462140c401500450805114260003292070800c56800000b0007030414904d107080781903d2040e480081d9140e00203840c0e6a910140c1c8004242c9841d020b1041e1540c0040443c00c5801c981002c8031015920100d07400c0c16800240f03060200b2029610101c1c03c0400c49035141c000350704184 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 235471654 1250 235470404 235470407
    0xb09070905101101051005100203040f0519050d06060303020d050405010206191d06061309020d0b070e030f061509041a0c0417010914060115080603010f0504050d2d 72
    0x14002141d10140700c49030a600e002c03e102401058402e08a0201a5809916080600404090078070400301075400502040c084040083c000b0000c4580440b055401101c14000b42010302070303283c01003078201c06c001642c4002e02030650001000c480c86907003143c0002c0803c04007180c86020314054240182c00030b001003844010040c000001401c2c81c1000002c0f10303540400303100d042844054000c10180c000004000c000c1c03404103003d45282c807000d4424009220903a0003d05012401000281007444d90000700c0d01e00c40c071610002090030310181c2101c484038a00700c0d6140d40d9000407200400d070320b0301e4a172026074a8144003840c140602c0d0b100a0004480440d21821401c1c00401004255520820700c03001998a0803401f280241d01c4a1500000c0d0304691410401c3c034040c11751f8020019030344517100401c003d0b0300250061000d95142d00d080d29150721514002400340000301c426280e610b08110070701091110214a14109103201d45440104511851414180258075010140d80d040c0010b10386100d40d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 235472904 1250 235471654 235471669
    0x200708090a080715050d11070b04050105010909080d1a040e0312090307020a0501110f0115140328030c050607030203010e100503060f0a200c010f1509090c08060114040b09070905 78
    0x96038000c102047e81e6403031000003041d54205410695016000380117200522400317100341400b60644000501c44c508094440c6009840f8907a0146100c6a8a405c0d00d0060341996003401c11400000380180001d000c51441c017541c0b0340004003030882000c074234400315900b0580041290710060303001d000e03c00384601e031400641d000f10b0505188a03150103000803100c1c402c0c4084c804c0100c0b6800c2d001d10030440c58100454000c0b0b584500b0358050003a84641100d0f06c0384661100340c580000080420442000d0151504a40d0103484400c010814410038050105480d01500910b060f00c0300e4075014000c0d41e0700d6404010100d0118032486406030000e40216090388000030301c955021140c401c001c00c1540c817502900b911060450760403580400c0110303014080075020f0140708440c07290180d05000b1105000300362118815640b1801040340c0d9145610340800803402e8440000703205060540f03035150b82d200d00e203640058100f00c94610843c03501c40c21401900d0201012409024255a4441000d08003001d01415 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 235474154 1250 235472904 235472917
    0x3061005041e0c0f0e12060a0209030f1504030f1d01080c0f0a0306150908060115020f030f0301060909060608060d05010f2a0e0303030a200708090a08071505 69
    0x2c80800d141c110300c07480280540100304103142e44d42e60100990100080045103500311340342c45100d500b403103510300d4080041c1107504208041401a503a446d0140000c0c98940c0d403100300c0c0c0309c034054110f070048003017401d0b15003900c01e07402500c2d18000b401c0d40300d5044a21980c80607400400e440d003a050f8041c1944540c40e202d40c131420604409107051804c00c8006129084108440000707030b01c8481c2803256420b001110340c000b1803a4185828440d00385580d00e52a07140502a000c0b440c81551542c030b14892080240b03252140004054035030f00c180c48505280b4070f510074000c0c100490021000015548182c0c4075220444002c0c0c1d507003010070703120b150810060041d038103020f503542e41d00d42c40c00800d6510719200e82d5107610702d10b480300400d1a035050294903458180b0154001070050881d00001a41c4000c02180d03409a82c0c4100001c0c14070b41c1d414000414003019803a500304c000c001c5084400c1080344030040c50400800ca0341008002d0b52110415500e001034002c01c0380241502c3c00b10042103000e20041d098 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 235475404 1250 235474154 235474181
    0x307120e0a0b011202030708010b0604030f0f080703091403071d0a110c0a050c181617010f03020f030a020609060d1d06060901150203160516060306140306100504 71
    0x80d00d40c0c030780382e48101050a80200c82c200d0a046641e0045140c1007155500900d00c2000a018160702440021014019444081e040032080d28286e0b0800c00c950b21b07540440f42d44001d4058403420b881c01c006084481c6805a400005490600c056003440c1c00101c501c215501c44031407180303c5074415024a101074010b00805861501c91070100c003107442e80801340440711400340082c82e210b100390400b54906900704540c94004d8445940120ac42002001c055a0141c031080341008504403100741164070380d1168400480740b103032081c008039156808468070402caa00844084200c0c0c00718904158550004e004000d610983c100480c4d007803401c0580240c0244610104001802034180764a0120b079007420102008a8118000b00100751820200a03400360000c04803c9021000310140a076032440b0300240c60000c01720000c4601c0c100034080002d0b0480700341e414501a06541d950301c0c040c000e07203c40e020b2a01080320b803144c40006070600246251050a00300c2d041e02d030240c0f41205020061041010184 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 235476654 1250 235475404 235475413
    0x5060a091a01051e21060a150506030c0c10020316090602150a0518010e030a080f070903110d051504120e0a14120d0e040605040219030b0102070f0603090b01050102030307120e 77
    0x210500824071900c6a00035000003410721031600c00c40d41411948c500c0240c12070100300340e40030300007629440c2c162907000002d658200e650b42c54403941306180039058100140120300010403c41c260400d80170211100c025519400405901d4050913a00c4c0c2140304401021580398100255200c0142d411490b00f02105613024040c00901e80031036801c0d82d081d548500b0281e0b0000a41c0c00210f58481d001503808a50110b0724291070900ca0001448550741b0310024000140c00d00c1c0c0d000d030303071384d500090b50114030707400004c85050351034080c1a00c01d0303640d00702ea00f5682c0c09201a8064061802184046500080181f00c11903842c140b10307040d00d514191050803034200060f00d46440c00b00c402080300940d2000a5201d01200c0100e4800f04416280550005030041d801440001d00905511100106039446820045a00302c1c0450040345050680d6004201c02e00450b84002003082d0564800d09100e405828401203c0c1e8075100166503d10080d90400c00262180c048414401e00030b600c40c00c4d07000b00140645 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 235477904 1250 235476654 235476679
    0xf050f041223030f090708030a080402040b040501060e10020c030a031b0b0c03010f1202010804080d0e030a05090f09040f0b0c0405060703050a110a02010914030a05060a091a01051e 79
    0x1081c5000b9224024012034400030500454030104c0031402c3c0e00264040003010901d00780b034a0390340c6078010301249005000888000c0303800c540d81c41d005483d0910300030b0403c00c1507603035640004001100d810b004a0154031000e6010748150310210340201e1844000c2e004007000122070f90120389601c506044456400c1c00740030341200103000c201116003e4180000c2c01c1d510303941011440202d40c0c0c125404031520b805140c10040040c0d0b0000b0b00a54401d4101c81810b488400b0b403c002d00181002c0080203445000c0003800111542d0404094036032602c00b5152000000b000700c040c4442403c0075038014084007100208500090b10031074690fa0302c003503042c800341d0074181e076200820803540140d64110003140010600801040d0301403c1c41c0c040490030401032000e00d0587e00003824181160049031507524802d20b107c941c507142001a0513003264070004850051a1010070400140b40c00801245e91410140d019007881c05c0211403141070724402485a001040c28504801c01d85141812050308a04201d000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 235479154 1250 235477904 235477937
    0xc03050c0304290310060309030c050703060518160e041a190f050712020d290a08071406090d0816060e030403030504090b01030209120109060f050f0412 67
    0x1400003000b02080700c030040201d118005000c280442840110040113200f003102c400250300410f0100c0c6e2076400d00040204142c203086560000080f4042c10300e00c40d4403000420000d04c8da0045100d0a20110311340344410700d640741d83d5100c0483c100c0700003000301456403e000407250314506981040c03144600c0022a1030b02510341e542ca01c02140d942210603011031044200c2c001034001c80044034450442082503150a1070054071142c41118480101507001c1150b4511805c103521140040c0d24491042c1c41100e039405041e6840c41d01554641d000300401000043e003030300c0000e400401da500b41e11038001c20b0a003042c140b020307980010a00a60040c1070003841000300b2844401040075120051038104411090f040a5040c1d84c80c0150140d05907004010030000310b87e01805032026203d10050111701810b00c0b0004070064010540e0841e40072016041e010381001c4154031241d00c60b44205014003025400c40e518170100d5000700d640c8800c01095400141c00907404100e000c442d100c441c281240070200c420750 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 235480404 1250 235479154 235479157
    0x506091c0506040201020c01030c020a0f06020d11091801080d05030406060e0108100510151809050c12010506120610030615020102070c052709070b0a030b090609040b070c03050c03 79
    0x3001c0d10325410150a000541d41d051045452580013800e0900c045041030100a654241802024203184900407105c405c101c0c054044584001443c0405c2c00f150308001d48041141d8232003ca5244030f40340c003055640f480c00420306902d0407120031401030903821001c07a90681e51540010001c80300e09a56202c00318151810740c5000e0b0207001010010920030416081c14411281d018104c4410b9109a51080016030000140046030059a103003600701c1102d004484048200350350044174845084c241049912819140940304000c00c0100c40e4103181da1701c0c41801010b00c1200751008a050501000541500345400700042002c40c0707240006100b40d0b07940490346140002c038031410050b500081c401041c040c0301e10700400034100480d06c2c2c90512182c030040c600d00800c034034102c0340c03036104120014a82c10b105101036030007440341d00c43c0c140c0d4450704044010010311002a180d4400c0d002c070b801081c1d01381000a5854810b60740401640a141c61707603030080c8c5c0ca01000702000c600f001801c00c00244061010320 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 235481654 1250 235480404 235480459
    0xe0f04050a1b090b121002090a0909030509150903030d0902130501060815040608100e071205010203010f080d0f03050a0b061c0b1f0c140307050d09090b0a050609 71
    0x80b484203180d4140200e0409850416040724840c0b00e0800303180d412014040352501c84005451030050703441290764003003240301300b59502c01c0c640310b46001140c4041c19004002007207100c03000c0350b20300030400e100109113416006400c10150503a0003400408241c20b20b030b5003c021180c1c0001d140c2030a4954400000003522001d0304890000380e640e03024480740603070320089a48184012a010b1289504001c5105d40e40c00311440c1000d03c403501c94450f4003141c0003d000030005052601c06d040c00d045d0fa1800c2081c040d510a22400c181c69480160001d0b00c613a011034141040304480e0750320902e00d58056011400741a01030a14040300366030305944004da5031071000800381d400f004052024104080a204400c940342040110300881024160104010030340c4e040313a004800c541044541c2c0c00032030a0107a401001c481640da098800001e098052200008040c908003071281d803011401921498210142c450000102d901b004910704103002070301e07041d00503103161300c0d02800040c84015586e8070351140e5003d08 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 235482904 1250 235481654 235481693
    0x50606241b0d0e0609040902061306030b090105040e1e03040506160c05030a08030408070c03080d050901060f080714120a0f0501050c090901030303020919080708060f010e0f04050a 79
    0x60715054801814400c012181d02d840c00e10a074081c4142c4045001c0e84a0030401e03501c999a2070008004660303403041504d03c0204100d004c001f050f503d913100030300284170581e0300c144200c2190000080c5803a181c094400c040c4a80c6029005100346a499041c2098805010900a010034840452240c0701d09000d0708806088010728442803125083c1000001c0c10b5070000c034002e400002010000c1030b048000c070303070300302d0750050301c45640c0c0c45541007025135841e41e83c2004040b800f000035003144490321904140d01841c48040204419a40c0798048030584030503200d210b40a0300f20390010083c030f84d80c0301024002030f40081c0c11128454295403606041c0034a050b0100d0380703011454501d8080c01024070403203038032036005d0b02c0c15440e052800000075004001444000d08160300040c844900b5216040445140100b41401e0002c03e0788400449880d04180d0141102c0d40c861000010040d92950b440c19040300c520005191035074540c1241d8003c5075030014000d490f07900c110181c0c1d40000745669440814482d02 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 235484154 1250 235482904 235482937
    0x6020306011224080106081e0703050129030a1502090409020a060507120503010609050409060b090124050712080c160c050a140109091808270102060405060624 70
    0x11044862400045800c6501380b0382c0b400340184000040010317070203005a0001c3c2546542c102548002d4078140b015040100154240402280c0c2824071000c0000038420003c80200304c54070719001e150740d070349442c040a0a50704100381c0e040b9a06009500070b1900d510094008203580e096500442c002041d1541f020f0001500000d580060003920003520b003001e6154500b281c40c40d450304100a005d402c0c1c0e40a003610a0341d41d02001c1c010131201c0d502851f107441e4040c080410969440901d1420340041f0725040d000003486107018401240304504880045902131003406050308001c1c0308803590600100441a500b4080240a0103511307500c43c101044c506c46d00e10120018240400d01c90000459840200000d01c0c1c821050700c9603800c00221816126805030002d20039080c0f4001c400601c64800000e0000359001800701d00116110070820840b0740a20080103c14540710012a601e01c4220341c00b40685d0407070800b10309a407521001240d91107882c410b08044090140f16211407580c40308000c0d5101d44103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 235485404 1250 235484154 235484201
    0x4050c01090515070213021b071503090803010b032205061b030603101509141006090b0d0e1c0c02090f0106020316061b0512061507060203060112 64
    0x280012450058042942c030fa80d00009030400402d124052000c1c0288201e41c0c00c007008031200c445034151141d030110110003544034001403020319190111030149400c0c540d943c021060070a03000e80188003e10758805840c1d4516841d000045a094002a01403548d4041942d206204c0303903014440a0b01c2a4007407406042d05007041906488480139102c01da41c0f00b480248200420742da408500c2001c0d201c0407038404100310340040c583c074609e04c1140d04140001807400a080e4018034009002d1440f5900c1071780415807090300c5001c15a12160301d07103e9500c3e00c1104010006200c2c095401001011003410225282d9165034410107080036540581c0c4e000154005040c0b07010740c913000038200d03000400808005125410100300075240c0c880c644c600c0072803150a690903003c2001c3e591118a209614010301d00c00b03503504020040080c2d01150030785451480310310109280c1d04d480384031241c0182da4480032600c0d0031800d0345d07220007a400043c03800e07040c1300000712002e01d40364560041038100380c10072409200408 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 235486654 1250 235485404 235485407
    0x5010b0f071502070615090f270201030605060a02030a0e0402130b0a050403060204030602070b0601030e0d1805060304050d021209010219080c0106090e010e03070f0201180b040e15060309060406180b04050c01 91
    0x62003c040c8c08022401c0c48442c2c42000c114060442c00d0084550242a2813582e034001600504500e03070207507030800d134001100030304554040041c1c008076078169182c0803c0003039102000140c0c02a1000c0504d1032a240c002040702e02c0302100104501d2080f428140c1c241980e98584d10100c0c0c116520546e282500001d0314400c22800e070503400d600840c03d080030009012201c211030340d215407a0852a0504c5041c4450586500c001c284541c000c24005150994901c4c080ca08a40c4440a1105410140c46440c2003441132010020580710706007010b03070040201070001e984101c10907083c02415940110700708541380340c9010a005400103401144008660408542e1180e400c5583d0302c14070b03c0081d002401b08200052454600342c500580900c1c202e00c0310314031003403c04000c0100f03a000040411001a00050080b1408080b6100749003000203c9460381d848010300c0701910085803607441a80103007000500041d00e9030f0100c0002c0e0f0304040c40007403240859403801c01044017a2001d690540c44060300b503210b503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 235487904 1250 235486654 235486661
    0x100509100b010f120c05090405041202060c0406171b0a080609150306010b220f0602100504050d0f03200304020a050409020105030c0d02121905010b0f07150207061509 73
    0x405081c40c10084418902c1401000030300c40c0040011130720744a075540d0b480d45100e0002c3d6591500020010030082c14985404111404081c4040015018030300004034020b1a035001d40302140c22644a4031460400760000480b034100040030030600d48043e10700140d8140c0c000f0083d14402c1215290707800182083e030f0400a41c03000050688840041c40000c250007a10003081c05070455000800058841202c6100c0340200d10a4040180c1c0c401c1046000141ca0003090550f1340c07c0300e07459001d0302c1d0600b078011f60400603148220340190690f40700c039115040c0c130740c800d0101e00d80000161a00150700e030200c00c0c0c190607030f04007020b41000b00400441800150310b4001c0c4250003e201c220360421105010783d0000c3d02a00006090180c00403000c5032641807410281c0459003881400702680c0410710b00f10031540500304251030803081c0700d4903000000c0340e009081802c44024000c013009241c2030405c00e90b904064400280100c64140e0380038462080003038858050386241c070800ca040e060b400c03403c1140c2c0b40d045 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 235489154 1250 235487904 235487921
    0x7050a02070803031009020d1812030e0604020d0f0312150905060303071703040804030b07030c0225120c09061721040302060912120a0f2a0510050910 66
    0x283c00030014815031074100a91501155220075002d40c40d050201e8800b801031098005d0402c003450704030036080810094201c3d216003003820340c0b0308010000140c00703c66640d11048a0081d088044006c4a10100c0c1c500008420030610030701d45000c0014107041c1201c16101c2ca11038031141803400030000d010b0108240900703035000800392700441c2000100d49401610002c00c040180702c480d40000407500f484500011070700595040a0384402038288200010001c0c0b407242115030041c00360b000e103580c5480f5a041e80d688400e80d030b18120780700642400d6041b01b94858004d001c641d03c4c04070b140300103244000c5000c0c440042100b2000036403a5015618100e05040345090140d072800000c0c0b0b86d010224400c0e5040d101070b00d40558030035850711010008a5042094003c240016103e0031051442c0c5407003074001041400e860759501c010303001407000305071081c02014212408810141c4500c01c40e2410080340c144c40c560040c4200e503a04001402d80c00216001034403d503002d41c01a9903000c48a94150040380c1c1c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 235490404 1250 235489154 235489169
    0x41e05010f180c03030e21060f0c031302011b140606030d090f14310b060c060a11090a06020a0303060b0f03130c08010c03020c06010e06063007050a0207 67
    0x280c2c0941a40c41e140c07940d800c0d0200406101c0341c001c190000b41c6441036501c002d0a2001902181d9100030905199135920855001140c05034400001d11400840740580340100b03d1607541c0908030010b94015a2015148404259171041031001c2001281c0c1d01c8000b0314440b040c078000f030b01c414100203041c90304080804420405000070b4110410414000304101c4044403040d01d040d102d21340c10700d0001001c030684006210820300741066442e1444180e516031480e40f202d031500070410400030109000c803034021240380c0c081903080f15000030416281a0040200340700102940e51a1442e203500050070b040558002c1d0b0016800b001c090810140c040c810500500404005103041400d494484041031000a20f0442e040d2401801d000401c460100780c00003511704540240700301242d0000090080d084500699114460103000190080c038142e6024085c0c4006004030f4a4070101c50b2242003041c1941c1070014400c403030410f024640010030400a0b02640d05691001d6441f03a1040d070080c0b418003213401401c07 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 235491654 1250 235490404 235490441
    0x4020901090c05070303051306020301060512070e03031602120109080417010b2b0c0909170403030219140304121514070c15060f05090901180803041e05010f 69
    0x40040f9080b10684460340d506150214595884500c2c03915a120581e000421882c00400049000c9421402800c0d0050120015021907500c600042381c00c04041c022180d0141c00c10041a048489030342d10400f0458000340140d50707841d0100201ca401c6407078806c41030724000b8022400f4044c030506000304413240c1281d040244081d0100701e00141d4410310a0104041c001010400b4041c5d521010403d81801da41000740c0c40c404940d6242e100000e002464001c4459400d040310000d001c070180d100b07031401c0d80c3d0542e00504850300301c0f0070810441c040381300303003a505061310020114544a0070401032025101000304a14615103502d4100b0116860091096100e424202c104001402c8524040c2e803107000c3d45002200710506007803002c8840b2101c403c0c0030509042000c04250b0b09410b0410324221002075510305c4107541c0e1050490708032181e10b460401c1d480ca444a00b00007054046029541060080003c10031280c0400e281100b610164401265070b651504800400300b0034500c940304a0703103080346002 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 235492904 1250 235491654 235491671
    0x6080708010b04081b3f030c06070305090307050d09060e0f300a0503033310110d08010504051006051b0106050a080303010905060406081b01020313030b0402090109 72
    0x55841743c900001401000f80c0c60740030080c50784d43d469858031810307540030304541030741010380b11510141201c208003009450101911042403a4000308542000403c070024040031307250700c0021805071002500803480c601c000e00610303020500900652440d901992100c4920a02e00640940040d1345000985c0c46008520b280c2c0d60349032902c4080c200245042c08402c40c40a00c15640380442200044181c40284100705810082140010003180504c6000304280800e03070b4203248401e411040001c0303401900c402c003141c4202a05214005400d651403038141a51304c0444406964079207051800720340d0000f290480100100d060503c941900f1040ca1451901e40c07e040074005091842951858091400c005c8441c1284074021760045c400303042e005180101a69030354110941c1da40080c0a2510050b25080c00b050b2145000d02c259821a08908003600c0c41d40102c0d520000e8030003503440b80c2d0341580800c0003c140c1c810301150002000c1e51180080c00a98200390041c40b40158050b0040c00c103071858425034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 235494154 1250 235492904 235492919
    0x30f1b0a020a0b340201080c0d060e0114090103020d0807021f0c03030b0f0109140a0308071b0e060f060a09080d2303011a0c0111030709150f081501050405030706080708010b04 77
    0x40c200c02c0e540a0071f20f0103070341c0c860700c00a80c1c01d88100340e1541c4d0310a02e02000401c614031268500350481da00022801844984107080050140003848002d62281c2101502c100140713540c005000203500042035049040c0c1c0320410707801147c1010118000003000b01062408140d01485040540842910300294104152001802001d5140644003044003800070000195071380d0f26000f4081c562042030291561407a20303125045072803683d0080c120701440203011400001c2c40760428401c5400518941207844210140041d80d8851060344003000212000410441010040c0c02d03650505603503110b4560214255200f0b190800301c401c072610507010001084a03680142920826107100b03215207a171036091040c5140100340c403c104e44181440401000703101c42d000010300080700d10f0489900001402808110b4221054a0031000450701c0768000c115080c40d10404500c943c1c00c10b040c03280c41d003519131001031b10b804120351000d80050040350400140d0b680c00144a4018101c03a96607a00b0300303050651 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 235495404 1250 235494154 235494247
    0x1b030b011701020f0f12010905090a0b060612070519030209090103081612031409060f070f02070b0f07030905030f0c0405040305070204090605040201030b0102030f1b0a020a0b 77
    0xe84049001089890700c1252070a50403903810030f41503010350350349001111080d01070b90417009012501122000001a0807100c6015042c4524202800781c4002109940c1d026401200a08925000401070102c440c51f480160703500c0d8054040354540d10707240e201e2038a42607411040f0490390010180107002e856800e40b282c1c2c52480c19640e000800b1501c407680b05281c14502c14018401030401e0481d060145003054244d40000c010760b400e40102c2181d0750b40d142034680c0d03c01d0103035220b19464060000040c0180e00c40c00c10000d15822a1050340c0c0203c0d9901c0f50802c140c0c000e068030f051043c1000601c00101038100380b5900c01014260040c00300b00d0440203245072201c00c0a03800500490722440010200b512070001c848038654014401c10030306405040881c0240070491b0100e000c02e00e00400601c856000105030740743c1d44940c401441c60030341c0300b145055a140503d22203082070b1003010800c0c00107940350742d0120b020700160020b0a407a01c0d1320700b0404990070b000e802d1a100f0658000c0c000c00d14401e0820 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 235496654 1250 235495404 235495409
    0x1218031211030f0d15050f1909090b060f120d140d0c0f0305010e0105241e070605010605040b0d0b030a051c0e061201180b0406060305041b030b01 64
    0x5100408244221905645114805070994880d00002401c0c1030000315000c054441800000c80800c82040e4101c02d80b9030100d480d00805038040100e8600ea04c492508000c08010b11803c1210560415507660400080e1104041e0848003c08840c0070020790b4100045400c1101c0011107000c6521410a2482620f90326403d03103030002c0290000d0f5991812201d0011508100d86a59041101440f844002020b85c0c1c1140c0129000a0600300000b500d04580714002d81a030300000e21401c1d03c50000b800c0324002c04080307000248080301c1400703d200d40094003010b045c0701350000e07420703a80d462820f031800908465058000d4010300ca0240404d000301810b400c01d907401c4a8a6000000d060100440043d00e09141da850003002c030310550300100003d080800d080c800d21800360311104088000101008910300a4208030f801081200c0010085080c011074500041c110580000030038548050105054400b290800d5000c291188240402c1211002c000c000ca010304e40c10148a26045036981c00d500321061 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 235497904 1250 235496654 235496663
    0x9061404110907020f120a0f0905010f0e0406090906240b03270d112b030c140708091206040b01031209050301090c060305060303040e010e1005130504121803 69
    0x85001070343c0b0074001c001030320b0792038110303411039144040c44e041204055204c1c140660024010424122845d40140040010345d94140c440451001c1f80340011658040d0303011150358001d4071440000b070803c0c45482502c040a000381c80c04500c03900c81c00598540b0401c4501c405205400740c10007044800901c0d41540e802400300c4503082d890784480100780e2114100c1c80c0100045000d000c103207074070840d0030002c60a06500408161554074000484458000d800300030751120340f1030002603030081d491090340455241e40b2a420584030380040060b811403e50460001282c3c07403200094008502d01d0026410780000c6111002000c042c503195480a50301c16042c40014814444600c0081400d401001700c44003a080c00341c02001115024240a240d42859100f03a4011924000104516041c00303c110f40c1501c000055644460b440c0660f15446002c001300420641c171450200421565100c030140032144105000110b0241000c1c02c014041206111038581800700c0560512240251960000b0407250003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 235499154 1250 235497904 235497919
    0x3051c0c03080a1e0506011e120509120a030209030705151c0b04021606061d16051303140114090a02010e0f040e060906060402030103030504050613080607030906140411 74
    0x12402e160018000c2030361a80e19103040680c0090400b40260b02c46031203951b0990310403624080811740f0029010702c14440b04001101c41000c90741b8006283c120760303001644902110000c20800041c920240c1184840100298000801ca9103a00e81000580c010300070407144508414505030603510341e4403038007800380000701d0114102c500104141e4000c43c071044014100399610344140c2c00c0000403581080c0704940240c54403501250000000d1600c41d04600391000440460303e8600d0075100b04103502d201c500400c5001c0040e1044411070a400070300443c030a40461403e5400c1d0410f2500303540004505005807a04d102c10090218000200700c00c031a50203080203100c210302100414081d655561045070070a00b0b06040c0740d400d120020f00d40744204440410349020f130311488200401e910081c40b015001901c10300c002d01c56403502900400802c0c07024510f0a01c4690740d10001d6041400441e00c51004c02d40d140400001d000340d90140c0c010564400f64100d10318585aa260004180300c4c44045016002 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 235500404 1250 235499154 235499161
    0x50a15052e180e0f0d050f130302030a060606080f06030d030908091503010302012c091806070809070506041203050901140d02070210020303151215010b0403051c0c0308 74
    0x119804003034203104100c0740d800c410700e21201010f04400e141c03041c2c2d0381c41140d04a40340804007254140e1074419560311545004000021141c0542000300c2c121003100c001c142c000700580d000c0004100140c40b50710081402454154060a4960000d0007102030500b0030701006510b136404185620844014100000d00d150310b800d1a1425000310782c65150084021003034aa00301d100803000c0e5040303a200b680c03039040351508010960f540c00b0194250100c010141c0d000f030400d5280480700300f43e21504407003044021442d00401a0304e420b50560341c44022a0700681801030320b05007441100e000c0e0000361340303140c5003d1910304074681c680a08400a4104040850341c3e6103e03a100e404441215841c01003200d84560000c1c90035802540b1041003248500c800c401c0d442016400030040d248a01c00107001349542c0005041401030034168100c608642d40100300b8100140d40245603900c0c040d1040018142d22075095160141c079040d14006585d508410079501c41c6003003a440b41d0841d080d20780c5485c201c0366507103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 235501654 1250 235500404 235500481
    0x15060d1a0703020405090a020c011b0512040f020301140f1005031e0102070f051c1b02040b030309030d031509151517070804020a0f080d1b060603050a1505 68
    0x4c1e900301a90040070141441750311000f5401078041004140000c00a03104003840803150f0301800c45994010030028062000c03941182c440071136005007e4400c24460a202d03a0002e802c45a000070721840341c1e0940d000303216810b4100841c6942c00006002c1290381941000006661401d0038082402c40d50818402407058400c20740649410710b90000c1c032440d060619140041c0c80d111080d0345460026444044005400d0ac074000082461240c5001c58102007569000d00015100c080c0d80d00350148402c101b0380380991401c010710321400e0495540040c0341314003084010103d099540c0413580c52800c045540714414441c403902c07030840f540a1051503503080302030b50940f084c11060b080c0c40251403c0c2000c1058068202800394805c1e84202da1503954035869000c0886155003a000e069143e5101010b17802d4014020b4480301180001d000c88410070040744c1ea1a00103944054200705c8503070300030180502c20458845204070315603104003020300c02032400c5583c800d840700032800000c456000003861280186c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 235502904 1250 235501654 235501657
    0x3150a0b0d091b0e040302060f04080a0309020d0b1603420906090203090c0a030803010b180301050903040e10060c030509120d110f010b0a0e09160815060d1a070302 72
    0x715060004104529070701e80c01a80012411176041c0d01600560000641044400c02039601c200e50281c0f425040412080046004104104040381c004001080450129440000e81845140c543d107181c0404443c29400505603890418103156102c0320045040c1a00141c040c1000001080843d00865451255080c000c0e03c2241d404071001901d070542c003080001d034940003948100041012282c1140f484414012441000d2101130306d800d100340018052150003400402c04130042a101c0d51a409038031002a08440055800801d26407002404000900000700c81f981d1106e040c034410741e4214038002000d40b4603034101c80002d08211b400030b040c004a945400802450300080703c1201e0581d035420101a205084002c0300307280d54819005480c05074103050080049110004e4920304a0310315144072408002000340000030640103000e109010003128440400c0101421802400c0b07000caa69000d0a44c01c0020340002e0003005040300c00b6002c24820039005040700341100b054203a5541745801100217 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 235504154 1250 235502904 235502933
    0x504020a120c18150807050d09020a0909020429060702041b18050607150f0b13050f01240e190803040e0906011220040204030803150a0b0d09 62
    0x16145004000e08626a0080b003c146420100030841c0716591202c9100302c614184450740d40008401500191103544544c01400140481c400041841e0560b940000c00760740c90382d0448055a42c2d6001c8040c01d61516000d4044125440d200420702100c92031a2140080d184200d0940240e8002820000710b40300d0364000782c2074030640c0020502c00304082d000186800002c3e240f80d503000e0901c80d40400c844c94020125055541d02c8503400c803030b9960b00361030b42c0e000d01075910100c0810350790b03915090b0080d16510310121182c05560800101843e000310070606145040c0c1143d408203450301c2c1d01e0f0b074452151400c480000c405d94207040c10103940801c00502401d0500c54001c2c440918441e0000e91490b0003c041c5c0192800648240515940d0b6400c00e696032000740f0841c0192440a911640460078130034088400f004425002c4401c80e070b214000c90142c0e881030340f04489543d070000400c900380c0c0d400c5c064100040c40480380b0f12043e5180c04808000d900904d18407190040e51643c81380c081040c0c4024a0b10b2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 235505404 1250 235504154 235504187
    0xe0d0809100e240903070605040f08070506010603150303090e130501060f05150304031e170c09040e06041502180301180b0a05040f230a0c050103060614040504020a 72
    0x54810710619860f01c450307102014039004240840342d805151004025103120b5a80f0310002d609180035522017401070700000e13106480e0000c000071800d011902032030007828028000d10091160b5454070900404443c2e800558a0408814500a00010303600ca0002c8040b500c031400c1c00c05464513203030360147c0030314000e00c00148550300c2d040c1c000429088881c00d0108071034040f110000c3c940d00c40c220380141480201c83c0140040d0300c4607044000007501040c3c015600410b45003601c2c1d1302402501c41440b028081e500454400b00201340c0400d43d00d014090159040700590181c440c50805a80d281d0521000d20000c0b0803250700440d0031854401840100494050010001d0044044840c000b00011585980070348400c0d0407080020303c842901d00a0a02983e404080e4098908494591001c15600d12240d032003000445449010360203801c129003c0e5840c014805081024038001c005001c88000343c0c005024840740c2c043c9502c4040481003030f03400302c0e5015140542d4802c40b10074200c0341080010800c0c80e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 235506654 1250 235505404 235505411
    0x1706010b1b2b030f09050c01080915090a170c0714040b090c0d05221e06090b0603160e04080a090305030d09060c1b032d020319030e0d080910 62
    0x44160b555449180480c0b0201c2e2000c100c40c100c02c14000c0c090380c0241c2005803159002600c160040d501c92042e0701e6100c3d01d51801d4034060741d05d071941c0c8107590b001569080340355400580c0e0902030041c11655000042510700713003145403209c024982030300d400282c4522095207401e0014840691160b030088108942e00070950300301c3d45001141c0f42c0d041c1c0c0103002c180106074034003000141c40c2c8950440d042c0c03410341c2208101409400a40c0d5040c040d4628004203490541184100d40c005602402101d401c107104100c0106a40b80c10424945003582ca81001203408041107400c2100d00c840810345074100d03401000c840d9071070000c942c0c1660342102603070004029100014298610f80c460350f116003580703446003500f44203030b41c54a002101c00780703c01c00902c0c0e0101079058410002038080c000691000e64014030310801002c08240510b1125100d88011300581c10000d40142ca450340015150b4082d985424100610850054101c0d13036440f1410b0282c050200b80e8000c100c01c54020800030403010324600701031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 235507904 1250 235506654 235506703
    0xc09040908032406030c030601030b090406020a030f06051014040b03070207140103050606030a02070507081e07050907091205030909040303091103060435030405071706010b1b 77
    0x3a8542d0044034860012070b40001441800040d0b60303050540c0300da0050483d411900d43e44006401c42d84081c1015050660324070340b0a665445071103201d4443c030b00824006807584540180030f000c1c7c0701c043c1e0715620321500e812001d214654503800011149005450464001a5400d0030030640388259003200f0302c02880401045103941d800106002640c0b103144c0c0b8bc01c50501c154005501b500c0050360b195502c02d000384001004464646e000d45400d6010340200c070541036540b420f80b400c002c84503441d91107224a1a84500c06824200035920081c41c09030f8001e0514030344a50b0041c1150380500590f05d210800000307103003d01004100f9203002c00001044030519040500e0090024079400004075502407450444680c5850003041040c451a0003240b0301a0740d240300c2c13210200740d030300d6910a46185812281159003000c00d1002643c4150300c21001040d8260401c0c040d101c5c00e019001c1303a0003d5038000d50040c0000c1e846c2c0010b071168480341641c684040751421982c24100003001600d4100c5074a410540c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 235509154 1250 235507904 235507913
    0x4060c1e05160801061a0901031b081e1009020304020a0305010c180803090112150819060b0a03080708090f120607080114030307080f120a0608010f051e0c090409 71
    0x105159410301010a05030b541d5625501030030780d00b46108506002c1d8002c00101c52065000004100040c1c0c1490001403841010b0030741e1204146a450000004240104201c1400e00018002000c403c90b1155261203103080c45103400c4400c4140106100d0540200c003040131512030341c40c18005541e201c0000d000c1248940001064224120181c3d6003c203d44040001c0401d03000c000c03203140c82c40c1030f5903614183c8100c0002002429540000348488654101c00141240e001d120b0041407100500b4030b0245c009407402c08806480d04920107a00c164044d5100300002100c00b022629926402070859803505000e80004560303180040d50309030400c00d0200d2050003d800451401e1098200f6120400304c2c0c5d07210000d405035610f2105581d03800d50301c1084988007054200001c0c0c41e60003001d2220310700d02040100d01d0160014141c61019446403540c01c00e00c1000803e0154071185110748408000c1880d1001035008060070300060401180c83c84000726651425000c02c071581c610002d003090080c40e090346003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 235510404 1250 235509154 235509163
    0xd020d050a0201030506060313170f0c0303010f060f051e04050d06090201020607141209011b050a080108030913050601030608011a01090503070608040305160f0804030618050304060c1e05 82
    0x10120f001070b04e401e000912600d840000c0c1ea018030400500d0048030f041541da29550504061242d451194082c4402d060b00601d00c4024658041260702440d201d514210303100021f44120b410110520490f0b03091201d4080c0e000081d030303007007100113500417195484c84602609103108a40005801080380300d00c00060005541100c81303618401e0b422904941c0e120b0b40700300da0300f100440039425034440070001a074945001d0345002ea00001c021000243c05100031040c0c4180c119500d1130940454000b15004000035000000240145070250144d8030b0b108010001034024441c035002c18030b0301555540030900310792007036101401408040008201108200150340107806080f4146800605100e502054506012030840d00302c400c2900d48100c1034a5036a8144d50703580018410074480202c0d4030f01880801c4003280304049480c082c0c80d10319600d03425420700205841440d40c0c244414410304411300b00060000044030116001443d20582c45c3d2100e2400c5416003a881c05c4540d082e10b100d4081a06001c000308 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 235511654 1250 235510404 235510423
    0xf1c030e0d05120a0603020a0501180e15090106020705130f0e0a03031b0201020f03040b091203011e0b0304170a030605060d0b040501061b03030903090510031b0e1309020d020d05 78
    0x900c030300c3c41c0d0365070000e0000356100e9010080d0018080f035030030040341d40904034a2400301004580e41d00c030f40f5250b481030280080229800c142801545074000d07020308100c0941ea016004174400307000c0a41c144000716080c50345c0c065001d0f400c955102001141ca03100c03540003544041003e401d441a0015600f00100900340b258020320441c481803200707110f1a40140300701c80c2107460b11044a400d5568a44541d28021001405001d26004403100301d003490f060800254042c060082214042500c4101143c5201c00e8940040100c60b10800030320020a00310190034003030a20021100380d54028040049015000682c04035400c00e00104e02c450010341300d81c1001c451280195010481c0e0b0ba62010200ea0510404002c08080000c81010001080c440c0c0c0010304564003904101c00b8456880b80843c04000e0b141c0002130000383d848150581043e10008a01c031031019034503090180c054504001481718052080d4000d2090307a4600ca01c1c115111420380c2c40c00c40790020700c0018200364500782962990b8244 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 235512904 1250 235511654 235511677
    0x8162007081608060f09010b13050a14072c03010e0f0606030111030406090204021213050c120d0503130c06050304060606050f1602010216260f1c030e0d05 68
    0x1d440c94000b0b928460302103803c0340d503004000e0141c0d844440a8002840c0c0141c07800d0782c1e554803002c404869494a4070310800c2942e588500041c50f25200034140c00f200d060a00b0250480040340900000030b6022004d014185400c0095440d500500c0c1c4500000c16024140c1030380650811041400544010503c0a10b0f8620b90083c1c40301c1b0344d1040101030890710007041220034038405101003000321711103a0081d49190710142005107080a50307400c045240004a45520424400d000c1c0d0908000040c082c40c20318200640f111440d52040484003511923030b80515083c03c200001c00002c0030036020b060022035540d0485001184c0603120000242245d00407581030312428106180000c0d4280300d5001c541c07107101e903415041d00b07222000c04807003803028450505a0451065a48220b5040007543b104002403510603a110000c00084038100c0030280760500c01a015004804000009640401d038044c000441400305906006c03040070503001070401e060015924031442000040040d0800b0040441c00c41c00c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 235514154 1250 235512904 235512913
    0x40c0504031a13030f03020c070f051207050603070302070c05060a0206040c120c030602030c07060f021c0b060909060a09090c06140a020c10050c0a0f02120d0816200708 74
    0x40112000e00c01d035054603a010440e44181c0403c001c20700c502c2107086220610725001d850008850b02151502055410140b070900c01d000d410056071511074040710490782110080c006091034140016424040180804145500041d60108021902c0d080d040500790003000c0c6600d4200049000756a41c208880441d09400401000b05107212101c0f107030720b40c942d030003207004000303504596038803000c0d40000e040284215000d03c1000d0004000c3d01981e43c9020b149000181c59a0754031090881c203005955003244079910305440b040454642c00c0407030752132030030582e04040319849138004100c03000c14903070000f540185040c03106010000e4840328030007181c01d80c4e911000820341e625040306452240752182c00269102c20003895450810003c6005001d5250410a00f030200123415203041019940048440102d4101c401c800c40c40c2001ca8280b481d010800284408120703501701424100020b4410601c007a0b11b1490040110311548290b000202e0152002c80b416035010642c5a4942c01070040c4000ca005 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 235515404 1250 235514154 235514183
    0x6090b090a080306040f0608010e0d0201150308030402040506061603020607031416120b060a0306090c0504051302070501020f0d1506031b0302030c040504111b07060915020c040c050403 81
    0xd440c52986800980c40342c0f8603102d03001080018101007071441c00031521140002954038003072103600c80c07900d554805000f600c090804002d0858502411100b042c0365a14028804140d410040d02d510a40c195000181c0307072903030ac0c00110280a4140700c0340ea4a4003011170641050342c04612540603001e80c0c0c40a000050310824800c0c00540107c80c0941401c0c3d04515031400e65225001010aa01d0750301000540000302c00f010410641c80b00c0404004a6103456003000900010320501181090070301c0d0060605051500259480004089090a8980100350242802420343c1141d00d00700b00091266034821012200724090450b5041d0303008102c107808000241c2030300074000d42446064003401d480712034010b5501503009400203000b142400d001401b020401d611030b8412850841c007201c120588072880303003a1051542c0c0880b005152144c00050301000640e0308041e03500c3c2a034482d0200072450f611200d07012032601066a4071154003d0400d03d03146401d6420900030301c240c034041c000101c03100d407 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 235516654 1250 235515404 235515421
    0x6100e0f010303080a15030b091f05060609190f170613030207210c0801021201080d020303060603040f050703150b0604030c1a28091415090f090406090b 67
    0x35007403101402240d001d4000503900d00c0b8541c810301c3c0320060086220900c0d500c0381c40c0c440d030003101260b590b00a90b00c20709030002d001e82d0320320164440000008081c4002d01d0001d02289043c001c00064030300071a03091036242c0410803581c0141c4081c205c850440403003680d40e54081740000100f02c809207424014640820a6103180300c2c0c078030100903055001025446c1c50700c80135200d420003d1425803c1203207142a04c07000903a840314081c0c01000100005615030b036541c1504252101e061340542604c1d84000c0c81e030701038540c02100f643c0d1f0242c01111400c1d01c95503070b81030104014201a100030b1090041342402300030041282401004481054420040da04400080c0f20440c4200e01026280318148401080031886003803120810007050031041d07007441691b90020400502c402c544941c1c0c4c00d03e1007204116694440785a6006102186210b0020524100890081c086005011086000c001400103464482c1c0340004041d8401404c0d2407558585410300c00000d01c0c02000c21600160540c012482e881d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 235517904 1250 235516654 235516681
    0xc03020a090e0901020c0f011406030d020d0503060d0602070b0702071a0306040c0c0203030703030501210b1b040f060e130203011a070c05040606120f0c0207050103021b06100e 77
    0x4400d5403190228141442c100740d074048002000c2c01c2281d03400304803c00c2058020f101440d004a4510001714000ca149502e0340b46400c40200524040d0340b2014482208581c0091100c4a502443c02e10568079111000402c285400b1a032002d0301403070000a036102084007400080d44140402e90079281c4803074840021b90008140a0f8000c50b140d2010300c007003151460140e00c0290311041c0b904044409248940c00319084d0307041100d0540200365250010040c0c48480110f059402468900041600d015940c070b44400b040c02500350320446001c505101c80f101c0c400400c54019113010500031a280e0787e10b0034010040c20494084c2c83c0521448007485984c1c0c2c8003030095034113850844280f1600440c03040c440d90401e420491080e01e070341b0409440002c890710359204006c007074021940c4526052001015000c161898120a200b210785000b0302d80102c103501282a074280c0703509280c05680e070701000000707944c080300d40e460400f035a01403003051100c03141c00d9607021000c503034a003010130400342d0f01c80810320007070f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 235519154 1250 235517904 235517917
    0x3180902090303180f0405040510060e040f030c030e060d020a02010e150708070e041b1d031e0a15020408070602030307020a0314070f150b0915101103070f02040c0302 73
    0x150b00038450160013141085001c40c4021010b00194a480f844400083c10f460060320300351103540096a85c002d0810755402000b015080c1c2c1803048826040a80c1c4504030178010070300c003130100803882e02074504043c801d0405003210803004100c240c03580300916142c4029880240300d00003561074603103c00355004020034050051025110f0759138055454050564105800410600402c662104800d8080e61148940c0c15800140c2c489028a024012405000122041c1e07030b02041550741030f00d402f01c913640003403024039101c040004800303048003400407d45410341380000140510000c11032040416240d9020304110b80002040b103898554900d000d0741c503880241c0d18100140c10440038000030a0144404906ca2411202c11510f412825207542e07205008012089030a0103102d2420820b940840c0501c000785441180d42002605020380780c00250700d180c1d0346160180131030000c952141401b981103127511680750f01c01c0c1c036550071551070940405803100030228822881c0c10303401d8141921903c2500c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 235520404 1250 235519154 235519159
    0x10605030f030a051c1503150905060712091e12050403030f0507030c020909060f090c1f020f0f0f010f05061c06020903030706020304050c04020705030a030906060e040318090209 78
    0x1601840c00e40440c1c603a4801a9880d150443d00100b00c1c1d0000c007544500b03004010441c00003545141140f9007600f0a401168048048d281082034a0303010420124003540c1007035072412b1450f1014091f00c804006415628405071000c1800401841e084000d4003c010700144107003a40000058012826225402103000150004d002410105401d030b0150000f04845406030804200c01d4400368001000088110358840c0075800c000107019100c41c444040d99001f04182d00a00420380c80e41000c41c15602c8920080035010503029030030780e000c0d402440004e03800e80300ac4055405000181030100d42c0c0d1170070010804070a600e803035038201c0e03604079038840d0038050540180780800e581d10103100043d1b11300c140d00003542d16039400c0090f10350a640810007000c07014820400540c40740303800d003851810889002942400b490040100c400040e00110481324408000c0c00d0004440318141000d20003044036803c40380c3c80c460100103210505406c4495031400480c4034603258101610362040c1400d03409100680d64 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 235521654 1250 235520404 235520407
    0xc030d0f0e010504091d010f0c050909100509100806131a040311010c020a02130603030804080c0732030a0312020a0e0406030c0302100c0f0b13060f02040503010605030f03 75
    0x18910340304145107010640145081810942c40d00c0e841400c640c409016418040344000c00d44200503402e00410303800c85036002c0204002000e4030301c00f43c40f92040c2c0041c144a00312000010704d00c8900310300c1c0f040203000054100822480c01d4110684074203001d005175800c0748102030008040594100745041751540c8821908480d82900c51100c11451000d0300480a1080c410014003016109200e061800d084580c003d1100103118014001c0014101f40c1c0b0316038040c1800c10034404642c20181160b0455807000f0043d0346c2c0c12618080c0b6007802e4141e0171200810010114020040d1845480c0160700500200414402d0100c0d41c2055521821500c0c0200031603008410307184040b0540d409014100c4081c1000010034070800002804c441c0a03410482d44000011401e0040d401d0202a090480c505418291104a4642ca90300c0358444403010003080e042881c00003030010800b40c121111243d501034004e02004860a84030b40103034000780600c6009628007080055140340020742a004080c845c8082d5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 235522904 1250 235521654 235521677
    0xc0309010c03021c02071502011406010f020f030c0a0204061523041706010608090601081b0105040e0a0f180f150603050618120306130c03061d01080c030d 68
    0x540744500d4411080c2c05601640600440b0410148551810020554080c2103171605095111b5202e0040380c0350340085a14105450244003001c2c19215001a8242003440d1500fa503100224604060660820860300001c101403250b0040000c0c1426124821117042c80190340f12001c5203082e80120032a0000202601169412503c010803150034a500440c000f0b86441d880d040e00c0e000e54900c0221400f210703803000c40104940795104840715000002c110103040954034080310f05a940b01d08030111031a041c2040c1d0600050380c000c0084070300a00c0481e0500c0c00e20301c1d06420040003031800e070010441e854109241030b0009d9282c0c50001945030b500807454282d00321030b601c40244d860003141d28002816617801000c004a0001c0042070300c40d40205000403a0782d071a004102d800c00d1028000204040d0041c401d00059940700411030101d41244080086d00780c2c41104114050042640082820702e481121481c03114103003041d06040c0c070706010469000d400740703030300380f590741c86012000c1030000c1d8444006 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 235524154 1250 235522904 235522907
    0x102030306040b0a090e0709050703020406140a0201140112020112060602030a0507020f03010e060a0c0906120c020c12210405060906070c0503010c030b0906010801080616051606150b0c030901 84
    0x5208401d8007800d900034498917240c0e50720880b8540d40711515281d1084404103d650ba950046d03d0703012105140544c2003a10300300c0040c000140001e0782c0f1500c0c103400305201c0391580c03017584210481c4591000b02d9510756990314030041000b92032201680005d80303041021451040743d019001c1140c00360750045103061000e8000b00c4030707030301b1003041213a01c40d44000860410356403d00a90381c50180d0318024102d24100020020b0440e01d00944110602070141c2080001c540c04c4444402c0049447d44080341e5003405107812414808603540c09075224003207072146080d20a0002c2c3c0b0072036084405454481e030440100701c41059000706d205036607002e00b04100401c61420b20310090300501d4450900341c0445520740000a081d1895441c00d20006a500ca410260342c0c175025031840c0d00840f080c02d01c441c240d41861000d5840700c0e0000e01c0c981d5103542ca1810f00303903601d00c508102da0155946491164a544c000d01c2c010b8064904071100303124106003814007003100c0b0720f0fa07001c94413410441001145000080b000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 235525404 1250 235524154 235524161
    0x91a240102010b03061513050405060705030402190605031f050a030204020c030415080f0f0f0f1b0f070318120303090201090302040905060106030e030a0203072a090f1a010203030604 80
    0x141a0440d52590f0650145480c01c0240364001c5d40c0c08500c041c40000d2020901000c801950ba0f4044030034244400c0c0320102c0c402240382e54018207240783c950b9881c1d80d64004100c003401d841e2490842d00a1034400090076581c407402450050f0386d580c2c4486c00c6003e180b0300c840c400304028013490b5400091139404000514240c0c2c0100160240c80c4103030390400c0e907588003150100a2a074174010200d000f0004208500512051456201890382180340d401c0c00d050003440c00740b0400400c10403c00c614140030410191101c900c0107102c07031180348078176a108215440c541d495045018124085030301c08181905410503981c400e81694070070500300ca01010320b0b44003100a000d502c02e003a03042c04020b803004409030b1a203000d50114640124010206d6514000c401021181d40c0c0002d40d5140e0800c2c0050090300c0c0d0302100b2500d01c1a00960703130103011540210002100c3c0c0c2d0198039425844da4049000411204681002031100c80c030b004100401a10042c01030000304c000840207005030403c000041d12407030705a0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 235526654 1250 235525404 235525471
    0x6040203010b0628170903090109060903110111010f09030507020a09090302120f120411150a050919080607020703030212040b030118110c0102040e100e0408070807020301020a03091a 80
    0x50003528400517104c20703050444007515030220f9500000390340c048035600460244000c0c2890314101410520707546a18540d0018100c1507410046815400d540054003500b01507140300041c00c1c1080501014680039040764170040c0201d001304800000010b200f0030620501c11880c0c0c050f00501482100b4524050441d48603600d4200d29000600c50341244480c0d40d4135840c403840c41806c441c1d0f800c0411004205e100d03a1620003c2000b400304111211119500000b90340e80554250b45003161554440c1c1412200c0d011078010461030f21540b02004203403580054241c04907402038017502c114807a503030050030a9209138060b22158400c1000104034031612100110000b542c01c039400106a00000390740400d0ba8407440a80e402a900410144601c6c0c10142e0240c1d006200443c09480d4107282c0f0300f546280c00401040a020340c440852204140306070359084640300c030f0b8002c000b1940e948044502178010b20425205442014460030700400032210148030758000c2c1c002c0302d203d442c15006142d0341c058039003041 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 235527904 1250 235526654 235526657
    0x30f0905060103030c14060f040b10062a0204140612010c05090906011b05030a020c0307150503190f061508060102100b0d060218011e08040b0a09020d030206040203010b0628 76
    0x300040d1203400f071b0a2021a005503000304524029050030309040e015010042c2c0411380c400f800040c104062500508080795800a152655559400c60700440076140052030010f50014140310010950524007401c1d24803524085505100000e0908a924201e4500f0183c0002041041003142c01c2450101385003940a281494034080000400660102c041d000f0901126a940085400c0b540c0e41d8051251201c0403105500030304080b868896030384c060800005106003441400404140201001f91041440210020342070240c010040c00400003011248615841e8021103560040021320518176180160016802020346030314403440b1900510062010f141d20500800d0b00800103a050f0000e820001946410303c20446100d1001600c069551090f0307110744070010142040054025002903009034000d000c640c1250780710903044008140245000c0c0d84030404003990002c140e80080c04d0341c8141d100ba0001d111240100d000c0c0710841c024640c0d0359003202401c0504030070b034036075101c110a80d20005 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 235529154 1250 235527904 235527923
    0x305060a02090d0519050717060c07140307050706090603020306010816030b18090d0c0c0b09010207120b07030b0a080a02010302091305070c0311060411090a0e010e0c01030f0905060103030c 83
    0x903035554a25100c5914031a40c41c00b509092200d01b403180501c40280108110000303040710740120244661030344c000600421036000d0214240003409440c04c1d14108840554040301c0d502c402a0402a668802d00d2060200080d140100418071038030a000b507074000c0106840e44195500c5044c01190b54464a0141108042c0d4642481d8840ea80d0078110002c810034100d8120314504100c0c0c50785e42494a405d120740107221401401030001602200710700c0480d031a01c419140c41744142d000403400c0031066840003c20360300b418204420300807280d03210b40c090100c586003006118005000e2011407640d5128170131080d0404411480594081d40081c0464080140180d03101566800302004445094910303500103601010004101504821224400e901c0b0900170903280c40c1c075955004850f080c098190b4001d020400c04226100c0203a00001c1030301c00799038005e226a074600d900c40f40d561054002c20b031340000c0c100780f490036440b01c070752050b50401c42d0481c0141c08103a085440558244a070340300101c1d0403504 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 235530404 1250 235529154 235529179
    0xd080c071b09020702040b0d0812100e18010c210c030207061506080705090d0201110a02030f011b0e03030a05130b0f07140f060601180806090a020a0e010305060a0209 73
    0x200101810203050b010800580310145401408115582c80b00a18040c48807810394401040094041d00c05a041e9001e9141007652028865564541568031000d0141c0000c028000c02c14050356042990072004002004112260102140d20001040101c0090035017800e41c221811304541040b064070303030641030261800000f07940c2d2000311103800c1501c030740111008100f80314140c3e010300c0d007540100c0d003071810714107200e0b41800080611f6003941c07009043c8142003900b015498405e006000b241c0d0f4006058a2a41200715030850103019402450341011034041103c040081c02031910b110000c1d80a4019410025148000c1e80d20b54446104101034800e02107001503560400c8004264408401e035a55460340c1c00f601d4030603900075501ca0300b5502070b042700154101c255000101d0700da0060b42440c00a0310000340141c40f556010030354011044c14015a420801c1d00340c0001003074800782c0d10954074050400d03034901c1075600c1c01c2403c2c00010265001007010070002c0c500f680192030719000040c0441000078 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 235531654 1250 235530404 235530443
    0x6040b1011012901090506040b0306090601111603021c03021f022506050112020303072409050c090a150b0309030f04090b0a0902040803041a07060c1205090d080c07 72
    0x81d10140f64518030010881c0701d0015688200317090000c1006441e00d508160500c10115010b010080c0140d009598144c001181a0b00c9242000c4583d841e034020b03078055840712500e51040402500091f030140c019041e00c022039a03044542d84c070b40160584c0c098210803240b456075411050043c80320420b01a004e00466142c0303c070181036100710000070395001000045510b000d80a484050b4000100303102c6103d00d41016850102c1210400c0d903112040b622200b0914400381304507883c002244140c10f2a15051500b0054001a0b140c40d20394111070f446007a542d40e07800d00d02600c075072542b40c0d00310204070032040100260034409540c108801209990518400c1d04890341c10360025840322001c0c0b6100d80c00f2888900780082204082c0c034850901390714182c01e00c254683c0c1ca12682c4200790008280307030b0041503540c01c418240c81c60306e540003905200401703000d94020701c4000050781d500c0002e0714102c04503c1401000440810f100e100b074030703020302a40d990300b0403503065000401e0548036540c1c0070105031000c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 235532904 1250 235531654 235531691
    0x71412010b06310f03030509031527010507090e1506070606090b040c0f1206050306010306091223030402190f081509190206270906040b101101 63
    0x180305007801c01c8010b0340f121961001c00942d44018085041000010300442c1c480e0700001003520b030181001d81da66400000400d2170f0446060401c8000c0c44450b00303014500c2030302441c0030380124681c01650305400c91951003500700c0d030068843c03038041022038a00704019496680002d43c04642007801d0040c2c06660300101c4c0159005032800c48070995210410b128400b0207100318000e4030401d40301002650302003103026140c1130701004128140000491036142602013a04540060840902524855690b9180100140c414410202c0340c06218040e4024840c0c4500d001511b01200c00824284000740e091040e2039903440500241d81041700b0040d54140411403200c103000410342c1d54450801140f4204150b8182a204090300107038482078024002c0c0342c000000e121f6820070380d46610303d44211451001900b20b220701d169229504d0844441c030b600c006500d10040105800644000909130342d204100b0089030010781106500c4403240c402a68150300c00d00c84c11403800700d2440005241d6130f0041c15039111 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 235534154 1250 235532904 235532917
    0x204120f020307090515090106020313170a0f060c0f1d0402030402060708120403140a0509060c010b03070e01091103090d12060503120327070330051209071412010b06 73
    0x44651b1822841121f00b448180240104010300c055424110410854040381c80d0601c83c10400704024042a41101001d00240e08041d5004803180740030b035a5860010080e0404500420100340d9449000022070b0003a03100641a010020090026900c4101040029040900140d810480600071580061444001825140342c3c40c3e226004502e044d00d0000c2508111803034920b1907082c01c0c4512100302d5082803d95020090486085407115012816507006104c2180110340c540310b01000000c203080250070081c182e41c1191000d1041260b022000031841c4019191001c2c0b0b41d00c80145407400c14401d038080202e514020b040490000c0c0c0d1f030400a1302d404808010122038078030010038840303508500940e08203c117100d1500702441480ca01142c80e21028a440040c00440301211959a0300041c049141c01c64407020000001034510750900510715048199a04182c00404c808207621510011308030084500d10500416180501000d1048d00b10b183e0040441964035598007020039070310400074144d0f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 235535404 1250 235534154 235534171
    0x4030f0609051204170c101d13020f12091203041101110d27030b0403080a20030108010b19050609030a1505221101080c19051306030204120f0203070905 67
    0x551703180381caa810001e400011602c42d0510b01c180b0310045410904047e2201110740a410217100d406000c5810314014841000801d0320001e020008104400090240305421408034082641d540d50b22503a50076070600700c85000c0301c091002030300007410054903401205043c50020340c10705480e5103403460009000c0950004c504440800680020744050b800b46e181d003140d410310700c2c1a00d181c0f07444d245c0440c0584040e08000241c0300007030000000350401809103e440501d4203c2800c0b0020500b056002801303500316550038801e030100e0602d0820f900c0b0418404c9000d40a1300c803860702d4100800b60303000f001c00c9501809007041c1c0300d020540304004001e4207880380c2404a114542503006600e82d6111a01030209040c08401800205e401045d03a101e40d03c10a09010289858089810810780141020607100c07001c00e0765141c21b996409405440000281801c1140c62515044240c0a0b8003507801808142d007030900c0d205003c07940c00401ca6032020b002800340da002580342c1038994255601241ca010303 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 235536654 1250 235535404 235535429
    0x6110705070f14090f0a0b030a051005041401020c060a021b010501030c06030e16030b0a14040f05010c031a040902040e100207020a050a050f010f02011b12050c04030f0609051204 78
    0x1d205403083e014041c0c228111450074891402c00002c100040d4043c010f144400c0e0b803600c03071000984081240a8810b60440102c41c1900c41880d0120040c000c01c0350100c0b8220040895040c1208050083c2c84280c5803000141c042591800700100c001d4010046100c000b03442c030112100c0c404130a1059a0186010300390000c2c030750b82400030107401d807518030455081c15445000254005000406000141c1c1c3c1d0040103e1041e40b10a580030300908030b440b0144041700c0510b818842004404240e201c0c40d9807003440240310520740c5079001d40441e104045909203000354118540800e10301a84403a040910080c80082c228150308000ca140c02600c24012112507400200c07201985403c0c10340b04010081120003681090510000c41c010117036030b5080d14140000c860f6101e1680703000307400881004024049968030f0b40090350303008080005080c0c00e02c40b01c62924003c29522401203040b1800d60340c20000c591712007480d61765a28020b1803d90015100c0d40103882042d0701c54100d00c1e004000030004102280c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 235537904 1250 235536654 235536659
    0x2100b15040e0a050c0901080106030203100e0c0c010c0206070e0904050f010e1608010203010b07020f0f1e040609050402180c0408030304030c060f050103021c080d111e0a080406110705070f 83
    0x2481110b00103010200396010074010340030540e03441105527064030309915000d0780b25210b50101700860403090300407081400f1080c0c2080f000c0c5251901818450500e04000c1c000c0161415081c0c0e05c2d40701c180c54410008012003c6e16460307003001184c490700300348a01e04490082070685070030b50854010389020041c0d074202c8003607840c03403484140707500002e070001100851131545410300403c1c040c4039405009004440c0c4095407540351751446080720b9000b401905202c1c800ea1403880000f50070703c2070550385119a203040000704800e00d05118041c403c59000c0c10805500910700070085223010000d0151a480c0c2e8100004254007038240041e600071031080d10380111343e808501d841c100f51280d402c141e0180e14501001040942c0d80c1c6200d00c0050061040c0400d40590141407400280c0324003030403404000d08021160b45000705d000c0050191a4a0040d80841d003400080e0200291080180c0030001511800115000c074466034406d01d46000d0603540d4915100c0c09580740c40c2040015030140c40700f03a1051004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 235539154 1250 235537904 235537921
    0x1051b0109030e1f12112b06080616030207050313180f140403050a020a06110702040e06090309040218090711010c020a0c032a080703050712020102100b15040e 70
    0x2070031004d410300c150410800c009000082402a88444d03c07950031b034540554205000e090011280d040c16010100c81c1d44180f11102142d80041d420a100b076a80d16040f000600810b01003251070080746101c11040030700c08440001c4010350050707242071390640000c0048442c1d5100000c1017034010209a03614483d0b07070902d82c0703202d81203420810313541d40da207400c042c00e456220ba240c0070281c0c1e00c1b075494100079848a4180c00100d10309040c40600810319440c19004a60400c6508058140f030b62084505105103054101c101d83c0719003003074889203e540e1003804003032040e1620b40c0150210250084941806200802c00101110360650f11080402c5441c080c040240d10217000d424400c2d5a607000408030142c8030f69890000c4102840b0240508440c000e1484550b00040010811080c045100009140c1c0b039484080e01d6241c2c40c0702c01c886603c6003140c00940e684080440301040b6030142c000c0c103c1da092254814000c0c01c001c00c02d1903400600d00301580e2400008401400251040450b0010140303019083d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 235540404 1250 235539154 235539169
    0x423090a0504050c12010e0d030609060b070b13020d02040f0209010801140a0302040f020d020403050d090801060515030a060e07030c09120210120605032e061401051b0109030e 77
    0x1400c06032904110400c400701c2ea0002d261000e0741c038240c0faa811261002007a240c01000c203494112500d0051100c0d8480b840c1d4140c00c20b0094420f041d2040044541e1503000045920404000800d2858044001065501002c00303c0b200d10780050001740ca0f80210790300190440f2001100300c1000e0350f0204101405503884141c00e030140c41800e14800c00d900c603080c00180e900f61148402489241c0360722100710503503015015035808040140302551510748a1902d5500c408800c0c14442c0094000702c40010b040505004081c110381024012038000d09200b0509082da1388010182144181c0780d070400550310389003441151181517a030703400086a4442c0c440040104440754010305192000708a07510150355030043e042440482c0c2d08007414054442402c040c0038100c550301040c0e0602030710110410313800599072100900181a240781c0035019040c417140382110128043c01d1a036003820300c11840c0950043d0024400160410300002c0705800c400c000900355240401c045000800030060440030b402d0000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 235541654 1250 235540404 235540411
    0x303021b060c030606090a09050f25090b07050f060c04080706030e03160c0f030503030a0506010804051c0c06020c0c01030b01081e07050903151f12080a05042309 71
    0x40160200b81803031101c0c0c5030580000303000701d80b0450001400000e5503544083c0d050052025840501007481c000c0144090040111100c03070040000701c40110b45124003000015940b04103403070342102281800c08042d25a04000012036807481070601000c0e204400b00301180c826080d03841410b543c0d41c281007046042601e240c0c4070b00181070900443c0d001a01c004001d490214294411400ba028400d040580c02842140d00c440715400d51842c0100030f025002c0000c0d03125840b007050a202d551503100045070303243d8007100c014201c1d030455042000300100d036a03140f00e10180c151501100c0c079110342d00c40a0413a4031a4001704c04542c07018418200650f00341c041c161038088242014926072030003038a82c040d07080700003104e103110240c076200098406004405854203c01c001d000c40d2403101c1d0132603401100207001d4451650614200380c00300340320204412181d003a01d1381ca03000b20b4044203d0355034181c03040c0c014903e440c06101c0140004204921512203400da0b00012100810040004034248076003143d014 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 235542904 1250 235541654 235541707
    0x408280f020f03120408120103030302030603011505130903050f1308070801060303080a0506040921020f06160806030f0a0305070b060103091a150a06030e06061009050114070b04030302 81
    0x407036440b0074824022058402c0c0240803015a80203075141c3c500401284540c0b40802d400d134046000100c103166050780514440d900a80080185a2070445803c240108610400c0c0d44101411500c01d107056650300000740d520700c03d0404900f849250340101001c0d0b008040008035825544404001030002088210010051400200421400c40e01d00602480004041030b881d9510b1307001091003a10313260700500220703402c00c0c1c00c1c00e00c03250200c0441b100c04e101c603c100d07001442046c0034010214404602a801607554100c0c01c0e415100088050300d01e02c40c0182440e074140501210080e6180301800b031508118400c0e80c80750340d10201031034103400780744000d00b007d41054605030300107000840091162111403d08103084e03150740e80704aa0130504901ea1240e07a50000c01d13171800000c5554140e0030401d1050780a2050346c1c00390703458109005403035540302500c1001130319115040002d540a01d06041d90004541d840746d11341049601d4070310501405940440001c2c1d40090100d1000c03031050140703d10803220 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 235544154 1250 235542904 235542913
    0xd0c0e041d0715021c050f0409051609080c010c051516090605070804050427120314040f0f030903080406021b01110d050310050901031401140403020706080408280f02 73
    0x80303c0c402507403880e0040343c1c506252140303070a4402050184c410f54007881c4059001c2e5950b0303038513149140c0c0a017000303580005207110006034805000340200c8055058038010402066610b00c01001140c0780c031800003054403180200d0501130f20300301600780c19910a0406095100f1125100c401c0102a00d8079580490208002400750100085016088500310344040300e010801b03800b0381e40484840a0220800d04e822401e0044100070048003030b41d02404000391b600d040242070500201d00b04515000c903001490000300d4003c02c00001e115541c0b695500e1302a182c4801460b2326540d80d050700381c0c0560444809680310440c40100003584000b500300d40764087c604080d4201d0281c010b5651003041c41d030598240403000c03000174060410266410001c0100818419903541d5905122400d4804d9103001400b950811040d40c100c0a10440c0c0940180d0f41a4028042c440ca001c104541c0000080d00854205504203e1110700090302c2c00100c114140440300e40705051400382003c1c041d40e0a40f1105400c1d07410 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 235545404 1250 235544154 235544189
    0x612050d0f091e0b0c0a020307050d1707061107050a050d0f05030411060d020a05091503040c0303050d09080a0e0901171209120a051b0301050105060d0c0e041d07 71
    0x41c440c0c1540210341c80080d81c00d209054101901c00e5490844c2c10204800d1008101d440000340c2c00280601083e000344c0565a117a905c920900800848081c0b002d8071719281d09072254030b0840c6250042c0030300e03805074400040c14182e031031940c0003c0c0d0281c00151040d602091401c024003205204102415209042030420481d9849029003140001031010f051f084e885052904551074240803111120412441159200140b40000d0042d0700003840c1d090140d0f40e100a588408075001c1c003100d0040c1c0d009503045102ca490342d0b9044550344d102c0880410800e403141117640000b1030701c502400c20041c540d11050f03036550302c81050000d200d505074400b5176000702c22401d4a886800111380a160b440004d000241e0302c1101102041714541048410402d52180c51055403e00c080030980a00721107092401003410501c6904240c282d4000f8026107900074000c00c42560312101981c0b00800100450518400035180003001400320b4810419840c22015400604000048144220340c041c04071100b40c1c0d400b014 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 235546654 1250 235545404 235545407
    0xe063c060402090a031b0305011413080d0209150703080916171203010f0e0a09030509100309060e011b02011b0e01021e0d0e03030913020306040f0612050d0f 69
    0x14054050350255a00182c0080d0f42d840d641030540113542c03c03d2a1400d016480b0220007034118041c80250317050351801d4248980300c80500c500038002d40608980290712040345c4c980d440c1c80d42c032240721106250350820000354a6180c2c80b80e0620401c0128050649a5441d03043c05006d10030300811299440e0046108031f031280c10034004034400c4c1d800001340c41d5520b070418500c0d14500000c0510004003e40048000070380034005130780150a4500041142c005038980c42d07120802c1c2c500442c0d004005c44e009120300780c03540c2010300e04c3d40e05030901072602140c401d2058903403904070340c900701c203040059458a40c00c01c0340050018481d0302801c3c80f403000300002003100c111305040d07807800b2864004000d054054107030140c6c0b0030000c490740c0c091441807400c242030300010465502c0805581c1480419001400102c00d46000300a031144108007402207082c0c851920f130b881d402548000c25003540700740e4034041801030361041e1041c1c0c8058201c1b40c20200801c1c10324100980b800f44c6c040c100e00108a103100e403040c40603 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 235547904 1250 235546654 235546771
    0x10909020a02070302120604170a050f03060d06091b0501050f0d0b01031d01050f06010f051602030f01020a0c060b091905090328120b060403150e06 65
    0x2924188001a21030408280490521500b60b101a500c29848400502611800f00f50a401184551f0440000c2907402c14081c805008011007070003c1030040c0040261a0806801180e100000504000c0c10304020f0303942008881c0e040009403800c11030500f541c0340d4060840820400381c842400c1841c102411142c1c0c0c001240b00c0c504040c920141c07103010014241c0d00a4014018007110030f6074002c0415100c68100380207080450700241c0c58083c21001c501a9401402072118001e900c0e522245017807441100e4500b01040100100c0c5c142c0308a0b07184140b0240d003880900720406140e03884034044e0509040441c1902d81c0915854414400300081c0046401202044182d01413054070215040d40e4074042107003140904d0f0082400503035103030402c0b0400c0a0006200c0880100c0703860b100c00c5801c99032404412100362801b0380350030100422042c0003080c10040204c20ba880e4400d40492035500002f05c01382400c5040d25241c0c0d00820310102d4449542070350b4038400d040e0401040000d1203400f680110142c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 235549154 1250 235547904 235547909
    0x1205060d02061e03040818040b0d0605070c0c090b030705030c0a050108070c02040501030303021c090512090303040902040905190e0304062d020609010e191212380109 73
    0x36180000d1840c10f8002caa031014408a01186595a26032070300d401c1c01191640189082c00300351800074400201445d0500c00c1403c4644047d11114941e00c455588900901c0003402030003d0004468800c000584d440d40d4030000352100c008041400c800c1001810728100c8243c0060f03110750443d00980c0001e4488000081c110303482441d0807100d5854a24090b184a01c1c0d41001941103030030100003000349a050780080104940d032a026516142e5050382410480c0c60080c00109184c0144a20f07000d22003008014203411580102074a1419988103e0042242e02c00e511240f003258a40040100d215120ad0085d82c1c0703c185440203204601e0081e43d10b54a82c407560141c5004e01c014182000707a02d008a5010800c0301c0252141100c00c206c203400c0183d6210401c494144043d820140c110070300000206d903000980402c07010000580c0070341d549905081d80152040800c209152119601c10522801030400700c146e00310b01168010150412013083d16514004508801350080e602d81c1c01742d0717100140604 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 235550404 1250 235549154 235549159
    0x110a060b0105070f060b0112020c0a0b0a0209030102041d0709030302030f18041e0b03031206040e0309090106090e0c030c030402010c0206090d0b06030c0306091504030e0d03050a1205060d02 83
    0x304050100d005844600502d103000e0300d22028000303030030b040088640c03103505008001d880b040c55800c26000c003103080e4030401907900019001004034800041030a407041d81c0102240e180076080c011410b01080c22038106911405901c2c451001002d0a44079159056403c0206483c10040c084c0c02c0d6100030356a440b80b20b02000c402007001901c03410401c1101f89035040310000070001d005048910050345c01c1e8192001e444107505d842e060090030341d031500004a61491700c4084101c1c08660312442000010b00d850034031840c142c0020006010159079000c02c03513000e054a61560100f050a10031020328180c00240f011210820800078014405015015a0fa206609280075083c0e00b0307103840031a0907401a10741c055007200d0348503409010000b420b0011032181d40103404880381e40500d00708055850400752100820740e04080e9585000301c0000700302c65401402401d1026000d242ca2020484000c0501000d030000341c0d02003034096010380d000794800141031488405100c00d080540c00101071000d0b20300d0092 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 235551654 1250 235550404 235550411
    0x901080f0c0403060c05031501020c010f18080703050307030206060303120606030901090b010f17010207230102071221050c0306042a0c030f020105010f17010f0c02030408010606110a06 81
    0x5690002a100b00e03005550700100c2401559003080c0040c106402c107132049200c20005500170401544000ba81c12502001696600c2d00c00d0704108065032500e42030a69426007195400d404101200200802401948510700a540e03818840c10001d0a219025081503c05d4108000650818140c01e907003540090086400903130f2903d881c9050f500521680381d009001310920030001903091940c10448003100c0e918080c3c480c402088581c100d080340306507a0010004484203604661403405840d000d41885400e00005180400310b0f2122419040c07807500c00b02c005082c100b10101072003048090f4154005100a00380500e040c20701d12003c0c6030100030329081c0502d540d00c05141a003014000c070740b40b8807200b001c9107014807001e030240100300c0140300310103801040344c000c11108001c4c8148030300c504035060040018165828681c0d80041d12560350748c080020b40d2a202080070014203481003081c01e02c1c20390001d566072132030002d84c80e003074800f07036070212041c0048944609451070001c14081c076078940c008e1000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 235552904 1250 235551654 235551661
    0x60105150702040603050d020f070f1a0d060e06130209030a0b0601180b0306090f010b070f080408060a05061005211e0f01081507020d0c020a05040207061406060901080f 74
    0x4840380203407500a54070500f000c1002007071082c0824000300514080c0c0c20346041c3d034403414002c1c0d5102c0c1c1c04d00c1541502543c484c4108aa00e11943c0341e507041401424080349072081d11080501031302c01036008042e03100c0741c80c4288481e1345405480d140807101100f0080d13007001d8142d40060340703412010714080d1051116070000f0340340b0b13881015901a90390030301c200001e1543e22040c168100d600120b908500681d003c01c0071a004072041440c1e81e040340c070140210b610f40f003140e42d1103c0048010310021180483e060101207100c00f0244055032140511590014540c60000200404070a54002000601a040002d030101c4032902c1c0840d107018000c07228001081c1c41e141c5030f510400e100801c0704244034a201e810f00000c04420b2890718100c0b03000c041207803200c02c0b10030306005a00c0c105540150241c2c3c00400c400f25028000d01d000d012280c0000c1c65503440070b5880020409980c000242110656640ca0500086041ea00f40c91354101005840d482e0a00b13072441c001a005c290080e05204650400e40c000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 235554154 1250 235552904 235552939
    0xf03080a02190e0f0108012306120a0506010f080712090206120412090602060105010f0c05100e0a140d0921060c050403061407080a0b030102040812130603020408060105 74
    0x1250005000b9201001c01c80030351520080c4a42c0c440c03000d00d4410780005404803d41d41c0301d00d1615043e10051040307aa6104006040055103030521990183c1252061100040c810543c0c90074607c50f80c01500c0100341c40c500704000503c01400144008107001000052000342d0f03070f1080c800d41c240c83c284500010205540c1c00013030b0103409440302c001002da26010401c0104041400558040c4103a40c5507007c010751620300590f210b0800b4065070f40050361201000d50910310580c0b550032403034003440c04c1d1741ca1a4030a601c00019581034441e00d918170703880ad403001c00401c07618801250b10b00004030040c0c5140c4504241c010a034030024401c0342444001018a2001c071905441c5440440b035000d4400c000d001c0c0e480d00040c1041c4c11074401034451518051062082d01605441ea51003030306669203240e003a94801d4044402840410740240c3c0640d800c0c0008a1500317000c000c10011548107440c810703101d00f0443d501d00565040d80d0070000415005200410207a907000030b0700350555101302c0703010715201403603400d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 235555404 1250 235554154 235554157
    0x901050a14030108011d03040501020a0f0807140313080c030c10050f0a0e040e0c09160e09010f090b0a080a0807020105120a14070f05160f0b070e011206030f03080a02 73
    0x7041c038805000000150545055002100d002c071600300e004160214003140e152039005500c96680980c00c44c82e401000920040150040d10340b080c0d40700d908180300c5480350750b142c070040b8444c00069480003985401d1800d41c21140342c018841382004080b052070100c0401e07215801c03255900e0040811403065214140600f05894080400b00081a20b90450300c50040c039056820000d58020703440d03e88045400c0360042250f0301181c5004e41607007020741743c5200b03030580e580745030085404001c01020614510703901d48009a0080c1601d4204c400f115007001c01c0d20302201e040c1c1103603602c90100080c0820540c940840c0e000c540d81d8001e080c903070300c6142d140016600c61003807060140c030410564003003194194031507000400300e512034000b46103160b9802c1825500306100c0c061210200d2400e004000441c0a802600b403006441003050070f451700c0d1a6981d8a4005809541180105d5082c0030100120b5920060000914a800d00c2c18003000346551201c09040600000c05020000418005280c0d490940c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 235556654 1250 235555404 235555427
    0xb03090109051501050a0b160b042306190e1009050309101112090a030204150b07050601032d1202070803040f090b0f0307050907030b130b090f0c0901050a 68
    0x9060f1070500d10f4850154402d61004d000f03142c07241e852603201007000c01807102621445550080f0490100e00640c440c03802d4400020800c49000030030700096000d40800d04801c1003011400c9000b8030a40c10049031926800828040b10301d041d5203041e035192140800000c60de900e0540c81e80f40040c4106040c01e001d401c41c49000c200c623420803110801589000d0703009038902e03002501d20060396040c2065640c0f2026512801000e207601c19400304060000d48ac2c0303a488104c0c00c0d80300380c04282c03400f5a10540d024003074008143c26203c0303410140040040c030000b81800708000785821204c0c4104424521005046002d025003e0443e110040c400c0c80b40754020040f620140001e40201d82d10346680c0d100464005010f07000749041d050800001c10030a041400107080d29a5004000d17001483c1400c00344100d425005050301d04054031380c641010345071100c05504c15022100302011a40d06040b20500c40c10b290042e15039510399490901300103c50f002d08040da5200b0300701746440d654800c0302010450f0340d4401c8a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 235557904 1250 235556654 235556663
    0x160b090d020706121811280501030b010e04060f1a0903060f04021c0c14010e0604060f0903080f040e010e0915070207080f0d0906050c0709110d0906270c0b03090109 72
    0x501c5030350910141c40503050303481b03e003121000303241c2100d21a50010710320070304464140829000410301640d0300a4000c644001c1061500c08480b0718000000b4007529020390008902c3c0c05142024092080780d10200e00d11040c40302c0d40c1624001240010a6581c04000d01706e01c0d200142c00041400c56580b020925035040c502c50301d03a841402d4906049071540d502c1e124240b848880301203200c06d2940034000160303100f03030010100750038039103072a0b01650b000540c000803004120641c03c01000241001001d408a000b008400f10b40f51802d01100310301c4000107801c0003890f944041d0070456180700001e441c0d990501521801c14807a16a05000c0e0310740b400e9134000c003480d0b0048000000000d540086e040043d10700c1560340c1d00c852039594038250755a04c10b01458603120781040b00244454100ca4220590030035082606520300916040c04604842184004803003442e120100c64039034040580c1c2a03146041382c1c8158a803c0403456490303981d40c2545204803058840084009550380c1c0c0e00798400803109420 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 235559154 1250 235557904 235557941
    0x50a180302161a19020c0a080a0c050d020d02040f0e100b03070506030412081009020f0d050117030a0c02190e01030b01090504080a050c070902160b090d02070612 71
    0x862801a46030b4410400c116041900881e00155460100c1042154903d6244900e85041039211110100f44040c0c200942944940f03007908040e80c560398926401030000c04044d1080c0d01051501a01c00344e401e50110388a411091700390005070b45c4900c03581c00300680c12200010aa80100c001d40080c1c810500050090b02a0002071249c036a440d800104850340c00303d0541d11480d40700c03410000d01d4002502c5c00f0300016445001d85148601403911241c100403401028001c0c29038a0350b10400360380c0322201800c18420042101e20f01c0740b030140613207400f40455441c0e01c120466100c1410341d81c0e0107920030000402840b02c000b0019501c1700c0290449c42800010480109a16024081702c090f10a200481d0540c00a00c000549034240d407240c00d024075440500b003850680c40507070480d0503402101d104107240c059624001044c0c0310510040104040c04120340c0e22980140c10101d020540084c0306080c2d036048040d445541580c042842016140307070b400d140da5444205020103004015010301c03004110034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 235560404 1250 235559154 235559201
    0x9090705070f061a03010b03030304080f0a1b0303020712020a110d0219120212010908030f060f0a03050c03070602010209060306090709091103240a030212030c032709040510050a 78
    0xd4a500101e8001343c29802442079282910605581e444211070291509100780242c10311054290010503a40d0480d1030034203144945040c1c0803000d08a43e91080700407907400101b400c20442c16010b96000c2090600207089100f0503070700d5002098011000c0544100c0050b4108070456889015a141b00c0c110550a2000d25849030003031084542080b4040e88502010021520f105805001d854059980180100c1c115156500c0301080404098001e41d4480040101c4c09069203403040090002c0d80210020400e03020094103150504c0354503008881113900400c101350707981e2143d03401c580d04840c0584800e440c580d2015009c43d42d86010b60054428542440c14540080c8403500185005001200a030585c4c011500200e04000a001c2611908440020b0041001d417414401e505103c94580081e00e1a02d80351750b400c681140e100100182030642d80a40101d1911005080c4585040003542c26002c0c0d41403640b60f581d034134819001e4480b1442c0d01c400020b03812401c03a800a40d80d95598034101c0114a1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 235561654 1250 235560404 235560431
    0x1202031e070b010f0b09090711101505010908030f0a030902030d27080d35041106070b0112111e01030e01060f05060706020c0706080703050c09090705070f06 69
    0x50005800752100d5400c90004a074001d00f00700d41104598017910340f54079182d508001d016503503000501a00500074403040e824003840080c4100d0110802c0602b00082507440b0000114005003d80c11180c1048004c840030312642400004494075403c0085c9066154070010b00110302a100c4914000d41600900e003801e19840c5d08001061150070311720302c0d94195019900e2520814501030300c40c050f0031707070b00000310000e09a0007109400380c0d0161015803118420440c409220740400b0811512241424031003c210511403242c1c00c00b402580f04441c41464034036551209110702d40180241c6004000d030103065420003210a0b0381640c0c1140207800d030b44034102130b1001c03003004240001c0750703601103800c00034403040080341840b941c000c0d80e0031000600001420101440f00c59040311404540030342d401c00180c8030489007000580c000f400541e0342d000b02ea1818080c0202564400361461100b140c0c14000b0034502c2d03641c82ea041ea40a80140b82003611000d00303007402031012041900107451103160450001561 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 235562904 1250 235561654 235561657
    0x60714010b10020703200a03020405092505040608060c091e040f0507110703051002090105070b040506180102121605071704050a0501020703050c0402030612031c18030c1202031e 78
    0xb24010503100c02031145071000015006c010480d0280d0050006405000626043d4001c540140040c001c82d1250079040134020100e41070070b40c1c0d802c1c0d00005080c04011a1805006210261821070080d0041e41020418a1064020104014030031900f505c9841c0300720016025501300d03400018014081440c0180b808001848191144e800190507180d030282201030000f801d034101d075407110003802e407030005081c03e100039000500240d042110801001012070050348015002d2402200500030605244c68030401d1248035a41040099005003d58a44171021031030440d8082c0c8007d031a1011000440b40440c5d640c8104440100403800c80325428035044020009841a0382e42502c0f100491030301c0d07100690b547d450380d01c0010995031120852803c541050b40140da000000902031800c940d410640060441d00640c0c1440016480d90340c0102d4030110b40d0158030010922448500305403c0c160710000c0081e00d144002034001e6200402d8150751601c20003c0300c3d4191514484034402820445500c600d5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 235564154 1250 235562904 235562909
    0x60c021516090b0309060720030d05062e0c020d0818100504030803130c03050a05010504031812060e100606020708070b04180e03040b04120203061005060714010b100207 74
    0xa4030b61203001c10011045001c40e402010444000c1100b55103200c42100d12340b03c0035010b031000c4e806c110580e04085400700003034440341da21070b407001c078480c42d02d0f40601030341a400320240c841ca00300b0803c000700c07485060440c2c50350318046498810010726280c00031402d1f54080480c020400c10000402c08640d20400100da24944400c98944c40c041c1c0d654002150940030303d00024002e001c0801c04581c801c41c1810105c00164480c10a440143e45c1c1da4884030f0925041d40320548843e5101c0041000309a48000541d03444031080d20240c4c1e0b580c2c1840346440c40181812001010b00740e030b0b9105625110000c01c201c10081c424100c00340489515040c000b07454020030b1003444150305c5810808079034115a07205407426503100328801c164621080c046c0701e003e010202520000c40c082040045891900c0c40000c0010300100c0184198000051041c9494004024186100300c500c5e2138082c03269a803014122407aa41e0452603e100740a010305440303004010044088d40d10104010302281c440d500441c5c41c17000c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 235565404 1250 235564154 235564157
    0xa0f060c030c180501030e071a0301082512020a0e10061101050f06090c0f36090c090301020c07030b040506070e0901094221060c021516 60
    0x402c110780310948014500b500e510302414001c010a11541d4800d61092030072101d2001102d03400b40e5186011032555080000700145c0e07200000052060000c02c000c0c80d0000c944080d160020441240d400303124001c1c00740202c80c0507182140c0200d05568440025102401007902802c0040c1000e044491001c0424070a12010449070004025441c50610803144030701d44001410155a541a0412072902c9005041ca48040c00a00031170030491900307c003410070141044403c0048102400807441d54281c053341e841c07064440208009140e480b400d13901908450304c102d5082d2507140b40320003e4064021b1594003000c1d03110b078074000000e005a44064500490042040d42c5c3c00307454179034003240c86030020a015600300040c0d100400584000c0d0f84601080d004018010400880c015500400300d528210813040228480c20316942000b0200310b18001007054498248041d0820f20700200460b000c0e0f880904440d640c0e002810f1091300a0000d00150014111b07110020b00e04442844d0340b0b4003003a81c0000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 235566654 1250 235565404 235565411
    0x1107170c0d0801050904080702030f010203010e040b0f070f0e01120504080a1704050607080a0e0609060402090a0c022d030409050103060f02090102031204112d03062203020a0f060c03 80
    0x1010301e80100010741c181c0304040d1803c0d00681d556158a0207592126504036058802c3c1c402d01e0500752028400745012700780d6004041da01d800c150a02c20192000500f0201039800c40b81c00f407011094100860101c00410350a240c100080c010006985140280c424448802e06140401c010000008014068074045860707001c0500c001491205c1402011140101240d1241022074029401583d034164000c9a00c04045035810111107a14101041920394a11030b0f80036a0508c4214a00603230025070041c22010100700c0a010300340d00940d6016242014104c50904441c04c684c10002c00c0e2890407884d00c82c40440b82c0c6c55950f10074020003840244020341c9c4c85450400c6850034203113180212104408140c6c0114101101c0f0811150403060103041150464030654007800303652181d550103807407603201c08422500d203d010300194a07146c0c025014107100381c04c001c080102d160189015001050002070b17640070b0001003454168581450018003620403c1c0109014042000d15006560102d96998090 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 235567904 1250 235566654 235566673
    0x6030605090d020c3f030307080702030c070b03040f0501060b0a111603080c160803131a04030311070504050a0f0f05070e150702060a0c1e020a03061107170c 69
    0x1282c44429281210ba44a5034803403a00c00301c01d0102e010119170341d46a100202480350800c40c1c0100300300c101c600f600c61641002c400c01c03c019801500d030340d0744210325001039440d00030078035032031500c0341401e0241d04c12010f008004281440403004243d948950f1000003000160b031184051019500305100c0000007601000041000d01400714801291b80503208410444e80d0850303403a071460b41c008828074141032103562189811400c420444200400745407026603034500d001b0000b814403142c0e54104a940d1502403e250036441609001c03202280d4043c43e0101d01100c2c0c44000601b000516031000f50711506241c140b200c0b40705203920000c0700d40101c0b00100f105581420111050341e84c121032003404251940040c50b81c0d403d0150380c4420254843c243c8924098150b030001d40b43c1d0300403290450001e180b000e8a082080b01c40646501954070605440ca420800b82e4000354030322105010040070151034005c80c8146040320030039035100030384c860290010b01020044000719500803800d070182912030480c99 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 235569154 1250 235567904 235567907
    0x60d170a020a02130e1c11011a01030b041e09021f0503180c0d0201180306050f0108151b0703170412021002042d05060c0c1f0507021504080106030605090d 68
    0x1210030f040d01405c0a407a0162401a4a41c0038800c500034072402d200d52801d003054214001c0c4071b10406103640e03061055154013106e00040440c2c1d440c6006c0350050b880c212040741034030200e142c0d44107217400380d901c0401c0b45604ea01c0405c1c04800c00c440c034100e021407448040b0a04940000207540f00301452020348020308290700c0102d0380c50304c2c41024a0f8000007500c2d540800b5500c078264071540c030300c0700000c8048115034aa807001e00300c40d000c8420700b480208020042c0282e03101804030103000030659112000310304020051901c5801d07090360505052900007594020103026492100d090b11040103c8104c1d0700d405c2c28503405c0e080488071600018012185070764843c0c0c0c160b200380d0b01a40c908403072a22034003160114940c82d500d0b2442040b158560b805100141c6552140020600444408040d054031243d242c2401525403000041580d400c426100585d99140c0c00001d03a02c22a8048608000b0040c0d101034040391482a500895820350820001101340041c03034000038002c2901800312a00100034600 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 235570404 1250 235569154 235569161
    0x31210050f13150f030210090e011e05092509080d111002040f0602010c030605010804120905040507020322082d0102040e010315050f060d170a020a0213 67
    0x24541d4801d007a540074111034102400e002c0900300800b1000510800d011040003400d407155840f81510f101400d00610440c10010f01340350003002642000c04200d4104556403925600c1400380400d01140f04050035818000002c1e40001002c010345a80341c0c034109040480f840f00c0b084c540341d2a4608038000e0503907144d0b10584825007228409805450682d1031100d045071080c0404602e08207034412610500e540012520003080200100039105251614080002e42551210301d1540d00b8103140171820007059800401141c0d000e40e000300240141c0080080a841881d03050701f001b50414a44002c01c916550008010803540011140598000307072503900503000441c0a02512101d0f420920b0004030000010041d03105e801d00e8414030804090008a0041c01c90304503a0020b50b0007080d1100400500030091040d442141d4207100900207464480e00300e80f01040082c1c002401100180a91003d002d080c0c4500240e80030011420342d503403c1e80304c60003556081103c0c0c00364031500f43c0300041500070480d0f21 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 235571654 1250 235570404 235570409
    0x6030a02030303060613090501061e181202030102190503060a050603090c010c1703040c0f09020a0f1b020d06061502060708160509030a0b090f0a020616020d0b010602031210 76
    0x3070045146684000500989070481e207598001c900b052640810a001140074060182c0000da0341c2000b584c090180c4050003900c0304803c00d041c45001104246a5400c410411090301c9030303110459400e03c5640f01080c02881010710865641c140c907480c1c2000541d04c0401540036a034200c4078202059142c3c410000c140c403040e200c14403954401115440b955004407030041010340030318807000310400710f80d88540c0c0a80c412102190b0480d10310406001c170b46281c0c00ca030000b420001d41c003141004d0310804042d11092140c54180b0030f05c007000c030450b20130107500c0c01c0000d05168098210000745103140340c008007500007030240c2c1c031451a880054002840c03000500360307c100040d503503079030141c1c6518002c01106581c0000020400a040100c185039480801034561440d01c01c011030704040c42c1c0307800d556081c00461020200341c0d0b04074414440c00740e90b6510a07555140750350901c480c00c800f501d1000407450341603100f00800c1000203900000d01207402001906152245c600320001039510708004940c12005070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 235572904 1250 235571654 235571659
    0x30b010503182e14060d170d020d02071511040306020a1416061a010c14010b181e040b0106031a030f0706140a02120d060b03040c030b06030a02 63
    0x2400000c0301142041c03518101074400c401514803068103e00b00341c40c2400c201000100c5511002e0070050f4100e40c92140168004600b030b2560060305056000820a182151025005040c005101c40010303403e44101c42d419083c1140841d607400f040078030140603421000301646e5400d0100061043c660f15405800d64035481640002c0c84c180c1980d40301d80081d001040c49004101030125402100c0403110000c00701c10156585820110002d40380401c151203010800c582d142204420005141e44c101403405402907100351040144404203400d54010710403d40343e1584500602c2142030164001a1601d01813008030084015841e490107a803100e4580a540007400034188000400c542440fa501050201c05924241c152078210702d00000e160006050400c002904201005c00071160000300803000d40b01d160145600300b1200d01c8000e0344078030352000c11768013003107002070004070050140c1e016501030280348460f03075182c4c00d16040501c0080721a010450340110440301003001440c5c001180049070303a00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 235574154 1250 235572904 235572907
    0x90f05090601060507050102070b070908011a01020c1003150905160311070303020d150b03150f03030a0c150c020102030a060801020c0a081c0504050109030206060105030708040206031b121501030b0105 88
    0x81034804c4131184d10030340056409550900440c07000030150703190f10340108120350342d13007000c1d40c10105032508440705800ea1000c180d07105107100515980204d10b0210740d400444000d08500c0c00e10070305a01802000c210b05403500104440440d05601030f0780b05501035a1450001000300c1907400b410f6003200d00c0e00f280441c1420f0306100ca82c0c00244aa0000c1c50400350500300420703030811081d091511529150449074024801000b0403c0640d499100c1d051000f4045414a1244843c6004a0b440b07104007094041040394103005d0384180410000445e001d9452014204018079002a00900030740069030101111400e00d0000a500d03c814001c3d500381500c090090304025403d0f55500781e455000904a01d0070b6048c15242060080e42e522902c0e12541c0902c0c0080342c81030943c680281012001804036062200c00e0061104050340b0020305644a5070640d0107503907a46401c03c0c0240400300303050780252450000521030203111130003001ca034040e10088010644560720703000150b044e035980d540e009002400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 235575404 1250 235574154 235574159
    0x1407090902030c04080f0c0909150a020c030c060c12070503190e0f07060c1a090604030c1a041202102007060605030d021b04090b0703050405100e07090f05090601 71
    0x103055000316001400d582d0054949075484031110f09003078600740c03081e00329040f2544841d030354108400c0681d0b000b040c06016081e11400c4201c0c00e0304a54000d0200d150301540410825200e1600f042203640c044101000c44080d4030b087ca10030011780d409404d0001500703e0301804140054010001d6a00034000f42ca8400d209100140e8504010226122a122948640c100c072000340b490034400d1401a00c5071b955603ca1540d5582441940c03501c1c00603004c000401d40d50300b0001c20403004180c0e00d410a625103402c2020f02c019003045c480328810404242ca002d669a01031008202900d82140f80185a6400f507034803040700c2c02d0700c1200711002c1c0810380803048400e66490104d0b0143c03600030035106210304d000041d07079503c400c003180c50f001c42c103a100300141c0d20801043c0d2204071070303441c2c0b007c61010444003888010042e585241d141c20015104d41e00380754445c00800c080010510800c40032504040040041901240d1a02e998904c284504540701e803030b01d500c01903c9025801402d204044c03d1004004591 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 235576654 1250 235575404 235575419
    0xe030304022b02061306021c0f08040302101b021506010e040b01021002040f0f0909030504050607023f0304030506070809070801050f010306060b071203050903070c030f0501140709 79
    0x509040c6035112140296111a00580c3d402c0c4c081c1074501180b00c00d204280e414890064540850250b40c810300f034582c05003520000c2d61000803402910703141d10b40500c4a440e1032400740c1c9000340c107078220710016052040030f0511700e11200c2040400100f55007150700780c0c031540780300284a138025030307080d40000c100800010ba5410660004008810184121124502c070440044200e8104e50090303007040341c520004000f030654404100020f0410441d00b08080312466401600d24425445200e004410104200b8155520000003902800c0604540d4880102d098107010360606040c1d074115118181800e1010650340010a45041c1c03607100d03009003610380700d0720030a4503000750046c4501041d11403048007150b685020b01400e4000d00200c000144294154a8902c042d512650808c3d0020036052014001040d88107884010b0140c0604000031181c031540b4416045200703000d00a008003804440000070040b40aa24a06042c0980b008006070000312001d155812000d940b03c2c80002c580c503e081c484103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 235577904 1250 235576654 235576699
    0x6020c0a0b1e03060a030b04050a120f0c031b08160b15030c13090818240a030b0a05060c0703150207021305070c0b0c0d050a020c0a0f020d0503040e09010e03030402 72
    0x11130040c81c0a496591320b9030b400185441c1120111066044010103808021415400c031218402506044444154013840107080d4232501c00c02608012451607030080c0c10b00704220403802a03070400c0c00c1c0d5646810550044e009280325810449a101182d400502d0b100d1110b1031003070304960020050841111000104000d146081400340c0d00715035901c4021001074041001401c100d01c0c1268075a00721041da4003044503070003d00181c1d81c0c5075180001008684030301c0c0c2044070112019418005020440c0001291040d440e40d00a6500401e00198034100110b0025650007168452100c10010b00e001c01d8032041a401000c8000350004103202048204035850741096911070014a0a1180c8a6280c1c99410f1a90001d807100460741d1000a680c41d44428580074603640113001480640c030304290496241e9030b44220150250403400c2408070002151740b11f41c401000c2c5034015040b207490f503442c1c8012041c0d5520689a0135000d40c1381c4003003090190382c0402628800d64009005124081c80c032030540030803 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 235579154 1250 235577904 235577911
    0xa020d020c2d0a15030605091e071e02010b040e1605090a020702190302090f060a0b0702010908160f0e06010804020105070816200406120807140706020c0a0b1e03 71
    0x401440380c0b0070014503281e540075800100070303518000c00d200c2c202010150407550720740c2102d4040c81c0100100610101201030004103a6445640300c00c6950395200116210101c3c03400b06003801100074260502c940e0b05402108803500101c030108410f640c1002103540d5503034000c00b0400329011902c420081864521402c9500000010003d072402401d03900044408583c00c4a1103100b103070304c841c148203604100d003a0310b41c48202140d4582c0c150414000090940c5010f00c150f800d07207000081c0343c0d011a48038141c03002c01008150b0441786042c42c408203841100303d440c040d20652481d2204002120582503420706d0140f141a1515074140d1520b400440b419800003000381e07410981004032a21010343d244240b00039a01032002c0b0140c0170507540c2021380c0c4081c42703042d1510841c1441c206100c650403180082c02429404600c140d40c0e44581c0c0b5002c00580c02540300c800741c901882d1000200c1a401007402c9100640c1143d2080d9826101e0540c00d009010755000d104882d040710419508240312803008540 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 235580404 1250 235579154 235579219
    0xf0c03090709090303201204110112020309010e0c06120c0a0e180601030f140a150e040b06090a020a050919150314010501020c01170a0b090c0a020d020c 67
    0x185a110240700c0c055070700c601d004600007170341c42541865042401007101b100005449001e80b07000c060329815040080050009007823904001344c860400c1e0f0282008000403008107400303540701e04d04101c20b035000300300441140c1510f00418100b528a80740500c00c56404a01e0580415096101c20f00d8941c0d030341d0401c0f4281c10900001d6400c10714980d54035518400c64900542c50b8000320300c3d10400040941c0da540c03540340101030405083d039003d001c288200550020903082d000420510036041c002440d034056010242134402002070009204008810510610f0144d5400043c0d4990058090884c42220000000124103011089840c5800a042031103500300c43c51f44059191900e80c040f100446489654000c240d03651004007240e003e0b041454010503007400500f04c030a0030742c00003030f001c8407003c040784148444403800103106080c1030380220719503030000d0111607152418440909450780b0180d13070840580300f04008034940500c000780c641d91411002d4400c3c49100710319483d0300d03401400a1100741 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 235581654 1250 235580404 235580413
    0xc050304030c0905100b0c030d1112190b0f101112030a0903020106051f0516050703030806130603030e060d1134020a0e090f0d030606020706080f0c0309 67
    0x31602d0344407014041d0002d200006214104420f19040700c6401e030f445004286810301880007001c10110070f45840007074100c00421410413010504045202d0a24103203203c88100c0140802c114680b19021111178465204000030310b511400c110058490444450b40000001c4c0c202495a00c2560703c0710740101c1c0e9104945c1903155002c503240d12a00215030083d00c0e596145c40c1c1a040c15824004c1030002e00080d00c540b0281005000c82040e44d0044072810410700500003460704c42e5030b0100c2d410507500c94101c000d0794600c1d6182d140091841c402136071500d100301484107108141000c90f03c02e41044030f6050322131138842c4a4205c103002c4980c00041a00c400a552440d003032850383c0c2844c0c0105120103072008261250a901c5440545801c162401e088169001e845604016250b8404240940b401071105c15400c3c0e440e40112072a1a121818101e40d0b4010010a12011a056040001600d50075001d8610300d944400080b2140802203400001020a16001c03522000d02030700115004096401500e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 235582904 1250 235581654 235581659
    0x30702130906050906160504080303011505040b220e1e070c02031b0918031c06051009030510020c1c030b190e070504051e270a110702010f0c050304 65
    0x2181100c204407075413150750300880c0c100302c43c000c0240c2030842500301c0b90400742c2c04d041c140b10f4001d0762070005004031310260800800624145000704e0980b8010a1004080d5540d660911244000c00f00c50700c806041c00004401c0c041020890010354501c107101c000310144500c0e21898504000c80c502800071024000303070315024400761b2018049d07290061400700004021002030414080c000c0d100a111180f218101d54202801030404000c540b000071042807000325691300c1150103401001c1075807056901080700082c000c2d0690700170b00380170300310381c0076005550b207001c0107890313a005034412601c0c07051031030308801d03004107d15a008c002510800d205240010710041c180c030200c2ca011664400c03c902001642d042042075119a441603580880585086030416140c81c02055031040705030303c003961503030340c01360000040d4441441065030520071191040c03d00f240740c90b1300b14000380140c1c5e00e00c00c054104080c440c40d004051045070b01e03199040e9268030b621120740c98108c420000500c030403200da00080100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 235584154 1250 235582904 235582913
    0x7020d240c02010e0d03090c060f140a0c03090602010506010207050d0c0509011e06021c0c03030e12090405060603012912040c14030a051b0301150602010606170105030307021309 78
    0x102202080075400000300c02e48480440b928010020030000100760808840000041c0044541780c100d4109040011035000302810a9900e030210400384503201c1381c040340d0b44400d01d0340460b12040c41d5000b17840d001d0b00251111004c900382c0390200c98860140c0e2102c8401c216901b8441c407500d0000d8001d00310340c00011f450780001441490280e0110400e241d403000030030001c061040140c8014030440c0010400a04030a00c1080c40c8400d41d50640c007880403002e0442d051500130b4000c2c0601c21400380a5a0b1120049104221560803100c9102c1c0141c0c0341000080080c1008012203040c2e0300b6909040c501107a68210303034001110301d508021071020040c40441d8080d0380049480d40550301c201d540c1e4000c0c0b81480c0c01000e12b40d0b200c2122074400e03400070300200702280300441c0c001131260780d0b10a081c80c013100301b00200c0e015006044d008620101c82c0c0b80002070b815410b43c082c03070503a0200e03507859024210380348581e8100da00a00400303900d900201709810040c505940b01135013aa20b80d0074080355011441d00c8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 235585404 1250 235584154 235584161
    0xc030409020403020a0f05011e02100903050406021204080c1002100903120b0405150402090f12010507020607111002031e040b07080106140d050903070f0501021c0207020d24 76
    0x210035815078021505204610b000081d00c400f0303142000349420407a1500d00001d240c3c0b41c850301c0b82d010200e07001c0480c0c90010302c2030049a00d0040000024002d5595900e001003059200744143e000600030280040d240308891000c480031240208020307c00040340c402007110070b02c049400c081c01c3d40700d00c05072041810110700426034218004c3c1c039056200441c0310140b00c10b6883c1d80f51664840e82c40e14013004495a20344641c8091004203860058036a40e244c0301080c503410500b11500c3e4003a684541042c1c0090313054000900c1951660700707654103500c40c01c1c01a241c0440241c90074142d40c000072046140c8103d00e0740559030001c495120405444260200d0070300c04101a0b40603030360a00e00c00100b002c0c40f90000340e00c82c01050305260001540564040b0b0240d9402825045896103480f00081000700c0010000d0b10072045e0000c0c0340b201003074000d01c0d106000354021550100301951250820841000c248240c8207681c0d000362405c0c154030240d44c2c40e040120307520b4202c0c0c0402410440000d090b07058521 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 235586654 1250 235585404 235585409
    0x120c0c080d020106050d051b060405030f0f010b0f060f071505011d060102030a140c0c061201170a0f0b0a091e03120209030c150903060403082509060e060c0304 70
    0xc040d01901d0707402071000b800e40700d05812941c05a941162808006400007900a0307041c103542c0700e5041d82e032041e0b400080640c895603000c150705200d480c0b04229002808169408040c1984000300118061079080c02a06111180c52a60000b014030050b805081504011710f0094819881180c0074a004107005084800a030803c0d03003000000700c2d801280d016400c100b9508840c1c01d000030340c284131703070544020301e0042c1b40c4103050344413100840d02a80101c801c20411082c0d0070000c10064903040000ca0544101a09206400c0051070019400e80034403408607030100340d980c220030014080705c42616403d25161001d0f000340b440325510400117011480a054260b8040649000008112854240101120b12002c031014426104116561180c2c4d00016a0b00c601682075070034000035840442c2030030315030051080701074040c0164010042095444641e5904c103541c0791028811101d4603d0500c4444031240d03c00702c0114501801c03d00113076000d1a654113010000509031807500781468a082c1c190341051b03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 235587904 1250 235586654 235586669
    0xd090b16170403020415080c040f02040801050a02131a090607050a050717010b01090f14130906020403031101020711090c040f1502060c070b0415020d091101140a02060103120c0c 78
    0x460248111703e040d00454000034812581e151186040c203181030340f0340c20b170001e021748101d658898810b0954220340540300244001d030000c0000c0d19021242502175403000c8400301c000a0441c03004a00b10084401c105d12140343c1a42c070608112110b42803000b9940807170402e407a80e10522428000140081080402400000808d110140c6240d841c19080d6000d80301c0c4641441840318040c4124811040d454048079078800f4043c1e0b494220401040111066218022049080031141c0040c085607800510450b4802d40d918021b0202c0000828200c2c0600d102c001c1c080c4c2e500c0024a0940d19100400d02e81040d1071503582e528040d510348140f240300c2983c1d80000c9000035294007407002d05070184101035001e02ca84a02d80d241c211207503911040360000403c0204103070300300601c20180300415030548029641440040040380458100180c0341c40760f81c2241c138001009105603501c60740d80c0100b030340c16014031500281420307400c2d992200313002e032015610102040304400e103d070301140c1c0740c2d1018402031041 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 235589154 1250 235587904 235587907
    0x1d04020315031b0a0f0302010c020607061b0e09060402040b03040b0a020405030d0810050306010e040303050c04090f02031f0f091a18070207080a030807050a09090e0313080d090b1617 80
    0x140d00a00031406031350b03803103009882c103100c20800260340c000210740b04450f81102c406540b403080307150640c010001610301040101040000d1003005400c44244803400d0707822600456141e5131103007007009a11440c0504507600c0e109001060000d4440b07141705420001c0f03580f0242c00d00343c0b140003007441c09100905a5000403034003c04e115002c0450200b0101a01c4158040c01031503040802040842c1409000182015030b201c0000c2c81e130b003082d0401c1d280a00740c1e50005000e035055480060010350425600c4070100109451001e001000030721041781162540741860881a182003031803801400c14444102c21400041d20a01c9a039071141c4418a030f0640c0341c450315400b401d0a4200a14002d841d0f00314002a9004410100200c2e07000b000c11648442e0529010b651081002e1080b10803a03043da0200240310f051840c40e130750040c404806054007044c400031030815103680ea0b10003551810000704020110341e03070751014070902c2c0d2100000c05440c1034038000350658840540d141403d0f20b0114000c0c03404d0090 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 235590404 1250 235589154 235589203
    0xa02040f080c010206060d06090b01061707031a010e130e0f070603110403120e030129040b100c0c0b040305150606090a0501050c1212040309061d0402031503 69
    0x126000c0d4140038007001001024032a1400002039079604018105134800d80311312002c0340400050350000c41020b584660403803515655804041c2a51040c0b01928004015981c00610054424440c6824604006050102d002401360040d1800e002e02507030540c0010192064203910f0841d40111460f14480d080141225100428183c0c208083d0340c02075010141400380121440d11000d003560162900b10402c02215101e48030240c0b1112280e5102c1034265007482c00384041d074904224421104a4200e84030032500f2404400c101c102c81d460503c44da4030044248200840910840b0082c21031480343c8220003180340c0380c13480800b0a400c075500c02c42c1e0503807280b4010244440022841038010b00191003d0307003486201000079002c0d084c00d0041a04008012520400031501044014281039110480c07542d14202c80b600c5209410045900f600030035441800024481c0c811525100c0f0007030000e40c0750200240f00e0341000003079400a0401c0c0700d10544075090051682c0c081c8a40b2000c2c940ba024007a40056 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 235591654 1250 235590404 235590419
    0x20409020f070203210d0f060e0a0f050105013b06072a120f1704030302011505032a040209091302040b0a0b09010818070e071713080901020a0b0a0204 66
    0x19407401440d40c00c0415141c00b41c20000c0f4078401e5850f01c4104038008507884002d407c2da44014110750b030120405e001c4100c24451003a6140d4004007444147e0303442403015a880da001910340320100d20925601031414201740d006441034110b905400a41800e0f03c07001c4c611490005030b0641c00030074095841404217800c100d10941d103134460154081c170051406110518102c007903480c0300641000a0714040c41d0403411410804284d40045c3c440d2f0200501030380721910790074028000c044070130340c03107240848480c0c022400d4600041c0803070200030903010b0000000340441e500e5000040040f4840e4115809100d0545569601d9940d00e1040030030901441500145004200c296099010710701d029002c000c0c414011800482d04540c00c1310020b0800f44203989a8007502070f1028847c61003081da9000320100400c64024158080e405481580c0d94681c10409280348151080c000b40c03000b142c2c0e4801070b00310000094900002d4290b41d00d0500507035082d0741d85500c1e5407054410403151034031500e81c002010301141 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 235592904 1250 235591654 235591663
    0x7170c0d02060414130f0204090614090112030210020304060506040b040b15160f03030504170406020d2607020c1e0a050103090c150305060109080a050a02011101020409020f070203 79
    0x14000c450040e80c032089500855000d100d18001c040c0f500101c500342c0006625924070703062413000d00e0401080101041c08180703000703420502901e00c5145c00c0c414001110500700030034219101c8018504040f50346403242202102000341d0040341940160074100703429458910141d8820b0f070003a80c000c81c1602c3c000c01000f04488521070309a2061385020f030f920415880351602c244c160302c100c000f0b031070b40c0f003003025201c00240c03c0e4210000c1241401119100c20507034503400030350003244121500600c4d005c407160146050f0046008640041e8082d0803586a100c4c42038001c00004623050b040d0103c2c1c00003030a00ca03110300c1d00446801c0e000d64003a000c10b400070704010300444080004d07644003003c0c941d8524005100800d203403160074100b42c0c40303682c0082885a03114003000106500c60340441d6907021108040c02410302224003074045526031100082000300440c03003030b10880d4001d000e052a881d240d80150380350f03e04210003800540d42030002040710207040c8000c0c0080310014001944402e902d02c10107140 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 235594154 1250 235592904 235592923
    0x703080402120f060408090103110c0a0209101a1b030307031a010521040c0506131d09030d05092104090606031806090201020a1e0501050f130b180717 66
    0xe03540300b20f10f40700c1e00e1000131a2542c1c005500040c2c2c40d5880311650012409032a0003107425141e00700002e0302001c00040000e80c0c1c200580700f540c4811103580c030016070042862851207a0303d80081310407034052500c0c103200000c003044016103401d540e4040c0f00030b29452641c0c008039200800300e580c5106211070810351004c112181c200910307010b440c2c0400814508040d40c00c3d001110044003c040c04102005003562001c4041c1401624844e10340301018014504202c25101c0d481d4910200c3c0e100d50805144024a02e216910f8100154a410078424121005002c000e000000d1030260a0605114800710441c64400707018800c05d084c0c98506002c2c40c002240c6041d031101b0141854441a441483d218080104400da0000c2d40019081c06500050b42801082e65009080490b9100b1964800800c0d00c100d44146000704000c0005503039a05250301e801c0c1094a1a480c000c401c10034007000110a052050b41c803c540400780c0c2c0c07424901104003460500c0c01d4012110641c1c0116580040400c1048902c04 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 235595404 1250 235594154 235594189
    0x61103040b060613030b1e04031d0102070b09280b040503120c0705010c0f0c0e0117010908031f030f060e1011030f1509010b0d0e0105040b0a0905120703080402 70
    0x504070541e1301050b074440151000030715101c1c4d200001445084080d154082c2420784c446070605a14041c60004c0240c0c000a06003c050b441010b10104154400607178207003526001422103292109590030010203002e84280150814165041c3c4400d2101e1044807400a00200d0b081c59159800c0004040c00c0c1441c445d03000885000c1480801128400005c1d444204c6000703080c40b034105119070408602c1207030f514102410180c121400040c001e2600d40440b412100380414030500030139191b601e0b0b0300340c0311918800380420405001003130001c2d0b1440d007076134545107101ca521820340380d881d03890b403c00c00aa01c009444040d030f269a04019142d05101036016034802c0360701000b00000c241c0c4c14240e83d0002402c05031070030507101c0c00529020901c0c0160515010004c04156113507035140c030f480b0000c0e401460201314260a1803001c49001005024080c080c55102c20880d44542c1d0340003600f0010721030707910192401e215080d403204c00d1000c208010a4824025505c40358245007600500440b103210a03142e01c2d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 235596654 1250 235595404 235595407
    0x31303030f090e04230f03030f040c0602010e1b0a091b08060a0e0a0b120f211602040c0302090d060b03060c0703020a020111160b041509050102030d020f07061103040b0606 75
    0x940f495a0500d18280d100d0300e18990005c4a81080d4548040b801542065120020900c0f042e4011000e00c184224070a40b0708810091701c5160803400c2e034181a07603105907544420480010001e044401c00c940b050081c1002000f943d46800460580302c0d0070003d81d09200402d2a40c0d4501e81d40007940c658041016204408079901c0d0828901d4040002845000341d02e9030b602000c0400d59a03201e14900d0070b411402194000460f0b036000030344807001210310f080190b041c40602c0010001305820b448101e00c0c0081c2842d000101a000c0c030024001c0000e6000c105a0308100c012000d43da4204030085a80c007038200081ca0403a40e0042c545000c00c00b904110705da9400388440300009500280d02c0500c20fa083c80e1100e035112492441c51701e40302106100c850414421000400c603421840d0203841115109100d00724110401402524110103501a01c0d00580080003816440740d12030f0000c2141c0f101c410a00382c940394140d12414100d0f10390b03003a15986401d001051000b40006442c1c481c0c1c1061040b50341c80e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 235597904 1250 235596654 235596661
    0x417070f05060a0f030209060a1d01030c020c060304060f05130c0501140423091602010b0a080c1210020f0403050d140414010504030f08040303140906040306020c031303030f090e 78
    0x1250381c003898089100300306213407541051081c40785d0140c2c2c01290300546915100c40744290050302c130f500300310315a102d00c44103059401441d40c4603004448980e20700d900070700740d000210b40c184012a840104150360803521150343c2c45101560380309052241e022005c1080d0034012502e005030b42c103905d130341c861410001a054030001e00725441e000c880031100c1880ca440d4881018a203c58080643d41c44041c1e8010610810007140100c10b0f001e242c0d000510360300030020344a0a00420190b0900380c0200100c42e448600d84d240c0f107061218003447c442040e00308480340b82402c0301c89030341030307a00a039510103200c0b0300460b0400410801304404050317003210b420210844d150740c080c102854007030b81c441c0c030f9070b207404110540305180d000d0401c40d130145410039641c1510b00b90754140340c00c1e168003030b102c06c500090783c0070f51000c1e605039040103589241030000c1c10549010700c5c2d51580c901030b42040c400403503640010003e00080b071070650380b07180040d4403c0d250741c00e1241501001808503150340e44010703217210000080 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 235599154 1250 235597904 235597909
    0x150203070e0103091505040302011a150304030806031c2d020d03021815040f06081605030402010e031005010e010f0503031903090b0411031009052d01020417070f05 72
    0x30a80d007680a00c0c0008401c010781c10328110440502001c507038003d103004140020b05606400540e1580c1e1880e0810803c422100d0500c0f000d0110f00501c400090300500c0400c001900c144d16241d0010310007030442c0d0400444811040800301c4405078040403d45400030348001146469000c220005041000018030444d0140030707403941070b41d05c8d24804040e030018891f803a46c5101e5114041408000d05104014100000040c0c640c2e4414000c0818801400c1302c0052002c0c450407403d80700351b045501076070300340c400c4610035611504060812410710030f041c1e04802c5143c50411160800c502094000f03e0a545041e4580b440301764103030000441034480d04428019610300004603088040c40da0710b500400c081c0342100710003c11140780000d09000c01c00003400213100c145c1c49914055002201a10720300403080141c4011980000c2000b4419000211203050b54000304800d00d12203881855001c0408429008081c00ca900682040009206542083c4420b00d07040000b40c0191214940c980725040c2417100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 235600404 1250 235599154 235599167
    0x30605070329150a020601030c05041803030b041404030314090d050406081e100e07021513060e0616081303050f0a02010b0a120506130c060509010c02031915020307 72
    0x1650b0401e1881921035503000d48401ca00c0202186032180f4680d1103030b0390b124000f500e4250a00c410354400030a0030010509260620942041c0002610003101348400c596054001c0c0c6002034926030300c81d55606107a817013000940c039014419403003540c0002c1c1d07044000c0042c4144210203001480319074003154034801c00310342000440302940c83c6820510503540d00c01024484801d00c0c8440c04404800d600700b804668003039046800c003514000d02c00103020342d5590303034102c0c1c1d41e80100380780301031104107000407a404040720071056050500032031000c0344800010305210300c0c140c41a50219a0f0700c40445140fa0401e038001e5256030083c8504d0848089c40c07501d81c400a1281c090300040f0075030310000054800002d4001d5001c01d604900142a2002c096900e45034031004640c1c0e11010348880c0100c40002e00603240d00b0b03410704001c65110714080741140c00c2a6084034580c00446071036060044032030030200566130030009844118189441d10f40b400da200d1400c11590034088012800c41d034010f0040c4150950000b4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 235601654 1250 235600404 235600451
    0x1a1e010302030712020d021005030403170f0c0f090406031b090b0d0b0709030b040501020307030c05070c0918080f0a0e030a150c0509040e010b030d050705120711030303100306050703 80
    0x14807407280c100c183c00082ca450964140003541701c413a100312300c001187c100029600c01d50003511040c50040410212079000d0300d088030300040400150340041e03100072000340900b4105090113103880c18542e0942c00305046a10030741081e6001c03503000a00c114004250803004020340a507000901100d403010000c21000303d01020003c0c606070034540041d414500c40c04c0680c0086402404020150406080c254001d51003030359104006414010241e140c240035800325220702e0740c404132a030902481d001c40c80e001014010030b0320a40c1304098450301d001c01c0c141c1c0041d00ca41060b12103c16502c045c0100040c1101c000420140d0080d00040c0c2c0c5c48000c40c140d8620b80c5002441c0031170210352045107035000c66152041c02c40b80c0d030b030083c03500b0311079080d4290560151142d01400d4040724000710380d0301e8060340d40c1c1c000c07200c00806640c041d480401600c00c8150203810031501c150321021000e5090b00000b030564204480400c0ea6a010300da0420034880c16001785074001240d8141040703240440981c0320440075400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 235602904 1250 235601654 235601669
    0x10609180309140d02151908011409040507170102090f0307030215030c19020606030606033004051002060f0f22020102100608070e0c18100201091a1e0103020307 71
    0x201c1c0d00d00041d8540d013100301d82543c0c3c01442c00b42c0340384018884254a4100300300c00b80625012030a24002140030f40b0896050b100d50f8240407089131111820803001c404010411100f07409805800103d9012003204043d0003450b450026880f140404140508605422455480381c1d002a03810805610f4031661013a103071140000d074a90340d541e92a0803001c14443c1120003895810400342000c160f82c1d001c01c4050140804505455003a1034a4080603070314a41c280040b885800015045e111b41341002c610344200c50042805e80d42019603502c0007540390644201c2c68005600a0400c2020002c03031100354582c46881040d910840341000e00340034000401098034084164100103880b015a0b008000b90900c2840c1c0182c20300019071aa141319460f041284602e480c0a0f40ca41d0124070516003450a54605580001d00c142c10581c140082203829207007404940d00359583c0b4480342c1c011807140302003201011410140d20b04d19080c001c1217071604480c04804070034071190309401800103a5012038924201e4040e07 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 235604154 1250 235602904 235602929
    0x15050d0303020c030a2609030d0b040b060301120308180a11010e090a06061202070503090d0c0906090c1103070312020a11030408060106020c0603010e280c02010609180309 75
    0x145401e074000e20510703000c02480c1c800840c8014190b503221420001070401d280310040404131b007580c003071030041007501d0f41d80c86a0428042858810f005038004079402ea001000401c0700d92503d03020961035031003130b0881c05c0074200c10640320092641141625400050141c580445004400c105648904c3e40010041c5142001c90385a0203580c4201c1e144801c2c0307240107044034403e080c4440160001c010a00c03d0303401090315103d035441c404c040b0b44266000700340c00c01c016515080000007003013840f9100c82401c40306071245610100d5028034900c00d050240c1001800021b03c0303000c1c0c0300080c00c20100d03060000c41aa00400c2040002070b488614814000204c020140c3c4884113000c041d43d00d4400701540f85020300c0041800148004000348060407599550203a80211040c0d4050055501c801d0080300c3c2254540c5002c105986130307204900160b901d10840b488080443c0c040e68106036409441c0d13600060391114070511401110344a03ca41540c01440d84601090059902070401c00c0c403403140d040c1c07803541c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 235605404 1250 235604154 235604179
    0xd0c0807150605090a09030e010201020a050d020901030608030c060703060e060619090902070b1e011a090301290a0506130603020c07030506010f0f080304030803160e041814011505 79
    0x5242c00c401c020f048001c041308540d25001015600816002034160002900c5e120060010350041c400c480001c00c0030b644852500c0246004c035000395200510950405543d000e0000d41c8600c02c0c0301400000d00c25030083c1c41e15090010005043c0c1d41d030794104403800c084c0c0d14113000b95956554102c41c4541c2408050501d4100e107020309680c0001a80c0c080407640d400040e40c542000b240d403400c540700d03991400e440380c0c0780040c00c0301f00203000a0074021414910a0306840c1720251301160007811a07648020004950100140c18411803c482d1490f44074401a2450202c400707480c090140c00b01524080da101c0c4c3c1000c06038003010040e80018420300741030581c002500c00d501d00c0140f203244003a607000030860700c2c41e5030741e034070301200c2d003291440341180511001d0001f00b2410300110032141101d030000751050858076403106003040713a000c64080c4018040e00e0300c01c81040e41c03a030b80a19441075091100410891500e42068070210402c100341c941c0030b1345401ca46808000e000d88004041d80c80c141d614110201 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 235606654 1250 235605404 235605443
    0x1020301050f043b06010b1602310b0907020c060322020901030803070906020304060203031501050d0c20010e0d05030c04080303100302041404020a03031d04020d0c020d0c0807 77
    0xc40014421400031035151185811640f0080944c1d6181c24070040704d1881c0e903150074141050241321070040d50003014104080c05440c0481101c10004a40da03210190580402c00d5a60100c03943d40c0c40e104055160402c4083c1d40c40d00d1207100b0780c02421030016000308490100050701601c0010f00e0a00c2a1051075261307c2c04130781c541946054260f019140ea07070170756164100130aaa40003290408001480410003045841c0b003c0203a804071690b07a0001c50441c0c542150417070342d114402603818100a000d12080c03108003d1400780b0380f1040807c4e01d510100e840981d00c000f80400b049502c80103d42e06014410b20009000144000002101d01e4055260745a40340820300c1442581e211001c148804010b01032030030214107269040380c0c0300f2101000100e4900f01c4d84485020201d9001e988a00b00d00000c00200c0c1c0155141003882c00c01c00c0c1085c000da0b424100280032600104018841c0d640d40354181740d0015010031110740c40c3c2030281402002980c2655464426200c1c030b54004020000d0f0552071007190 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 235607904 1250 235606654 235606691
    0x1e0a1113020405031e0706110a12140d060303090626070c0b010e100510120504110a0b03010f0504110a030b060d0e03091509010e1c0206130f0801020301050f04 70
    0xf00b5008056032003003c19102c010484810107820040d950282c07581c002643d5010b80b40e102c40c40d01c0e01b000940b03410911612000003250081c8120014006007002d030f045040100401003c04a0b41d5010000d00300e401c50038010050800b40d0000c0c010701c03032904903070b0b041444035001c01025004c440b04941c2c0142d0714104125600b882c1208003c2440c01d90100108074212900300c258451040110f40c020019691001c0041043c0b0340b076503100210308800c91103c1200016004158410701842c030040b05005004041845410f08d6882404080000701c01481460120105500140002c8400340705803001812400b010340319403900541450750340c8100000030344618098809080c080501000708041c0900026203039070281c5011480352200d40c1040003110225030544440b0001a950703601503c40540621481000c45d40c030420b4444107895940340180c5c3c4950090000052140c00c0012951030a881e201c5050125003103c10b159005000602c083d445100d00401e4050b41210081202e00c640c060800a2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 235609154 1250 235607904 235607909
    0xa0b1c0f0f060e030408010c0302070218090a050f030c0106150e10140d0b01031401260a0b160f0201050601050a050306130504061a091012080d0204081e0a11130204 72
    0x1800e100c5101c5583c58040b011304200c17041007009024101c11400100c0c100d20643c14000e6004025101384071800c0305654003140d0000e00b80b01282c901d404140c803224509806c0200d0b06100d40c0c000110040b4800302800341e400100300000c03007134100c4c400420000d08a003031400009400f440300181c418460a20400d00c420710f440e045011241d44d4101038101e880546850a10507011901308940c040e00d504000b140c1034121101c000300c071404014080300c0a628640400808405071003689040008a80d159107480c0c000c221000100c0e01d0020030070405000b000440c4580c0f4190391418007086482d9810400b200d01e109003501c2d2044c0c1d06c0c1d4034500010707078002030080007175070061500e0100010070149a100380102c4010140540f00c01003094200070400300c040390503240d50410f6100402501040f03040c0210014420820181070007400d411040c126042079001d150140e00003070101031118080c19010710580c1c060400b62010700c7d015100c000f00072100e00900d5014185843c001c0d404c40c0c0096050300c01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 235610404 1250 235609154 235609163
    0x40b010e1906120b060d11120c0a08060114090103030203090613090911090a18062a0c0b07050a020a020f031002040905010f06090302011209030309080705060a0b1c0f0f 74
    0x1407207843e007078880e80020f01003400b00c90101310103000c6082464844444800300d503000400000d401c10140500440c060444e8140713915118000f0700d01120307510f200c1b14070081e0421400a010962500080c190301c1c2d4203201455008179098001400841e50200407241404803d503210f6580703000744103c481c500040c992001124600e084c66a0b1300300040504030300c441c0b00c2d046505211a8803684c0000f03040b900090342c403881c095981000d00380024016044031103141a81039620301807182c00b0501b070380e03040300341c516040c00512000400401c21a191048942181242c83c001f4180f468070440a5074881403e01d02900c120344041c14105240e0f420060382d9408071030f4900c195140e55566035050701410080c0101c8400e81403107240802d03034074854a0400100c940581d0b4075910b1171060001c074801401c81d05c0082c0c0c105500c9408c60401f08024078000d00100d80b040009000501e17007140c0802c12034813454104d070720512034a54040d0300c41d03582c1c1c02242034081d0440780100c00c00c0e0007031400f4038420b82134050041 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 235611510 1106 235610404 235610411
    0x1409010c020a05120a03120501050d030c0f080d09020102070509070c0b0a060302060316170609160e031b1002030f070f03170901060503070509040b010e19 68
    0x5600280115048036192800704034442514640c000c01d42e40070785c1903203003050340c88030004040001014080180707505100000380c84205180d00607080051802056050003200c04100c003010740e01100007561040f0040662000d030100c03810a034050301400f10001402e0411414091258089960351144a00280c2d1000c0c0101c0b4041c05003408140e640c480840103842d41c00c02180541c01903c2c28092010b50a28020002501c00e0b2614003407440740e500b030080c01d0f1102440c4903000b44a0810b40342d860441900221101a0301840e01341c0e2603c610610b40341540584601020a0301045d07035541c40b03c85400340c0590740e038400c00c00a03a802803410040000405c0800902c4a80640300707291500e903904490b0590f6014071000e8900710382995503040100254a81040301e0002807405941854441c46c046d1a415560b001c14411804140104000108801c902c6030400411003413174107003003 = true := by decide +kernel

theorem cover : BRFrame.Cov 235431654 235611510 := by
  have h0 := BRFrame.cov_init 235431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 235431654 ≤ n) (h2 : n < 235611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
