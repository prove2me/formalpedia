-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2271
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:11:54.260213+00:00
-- url     : https://prove2.me/submissions/10c933a7-2b4d-45d2-93b7-ea63020a58a5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 408273381 ≤ n < 408453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 408274631 1250 408273381 408273389
    0xa03111b2103270a08031501090509010e190e03210f24061308060105180603060118200903010c031b030203060102150a1406030d0c08030c07061503020406 68
    0x1d60148203000c518000044030750b06080c880450440c100c84400030440c50090b090400401c002000010001401d076528030080c00000c003a03c901800686400401803950801d016002002d00142c00003920802c0c0d0312030b8070000c41004000080c41032106031ba9a801c661041c6107031800317852440d071205404030a1003c01c5034000b8043e0260301c4642801c0199548408001901103001c0c0710b01f002d00800c40c0d035000e045910038072105020840203640e400b000c584914003442543c4c440c2c02c6a02d03881400c1070314126540c0c0700c4d600080c0540400c0e030a140100f000d4003503c070b88240c000b83d074907640c0d1907480d5806294500c510a0b1100e440d5241e040300c00c100350940315461514000c060900c280281c1403038245c400c1400401e501d0402503103a58420300101d02c3d00c10b0b40c4208024030580b61040c4800746000358005040d00369900c00414071507550340140740d61035a04103150400106003405103008142144042d542100300703e81c3c0f05140c500e16031100c00558402000e14003480109850800452400e80328410041c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 408275881 1250 408274631 408274693
    0xd1b080721110f0a0b03041a1825031401051506040605040506071a0c0d0b040e03090405040809030109081309090b0c0d09080c16050609060a03111b 65
    0x16400c0c0e038403580030075526240355005000c3c0760f9040e15999109140c1d070018014860032603490346003505000030242c13101c011040c0301c008000b010405042c08101d958425020f240e005204402a0501d0301c02c0d4110848101c140504000740c0104c0007031080510990040800c5002003054104044200942d0141d03801c9240300303070001c200c200b10340c58021043c2ca044610842c2c1e1251a2006402c01d60420103080e000511820924410004510f100c1c0d8003400322011086800c002c81a1108180411264000b2207416243d00c14005403d80d460706030050f5902c00e1040044905100d480d0010030700751343c5032070404c503a10030000c2114403030650b0b039254803001010415000c2c050074500743c5070364202c41c5014001d00e9035200700007007200a00034280c00280307525030f1110401e90356800849107a41c40c1d10302071104000e50b000009000440b0b1410505030b4100120080280b4a031051044d003c3d0001e00c50070800031801c0c0310500880004541d001851100c60a01401814483d032503220035001c2c99110340148514 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 408277131 1250 408275881 408275939
    0x1050307170604090203030423090402090604050907080f071e0608040305130e040606090c03060b090103020903010b0612041b060905040b03030d0603050d2c0d1b0807 73
    0x302603201c26004110000d0100a08003500d6800c0414090041150069058407000a00040103c1e191800c00e2240c2da0100030000e04111680421880150542d0043d600650000200300307580b030709520140d00000080e046560b240e554403585410690705803021800d41d08421010403d100d602c40c01341001c8a01400701e40842424803001800484002e0006010410301040000d0804c2d1080101005041400d441d000503143c40d25061000c1c20060080b018280e0800e9070540c440d5009014510680f04400b03070446c200046a00118001d400144d910344e459074981d885440103407500340007000000484144c9540901d4036003000e01b4509107011045c1900300303071450100503450b40a030304241a0f0310111408210140e450000a02c1c43c043c8458001c85a45400c100104001c000114504000c0860316502041e42108d4444201e6402c200301c3c52901c03840d030010900161070107016260041d0300c51451103503040318035005c003c68091180c00c840b645a1101c002440007445001c1a0f10080102140e0000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 408278381 1250 408277131 408277141
    0x1503050d0e010e21030408060112060609020307020c010806030c090a02070b0f090606010f030209030d09090c020312010b0c01020c1f2a030e0127110105040b0703081e0a05060a05010503 81
    0xc800701600b40c116440c429051343c15401806004a4006105400460749556101e13001801c100d9100c400444555103030040000b123842e014003d0301d00c224110703006442030f0006000159082c040042405a160040948060f00da40d200c10142d401103822110058480c00300b0324122841d0a000b170080b040041c00101040241c000001b40c0c40e910900a107030540c000002102c042e0043c0c044e140107198140540d00d1800c031042e0744031f4000b0040750300e04041848486013229050303803030303100f09046201e503183c9240040c09624040c0005021504148000516210246160504014000300c40120740d90b0b801c1090442c040050080c100c95090000e004014010b0b048a43c3d50b440083c00090001d25450351030008022101b948890702c0283c1189540600c412442c41c0c3c0090b5900342ca40441ea901c0740b140d0710806551040d000d44040e5685200200e00e07104803528180c50400000b05440c1088810f0406990110000601d2034050b00001030007149a007400d41c00c0120792034031b0360071050400c2428808c202d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 408279631 1250 408278381 408278389
    0x8041b0305100908040509190609050105030a08070203121216050a0836010c03050c04060219060b0d11031905030a0c08040e0403170112030f0e041503050d0e010e 71
    0x81002c82d0301c0002a40d44258a0301d00a130340a164422039110400d141001003400188000000f280c00c4c0070400c0042644030459130081320070038050030307401d0f61100c00706c907000800500c01045010700040c101c548030103014060504a0f0f00c41404032000c50400800e002940159000c008902c0000341003d500381503803042c008019079402482e14001c0340b0040c01d210034400252000800350319848541154000000c40078501801c0ca9800e00c20010349040300003165500c10303409540558001e0380c042d00051904c03c10200c100c01c07000206690803503559403000c20541d40c2110340203180707104500305032a64038a007003014180500040c107144100050500000001c2e404400ca8403582000e080840e110002800c2c140b4650043c1c1d04140f420f0fa0441701800b00b0305030803041d18054011206071006490b0707224462801d00710100c81008011942d5501c0221009028018030240d103800540b0014102100e5089213101445079072064480d078001c0c4075441d2060790301c000d092588a200307003845580e802c40c50005c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 408280881 1250 408279631 408279643
    0x218011209020d0609021201090b0916080715050c0d090f090c200f0a0b01030204050601050c153304150503030405060c0313030b0f101d101508041b0305 67
    0x4c00d0550395650705130031540c2d0b18214400c00d1128030001c016000252602d80680082504e020300e061154000346031600e403070343d50101d040e2082d1401900320382d450041070820f03410000507070710184401880002d00c8010204000710b01a00160b2798010803510701490340064020300d40000d454a0708080301000c0a581142d9903007002c1d03804401c203030201c1c24580e030303418241101c1aa0075204c601070000480e052000c01d007030b00750507240229420800d9440348030041d00c8610410140840c1078001e20540c42c0d90812043e00c2070b0f484440182661810440c4180600800104054100c1810450902071405040c5841942890640c0850a01c07015003003a000176aa80501d1051170320030f80700052003141c0c5590620540c0c0c1c0160ba201000c01c0143d440e840c003030f82500700031a54030600501c00c10029800602030140d4004480034a0114022503518a405001c02c0310001e00007032154081d10703c0000e00049540202c04a0840e0781c2d00d407051824207180040e140210a000880c2c4a4100c14061022600100c0c003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 408282131 1250 408280881 408280883
    0x1060503040f050f0a0807020909060106020d030222061206050103051e0a0b04050933042604090b03010509010e07151803060f0b100e220218011209020d 67
    0x2c0d003407a120b00c51401c0d40c501210f84003d540c960041007150010024400040d0500c18070880702c00070165035495240751b450781c09100345001030f441141c0e80d055082c003a40c0108580030b2428840350090b0f01d0300300321800c8240075074000c40020720022840703a0a40100d00c00c800c041c0c4070034030342403149042050f010101224440c22800c20140d00740085a05001d46a011001031200a403040c05249808a0100e803104004500070560821001d0600000907000f100764a4080f500c07098001c6d1a119a00e4148900002403d10000141d4084140301902d00200180005045617640030400681440c14182555005070040d81c1c00c0e030601c100d2400540c030101d40e03402550410190001d04d481650700c11220f01469507150417810500040c0170042c4203850f0844941016068800d10400184506001c0c0e09a040810140020021382c2c01d4135051030561511a00c6410745120346540a25450141c0100d0707200d445621001e01d1009421403455030806078200702882c1d17280781007100e6a1540c011868860041c90 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 408283381 1250 408282131 408282143
    0x9010b0c1b0f01052109010b0108010905041502212e03150c12020c07050108010b19050a020a1e0314030f010b0a05040e0f06011215230d05030406170106050304 70
    0x5014400c44405d2500601a050001904500b505140004600030040c1850590000704d080d40003040f014014040c035405140d0144032030390b19024807080a00250010a5140c010307190303031080100c3c1a010031441c6405540c21202c8680c503c00190702c94290581c0340e0302d0905560568440410100e182c0400030408014900c001080713041049a0403140d030a03660a9030394542e440840c1d01c620380d5100040c8003060300c038280c850369607a1740c0750101c2500600130452202d05031034410040110a81c4100003802485e07400d8011103065520356602c0e4450003c11200c808a07201422640c0400d240e80000d20310b12104400c814140f440c10841844003030b98005014450040c00c00141e8404000d2084045038000c01071900c12403000e05204107001030900055900a000411800c8045030100851040101411410103030760b5280380b03014a00e4406100803403400f201c2600f0b91803000019150501e004000b10311075009160b8407414000007a180b038421200750025035003840014040190807600710b0b07030480d4201c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 408284631 1250 408283381 408283387
    0x4031a090615280b07030816080105061804110d050906181e10050403050c070b09060409090204150e0708130f0b131b03030e1807051809010b0c1b0f0105 67
    0x3d449907250310381c1c0c0c1d00040c580c65001607140c051560100003180103d41005000b1240500c46408480540d42030145640c845010810030340341903221526001e1114001d400415031001c0240200340e00d401040d4505401c546500800c400c400050100707940c80030040000070545003494001583c1c0e03201c050864109405954824505580100895140c02031120030600440c901850001c1954211411031400d03449178820208440c0c00079020745840c001c002e49203a00701071071b00700d081026015006081e604141c0e202080c546a210400903900980500b440508090516040080040800a090f5070300b080c0280d035040001003812000c0613219030444118412502e0740c540111040401c40d00050040c1102c81039418080c40c001000400c0324000e03190114900350213002d009442c049030702c021841011902c0000c03505401600a081000c0500c12800c1003140c010f0040340210100b80c00c61289d40c1c0c40801e004482c0d400822111050841c620401e1403c1900300000c106d0140740c45403200e060002c04 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 408285881 1250 408284631 408284689
    0x4080306120c0d14010513080d18050102040b0301060f0e0f10020c040f05011401080c120c04080d0c0606170a1502161a09070f06050a030204031a090615 67
    0xb040100d4140c0d0b8024810364100d241c40c6000079922050a01d505425400c000c0024144907060107a075403c81e0b0445030752460a030380005190000d1808000e07085600c107c511054001c11002d1000e00f02400d00903148990725410300030044c040301d410900e40c4003088050442292951280076008422800940750444016a03640040c2d00b094202001c850300f00c0d24110504420b4100b0b03402950490f0512002120701030718001c01100d488200b20f07140088010200100c414070b411150340c4c141e2040740d0303222817420300c1d807100010390a0904400c034035400900d034071f030301802842070b28401e003001810301080c16001409401c01c01c3e501d40c100000060310110307108400052404440d0102c4044184c1002c80c482c441c4010700d001c15441d8508180184045607080010380900400600802954100f12480350f100d45000800c40786944043e440c002059020b0000100240c54101c8070602e41603600d000510528126031701502d0020b0080041d0840035440ba184081901c40c4280d03a002c42061001d1440c411502d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 408287131 1250 408285881 408285883
    0x5040206041d06012006041403130e0916050f10110f2802010c0b070306030b010929010518030114040f0605010905010b0d0903030b0604061d090408030612 68
    0xc5074032a91004580342003014110682c00031261044200362200b100303008181c0541c03280035501c603c4000c0036034051800304002c254214016032504183e0b5041764540341c0b40d50a9222a40308130b5000d0f240065045092000012050144560480d0340bd8104070a442c5840c00103a40c80d20001030032402101410480c4c48828441ca940d215654883d1003103440350f0b8503103400150307110f40c40070005150300488407081058400c5d11b103809100e90b030160b48400c640905611f80180c0da00b0301030800c1c01070603642c100c0000005c0c5014650390081c10130341d60000b440f482030046107841462014400d0300780071881845481c240e0708071003500d020580d4040c0c81c12400e2255404a80104001d21119001c0c640c1e50082004102032207040c034115038402c070420f00c582d983e581c400c00d054031401c0c068a504040107000c0c0048001440e0b011301c81c418044d11740850061000c001150055115030440800a501c103004e10dc24003c00706401148441c0c01d031280d01c00c500d45600d41c060203010107020288180075007540441c0b8000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 408288381 1250 408287131 408287137
    0x307050f03060102012a0207090203040c03080c01150314060f0106021b0f04020d0209150a080c0309101505011106060a03060207080c03180a0b0309060c0a021e010504170c0a02010305040206 83
    0x40042d542e503480c4036125070740c6d1074002d90501c0c0035006124035071001c00c240080d4000c1c2c2c2e008552080c0840d0308541540d450319015000f0580b90000d0f5940ea0502c10b6010181071040d0b4000c500a010042040c501c0c070fa00c0b00c3c20480c0051580d103e0050100042120750f600241d405078064502000c2d600303110541d800540c61040e0891003540c01400400c0d109604191580244072143c2c0440d01c100800c0000d40c000c40c41d60083e5030914000c507035003500040c41c502680000b1a4400f0b000c00c10f403403285004030f402c2c10031140040103042e054a0072800500081d60003c01d0400e4080c0712800030840391800350002400742d4514080140717440d1700850000304020316070042c1c41205a00c00c051320345440c03810900da640e0640c845902c1f4070910034100c0005045280108484c0101d501d04041d01c80c59640c2d1074124419400399800400b1485202da51540c904074001e00003d0003508080086001d0802e410304406c040150828211004c00401039000700050024008840d2542802c01040c0f503aa40c0c00000d1240c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 408289631 1250 408288381 408288401
    0x601090302150310080a08030a050a020d020a0c05010507091202060702030106081207020f0a05060901030e160914060108060d26070f03140310031410090f03020708030307050f0306010201 82
    0x250319a01d40e04614000c402644c491224214848800d81d03941c00316a982d02d1010b070001d040c5503020804260b404560303410040d805600c03110098500002018250b04907404200e5601c0010061000c84042110078002e440c2c02000f1891310010503401d00500c030618000a40c0020b108650001d0b405003151029048080100301d15001d8940c072074112505c2c85429031040d10308905c9081446039000d034601d0007000c65030a492026008034100240d200040d00209010703400b4003c144605940150b80c100c110703200c0d002500d20f008020890103d42c1c07220041240e00a8410340c1408100c400304a142e88420016a80b440d4002031113041a01940c01c070790744109014803503070652880015050050111039640c0e96449446640c4110021213590200e186c40e0106858102d05900c00c10740800108030140000aa040c2c0711900f5145000d803e002c4010442d11a1242200c00c440300c1031110043c541c06116180c0140045005145149020b00c402401480b0b02805441002c0300400480c0e956407003540090310b84 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 408290881 1250 408289631 408289639
    0x204080709241d24131b0f11010627090c03030e01021b0307050409020301020d0f090b0a0c020316030c0203060a05010f080a0c03030c03230307120905150601090302 72
    0x599241d08850b0b40740d44844071100c15210040c80880c110107100444020301401c842110b113100014a070412018003840c01103805e54640710200841400740503504000c00c41c515480749415850b902030b000e40f4040d1000c00141c1b490740b50000800c031035070010b98845814064052110903148160b418100201030000000c0d0940c10008008030400d50017600218082c0c030700340c00302c0e850210f14240000c0710401d240c00c840e4054020305020041818a90010030000d4401000541007101c0170a814084070304a082c0280c201f615444000c050010401656030085a200f81c01d02c03271201c0300c5901070b541e8441c0000e0250082c94213070b040d80034140301d04040c2082c2503009003034540900300707490201d001d05002c1c00b404001012881001a4a480c009881d04100303a0203c80801881d01e9920709940c01000b9800503414440c4e440517607401e85200c80301c50000c3c0c0400303500d45903d0342483c4c00021325040041e030840240700d02d030240c55404501c2c00039844e900e440320198480d4443e90351400480c4e6803600303a030009401c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 408292131 1250 408290881 408290951
    0xc030807110f040203091216200406080a0308041e02032a190b0a180314011104030b0a0903020f0d02060f09060f01061b08040b0309060a0204080709 65
    0x400036540d481c0503000c0011120011411190030403c4120303c800d550b01038040d803000f486084805e400d003000c0d004020008400d000f9442450300c4424111a248584c00704c1102460a04031051620741320301d80c0035120300802456404016503024080b40001781c006010410200302410082e1070450403a0301e840e13030190a50340c0c1c0290030400540d18541054080c11000301101034100942402405a00d450b2030309181d9110341440c008400e039090348a605504100189450200f42420340000040c009612594011200740282800a421074014561220301d100b0100303c2040440c10054046810804140c2c0000305d2102d00d02e0183e16024100c403028207180a0118440d6000ba000b1890510400b03002c200c818442d668040c070261100780c101c0341300000d2000f410040c002c0e83e200e240c40c08555a111401d40b08681001e4548003259003060b1311040c0b0200c0000200901040148441030300301802c0002941050304001400b40c6400050166500c1155525241c20b125040f003100d8a12602145031030540c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 408293381 1250 408292131 408292133
    0x270b040c0f08160509130b040e0718060b0a030c020a0203061801112b061208220305070b0c0307150c0915020a12020c04140a150b07060203040c030807 66
    0x3086403107000480340441c01c59000203d00701c1da0807019040c0c800b2690b5a031440c1000010802c20603400001408000c06d58032801202e071a104d038800c49814100001c01429814540402c41030b00300010408050010f082030401c000d4020301c04184d5040702e40d04c2c20081501106c1c950228580100020080e616110310310034030140c015511101c0e0f150180540017480b0019840728203072014461118040d9220b4810800c1d0045000f040d030703091400c00c03070031b2a0100e2415511030141502e441880c03000e48804000041201500000d5804000c08910782c50b52055102d2450301c1d929103410441c450b03414030b40800100721800f0201402180c0b5155400441d181a01d0300d83c2c0390707100003481a07030011004a81c07401c0000c584c88500721010304503c41c0030703402800b217825695200554403030300e00c10321401e510a00380b4104007030342d480c042c05500c460140c3e0172002c54a04247c014007660340c0e502c9100d40c1c0984a00041c0443c007841c038220f80707003140c0058000d07a0340e4450340343c415101d18065001510105010401078 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 408294631 1250 408293381 408293387
    0x111011b05090a09020f030106110708011a010f021c180504050a0603060b2d0105190e090105190b1b120c0615030a06052707050a060207270b040c 64
    0xb090000b01510b951070a142c80d180007004900c00e03040040000e141c280b004001403407283d58a091000788c03982c00d0320300040d81c540300f581c259040c1102c1003004500c2c85c17003400665640304c0030045030240740307100515000004201c80040741180d0612081080f10408820482c00502c06211000701005481000f003464500d1040f001450140021140903042c107034503410b549840340043e2000741c086001d401910b101001101040110340444ea81800004e0013240c13016051491610b032075500c1da0700c82c071420880c407030200070901c4016080144501c43c40c6c1d41d001804000601c0c41c0b01541c501490407035951400c1400b580640d40e450904503214820380c41401842982c01018110300c4007448104c0d0416100d24850038000f1000c0301d182c0d034042d0b01a04120340820b5058010640246950040c8035045c00c07003a1000c1030301f44145204c408241e001c1c1d03208100c0e03400d09619040c000d1210b840074050650901b00d8050110701d690b00000301804060f01010f408210035401030b0f2032200f0003401009008201d01004d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 408295881 1250 408294631 408294637
    0x80a0302030c060c030906011206060f060507060b0a0b07110d0b010312320a03060902030c0901080105100207050d0c05060a0e031903080604111201080601052d0111011b05 75
    0x140e00c035001d5040400c100013000c50649004804079000360425a08202003510480c07815101900c2d07071519080009408520840000081c2005541d26940c40f401803c1c01021303a9600c008140c06844610020070403007880c5000e84100a40c031268402c80320031284002071680031280000b50000442d000000304000080c2c4654403180580d8407081e07401609803191b2a030003041c1c1c04220642141035101191311904030401001c411900c1d090000e00c40d9201c01008041381c00490b42200d01880000c0c208000e51f03041191315005000883d58070041d000c00ca103000307499023010700c5074a00a01000d4406030400c49400c0c441c17005844050301c055103c6903c614010026841c030780d6094000c2c010500f03019000281015422401600f584418540f52900c0040c0f000078940c0c3c9030038041000717090210075286039010b0f01b0300c2d009241002c003c000c0c65043c80c0c1041040c1803c086038a0805480d1808410b080d0703412408a0300314402401c0141014031515855030141401080c552a407400007c50044040d40010113 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 408297131 1250 408295881 408295897
    0xe240310020c15010f05101209140c030a1505060d121e181a0c01090f030e180609060f060c0a2a09020901110d09140906130506010207080a030203 64
    0x1143c481d014503c800140c5141e00380140440010304038414045414070407010200e0300c075503181c0b01208440060b8100100c41c1c49810880d6104426001408100003c0040035031440007100a00001c007070035078440a982c000c4120201413039481d080050015501c02c4100c05e111138025104501c01d8044c40303002820320030091468104c02900c0c00e08160468415824031010b460414942c03240b050078840b100340300c404085803402d00c1020810800d22074000038010702800502c140a40b1300c0c940c80b18a0050040080b444100d40030300748240c2e00341401b06400071155000002603880150350349485011510f0321107050141a00700704001130719103041c0c0300007c1c0050818018080d0017010010681c0301e800007292001c0032122103050746000d0151401ca94002c00c0c1c0000141444545007402880c840d0605201d10b00c08400726503510030800c40701c0e10f00c00410200340360803142d0307a0381c034034220001031140703406182c0e054683c950fa50f00061003a4000c112a20103070680c542100d54204492800070b5030782d406094 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 408298381 1250 408297131 408297133
    0x31c06050913080904051b040f0f0501050322110d210e01050702191d0106020c010201020702090a0510031502220305060c030406061802031e010e240310020c 69
    0x20006080c5082c0707240c080d000640c0140c41d0f5240076100f40410015010181514510015541c0340074140c2d505040140028808005028109440c2c13200312604841150b02450501c00104100421a500c101d504a280d0545a442400c0704905050010300e2080380070203a40c01c94181e102c04414400202c10048a9911004002c841000700d0340341121070680c0c0d915071a011070b100340b280c2001850f15003008601d00044d4140000d000e035443c1d40710310380804070070031200d15586d03801c0c014414540e05004001491f0740c203000039807400320247d0105c0c40004006096041507956000803c6481d0002968000111b410040103002c5100094400f002135101030013442c0582c0088030502003507405d4072a02d034212604500a04004d51b5000203000e920340c4024011070f241940c0701008555608002c0040c1c01348000d0400058072850040140e5030007034062211b980804e4260401042410360702c2403103079480961003680328499891861403900e140c0201c600c0a5050188040400d40c1da16070764040c20000440030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 408299631 1250 408298381 408298399
    0x11030a02190e0105030a1a0d060203040308010e04020901181e0b0109090e2d030403060b0a08030c070b0a0509030318010e0a031505060f120c100e01080612031c0605 72
    0x901d003907402e0030300031050714041101440055091002070b886540d00c0b000550f045440c0e80d12150014882c0e078003112040b42c200303501009010503d60300881490142c040c1000140c102e0416030000b0b01c030302105100d45840140d8004150f40300041d560440341c46030140441c1180e01c0c07943c5682042c041d045120845001031042103001a0710340050080074141c001ca1000b80840c0340301c0d01102d005c51101c2c650a180c42c080940ea8901030340000300003c100850050b500020382030607840c100325000b0701c0b681c0a041551710603c00c102d10200c011560300202c40100b9001944e600d54940b0550703080c01102030b440d40c54000410050b89d18030740c0d440c1031803642200742d80e03080c0503c03607070b00420480bc50207000241000f043ea0b603400d49600641d07071029400050003008284541d0f220f000041c0c00710300c0380800c141a83c001034210315150030102e8521002c01102c0c01c2c2007004030f5188000808122004000703520803584214036015004082c8111803849078841d001d00f20313107041004c1c0324010340304502c21305000302541 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 408300881 1250 408299631 408299677
    0x80105070c03051608120118050c0c0c010e0a080a0818060c28060c05070615210606090c020304080708030412020d02150d0f1401060f1211030a02 64
    0x2418440800e103034140c66450074100c880b1803031084070103600c20407a0025801c20400f11060400364400f0300a10210381d0f5001510740340c103804409c1c1d550107040080101d00c00d005201903070300003180013600f2040c2844c1c04415400a903000801c0821258008a901d000b8600140d0a005000b001092915116489a0801080d8105200c000d03c200c603091b94080c0c000c05a505000072032001e080c0b294480300d100001284003952907550445e41c00f041c0c00008502d0000d004010004c2c1801045456919200d9a8070058035050740d505004030626014042a000390b01410100701c5203a000c0405800050f504011001803190065070765881030190115a10805030700084009001086600345c0e1011003140109000a50034800030440800c0301701d901c030780388118542d69985030758090030781401c03c0100030030101700b00d4410104807141e540c2c0105511f21500f00520003140c02c842030101c11152413602c81401442101d072080209403041c0c21280400b0000144020284c0f00e4001d001d00084040d00c200c103107005 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 408302131 1250 408300881 408300887
    0x91e1428090501082b020a0206040b07150902130e011803030603050618030a2d020d0315140108191505040507020d09140604080618151b090a03150608010507 69
    0x201c0b400307000000c500100d042402031131617a040500c012482c011984200e80a0380000d0305030b00f003034001042a14000c43c44206011641c06041441a00d280b4200410361542d00400c1c05400c807541c500030b0641d1204500395807010258803ca5124005040a0350f01440c103140c010043e103420311050303c442c8603e6000c02c15280720400301120200d807890083d40340c5800450113982c2413050030301f50300f4072030014a0f0240e04640014600c070b5a01c441c0307a0181103840d80569010b011910703c42142291210003040c1802050310801d4000d00b07803013003420310410320380d9112040080880e6040b1807102003418200b1119904000726602410340d0300c00c44051102c0d55403071600320790310099a14000001211600108011001e840c1d180c6992030010f4a05441d10b074072010660300d07160040c0c0b006130302c140303c004004040c10f000340404120805024081d9405040132250190000136601d1000c114080004190440380d482c4c41a80c1c0c010b6622101c20395504d40000c040318000c299912440c220755007008009445984 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 408303381 1250 408302131 408302143
    0x12030905030d050d201b010507020c0315041113090b0a140403271e150207140418061506021c050c0102121006091e142809050108 57
    0x2c00d640d0300d0308180da0560b414028041500c8018100343d00034001e2048082003034001c0212101c844d41001c4c0781c0007a94a0b1600b140d9004102178110341099490220036640411001c10b80150452248e119440c2e90900d000f45281c52607e282d40b2000240c3e01c101125102d030005030b8400e0080307066429039900c66116070705903001280e85551360304e000340c001000a03002c1d840c0d0a03c0010700c02e1000d504400d50f0b02c0d114101c500c04d5003224070002c444146000c42c612018640c42e015000513000c80480b0485420003a41d83c2c0d80340c0c050b41008110700c1d001c022464466a000030103110903c813501419001505054000340310360b480c07031440002c6070070000c240c090000521005005030030600147e20800f846080798540c0050f440345c19595000c00040c41c528400700607107400780400c03000d140000d42c40c00750301400f01115980700811200300804c00a041c0c0d5844904e107800c454254000002100c400000075000f000c2d00346280c5443c80d40250034004940920442030240d8001070030401c5941d0f2508140c0d50394035 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 408304631 1250 408303381 408303403
    0x303160c08190b0c0309100e010e0c06040b0301060c0f021302040501031503031d0d0606080d020d020f070b090402070f060f0c0e030d050a020a0c060c06050a023a02041203090503 78
    0x402004c60701da000e40c2c030003c40d4000602d0095400061410384024281e0316004851021691a079050b80f011901c18080c1002a0400301c40440c84c007071030300312002d00c103000500c10b14040c41901a442c0080c0803803103c0e0109a198010314200c1c1e07e55900f0082c0c0000d4003e8007400e030019240844050008010131038080569406071a420380070300f90341081043c0b400da506010341d0090040c0c0c06e00c00c0092a1070192a015141c9400940b240f090318540c000c0c54040320004200c00c640c8900300a8002d50408269030303003501c0140c142c0c1541c5400140100b0040e100b4110006d240c0d1500c112400700703221084c0d0000b18000c0e0300d1401404140e80c403d1080320b50716140e0502a506802c941e0119212500540040c44154102c2c01030f0b900c9824607407180350309086036521281c080340289603500100010340c450540c1c40307560340108504020240003d0100400034074102c21020403100380b500e900085500e0380c0c460030540354105665550725080940052400400120080b0701000380126061501045100001c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 408305881 1250 408304631 408304643
    0x91a04020310260d050421030e091b0409060303141201031221050402030705030d12200703020615120303131b03061a06040315050a0603062f0406021203060303160c0819 74
    0x21040030410030031a4980a449240c0d861000034040c1d044bc1c901d0340151000300321880002420514609000d800300c4520544894064400c000c8a80c2543d42c0120b4039040da034204207014011000150f09032038852048800c5840c5076203229070380d00c3c20951904800d124520a074199185265100c2c2419900c00e407140c803420201e0b210100c482d9080000380d014649005a440d2091108943c400c0e1a8625620501c0c1c258010b800c5141005003415003000c01701c0c007a080c151501180100b02c906019100c0c0005058504614880c0c2e0500c401d201c016040c01c000a07035158003a1140341c0d60391610400600c1c0d40859002d204e07044050500c420700c1c2407030643c0c0403283c218402d421441020041c000c02850000c000c81026960b801e004004948140b090181640d00c0a00b03682d41c10003007030310b40d100000582640b03c152902c100700c1030006c03e6001c034000713043da00202c602540760b4440c600007034258040c80c0c100458000f08007c5010a000004000ca0200d400725400c5c0ca0051011409958100e6401d08002e440 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 408307131 1250 408305881 408305897
    0x3020f1c030f02070b01030503041a030606070f022808012306100309061103090606040b06090d0507180603031d060703050906070c091a04020310260d05042103 70
    0x540c074000c0d00100c25941d00014014a41200c07a40c401c0c00900c803c0c0c105680c281e00c0071909000221a5007041840d241d0352000f81411860310b400002c22510945500a081c91801c0154500b1502e52005c049140640c1501640142400400c7d0300d804d12041c4c132410045600380304440e89036a00100c00c600c030009074002c2030b5070a43e4405051041490b40301c0140c0341059501c0445802050003882108584c17129004e0700365503410f06401d050725240c2d01501d02e51083e0714000c0005020f0780d50104803990400c090b00c4c07090081010341881401d0407002c0d40b0804810402d03c0c0c500c0c0300c0600c298403030303802d89100741c5030741120305941502c158134401040d000d01c0d0445802c00c42140420701a00180c07420b600020300080ca000601c0e5607800140704a5880081500e8945651b140b0315010b1f40c444c07020b0741c80240c2d000c504600d0b0110441182140c6403007020700c440884c25208450b1000700340b414104140800446800421030000100990701500c900c1c24072540c003290007010900e0010507445480d82507a12800 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 408308381 1250 408307131 408307183
    0xf0d17070e03070317040302130c0c021c0b09101d0a08030c09040207050f0d032d0e120306010206010501050f19110a0b0a06090207050d11010b1c03020f 67
    0x1401c0c0380103018035506118444001001400094030320081120b00c1c4030881d1120b00d544107201411040c0704000c007182d803c01e04c080d405998009100080c0607011102c1a440d61105144400c0d0f044191401800c8085004104000013600148804035040526000c0154004400040b1514a2201400b4140703070061102040804c042c00040c540220740402e501d407a10507010000740880c0e0041a0450329904006d080300700940c1d091183e100c68184a0a0502114505101da00c2d9030307464040b00743c80b1914449800440804e8598009034540f07801104403901d80c041c2100d410401c0d0002c80e0b0450040c03144800100380ca502c198150340c030340040c022200341000d114400000a80400280d1201044130001c1040e940c5c15041220140e45405101c0d17803840780c00d10050315802d6900d2600a00350042c01004860006840000c03620000401480d0183c100c0a008000d14090980d540000da0f003c9000222030b01951401a00b16a041e4840e0702103071600b5188005503a140e1240e00380101010643c140703120 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 408309631 1250 408308381 408308387
    0xb041e050402031b073f030b0d17040504050712052203230406110708070524090604030b061336020a08070e1003021003020702060702120f0d1707 64
    0x10451a10070b0401c1001206542c1c1050100b04481072911b2840c0014901600d181d42c000111480c1c2c0d011524003880b010641e035003c1804c140e49102d0050900307121004546000724031f0000c1d0f80181c08005c1090143e42040e18005100341d4408e003800100c035186c11302092250040c40e8890a80e01404210000884640d4406036503c0340c9000b103000c140c610b1f00d0300509520342c01500400140009071105100c0030450480d06150000075005420107a1140c00c007840566a0310300851a014840c00d00c10603001403410f620341e0f9501440b08001c2d0000c1000c600801007042101c1d4051040c4130680e0b0018940001c03484000c1034808488120000c2001c1076108101044c141031441c0600250407040051140c55902040d604ca00550001c241600400414011640d6134460250040d1001d0300c803004550564000607420103111010b0402c0c140c0c00140e100c11521000155200d03a6001040d00c00052075443d0456110b0701d0301d0442680310f00681034610101c43c015511040c26510300301c001c4580c0c0d0b07150401a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 408310881 1250 408309631 408309637
    0x11802090f0d06091406092109060f13030f0b09010b0f04020a0201090510051501080103051b0d0f03020a020a17060a0903020a080d230c160c0b041e050402031b 70
    0x103581c200d44402104003c14102a44100d64070103140c010540b81c941041c7e02402c1c6001c40b08032410f00d01d2000480034020340c007202580d40c094410ac0e01385564044c0261441c1551142c0c1c8078803c0142c1a000c0000288816094010310140c09084c46c8029552500f2a0900300d410f45c41006903c40d2a01c0901440c906155000e008919080c0c0000a4060600d40361131b85410a54070030318030410f407900100602103801928000d10803c0c2030900b01800c1d41944e88280e214241d0300040c40744109658442a00c940e292541800f00c0c0343c100170020001c19182c00d00946410701c14005034020100c180300001c01c00742081d035020924140c038018002544880d1401300103030070408410340c1140704c0c00c400200450ba41d0340007030100c2005010006401240400400c11a0509407030000c200d0020f07104101e0801e014108441a441e00a9004543c2c01240c2c074001014001d02d4000350b40301400407070082080c42028401c001c400301c01d141d1402880d907a40381000240d00c003c0350303a40000c0701c2c041e2480d00241181ca001d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 408312131 1250 408310881 408310883
    0x313021512010503010c0201020a050d2c010e06090c030c010c050a0605010b0310060315030b27030c1c0f0c170a0f03050609040c140a09050c03011802090f0d 69
    0x5001495408030100c192503030003081c1c0c422501c480007401000a807600b4401c040841c10940001d40c01d028030040301500e2030203028071001015450311252480b103694a8841c3c3e04151014254108003101905500c0c02403001401740c100074130854002c29010100040d0400d04900014020711351003100340c0c01111524544141201d91f48241740d56000066060301505020304400a419600d91900355000c803011801a40302c2020f0500d070501e24080c48541401074005d4940086c0300c03100b2525a4500b04400c000582103a210004030052004000346010005040c15444c07241182c81d0741055080340e05200c0f0284e0904004200341c1190301202900038100041c4807401046040302c0c0d0300031101c41042c13070b5000d404030300002001c2c98110744030250075100c0d00d90032030001d9944003541d2800fa520b001c1009414022615900c084042da0350440e036981061901400b007000c01404181881b009080494101307018003202491890b22030f540000c158800e41d04030751070080464221042c040c2c240305034051a050 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 408313381 1250 408312131 408312139
    0x5060a0f05040e011706070c03080114120a0819050c031206120304090902100516060b04090f0b180303070f030b120316021908120a090806040804030b07030e03031302 73
    0x81d00303c4120524600804141214041044202e0745083c20024014003600900112904a80100780d001044505484100e070fa400c201e04411400907101107034500b02d0026a204446290041001200c06030050403180755a690010008080c1500c4034010004045078a62086c400c0c0500045002001034001502510b42c0803840c0e00c4901c1581190300a401900215448038503060071400c286128030303560b143d18130f00035042440f421940320300030801107400f802541e01c604071301e01165683c1e03001020003540000340904a8417285041c0b2441d506c00c0300d607055011a0628400d55090b8003204a038882d11050741c0c0d403500c8031442d030002d80003800346005071a04076482070307030800c5020700410040000e08030003101113a0300c0406204004192450603403408440c201903108216a801c00240031054407280c010890300c941454800701d81000741c940c01a0b4031481070710140028447c050000303100f5030b40501a48010342c0e9a048044d0f061380d20b0341e61010385540c010000152040700e104407407240103100074 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 408314631 1250 408313381 408313387
    0x60f01030b0d05030a300f0216050c03060f040f0b09030403020904110405150d020112090c0e0711010c0e010f02120a09080705150306011b0b01090903080f0105060a0f05 74
    0x107000c5144064070000844082d8000162a59455000b5006c4003142c11b802080c1c0c3c0d8944440c13444918005561145c1011070394550083c038400c511981c0550354020400e0450603602030044c2016a0791320045207c0c607020b4004d81010a80ca05100300755a0321480d00500035a8142c1190b507035800107640001c001c114640000c2c0000700040e6074054809000724003810841922004543c01c00c42180e00140c00c4a0011000041002c540e80310442b02c0c0a1440c0c0900b0028a0401c001402c8005461007480c003d1041410100108500c01d43c1c042142c0503440e01c0ea0380346c0c0c0716104d82600c203080711001c0d0301d000b02003140d40841000943c42180880c0c0c0e44106441070b0703031603155a50310002154000c42a0000401d5150700140705071641005480c006003410bc0300c007582c0780d4410b01000ca081c0b0015000c02d04000300452a0110b000c1c0c41400340203a984c1c4000c9817441581c5d1750914000902003900206c1c00a0829008140d0b5004810b1440d4140c41004049900d002c10045c0306540381c000714402c55051040078 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 408315881 1250 408314631 408314651
    0x2030423190c0503010b010c020a09020c010f020d050403020714130c0216060806030f06010f0b07081c090605060f0108190603021915021204050d060902061c0501080304030308060f0103 81
    0x40807aa0312000d01c14800c5103812030a0008040c2951408024181080031803c6501c4c05070741e59944510884806020050b51603410004950161424110145403140000380c140018083e990003103210314001d81c240c5a0365520342442c0400c110b2844c00c1c1c160311854020345c504214400d68030a0005c0e0300240110b680c0e03020312009071110105d181e480ba601040320542041800e040500c51140b60f00b4018026148035814030103c0700b09401d0718001d10700c42603004908901006255001c0b1450ba00001210f0020f100b41990b6032030107048404011140b00c0d0801010890f6800c010044000350701058441d000704d03580d03501e18244032442c0c0030303565109603489400010160311641c08825007044018a98200035003018100c10b5100e21040800d0f085500503203100400c020308000ba6004d9400898920762010305900300780b4040c003a0a800a5400400005c0c01d005030300d001c1c495401555a081c0080c030485c0c2e038a8090a849004a100280c049510400001d100345020f00c9407221034403050400241c00b043c5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 408317131 1250 408315881 408315913
    0x60c070b0a05090d0c03060f1812020c030318031b06120a0b0d0309090c081b0a020709050703090302010b1f030504020301110f0d0b04060308070602070c1502030d05060402030423 78
    0x24260144e4080d20401d0f010f200307024207805102c070500030123a002c0c090304101608411407100f40000c09418118054441c800107031090080000d0048010201c0391641c030351041c8403c105080102940c07003480380800460210070405141c60032600014542400d04003000d040910400e0b0091110613001c1c0c0e608481a0a070355501603602040b4000d90319007120b1420801e40a08595040194105208000d8100f00404100010340d19441c0b0308040d00a480d1130039441e0907031070a107031034200ba0b100500b04800c01203807640c141e000d2708002c0d0082d0700a00c109501e607000e2001c0000100101e4254940c00c42c03100d00a64081d03001316400034070160001804500b00c03081052190400d0b00c462400d8074001407840134209040c064211a26011142049154a10355a000c458410076800500241c1c003c541d01040c4403203640540010f00c1450080c1245640e00e260080d1030354480c5a8003540d213850080410300303e040074400c0c3c84c8034950068401100c6400880c050442c0282d45c41003100c50f101e60108042d403100c03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 408318381 1250 408317131 408317149
    0xe07110709090b2a1c0f1a010309030e040c020307050601080d090e0c0d090501090512030a0c090503070303050714010c120506040e060403030b010e0d150506060c070b0a0509 76
    0x851400022032010903d40841c1d004800391140d069a00401c20354611380e401c24003040750700a200302d80c02d641c0b03d0900c0d000b00c41009820944a8049181135110000790429800281b1100342c048049044410b9880c010740445804003800713800134640507100c50b0706040951000250030010b0048905103603141c0d495910b400001d030443c00d120303000380000d4101c0c50f07000104400076100c0000708050b90700c1c1018007820540200c0c501107034116141c034402c8085c0f20307084d441122100d0f0000191151001e0001141810340c0c81502c0140a03645449200c05280c0c0c030075001c220503220010080d000749480c5072030480e282d41000e0010382d1511902c00302502114824800c078500141d0507150b044050440b041008100d520050100303004d24203222200f403040401044590f8481c0d81401c0c001100320740d00b40120b80c540d1803040318a07000282089544180b120300e058622000c4d2003080188540e5443c0d509100060150164040342940101e90601c0455600005801c8403c05860500e06040015000800c2c0007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 408319631 1250 408318381 408318389
    0x5180703080c01050702030f390a03120c09140613080106030201020d030b0904171c0b19080601030b1902180415180203060a030506041a0108070b040e071107 69
    0x881d0004550b90b010900380281c990040040c006141404489003544c001441900c004600380030320070062038000001031081c01d0309481c00c010b81d1400a5032600d0400d50307901d5900e5064000c10340c207080e20640366049005a0704807090550b1509031041c58010200a0400e0f01c104680d030102d01840310309441700e007100c2c00c00014180400003040283c80d6000180c2440c01d0405c2d007904150400007107140c544c880a11140d0451b41c4411110883d0f00001c001d84424040c1c5908072a4a210110b10350f1850030641c0c1020000e400200c64000c0c101d114801c558a107401c491003800c0d071542003500108086008401d00990002e140c1d0650a42581c0c0400e011080b40c3c0004030006528406400e008c000c0d05041c4210545031055254101c0e505051000c1c040340c106101102c8d00c5410f0b00080020026114103402c07400941c1d005040b034042d030800346000c000c03d03024236071b1101c1720380e80038000011407500000d940e400f25070800560358909400c1c03612507004244010700171002c0c8481400c030700100c4401000003400170 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 408320881 1250 408319631 408319643
    0xd030e12060405071403030f09011d04060b0403030e0907021207081216030f0509070b0901110307140d03450c06030e07050a0905072106170105040308060405180703 72
    0x1904100c040345c3c008420301c150034000e03801407140807806101801200e41850302424481541101d00358010251182d1002241c0c119040c042c0001c2c10144d0380020704180c038800d40356000d11451348414803542c03110403640f5400687c408181e0381c09185c2c040000b021032601404405203400311008850020074000e403032010201b815030205000d900d078140f0840a000135080f805005504140d045240e0f500024012242400c2000a00301c5690b8043c480385050a203812060307a481e009142071451010420082484050140e401d038080c03010b11038400e94649861407502c04100300b0700ad81a0206801d440030700400f140c8000b583d2420610425021080c0b0396206081501d100f5050400090541c1d942030b01e0000b9607172043c801444941e0b40c01d080b0341e0030b032240c031100007825030340d07007001158501c0c20342000c2541c044a2082c09000c030580740e0000403c1d521048500e01480b60305001c014200c2c1d808803800341c00a0071030b80100d40079150039002181c1207000c2c1307100c81c003030300701c4001129080604c2070f0300071144 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 408322131 1250 408320881 408320893
    0x5060c040515030f0708190f1a0306010e010b030417072f0f060d0b06040f0510080103030c060f1e050103060b100f050d0207080a23090d030e12060405 66
    0x240b80740400081c03194910758503615041d4280031440d04102134000c0d00309010f0104e56400250b02c0b03030115054001c03211818105002c0105820320100062151103840d0081c1d100145a485083c107000914074100c0c0c20b40c1503108440d070f1074200f1504554002070821104200c00389170801821802c0c6016014460081d201e800092841000714810319803690701c18a02e004140c4a0001d0543e0350645013501201c0544680e652000d903071030040c0080400d82100c941c00300c0045070100300562140c5044003900c80070340d4a00c020198420302994030f05424880280020a41d0b00000000b5170242c0001c01c031911080b90210f00756800d05803800c0c000c0303c07404160700e48a81c0e60f0010001d02c241401100300004051340c012040d0804420300810740380c0d0841c800018064001241406d03001d1381c1d4103c6400d0350b003004400b5200e000003030740280b8981308079000c6420144c8ca04001c0f65070003540c008039101c610004001045c44078440d80c09699643c62680007607804540e0342503442c9400c20521504e4440e078495006085 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 408323381 1250 408322131 408322139
    0xf0b0405100501050a0309081e0c01060602060f060d030c021c0b0c0c06070507260304030305100807180204090f050603060106080402010903060e10110903070501031401050108100305060c04 83
    0x411503200a00141c40c400c00d6140402207641c204040341d41483d0b442c50042501e10f02c60a10400c203104807200030000064440110901032045406422812802c400a0200325034448007242d580506440c800000038180000c41d4540c503111821140c0680702e400c020310140c1e02c9400054900c1520b09990082c0502c0520381d800b0840700041d1154070501000e2070f641041c03d0f41c0b001580e030b0303900100013000b8010b002551209000305010b034540d6a00e000010300c8588202c10a1030312017900203860860200f4144000300d1031210355052207000307588501009140e842d103001c180030a54203100d1036403400164204030200304d1501e81d0058030b01c0003400401c04540c904003103003418a0040164000c0b0200030314182440300503a030000c0d80700222a0440da0110300b0a004c10400d6007030034084200120f045142c038000c0d104042601c2c000d042c0c240c0d000ca05603810740743c0e10300c01075003a1014040c01c640350780e21442c0180560341c001c01d03030305410120002960b191280c0b6590f42c54506181514581e0300c3c2d07000031500304 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 408324631 1250 408323381 408323389
    0x3051b030f070c15051f05010314190e030d0b0a050907140307051918050d0c03170c1b03010b01050721050d1805060c0c070e190f0b 58
    0x454446014a4014918030307005158440c451000303031007071041100d1490800306100c003210200301180c15504003003000c1d040a0318800d000d4000003c602c400d030040c2d8030000a481d8000d100f14040403495100302103051380d541850818540c2c017810789058141d6500c0500303da0107010406401240300346038001a40807542e604004000e022584940d01c214050810414070a0784251101941000c01218a441e500c600324140d81da0b01603482c01c1d50344844030303e00d06041240d010380402e2900c11408481880c5a0715441441000c1100c058040c202c4414801d0800005d240803400c2054204c00398015428480d03003031801e60903c1e900f500301e5020055403030b4091005140a2003031b0000d00c0c5090901c54688045a0303104a1000001260280d1002c1008400500140104c0854030500282c48080150036641d401200501c0c90032341065929104010000c1c55090300101100d0f060000c030030040c0540e61400c1140d5000d01001083c402c80d9105400c2130514060260107941417141c00743c1c002045c0f81301040d040c8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 408325881 1250 408324631 408324661
    0x7030c0306060b09060712020102070209151801140f190608040c08060103021c020103091b09060e0708011203090e1005240901030b060c030c1507020109021c020117070305 75
    0x5a165034104044d0607151303159801c5540300317540088891030521441006900a01401c0000f80d048400001004000c170b80410100303c00349803c84114034203903032800705040b50301d0742401242d2000c504080700c03011620705410b15840e040c01c014401c1460040052031001060300645c0210003041c1c40d0710601040084d4031032010090f01005004004940c50b5400141c0e40d105009c0070340d20464110f10090095900c030750001c0c10455003280316900d01c4042c0980d1070080506c544502c3c1c0c451032070320501094500c40381c20010f0007014150f440c81d00990034000c110301d030503441880803070038007200d54400100d0a01101300c940c8207548418480d69014588014060414514001400034400300707101d0030219101e10301505e610810038603001807402c02c43d40c045900703403158500c261040e10020480171100700703000a109003003554043c00a081601c0c1c0311801d80c2600c0411000070f500c1440d40e4120308800888001240d61540145050144030700d801641c0040c02c3c00546800380000e440390304005008802c4610 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 408327131 1250 408325881 408325889
    0x10309051c050307080106080f042010110709060e0a0c2003040e0112050d0f05090a120515011230020a02090c040806010506031f080307110a03030c03030e030c07030c030606 76
    0x7488d094a0140041d5407400c2000308014180441d44940d40c44241c1c841c511a201c60b41e01401c0b54100000101029000c0042c0d065690101d00c01c042d00461110491b020354003c070303080c81e00306c4089a1507010300d020150040c2103100e03081201d01e080c4019080d001c080601618201c42d40955543c03414440040c04200d41600058614142c0820b0000014000038112013624480d240c00520740801e00000c039420311500030300981c043c1c40c1d1200414032510042da01c0300a0780c811000c40720118080300080000074001d2103150500b1481c8480700300441e404e00f06406003039158140380c0310328904030010341d102e004078826210010f07400315455008504000781c0b26908429541103840c1810301e0100800d60b5140140a414003920000c40400c41d11801046c08004694007040c0702c01c7c046840d070108590300d0308942410b13220f00c001e40c44542003d08005444809a80c0c1555079420000e110b610141d000d8150500c038914240720820a140f0380305810311105000d14880c204640b881403640c2080400d66282d904 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 408328381 1250 408327131 408327137
    0x9040b0109060c060b1f08010f090b0d0303050705040e0c0331021c060e0d0305010501051c150302031e010b30030d0204090f0e0105090309010309051c050307080106 72
    0x1000d020722500441083d10b21644200c000c42c0c20041400407452a210605001c0000791034804c1850086401000b4503050b02c0d401800c1d034070741e140c1d510005011345041c2201c0507001403100350700b00007080c4a60032480d840381c1c2606001d445e2540d140310302501d11004860014188a0100c02d1000300e1401c08a150b40c904042c8050800004504c2c481c403c1d80101031000a12030704400302a445069a003d17400c6106c503030400001c01001c0c503e0180a43c403000003c5041d800286040001b0600b9030003035081d604100718842e06100c03203c0301710070048007d01b4001080048921322a10000c0141e400b0001c0d17142e03030803000c00451201174102c1c04450a498500b0791081c451548030400e000d1013600032170301c03980302c9907044c0700f41c044000301c90f41e8182184100410360310424000034002c070310003190360402c10f40445092801c0010360f0141607090300301c400035036895a40e07410401403c0d40d20361090700548034480c0100c0c107075a00341c01120034891454426100c0d102c04a00003000f00b03d151078100c0a024014101c81c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 408329631 1250 408328381 408328397
    0x1915030204060e0d0b1f091d060f07020a03050d0f0c05090102010c0305090d05071502030403031b052d040504060f260d080a0f090507150f02030f0a02030f0d0209040b01 74
    0x5501c0e64642a40141450b85201203002c10b0f201c0c0b01000c06c100c0e80104651784040000204e01c040d07202a02c0340190620907248148004503030200c40340403910b8407500710766000d086c0144856a0485241c0d01c0b810325511210b841d00741c0c4001001540c41001f4443c1400c1d00e0345552600103000290079250170500000504d8507000c2002804040815000b182010030300e40556245290b00d0b2071050003042000480b03c888c03000c0300b080308141d01076014588170082401d02c00410311503e6000c840740d20903440b07030728207001e0314481030f411080c0903503101391003808004d50741402c103a11040841c044406550262645502d104000c104c40144061500443d031181200f01081d180042c3c022540c400d61441540308014036880064071442c0503600061b5a02002c9500748094940c07420015a2203040c1e004d81c0c4410050800c1b984c60240c01160020651203240d00550300f0310110980e12000e9410000c0c0c03100543c0003c1008180e1030540740300030407008114900060b118184003051004503012010950305100702e070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 408330881 1250 408329631 408329633
    0xa0608070303020a02040e071206020405010207170d03110903011113050a0b04060c0f02181602030a021209180106050414060403150504060f05070309021f0c021915030204060e0d 78
    0xc20382428458055402040031f0b5492a0020300c0c2440a5202c1085411054600c1c070400c07565800034030807960240d003221038070340d1660100288082544441c1c015540001d1003d0f226a003c1d030040c00038161507400c070900b80b15112010900b540c818461560208e01700080310b105480301c40b20789030702620080d10380601d11818240014528407aa001d50000d20801e140500104080d240015248070360189c42040c0402c002e410032040d0350015603560502c80410381400d41d0051001041d1400c10044e0b81c010903440c41c045800807103e074444031f90141c2000007030783e07500011000880068000d00d09035660507a15803804001c58a002800300180740f02d48030070842040841c0003208424400f03100e01c00006040e844e0b503d0094003c0043c441201507550801c810000485e415900104204d0700075100400b0b0b014041031034200e19000d4007002c001040f11201c000c1d015060a200c18600d4500900b5240c00306a110380f21000c0010b0107120308400260009010701215a20582d403451281e802c0e600d42080b4426 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 408332131 1250 408330881 408330883
    0xc0a180e0403120612082109060a02070f02120d1146030305011a040e180316050307021512070f030b060d060e090d0203030f041106120a060807030302 66
    0x400303030000c2c0070400181e1681d41c0c01c1e0880d6004500505016944207036180081c51b1090300c03600150264615541c01c226a11800d109840d0703110b2147c41143c0190585035a0001d8180094003d14811380e1418034045078500142c03a10341e096160980c001d030042404c02d1261400500b4400d0041c2028465008030401015000c1541c4880c01078100d82140e40180c031882e42d04820001189030648004c0d50f2506122034181074143d4025410b07141104401c50b4040e442d200d170480c03a44180d1044ea0000320121000411004145c81d0f80e982100e1500306603858540360700709504d0901600039099a41d07400c0020341604515110b0703d0f0001612031504000e08114007581d88404403100100b04030b040c01700b080f0b01d44c0300702031199000515110008251903111345210340c101b8000d2202d030080f811514400e002103490710b24001840484000b89900840c80c595420510100f4140050801c40345454010300000d403e40d40c41d00500380c502803c03a01d81c0220b140104080007991010303030200c0061f8012010030b0000c264 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 408333381 1250 408332131 408332159
    0x10906142a18220606091706060906040603021825020d141317120304020904200406060f08100f27020406110c010905060412030e090c0a18 61
    0x441d10310661042c0c40310350007080e10103d1520408550101c0258611036004540c1d0024060b40c00c1c81c1d6501c43d10030745940c2d60841c02c440080c54501c440e030012000400b01d10f081d011142e17208402500220361190b581d0b001c02c0e2130351090386641e030240300d0300c00400598149104413084402c00755083c8182c43d00301c03408007071b4442c144014942c0c10001d40410944e80c2418600031500a42c0d00710000e010700d55030741d88401d0200e00744440f1080c5180501d200410200d0404000e59000f250003e219207102d071201e6a440600303400f400e103034441402e466901c54074039681d28410f1000400035030f01c41c0d80c41c10415501c000c00c9268000c10000b601014480180601d10b0040c6c0d0702015a8500c840d061101c101c4a00c03190b44001d031040410f43d000e0b000260102c4c070694807138907214188608170100c13010088440015078a196440c011241c0200051004010003141d2044410f102402070501220720202c0e07002048111030304981408c41c4070310000f040700c50141c1c003022042d002d04822007801e9849040030707034001200c0c1e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 408334631 1250 408333381 408333397
    0x90603060f0d0c060c0506010803130b13050409080909060a0806011406091e0102060c0306061606020d06030602041d1509091903021f09021011010906142a 68
    0x40d036050034032864451000c41202560410fa141d409141e94a8004000303122101d01214203000e070300b00001e4000c00010903941121440030365010000d040030290206030708071800751841080024000102902c41d885803640b000e00602001b556010750740705100b40304e00d0261009000f201810301c1008140408941c4a042d40c44841e444240349145100141c001e0048052042c2c0c4040d1074081c40761942111405540800001e03000d80792070759640c2d0341030100c4d40011101541c1101080002c00b5220604d0301c80002c0c032903c41c090050900340c1c5803606004503440c0c0e42045512581c001020b00c069024070030000a604a5103180341503d10340810b04003902c00440c601c0c540074403401d0b000720b25a968144a0b0351061801c00310002c50207030460500954410740b10051007104010000d00d011040203034011008100d03000b07044018505501c0d0341c211400c00c40721003040501c0d50fa904404000468500941c06512219040c0400c6030400c0d1184000c242d00011108801c0300402c012585010040025900c0034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 408335881 1250 408334631 408334639
    0x503070f052805040914090c030703031d0103060306140709050d020105040b09150a02010c03061202010c0f080f0c100b010c021804030e09040303090b070216030b09070b0c10050c09060306 82
    0xb0448800280d410b40500d8103c040880d060800c58202c0d9154060028400c0c00418200d0300d4043c40038050644400d0980000340000303d000d2500201680c00c0c49441d201001d0602d40021480d65a44a4000320741a003540f55002d005203400384441550300691000c007908046a1000816041f0ba0001e007081c812485002c0740d407640422030755815075441c44004c100000030f84440d942e840d0101c0000340280342d55a641c80100c0c0c9481c10105094242d0007480e81d0a41e41078480c80070400040c0c46a405078000c000084071205410454140d40c1c41c07660b8040c3c100d8800410003425001e44602c1d0ba0010b854000305114100402d21461030096507030380c04441c10081184d8071000944d141e9040c21070b404061203440c00d42121803041807108155056229030340303280c011350a20b841078580d140c1c00c81e00c0340010580840750200031001400812103007400541c0191b00d031001c4807400355642e0060b041e00c0d041124000c80b190020910300050b4032090241541c03003661403110602d000000c0c030000d180340c000a8502406 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 408337131 1250 408335881 408335947
    0xa0e0d050c211f0b0a0f03200109030201030b0406080f151b1902070305061806070914010e0301090b010e011a0f1b3d05091005060a150503070f05 64
    0x41e004459208143c921030160440c0189601da203541c1ba052412440700700c3e80c1021010342814080f0300001d0000c0440c00581d40c14100300d00d5a001103014001318000d4030ba1095454100184515040013014941c10090000e09400410000b561541c004010044001d4403280300310162410300500c11100311004501c00d003020200c030708104a107045119003000702a071040909101070315401c1a13203100c54800c1e802c01c030340503940c403060112a5201c00b803203200100031082e40324245641c094001c140c68140044c000040542e003030b485a040e544000c2e0300c45900c054002005010240d400019041c0e00c410041489103084000106541c0f6445001000200d04090b0541010740a00500199008140803581184500c6080100d0141c1d00c00729452807a00c40070900c6da500300c0000324046d581c85100c0d018090f02204d04408060b40103410000d0150b644a16032610124052a000851544d840c03000c0ea9210744900e0320940281803149100780c2c02c0103006d002e1041c40e0303003062207065002c2d01c0840c1a154ac40 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 408338381 1250 408337131 408337183
    0x30f0c130501121205040b0c1f02070c06050c030c1e060106021227040e072c01090906020705030309030a021912030c0504050a0801050a180f03050a0e0d050c21 70
    0xa00345c011b80d00300200030800019035540c03101c0300141044402641c1c0c144640703115514141e200c00c030320503040000c0c0710403088102000300c02d000f0300c060140d85441c81e05032460240b0254030142001c0e5002894402e807910703003034003102a807002c10541e07000d04142c0c00102814800003059000c0b9000d2a4001c080c1a500461401075844046a0301c0780c81620280040c400316201c0c450443d152025401140f0080d004005891000008407090134040c00e40014400b40607401c0070500009080c610300c00f5201c4d0741d0208403d0000403403c100441c8511280800380d610f4800c020070003030402c80314240001c1a0b40300c50b481c07580401e004c44107001c161b41c2d26007400a807244895005590600407079005550045140d040042e410b8019040301e440361540100411101c104211214402d04014401404010080e581800003038020402040c0080c42d504040042149a02c00580f90b040010812610b9411101892941e8109001c000302c919400c144d000000d008002802ca55603001c0906000d4030912000a0762 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 408339631 1250 408338381 408338387
    0x170c03131502040909080306120d0906031508060c030a0b09010e2a031e09011b0c0602040504051e150f24030a0203160c050d0e0f030f0c1305011212 65
    0x3e00916001c803040c0030600d100c2c02c21103002e8008484550154036018042d9420004c0803848030041c028580b0741034007290030680704a008003089a41d9241c15104404013040301c3c001045094032942402d5001d9030b9034940842c4500994151004d194010441d120042c4010140c2641182d4410300c0c814202115684c0200900214031080b111000351000000a0004540c410311070340d90603650720303080d400c210f0b11040c03940b81c00c807140380703059400c2050100b0714902e20302d100e614030080940c000d8101504140e103800010302140d40c00c2c0c43c0c0404508504180c4800c0b00c81850352554004840d04a0845034003030a00451040170303c00c0c148500c1544540d080e0702e488101c00d0041c07094000a000c0168485c81c0c00410040290300a9515445010300c0c03404c5201e0442c41000132803550703030381b00020f00344840f824030041e02c0c8844450340c110342c807450580303401030651010070986685804000050030035241c407900784540b2803a4180d01104c100d090400500901061480e41c1c068581d2100c0c04a150003000700f011 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 408340881 1250 408339631 408339637
    0x90103021c060e070f0c1101032f070c060c02090a050c0418060303090e0705070b10080a0c09050606091c0201031b09080607030225021201020703170c03131502 70
    0xa404020b16000020450740e1081d1000c80c071451540c0c40340c460f2054241c005944030070340b0050046c2040182440700c0079070751080d00f1181c1c4100812108400c41c5040d0b103500700000c0d034102043c0b05004000b0640a05120305c0180200040002d801d14079810111038005ca10b0141c0014040031748035840380d0200303500041c11000c0314000c0405582415160107190900009441c4911060300040d0395000003040c4800082c0c1b00780c0c041c00031500c03010b28020040da00c02c4610000204100001441050300003800301041c08400c24984c401d00245030120b007080030300807c50328080d00990081c901440040d00d03540311111070848005541096021140c900d1004a0150030019501c1300b05004896001c141c05070001cac00e60058aa0b000c0940c1c5091380d80840803412805950603190140b044a040141c0d403529503004903801034006800c0000e0403014015060070790344030b500c08500143e0b0030110041100310071520503400c11a0341c00e416207982400400203c07681c81d440b030050012920b100c0d000b091195070b43c0c12 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 408342131 1250 408340881 408340927
    0xc050f01060b1809010605071e020603161706010c0f05010204030206040b04140d0f030e03120f130f0608070f0c15050601030b0a230102120c03071b030809010302 71
    0x20700829480d40c0911500d03030000760403404007504240a180341494010044c83c16110303d99510350421200707480b00207015407810089040403821181150150319544001d610604c0ca072070340e4580340746018400410b10385145140c1241c0c02d120401b84100da070303442510030407990b42100050042c541d40f420032500900c034961009502080010700000e812600d40082c00032144c0b4416001140100982440091f00c210200240340c1d56202041e10b00090051900010460000c0c00f180c0d8a1550790050380d102d6030216a04100044001c200c49211500102100d405041500da03841c04040ca00b103806065040c010b04a101030006900c1003903038051041c503101130304035006805101e03029501c1c3c0303844000b41410340310180040d00708122044542000100b4204455040280e00b030040020000300c0c500c6524001050304500070503000c9018000710002820207a5102800307566070340304038544569a40c1002d51000b203016a03054080000c981840e0503151041401e003405030307071882d0700030108a04000c5000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 408343381 1250 408342131 408342133
    0xb10180b0a0309150b01052a0a030504080c06070804210c1409070503060312030a090b1e06010f05030126010c02011d01090804120201020a050607050909071e0c050f 72
    0xa40207120310b9164208059031030081660030b8410711001001803e48141d00021808103004000440b0042800407050000d280d00c1c0295001952501d0726007414808690410380004601144c18061f034942844011103600040b50410b20b01100c599411201d40240d10800c600407002e40915000c0410010320314100c41e60129525400a446d17005000000c1000c0c0401c42c09520742d1000552268060b8044a00440d801402001404405550b018403035000810a046440d10382c8a500b00044110384140c0c01844055140e5040d50401040c8010308103004103e50304014030b4040c078240e45500002201e05550f07808032442004070820241c01c042d03100c0140c06015545ca0008541440c0d54194001300d02001401c03c0c00300804200c3c0384103801c1c0d036004007010742080301c00c000c01c01034020540d05c800c02d0b80b441801695a800c10a498845c14600c0880d450b10220b440091609a50b14103403035044d51200f046d042480c04010300f0341c000d81c030010510101c00f0504c40d00301603000c01d100c1c040040d245480e0f1580 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 408344631 1250 408343381 408343387
    0x60503031b0d0f0c02090c0409060e041205120414070b0705010b0a0906082805061303020c041518060b0a090513050103030c02061c0218010f030b10180b 67
    0x80740044800d040c200380c1e000140a980d0303600509522a800341281d15010355521070105460381c080000409018101000ca210100300000e10b40c442401203000800c1d10b1a480101c07403802c2d0404044040d4510b040c4410070101700701c29070700d100d15814403d800540144106023007540f118102c0d0314200c80c40d044050254000304c0d060707041143c15046a000e40805680410a0a179102c4014040d214907016a10741030b0404100c03e5000b0b40b0603000a410b17129600e200c8108030649031151814031000780d0f010034407101d14401400900d07404000c03041c0000d5040d142002001d000130845a03074100345000d0180020310400c1414905007154120001500c0c16041c80395881c0702e01d59010300102d03130900c1001d00a07c480789240786024118461a4101c94054554403e0003000e41d007041140d90240c035040c144400108505400d10034130f44050031001c054956804a080c14640024000031400182c0c0010035082508024141e101d101da00f04c1018094240044c3d101540c094200c854103284d002009244008 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 408345881 1250 408344631 408344647
    0x9030b1902030a0506040b0a03051f110403030e010206100b03011701020c0f060709080109050c090c070b0106051b0d090512031e04030b0906151012090309050418030e040c0306050303 80
    0x741d001324040d6100320303020000b4680000500170403141d1840050220342004031078000340b01c5045d00070289003040c00c50003e0305450803121032005030019001940001c406042002c100e50b010414542c00112240074049202d06d050080b4000380f0050090007508101103901511440c025010344480c03c511100b60749480d1a0249a00d81d28403040315040c0000d5191280054011418400e03001400e801c10f018042c1c1d00041028846510000b03407003201c3d030784000c120744400304080c120400c1c06480c0c0343e0b903803030341d2620700001709400c07034254280c4035902d1341001e020307900344580002d01032040f01c2d0103641080b840c125000005003180685a4007800b5403101d144440320502a49000300141c1b4410751061202c3d440e40d03206103a603044120342c0302001d40301a030303102001351402031406420f0010500e0800303d031032a0350b1002c40c10303a80401002c070003166000505010302e143c10700503000c000b1507010170121914000d0710b008207440900400140130315540e11907000d40134800e400c844050200902125620902 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 408347131 1250 408345881 408345901
    0x30702061312051609020c0715090b04090c260f1506040b0306040c030608061f03140f0f12090405060303070b0c07140c210f01230108030a09030b190203 67
    0x14101340e900500000c400100d01203903e4405c0d15101261640105a024101041c0152444803a1041407d0040503940040e41004040062001e0001880046a2402d01d0a0040c100c038841c400b84801a42412240c0c03c2032031100184194001582c1591400da0303281d00406d1030300c0d0b8152529854002c00001400b05401ca100001140100000c2c0c0d02003106d030540d020704808403440c40c0201a071380c0d00300301c2c08514000f030f01d0411488540e00191401141c00d40da80d560361060501d0900c42c2070703540c0001107078071701c600e000f4800a4030744903244000e407090020100c001e61162040c20505481151360304049603241c2c03000c105031543e1070741c02055a03142d03082115034081140c1008800300c51080905d01824107444c408a200a00341c42c0c082e01c0c03081039000601c00b44c065034a8411400c0b0240c410403885009040c000d0164030b194031301c2024800c0c19281d0056844040d070034160440602940100803003a041c036400492032003144d8000305007030200c1d04c1d6030b0406c070241c01100d28040c211b140084240041c0041d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 408348381 1250 408347131 408347143
    0x5010e01090c0e0f04020915040c0305090c0a0305120a0504030b04050a1401020f0409020304020d020d03090807080106080d140d0203040606240c0303050618040c031b0803070206131205 81
    0x4050164080a2a50b45800c0714101100316407843c04d10540c030700807070011706140140c6034004002c80f1b071500107a02c090000c2403c50300380704a0000020788034030a201c1c0c039441c140020785540800f07950500c2c2d041d04545500359518001040600c1b504000100c3d6203c00e8842c9040d50003450780025507100354105800d28650f500540203096422410342da200504c0c0c0c030414821603580074581c3ca02c0ba8107007483c0942c244000d400043c8240d8108403401100d80050b900e101000500d107101e034550052031800d0011252500605800200c1140e01d01082802004400600b0201c61001850300154048641d60010f156009941170327010020b0010003408100076080d00460180c94007248521740510702030022000414448000703801161390803000310b01082c46900060f0380450040c0c011161240e512809890508040310152000074000005204020044400051001100181021031400c107800325071a4810014000e214450005000561150311182003005004030188801540641d0400035101e007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 408349631 1250 408348381 408348383
    0x181c081b01151503110c031c05070e1503040c170705040f11030f09010e24070e03100e011b0c02030607090b1b010209090c04030b010e07171305010e0109 67
    0x150800180848000c9000d40c2401250160000383e161400000400d40003481c80005248080b030040086c10855881000208041c198002407a0714100840d003a174001c035071f40a48410108001000307001c240d0b6881030a003a003d82903c1001c0c607030702c0d1038918042c590303841c030b5a020803018000800104a020800304012084910030b54081c005009094802001c0307941c00c3c0c15031410950140040703200b20001d4845250301c606010000038110203644959850b100880000000b040002c20b1401c0b0044140c000d120741055031402c000035440d03d001d000940f9401c0a120780ca05c5144e03601c0d17005040820135041a0f041004c981c0552202454021009000c0c1044070400d038040c6c0300310400710b0380702ca1080200c00d04803086030000302c1c14144581081c0c403001d5a5803403141c03031664092110818640c0c07551400b0b402040d00545c81981c59240d85090509003005a2041d038445081c94108001c6075000164542d407810b40010074240d581d01d17031041081082c1d0480020303050750701e02041d05d4a1780105520110a403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 408350881 1250 408349631 408349633
    0x2090f1206010e0703090308010905040521090a0b04031109071b080703031a01090b0f221703030105030606090a0e0d0504061d031005092a0a05010302181c081b 70
    0x9a44d540e80540503200d0514004001402240040006101540c01190410300c02c4e0280d81405401038002001c0d61080c0501032283e00000030410501d191044a050081041070489070030241b550700e07454149080461f82d1030144940c030f400a941c5520803900c0040108052002c00d80d030b0061801e083d18140c12244085000c40c1c5810890a28030803148070030400b80805950380081d40f070a080c404001c2d600b0440d8a000d14440511408412680c03503c07200f00229140350b0101d5001e850050740400c03504a00c4141c410a030030803c01030101d40c0b404640564030000039101d00529488003002040103101a45941040380500c00e04041c0550b0701800030801c9801d1070303540c2c0314030318094501000b860303c0c0801025810b510031410300c0c0110009401c02c0307502850740030a481401a401c01050380c8228015500c220485695880c40b409282c08480ca802900080c6411420019000c008210448080340c0f03e51082c03440c5000e0b07200c0b43c500d258107a070845c2c3d403100703c2540ba070305200c03900354850b510070f01c0038821 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 408352131 1250 408350881 408350909
    0x9031d01081620030c030d14010b091509030f010e010e0726070e0406020a180501051602031e0a020a080c06180303040b04030f0210140d02090f120601 66
    0x203903110308680d5008600307a200180720a000c1c10070955490a100a8010444901c0841d0310340070202400600103621011002d942d8450605a40c4011265600082e010f041c10550050201212410079601400c2c0181e400085042000e50058802e000314032003182d0501c943e88000c00071420641000300c80b0038481c0020b1211321354000c4001d0304d58480e406100b8040440c0c01800f241170035030349042503c0c0c003483c900f40c0303150300c0d240c00040003000c004481c1680c00c1a0001550b14005900645070101701d513410420b03c1055091800080c91403203450fa500c00d44070320030384401c3e0641d42d0034002c4212201450070344204503041150b2080e00e030502e10800340d00c04c00e00c200001031655400f0403c0c2c0e18440000b0032031480c06481d900310f205a140032400e4250188401d00001c104c40600c10010000746001d404c0b440011080e5204011440c24010b400d113003004240300001c0458200b200c00e03211620309600c0e001d03884101400100300c4105042240070341c4113440031031170500264040380700c50580b071030403000c101 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 408353381 1250 408352131 408352187
    0x323100b031e0a0c020c0f0a0302040e0a1a010f05010f030b0616050118021807092105010b03121e0708040f15050a0c020d0f050105101e0b0409020a0908010903 70
    0xc03c4555661842c005604600c1e855451441d240d618500014001042030b40e0489d100e401090172607082a07a000f509900003c0e144050010000c2c40301404410030001c407000f07605041030580d02d03501510410b81400440d0742116591030080e001380030400005002d0b15150144143c0100c22440d44020990b0b15502e44910110f82e889080c1542c04400d07009001d00384900416151003502000041c00b0380100100e030000031070309503130503508107a042140050510f50990181080750031540307008100d07840b035404030750001c0c0200101d00a030359421030a03240c503c401c0300342ca0b070310481e40348981d0000030070b02c404c001000f16084501e600500142c45800c1d40c652041000d00c40151500d1141c69001004102201e80240042c60104d210340d4000d403150208050300d40b5507540305825a003013a1106082d02d122141c050045010442c0c10190160000983e010500d1800c80451300500c1a8002c1202d590307000640030420070700840f1000000c115100c000c21907111766040040c1310036044000c0314141c1c0d4260300001c0c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 408354631 1250 408353381 408353401
    0x309030c060f2410081f0311040501060e01140c030412080a0225030b04020d0807030c02190303210b1302130e0105030303061e030f0714010323100b031e 67
    0x8400e400050102d45604442c07500a417607042004194401d044a8058520b503e4a141101c075801140724580281040d084101040140c820580200303081009403801d021076680d00c0f40c03040c1d000c0c999080026507105640c1110302c1c290320030368004100d0040117048503410080b00000805d030a51555090b1140304a02d010b2066050315049100d50720711a0400040c80070030b1342c0c4030f10650400e100a003140200707551655201070039040003c0903008900403010710800c0d42807940540d0102d080000401e401c0ca030a5070380141101ca21958183c1145580d000d848034800d01540c40000c501038010101031001e80030301e903c0c078065882502c02e03010ba1904044006000072084d5001416110002c01550442d580c3ca02405409000c50000d41301c01c107001c09000085460a000c442503e24928010b4a00b00b400c00880459200c0421074581c10036260011500781500c540c442942410070403480c16181d6210705100054100060b0403500b203120300003081c00031080c034044006500404030401d240c01c0e42d42c1d40d6260 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 408355881 1250 408354631 408354691
    0x305040e16050712020727060e0610050306030f060112060e0105101202030703060e0a1e0b071815050901030e0a26130608011701090302070b0309030c060f 68
    0x301046050084400081548044c0d480620b11441101c0c803661307458952688410604051410b660104542c40007174800f40c3c054040644042407000078503003400e01c085903004035184a00b40405c6800310128415a80501214140d602c0410444025585940074011180c198510858040d031812000d038542880c1030180910803200604103111030b900d0910640041d180e1040304a81c98005d02d6800300009419210303460007a003070302000300040900c0d45420b8002030003c0c0da804100d20406894240052000c560361907201d10307a450140b40c80f105002c00500000002d800a40c030004104190f50b0349594440007906041400760307424403030380580803d000e4541c403d02c88007401c0c0001d40c1040511000031a141c10b001d40d0001c1c07070014070f0198078007070384120254a40c02c9030700028441c02c0104499040c2ca135100c030107500030200801c0716008650f07029603500308a00c00e11303240400101c0040c50300e00f41407068030405880c00b004e807569880c11080d4842c041c0f800b26005034510710802000c40c1145030308226 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 408357131 1250 408355881 408355921
    0x206160c0b0c0a030f050a1a03160302102d0e010e1e010e060f0a030606050f0901030b04020903010207110a0605310b0a12050a090503070b070513030305040e 69
    0x1c040303199101d1180510b4150710103026042407644030780b0351281c44400c038801c052141d1001e030000100e03040f00e140c40072451004946124840d074805d410582110038043c90110460340d04840c10210401624015500b0501c0a10402031107080840001d8004030b0307031102402544181cad52910350030302808005543c801d9901302455003181c803420f80403145d40301d200300c00c01340d010741414581800c5101000055080e40030b9481901d4401010951541d0035415008510207030101e800d100d42011030060111000d0300a42004c281015168403208900c5e0700c80b64100d4010040280c000d5685840d14100700d0341807800351101d01d004980c1c030040014200e01c0f480c140e03021001d440411080d02c0c403000300240414290014030a2411920303076030004000b541c00008100e803910b1510b48008600c0c00360540e200715400108028500750406a9035000580c000c0111580540e124a1044003502c07181301c100c2e240c0c002e0002065888100e100003005054000b80580300700d80c44011204500d9940340c0c0040024050010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 408358381 1250 408357131 408357143
    0x40b1b190f0c061b14120403051b04050c12130804090e060705090105161103010c021507140a050d090b01060c140f0c0603040f0519050c040c020c04020f0405060403030206160c 77
    0x381004c001a183c0390740040305001032044035002c040801c500340c0d00f54043e81c01103c040c1e00c880e05a40c8001e900004860520200f1101000180b425140000041c0314540705144441c070264000388501d005561404061900410110f40302d90f00e03800550018104805102c505c0d201c0c90740020303620f40c4104102e840040c4103949076407c0440c9085800300c2c8600301501254400740503001c3e18040d4a09105000c0d0b0505254014801d0402840c24030b0031160780500748008004461084403900d0780d0540481e020b10170640b03080d55840c410303200100010421050001d01d2031500c1c03400052460380c04421122840c0c0661440c0c13940c10302000c403d40c1d0701c00440305550ac9940010446418070714000c00034580c8140588289049403c050b03561030300300344042c0360b01300140d4080c00340d030001e1150400c0140b6030341100b51010400d680d00190044e40e24000003c005115070f4000903e5000071100314140d400602c406040a521070b900c1e880c0203515000d08a0b030203cbd86035407030459868228800c00750700d070320710790406 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 408359631 1250 408358381 408358427
    0xe0a06080313140f011407140102030a0506010906080106020703110105190306081203060a0306020f0d090609210e13020705010f2703080a090305160b0105010f0302040b1b190f0c06 79
    0x1d1b44000e01d41010100791030712691954400c0341d02d20b0a0004510503500c2c048001158034080c1c0003d85031208940001c1d0411800c00010304c0340c1c0d900003403082c2c2501e80115030400d151442400480e003a01c112079110103400344161058840c2509500a802074400600c180c070745240004a0754403050004440e000c7e48407420b4402000450420350061900340d0300f800800d07203460310a40c04034040d100a060f0845226540b1355443c42070022606030078800c0454415107442c80340f00b0b503500070081c00c0381c546401e00c41c00030130001c1410f07955103074100c0b40050f60043c002d010121070130200c6401011440d0b40c40d60308410625041c2c0e080041030031058080381e81a00c40c2481a1100071700f160007000b00100840611400b04080c00c222040c5079030020000d032140d801c4108960400c4001040000c45008610515006110501100d007111050b2281189a241d041c0c4110301d03482c01e2a0b1074040101d02055108070b80328041024400c035004107111160151300c41003000c95460b00112010f9480428000300c40ea03c0f1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 408360881 1250 408359631 408359657
    0x50a1707030b06030f190e0a03030c0e0d051e03070b010902070201030b1203070302010e011a0f04110a0207080114100e060a17150109150e0a06080313140f01 69
    0x55400a4015409160010700b48980c1808500d0039030058408045202c5000d0400403102c2d000040004a01c42c0c40b04203020800c008903140d96504000d12008042c542c94611143c2000e01c9105101c40c1c1982c018414a0b807956207060540e00c80c0303041c0f031290310710007003004240072150301c00011074003c40d42c041200d1106a2034002c01400035005450124105503e0b40c410358040d581e0000140180d0020402440d03584540e8134000c0e0840e000f442c210b8103603034100040c094102400560b882c230061800d5514008004c0c0c800001030080c461400e2010b00007401041548200c0d40c00500e0100b0303a0f0502008000888404a1071580724074100c0c0c02c9550200da416040c17215520240c6e005810010207050074410944500d0743d025901b051112501c1c25500c95940c4450fa0040014602c3c01082c10040070440007940009044440405000321481d0f011032002040940b2080d0b4403001c02410088142ca803074512a807869110308000340302d000c129600c50b0302d0311540c82c80c1070503042c8501c440584483c0341a14107 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 408362131 1250 408360881 408360917
    0x151006020f0d0c031209120f2309040c02150f06090708090709090503270a050f061204030c0611040e0f06010e100c0b04060e070b070302030f07110d0b040c06050a 71
    0x20103a080c202c4c5c0c944034510580091214003005c8503500403629144809040c0e508000c2c02c03031200f04c003400c003a061a030b240c0f021b40b40700550484a2000d81500e02285003d041e04050789003071141094180a140002e0810007411f2040d00c8076401900308a03038000345500c03082000c0301d0042c01940d85840a401c44481040452034680c0218120307440385040c2c9051071301000300102c844a40300090800c035040e50f0280580c40c40e00221320805840100c80f4040c0401030100818058010890583d0501344d840002c0740900d4010002030842c1c907400740092006005240001056400034403174002209c20000210301e0b07101101c214107124140696913540d00c028290704104c1c9841800c0ea450042c45950559100480d0030490b24920a5016403800700703d4481d820078039468203056034002c409641040c411100020f50200c00c42d0307403144400e00c90b66242c8149003418441e107a102118070b40d001810810031020403000c401480d10482c02070031075090080d80d4103400e0780d5500c264a403078000038005520301804041 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 408363381 1250 408362131 408362147
    0x1706010608042307080c0d0b060f01090506030a0902010f0509010f0c0c0f0e0907150813020402090a08010509010e011b080928060507021b04050405151006020f0d0c03 73
    0x4000c2031410410780c200c203480401c111411003a80f400c0d8120500600251108001c06000d01b003040d554122242881d45904030b0019016216a1080510b2841383c40c480e0701c0707174914a0140074000c003082d589040c070f001540d000342100002203012130312090100d4542e5015000350380d51080c0603100c4010350f645c0d100040310900d0a8501c1120000300510f00418000d491105c280042c028158484c0d40c030303003030042d90103107025002d074000c03490702c002c03a0b0180c1d400550220500e9000310f50701c0d408000e4a484e6100040c041d00411121a41008800c10b00107003032401500701034014130b090030080001c00200b903099400d17503500080c0c05507034a0740701822480617842103684ca40d00804c1002511084015410a281c0208c1e03030701c11075070040c00c0300102c042c2400158403d082c0c11600c035000622034803000c00030509810481500321445a41d495000a0078084e003403240d10f1a07414800d001511b5480c0241030003600c600706002e0100144500c01d001e010300b480002e03880c400d1080ba511401c000c007143d41e800b202c13108 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 408364631 1250 408363381 408363383
    0x50c010c020d1e0c060903051608120a021011040914010503030f090111010510030b0a021801050703230c010e010603080d090201092705070206040c06030203091510060207170601060804 81
    0x440d11680f080440c800444901c0070b80801d43d10304101c41e01d14180245010440c182c0141c658000c0e1004000607000029500e0074052a80c0c0c0c01c1d529140b98203002d0f800c1c0f61070a01401440c5081426102d68048100010300c1035800d1107404000708442440d801c41589401d00490390150720802200f500103480101514070b40b030701458810f590791320020b82c2c1c50a6840695041100107101e480c24020007a1040c04141c0c8050042030844c00e04003010007500d00d44005101c024140800010240c0a05201d0144c28044403201190300d441580b5400000c1455804070280d02c1555181c059501c003608418001c08040b04d0f001100760b41042c00c00c2110f5002800c0b40c0030124107200400100103103a90884a4402c1600c1c2100700780c20500003414004015514020080ca04540084040000042d1942c60410540c4c0c0d440c0b80045c0c170390340d909132030900d801000402ca842418441040100451007401904240c56680c0e080c2c5800d1941d9460504080201c2404840140c2060006103d824492704843d5130107 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 408365881 1250 408364631 408364673
    0x30c0a110d061b0f0c0309050910030819020118050604080c0102190203031501080402060d090602090406030f1a01030c14010509040504030302030906150a0b09032404050c010c020d 79
    0x4a40035640c0d1411588001509100c4540000740c00008507000313000c8801c6205503003803241181c00950b900504c0c0c00030314003403188034a40040c041140e041c055000c030406168044c4010b56078401018000c9220102e25401c43d0056090126140f55809a8514040c0c410750100003410203854641d00c00c12240c0019003103080f5590b0902c040e00c594200c4507505c40624100c1c1e0080c55903414000e110141640c9051003507414030110005000040c1c55082c12500c0c0c01907240400143c1c40b07054039000000c1c2c45032180c00ea50050900380080203006600043e03492a610600c509182c442200324038513010007091201400d1029045070411480c0742c0908100301100c0140b40040ca04045800081c0441d101a00c0950010f0703404801c00400250800101d90040410700c2044004403408000805c100301034050b00302461804900b40c1d00544080108090035812200b048a419080440c0102e207100308440644983c820701c2144805540541081d00807140c001d000342403209055140d07103100c8455080c0a0901c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 408367131 1250 408365881 408365899
    0x30d02070203010213060c0b010e24040e0601080c01110111030117010207080f04170f1c0207080607050309060c1303030c020f04050a05010f0b160308091009030504090608030c0a11 79
    0x105c41030a544c0b600180c01140c95003100f0401e10b0a0520030320360142c2106101c40da00d03005205503140462502203818031800d888500c003040e084042005003000d290041c1c6244180340010400441c08070304500c14843c00c3c1d03a9940b1012088440174241c443d094090040c0d9802000144500024030f81840704000b1500005072408030b40b0b56509007182e000b5507141c40ea180d00802c01b40100700003500761104160300007005200100320a60b9060721060a014004011980003541e0201c8500034000c95004042076000d441d80f5140845c07015095520840c0c544d0b5060080b10000f030400d400c0f41d02a14514200d002100b06650b085a82c2501c0850400398183d0340100d00348040c0141e65110300507188101e41030003001c28203502d40054000c60500c680c2041d890040c05003c000041c5030800030b202d94041c0c25103010074158039003104a03420403e180c01d00301d058a090102c40d070149501300000f0000c84400c40c204100c0e81e40e0340c00704250bd900070b03107050341c2107504540c0c520004908000c40c8041c0c25400244071002d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 408368381 1250 408367131 408367147
    0x1030210050c160b030a0608060709090f09060504060e0c090103080405060a090e0907050301050106090501050f0a20010204052e030c05040504180c0501030212040f1505270f030d020702030102 84
    0x48010070360ba108800281c13001040003d0118603001d41c5009010b200010182c40c14440700181194405008080c09669900034105000210750014190300c0d8002c04200800d04090034040f000d400d011541030018440e0b40c948144606200c2040340c106c0c0d801002c510300301418581000603507880400720808000c030350140840c0003100305162500a1300380c0ca0003001d402d445e000a041c00d48605a0042e8240510b1203130402072a60408100c9101c00f0201034403603580c00f4400381c01c0c1c41031100403400390842d8031801e0004901100541c02003040e514200c4000003c4c07000c0080d411707005c1d005c0c050f008c4c28030100b44044c0440d045c000d03004880c0e000c040707050590601d5100c2002c10111044581f404070381e40040d07084002442500c002210241c442860158074043c0c00050380c6120490241004041c20301c00c84100040c80300340e03a120190000400020700a42c07c0c00d00c2150100207980d5078030100041c81401c45404c070135000038020700ea07c0141011b1814002c06801d02d90094110b4042a40c0554003044201 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 408369631 1250 408368381 408368413
    0x10f0b0d1d030a020d091503090c08011118030d0f03022109010c0e03010e0c190e01030c150c0c090b0f03010e150a09020a0b180d03030f1401030210050c 67
    0x41d049200c0340d00035600c4601d0b400c4024038014901c00850300b03000342410b003400410700700009000c0d20340301ca09020400c1c01152424030308050340c03a84000380b80e510780036072070440001c0000100340240070013006011940002c410140c990303001820300030205440207420400240a074020340707408082c9079100b00389041990203001385c82e1400c90320305a10b40d43d911003e0794120342085221840c00d205030000c01c49040708910090f80e61040c0420b03144111407071030510200405244560313015010340c0c400c0c06680d581d02d18140324000198003a007d41c0300030b418030080e8018400d80b61160f46a411003174054045181c000704800078000c031411140c000031404806603180e1002d00a018007041c4100c0104070082010110003041c0c00054403c0b20040e05086010015a6690a03107506031500c402c407495035403400c20200c18103800e035510000d4000c5410052442419056407200d03101d007501c0321003031051440c4900c8030000b000b000d010080d801206040007401080c443c0b0301900391503441d241211503420103031004d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 408370881 1250 408369631 408369671
    0x904021212030703240306110d090f030806030d210e1e0c03030307080a0506010309020301090b060102061812181f090f061704050c0d0309030b0906010f0b0d 69
    0x8020900002007401900c84d0705100d24000024401d282c000070030030305145100c1003c01031101500180d120400100150795140450302400b5014808002c299820718010b0030030496000e040e0040f4107a10005403a904020480402c0b440300b95480c25619001d10a00d030450200700396134032a44c50f07901c2d203924481d00002c02a005800704c000051100719401250348914084c640710116000c0e800c14030502044507000407080d60098403041c408140c542d94080100d0003480104c0c80a5032641c03c00300348000f44000c404d407030307801403c0c2a8240d902c15903130006402c0140b020b51210310f00c15440652114420450100502048c00303640b002e11990307044010006030340700911800c510360098100c41403000c075600310500358001c0ac00d108c130391910b080c504003000d44001c41700a0499103c0e4810000101004000d0141c0040104010044200c1c01c0d403a04006100044038003044034103d00010124070b218400240d00b60485141103580c030105030400d0740845140d00b10b000c02a111f070762941d40a8014441d00240 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 408372131 1250 408370881 408370903
    0x1725150e0306010609080a080c150c03090d050c030405040f110705070807050f0a060c0309051009060306050402040317160203030d1a4609020a11010209010e09040212 73
    0x60310940540034010942042410380c014024048540010080b5080c003107505500981c210402c00e03200c051803070b0b110341026a040310901c5180c05500801590788890809140520484002c4484c000f030000419240d038414864070b105642c2c8103100c02c1140385043d4100d0706119210a02c0810905882c406a0045400681048615403c56041440404010010400141012607546c6084800900480d010f80c81c0d900031300341005041d030802e50070b1601032112031006082c083c045084610186000810342c1403035008000000c1d00307051000660386403900985041d41d411030b8101580601410124069230f00c02020381c59105404040d84002d030703509101404181c501c014004c43c1c1c1c504044180301d03c0c0c0d000382c040f19206250071940c411584a05075042101d881310184005925031148846180448401c01015007031105072101150451a50f006405120030940303c1000307070003000c5526400d0b40100403250340016041c03072802c822031402c40000c0342c0042c0080c0c98554480390b90390700142803054a441e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 408373381 1250 408372131 408372137
    0x30a02040e100605160206091e040b01080405030f030712110304060c260a0209090a0605150f031906090903031514010813030e0a0f030606172515 64
    0xd800c00c80404018000350340110080d0b2010850360800700c0203032682c041c9140181c0700328040e111380821520380c0e03822209400801440c4040c0c0004041c1c00341c18032007c0b00180380c051800e0a02d03c1c1901d50290388a140600d0f4000c01071410b14180700708a040030b800c0200310a0400058941031600c00560f48118641034408410103070352403500d0708100d000c0e5944110110700704246246003c01400340d8024080c110f15056003030481e1074440808100c0607001e8907054036407100c511000e000421800394481d508940c410350310030021480c1e84a10940c18050300014030001081080058180000c1000c0701d03540c0d5120720000141c503a200e5074900203c60f1800d5040700460b40e40c007402c2066004644040307008110300400ca02e88400a040000c1440401030481c004116070078003c041058000c01820080c1e840c00742c0020440c0740d46000d00c2d01c40754060722092361003500d001000b03e908806011030360844840c100003444800d00c3c84080580c052001d004040201151100104825008440b4400389440550f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 408374631 1250 408373381 408373387
    0x61909021203030f071409040b060d110702090906040c0614040902030406240b160228061e0f080403022e0b10020a03140f040308030403170609131106030a02 69
    0x340c40e41c102c00d040a000c05c4207110302c90140c008440d59a0003150b4905d5001d8401080064140d4049051401010011a007440c1445580e101c005001c0c405029018003c9840307919580303c02d031445444000c25580507205082e0200103101441c05030080040240c0c0e8440403514042c3d603007000740100e800544080f01d00684504c801c12503005420161080300b0fa1618041103840d280c41340309290340c410010745500440c0f6408a4a0942d682c401164280246180c0c807121b40d040e8a11030f200d0181c01900030000851070302e410f2276100800510350140da410b103541310044554015203003500c02c503d000708124118400c0a080d0480b80c100000c1c03482c550510301c000c0c0890851901da245e01601c0c04852010300407180c910404c0406a13000501409507074246c10014014101c56000140f548258040d2823540c0e40006400400c20000c1d4000351f210350701941c0d441c030030015006400b91034194280c525540c80f000035004034218017280b03030810002c54820014001030340100f9010039401c0d0000c4901004055000c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 408375881 1250 408374631 408374641
    0x120215041d060907090506180a03050a0308090d05041505030a0e0a0b060f010507080d09020105041d010f090b01080a020d0608010618060b030f0a111c0f150806190902120303 76
    0x55515508540316050805d14141480701240050040403da540c1540720b00ca0404203580f211302c0390201854200d4180c030f82841c07140c100030303200c4001503402e0800e500c01d200c0000c0d016481502074809940e4540107064000344507000c210f4003508040c00045100307aa0f01c0c0030341d01d6840100300304c2130482e100d003455403010b2500404104040848a1009044c0300040000c000040c8500c0212482c0b0b00315528002040001800100c0b024003660300301c0f08160036102c80d421552030190075050304035400605e2111103591650301030011744100000940c0401d1a24001c40c6d206030281d0041c0041c00420507002441702d68444405094480550020550304082101d500c400309641c000c110141100d60741540c03550502e0710300944413480080240030181e940d896104c0079032502204540a11140280d01c8503c0c81c1d14844504c02400000d40e81c07400949082075440c02c0c1158010140c00f180d6080c07000e0102c560300c080070300c140c3c11f80400e9400003456803120540016650034406203042c42a0030b0013540c0760310305 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 408377131 1250 408375881 408375889
    0x12040f0b06061305090403180801050a0515060a0305070e0d0b0f07090e0c0f130e15091302010c05160602030309100b0f040f0e030a020c090a06120215041d06 69
    0x2000d0700e4140550800c211030000c0281c018640001c5940507610700c1002e035a2418119107841003861004c0c0c184401040000342c07007005401c2140150340c07000003009141c688030070702e50004e50402c201940100007888402640d900036801a81e01c05981d003030440d9501c401d000011a400d14101c0708540750b0380b640c02402030781541054942e50003800760030110061800d01003455590080145221a400c000007180702d0920070300019102041c946405080c0125110a00d001800f4021a605070600c4441105141c0514003046c800d4014001c0b51a80d1000000c19001103600740d0100c1c0b810384107842203106102586054141c000001d100540c05181c607810a030f40603905080b0000e4070221010309168090b050350b61822040300040608071000203940c01902d20682c060210017000041502010078107081c41350b004280f09400050481d0700d0190b6540d0000020b04440302400382c110343c03840c1c3c469540010309101041400c0100d840340061b051541e01d2800f0203d04140f5002017054100cbc9070705012031410 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 408378381 1250 408377131 408377153
    0x130f09021206150304080d090204050709080c100801090b0307080307030c1401020306100c0201021507020715020105270313030f14010b030a1e021c0308010f06020a120512040f 77
    0x2c0488a102c00c0c000d581841c41482d010107440070b0003d0500040c184c191101039800b01c42d070998068000d000c946006800a00040c541c0e2088500500503140c040c5000d01d880724a456482080b40c0700c000300c1e0323400c003265000103002c0880305030f4262003201d102240341c2000300050300c2c40b940710350788041104140d4074007090541001d015a020a038010300500c441a0b0796000000701081003807411021a152070f00040b4681801b103851070310101302401c140130341182d000c40c4010640d940c0201c1410b8140c0424002c07400c80c0c0044825405450380d00c0300855a41c95000354100780b911190b02240c0c14141a42548401145558811a0340c030307010580c428200620302e80001121a91034008015410801e40130a88a100e010300040008442c020000d407503207101c1c00c81101e102c1e0040c1644181c1e4219110b032010811000e14143c021440c0f000001803048120003440c7c0c261000c50f400303010704c0010385d92260311420901c4031581c24002c0900c60544511401c1a00340e00c110700680d102c0c0311310030071410452981c0c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 408379631 1250 408378381 408378391
    0x3100b03031612091212030f110a0c02030c06071a1f062f0a02010c0c09020a11150603030f0a050d020307030f0e0105070905090a0b121606050a0f05130f090212 70
    0x19045403005c01061401a500113a40c0386400d0102c2c0007030400302d0f00ca008040348185007a914201048003d90f113a13001043e042d00c988280c0071038030071501c2e8904024040c050004000c0140c14079815074140164182e82c0c0da90080c0300c01d0f40345040740c50b221304042c2c1d001034507401403000608039031080e050001c0204080151401c001e280814013a10950036207440d0700c480c5002a06110440c524002004500204c07640101b007208021900d442c910007005104048a40c524803039445070400301c411554054003401e00880b8000c0045107041f1a00c61000070740d0708841038030000d0010030301130440300c0c1829000540c844c4405a40004220412403501070440c3c264100703c0c034072a85040c08001c515600b00002c0b1041e2031084a4400281c0ea0760f520312070107403800780c500c1a04405202c1050f0741640d03000441680d070180c4601c00011240e11480200d0340e501481180d80005404e00144020b114010f600500d80c07014086420705165444014900c4500d00c15405071203095800111040150000c0f035100c0d80203 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 408380881 1250 408379631 408379649
    0x403031707080c0f0a09090e0c15040501020606010f02010f0c0503011d0709050f30070b120a0203060d140f1203040203250906080a03030b0d0203100b0303161209 71
    0xd0070001e042200c10300a0303080130118800f002030105009400346240c0030061420720028403501052880441e01c8080080c211806006040c9017030f2080c046103001c0d00d05848040e4003c2c1165540d03407004446007103044503890103656070740700201070f041d9950140c0049144a038503401e0781d9501d40880c0079424114503200c6894030203080203001c8181d6014110900f140c0d4122030007a810101200020010101c05000415501201d907019000f03030603802050755581d00d208240d4004c3e07950b40100b1240c91080c3d0040400080700c02001480005041e800345030407507009400e40440c203a00d03941d031740c825034014414004158000c0c0f14204c0d86510800002d42c420803559070090542c1026804079646150030502c03001125a03000a105808880d0752001c0c0080103202002d1212642c0c0c0c69103540c94000e800000e400090038204010b149091682c601c07121240c0c0034001700950406800b6190050001210480e071501080040102c4e030312024a0303c070310480c0121400200e220240030b016000b460141d010303840c8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 408382131 1250 408380881 408380897
    0x70504060806010c051e072d05010f0813060f0c03050a06050a080c100e030607050a08060d0f12200106080f1906050702010908041403010506010503160c0f080403031707 74
    0x40c00101d91b070109a1010a0500958014208014100007168001d0844000700c041c2480c40580c2424140004040410000a1a0342c46400441d081200700c030821020401640115181e0074240c0c0c02c0b2907605001c0c0d100058245211085502520000102076001036111014452291480e1180000030071b42294400e195501c3c1009468030b440d10304144900c2510000d128001407405251034176000702d00107040e03844503e00940082c7c02500160b80c410005005280007581d14101003210710300d504d030030204803400e50301e06568680074461080c0d845d204021881e6400c10100a00e07038811080340d4140701c008166242040a0240750414003038903608281d01114040c070481021280d0034401c030380c110001042c203a542c00b0003a03002d8070409000801820000500107000100050307204500503040f00244100c0c0c6440004442c180420740c1d0040c111101022a40b06042c005d4440001d0203100b40c48003200d241031921788105d150020f61041c4c010400b101040100c0c0c1c001100b050b41d0000c940c1c201151 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 408383381 1250 408382131 408382133
    0x60406020d050f1303120206100e010b070302010f05131718060313050a0b011503050108120a2109020111010c080105040b0609040e0f1020030c040905070504060806010c 74
    0x340d29000c60022009100000070300c0d00c80d4100400c04c0310003541d014810715949903640e1400781040079150351520010f00a1002082c4c0380d074030810800040711303085c0320208642c0c1d00300012040f032175011200840956607035940c19401a4140d0190910030703051500744040d184071506081c03440222000058203141d500b00f006454800d040c0c00301032298003040e5040d40d107030741d1181442200144080005069407140e60078100800103030704845410f8450f0300d03407140450301c69680242c042c2e80007070146810b50307000100898030f0031200b803004c0c00c06000c891500465330241410b215584038640c0140c03000035612a0210819942c10129080c0c032400303010000c001c4004004802480c8240600030184244e80f2401c82440a96030f12080d10f84804001b00100810340b010039155580c1d054581155040b8054000d071415141c2d12885000341d03461814412031400e5603e07030710180c81035000602e200e080c5901440041080d09062090038490070041c1c4135142e6403818440e0242c01e5a034000d000c1410031004480c0b41d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 408384631 1250 408383381 408383383
    0x105090a03030b0d050303190e0f0a080f0f0f0405101821060e0a0203190b0a0c03061d0f060d0f020904020f100206060f06040e011e150c0201080606040602 68
    0x140c003103601840c0005202c1540f9002400d0030040341070244c00d80c8408028440c0c107203180b143c504d01403003480204010440591000c241c503506006050314454221902c1c04012400386001819500420a6030340e2810112100d8424a0b030032411f034141100310040742c20b0140e82007082a0100550f160304180107006415002845c442d20365000d403a02c2014241e00303940c0707003003541081c52800c070340e02c01c0040c022141d12590044e550075600009034440c0c840c0c0640d1044000012510700c04081c0c11800c081c50756510802000060309202c5101010141c0d40e1900080101840d003400c41140b03034242c0d0364040c90401805a00d09858040e01c03544c49104401740800008100302d0401800b658107941d9000595a2400060550054807400e03d800c011134002c801d61550780840c02034481d190440e1645504000d038001d21199004500448030610910f90042c415845400c000d5500485011214078603c4c0c0c8407404c1ca00050003040d880300205821001c0310301150781280c03801750300210030742e80740e400d00380307000e00003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 408385881 1250 408384631 408384643
    0x15060b0313050111040b0d050106030608120309070b0301030503030103060b010810031e0206160b310c05040f060501020607030e1f020f070507030b0f01051012020705060f0711010509 80
    0x14003800d94600c020a04010b0203400c00c448203a14594503035200c99840003c0c00e015800010b000341414a002c0010a40e45d0080c484c03141660001750052820b03040142a151403940090200c441d14815490001101c022400c010340c041d40c80ba01c00b95803254034624042c1c00355410125080d040c400d080c01000054060382c285002102e0b0806241100e20303c0c011080c0c610103400300d0019400c00c100180103840c00a40980402c007c503c10f400441895880310410113810a052044814a40c4802041c42101107102c2401e01400d0141c507408010550310400941100c003c44000d015058680c8010411503805003c0254403001900b0b090200d0b01d1084074035501d46007001460030302d91005400f19022a225076041d11071402a944440d5500e9105040c030319515240d5200844d1210401c2c0006800c0350301d00b140c0c007412074401404814000540040c2511130404001412407826401d100c04000300c0c03c10071159010780d07400050a1014103080d600204600c0986000c04da69a0400300dd00503018000212 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 408387131 1250 408385881 408385891
    0x120501080316110a0b0406020f1501030219150327050d0302030702010f1a090619120f020409060509070b042304110708030f010f0806060f0f04090f15060b03 69
    0x580c0700c0c0c00c60500e40030b03e0100c85802c0194000c034011801185001070380c0020803e9607036a07000c0b03030f07556401c2d9014140c1d90344c080c02030104a83c050300700400c0141481d81c80c1120305290280501041900c40c40d50080c001d00c412502d20000e03803140c0d0002840d596620008448042c16103030340904180c01d4580341d54444d141c1088000b05540000041d864600c02e41c800c0c0780f002c0b122802400741c0004594445569905620420b1050711000c0c080b4082d454462007110500114241a68003070b880c1c1140c59100035040d0a080d225107408030405001030f0345500c11280182d210f10400202030405a91203840d02c2c003076070816981610100814004510031290048035030b491958504070303040c418400303e0082e02d08030f482c1c2d56094201041070010404401c0c040c42c4100e225803000c04c80b5a9072001c0285540450b88507a01d03c80d08040c02040c010300341070002c001c542401500704075100c150030380868101c03101d400c1d0984041121845071020010020703603100d4041c0b43e14100b40320305401c102d4246214440504 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 408388381 1250 408387131 408387157
    0xd0b0f03030741253f030909020306012f060c0307020d09060815040e0f030a0212090109120c15050301090b010201140a02070c0302030a121205010803 66
    0x190082124140b1144048100210303d0300c140c0038854071000ca03441c4080080c50b8038860062102d45044001c90160b2086004151032151002c20320f030480b04171513240e543e1540881100e4140e102900d022021070b1107a24074901002c0c4a01066090500070500e9086800c04c1201d18010020b0040c50381e803100039107168561420241b030f00b44035072056003c600010140c4601550007031404000ca0560070901452040c140c0d902030b200e496141c0c902c2111401401d0041c403000c200b002000c10302e00910483c1003510b81c600907200040c4800c2401c021450a1007501c289142640b00154104100ba03051180340b5441544815007801d007540c040001c1c1c00302146006803400c1e08008401c40d0240203010281d04d004002000b000940c0104040b002401a4002d0152041807410038100c0300655105100d2a0100d418603070b41d00c3e989888500046010b03601002c0241c41e441d0500001002598040c0148240d0602c40d181e54041e14100c4c100240c241014134031110026480c143c0100300040c4048115010b50261170 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 408389631 1250 408388381 408388403
    0x30606091909020904080304120c0c0e09010207020a081f0902030a0f080f0c1c1e0f090e010e0a05090303070203040515070f030207030b100803090d081204080d0b0f030307 75
    0x81c480340042a1a02020758800100c40c02d04c018400400c000318000d900500d000428582c5000080d180292210b100404400700000200f01e00718400041d00c0d04014210005843e200403a00000c05090f01f98105220a4104255034485400c100901280030048460203004000082d00083e84800440d032024094a200680003000c10401b841140d990a241c4c0800c20303100c850000050342c0e2660350005110025000407030101440d4002d03001d02102504910008034108a00401155441c0042d410304050109001011480c10380c14400680601081441a0900c2c0b030201040403e80d40090a01c0409400030014005001d40c040203c40035207209070b8400d50b807200c500414825920440101401402c510341e00c107410550301045503812240901c10340442512080b14030b4030301e080c07548907030f80d603591082040942c28200410f060640e6402000e10b10f09020103901145058041200e04a4554800054550715640b40f4410000c48180c2070300e503d503412141d4008607941e8825000d01402c845251 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 408390881 1250 408389631 408389671
    0x30512060d0b011202180c0304030e0a0902070602030a0614090a11190201050f07020105131403040e2d040308010e0a0b0a0923040b040210020c1005120603060609 71
    0x304841d241000e81c0100520499a03480741484596502090100c0c403400c460301c01c0f0782c030610105c28031078020f6141c2003020f031840e00c8075a01580c42510300c01a0035000f0204650010b0059818400b030165103000e1900075035a40b0741107900c00100c03002d6402c4030310740180401203000c2c1510b52003807043d80040c401c1c400042c080300481c0b5181c032a0164042100c40d0901c00c1c8000c000080e41034120b1801120b0f10302031100e40e521b42180c01d84c2a030303100f101c1000e4074408098a003000305000105101c01c12015070166490180c03a040c114040b108104c0c1c1282442804003202050721565502d04001000040412010703400c0694008211305411b1054589030b503005030108242c1c40300c80d8041903a00b680148164a13260f600e4607104040c11840c2210b4481d0354440d452041342080c0c07a05402e00c40c0345c0c440319400107952941d08200b440071400407150118480c4002643c2107864070f0051000b05000340e22080e490f840d950303800740307590740c0010318840c003a42100d8240b0000b62a98801e4a4000300c0756200c040c0c6407004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 408392131 1250 408390881 408390889
    0xc03030c03190c03061e0e0a090f1b05131109060a0315030605060a0f0807170f01090c030c080d0c03050f0d02041205150121171b0706020a03051206 65
    0x107603801e07403440c03518110f80c40120903055484030b001c455944d0844101b401401488080500c0548a580c0e131040c800000a8a158071543c02aa41984079140001c0404180e4a400e112030301400142240e80d51035060601151420b030600100185401c10248400540b52003030b00114020f6481480c0a481c02042100400e4001d80181696031800540303403100b070307a030303810114040c040649042d40a130302c1001000c2085200020800107031200c160051174424079006080079498008031850440d0300a495200004900a0240049031030140c59030442e030300d0940c00e006801c00a2544142040d0780003008034031645030040d041d0421607816081003074031580719555082c03451041d400682d4440c1e10000740814140d4075680f000135050b00840880303524580701c0ca007990400100703006290b03c02252118040e468101054010141e6100c0d80000d110801e41040c10403450704030400c41210500c3c1103c285014500411040005001720b100800303a100c0300340c402800b0751085e40242c0100084502c0056001c0d21 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 408393381 1250 408392131 408392161
    0xe1902010e0111030307120f060324110d020315090f06091b0a0804060b0303041a0903010f05090606040b010f0f11010b0303190212042106061e09110c03030c03 70
    0xa005004d6a680e41382c0091b00812800300c40500306400340c5099030104d03120840f131261805807940095000d081c0103080100c80328280c03482148144c1c1c00e4840c41c0034820000c41d0406813035000c0740c2d44005606c90030404e1000c80040050051180220742070010001d8942c9500c11054012100b86c402c41941d88079891007103616000c6401244040500003013203d4550361213074070188140c3c0100000c2001d00300110400d900d80c403903031140e03010400040c0020046419100002c12030300e90000c000043d00380d0101808029244200c50424080c1c114900300006401c150180040c3c4042c02d02e41044506030b0004098160090b100c903200411425050890000d4000d502c08081d085009049a840300000002d07410030164040315400180224604411800c41e00010f4070706807080b0356031004452020400b45030182d10303408003e558040c1c4888000814107401c6021007a91540511900032490810304103030b041d41c001074064106018104401041844040700f580d0f0001c1505140e03a5a80c0c0b03d401c1c0c400c074120 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 408394631 1250 408393381 408393407
    0x1020a02031902010e060a050405060307020a170d050f070f052a06061003060f060318060c03020c0f0a20030f0d0305150105191202071502030601030e1902010e01 71
    0x1110b880b81c040d24500d0301006503450603200341d03280803c81c1000c206100746805907406070004100284401e102c1858901301840d4808010f204440400e1a240c07600b50125042508441c2856000126909070300d84030300400782e1205c0c0410389807803681000724000b80801c90051009040160101308940c0055075540820140c140d140303200421024058803454a401307090710483d02c100c0302c464542030040c1c02030044a00303c0b8000d003496a80589401c00a4000c2c03d0000c580500d202017503002e41001035001c1c070884600c480d0543e40182ca40c5840881146001702600000700954442c0600b03800082c414010310780300e44103504d1021880c1d0100b10110f460000d2418801c1054091039641e0040d06da030552046100d6400c61880104961500c40151410302c20510b1495012064005006145003d4000740300c1d00350f80320b40010b242c010380707440329040301c01c00038011407005800005110096038140555800501b5600241c400103031800e00a00c2008200c81e0028144154004204090303801003420560748 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 408395881 1250 408394631 408394633
    0x6030b09070608101d040f151a01020c030a11030102040e04120806010c0305030a0504050c0a03030c050606040b0a090c0509060a0f1413031104020705120301080114061e01020a0203 79
    0x280c10500c944a03111455402a140000e40c0c1c80006480301002078100ca0407110034403440d105048500035864908200140203549070f4441c0e001c0d00e00010700400708070300c1e901901c42000648206a9518540680070144242c2c1150301c0b281c030501d0300c2d07600814180c0c0c14541c01204c40700400c0705c940c00702e0702a0249a10058041c0134640c204028085400000d940e10b840d95515401c1e103664400c01500c00500c1400083c00013203090001441c81809640403030b80043c083c0080740c200d02d5410000455104c03154100702c0c001040d4114450800c0740c100000c81d00902c085509000100da680c0c00f1a0080f042c5219400406403070b80b041c5890b95018504a444200b0040c0041d642c03103d42003005401120b4448940c030000706c110404001003202c03207042e1442c00d070403080e04c1d0125a15640f03d02d1a1b0b000b1a00c0150781c0140d01300011800103900f048890410643e00300895181e6140144082c2192060600e1409070180d0504000050703482d4050036084080e81d1f000c03000c3e10000000100d2924030301000007901 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 408397131 1250 408395881 408395903
    0x103050a180309060305100303051206031c051e0325090305030409091b030308180111040303110f0303060f130f0905100b03010b0d121202121b0901080103150603 71
    0xd0543c00005401918100d0320240899252007404103a0003002e880b0140c0000d01c140540000d0100c0f81031550b404c50402800c58941104222601c0e40486102d2107003400300d00001205801d4040c000410103001110000a60440c500005050b200c0c07401101d18601c0c981c0c51404428600d4055400350380507503001002c41e40c5075501c801e0240002c100300c4034162403c41010328510144024880c29506590345696981c20300e0301c070007a0b99024807041d00034101c420b5413900b02040d9460320600280005502070303070f2040c0d060201210300d00c1c14058010940e190b55042041040f1454446484030b40125000391440490036022944400041c8105104d1052003414074884a0601c1400222076100004400d8104900d80301003041500b21103c0d4886c041d0000510f103420000700383c000e01d41141800c450f0601005180f40d02c10004120f82c803041031a1151141d1300d0502102150b07441501c0050010343e4a420301d4803510700c0010f80800c80502c4020442140c3d0317404141d8248141d01325100441c0e0088071464 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 408398381 1250 408397131 408397133
    0x150a050d05090a0c1203090509150409050303040309060801030b1b0d2c01060f050f24070314070803040b10080304090615210207030201021b0a0218150103050a18 71
    0xa152403440e503043e241098500404250507003014129600c040c1c0c143c5400300d800d85030400388027014100170011508403006144039006031700d642c024210300300c1c401c038042d40d56440c0618024040d0308190704240104440f080051001541e001d0302035400c841600e00111005180c045e141209101c0c1c5102a0116402e0200070fa0900d42c400f030050031f41e4041848058800060b551409089070038070301c81c022030b000e94104100428101030008410052000d40480c01042d80400c0c0f80c03580403032504400780300c0f480000712007090650098064840b0b10ba95000b041c6004095220856117000241002d404034580701d0124521740150b032020f00081040c101502e885950301c4040c48001c1110313101e1040080d100d425021041c91194100403583c20200762441100d60800341d44000075004402c0403410b56500300710b52804c4d01500d629500c220105d240040500341054818045442d060b098410108040f0ba402d00280007a9030700400b50120013071a00283d070341e951041d984013034400c29214a4170100c029602c10 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 408399631 1250 408398381 408398383
    0x806191e1a0c1e101b0f0f020a03110c0301020a0c110f130e2107140111041a0f03100503010b040509030904330510050c03042303010e03090f0f150a050d0509 69
    0x300c411780c0b51207059240004400c1960140a808000b4005070040840400002d009940a50110f20134804a8450b0017030100803a089910800302840403500285c5010208100105c0700c2c08007000a4489840c1c3e10110001708000c2000b140310401101e40b140505051401c08108410302400750003500d0308405e09d40030f40707002c6907404501706070ba9061b940c00400020840c140280c0c6950221410304924061800b4400c2c55a603408004d0300c1d59500b42046660248031107400910300504008088400087c5070408240c21120f036000355a005500b00403c0014855005c420f03030310754240a850209400b10081441c43e000245002e904410000c0180c04803081c031411190001614801d59684580465001c0103443d1030243d124111203507402080103206c1f09042030386100030641001200c0901c82c0d51200020300b5541106000081c0e07134008925000645032412103031076232a9041d600895201c2c0042c0c0030641400501aa03801702c41710009520811030302c10b0003221450b07000760408100904004d1040303 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 408400881 1250 408399631 408399671
    0x20606090604023a051303030507050408010e0706110604030e060a09050418050d02060f0c16080c21040e0c0711061206100801060806191e1a0c1e10 65
    0x7800c4e01c20040d011400280203603106041c021040e0115180c1c1c0400b990354220080c08006240000300700080c0030000705c103d0309024840250403814090080a405d00340001d02480c40d080c4e400109038004400e01002c642c000010803c0d600e02903500e50ba40300349520003501e000045910240d0068640400c0e10a40d038031500c6100481845281507503190360003a03100300e03942c40c1c09541e0203e11048403c00712342c1c036041031801082803108480030120442c82c1c685401c01d0b150400040c2000700e800103201907a10014440d0003515840c1d992002d2402c0c58100503005440100041c541404a900022102e042c041c20800f08403020400500350b5948403041d8065400442040d07038060300641400e008103440c1030140200c1410b07604166505151790741c0d0101080f0001d00e0402d440c071b01f18102000041303500c1c501d106103a410300d4032488150649626100c2c0030403205040c00030881401e1000e00800343c109801207240d5610300c0508610306411031003407000c00e00700102d1882414a00e071030a001041102c002d41e42c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 408402131 1250 408400881 408400957
    0x803040915050303070512070f020a0b0c01061a090127180b06071505040c050306070f02060c040308040302061c2a11120c031c020c07080d02060609060402 68
    0x7892811599801070659034010004000c00305e070052000c2e40303103000b520b101915203107016030310980010320180c000c81c01484954206608400340080c00b031160030400d008460040c62505410159031521480c0c0c2c2c039850103248862410003800540b040001c0740c00ea040b1142c050001550f03260700b02d03038810103141015285c0031003800300c1c0d0400080203805c0c50940e0669081940103130032086140c1e60740c55004001c3c0001401140c080d4400180802c4a440c200304492191201361030f8010841001701c0302a151503401013103200d2002042000380000341c008029203040325416203060340c035102d81c2c6031441884072007601d8012005140110740d440d100c5a200c207030701901c80025903401040f03c0180044607100c2c0d50f40454403040e80180c1345a442e044007000140111042401a03904104076061240030402c2c0c100a44d0358015008292018551002d00c005130050000c0402812201c2150304080d44035000103100c9480b0f007803035500013035460300c5540442c1d00d2500038914458443c0d4038400c10b801c0794440505 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 408403381 1250 408402131 408402161
    0x70806130b0912070f02031c0f0306050306010b04063b040c110c010e040e030301080c09091f0207080c060f07030501090b060301090209040e0d0824130b060408030409 73
    0x3250030301c82d000c80e450f035001e090095210702c1c00700302e61603100c01521807580403a050f105104503125a09814035151260310341c5561568110505020010180ca03020f8124a00c203410003c01001443c5548048608582041c01c281d4803113804e244c149410820340c03500b91981d14680062416a402145840d41071048080754100a00c2c05141022038580805920360051035001e03000c0d100c4c00d98018810410081030080000c611500d0107000342d402c580003031f4802c1d0115400300b04565480e140240302c05034040c00798030003400150300c0720300d582140f40c0c03400c0c4088035490703400282c1e1801c0c04500422901100880300c11141141804c010f10300b04064211383e5540024035004c00401c92008030b015a411000d002080ca604607403c001061000354081446203601a95400d00112070100c10300044810310210380700c401042c503003d5107400310480d80402c0c049032084440c2111250350785035415199141d11000e00010709801c0300300443c0c140c1c4160b40208e581844045000260700303081d50001c0d12380d6800c0324 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 408404631 1250 408403381 408403403
    0xa120b04060b0328091a0c1e04150507020a1509050a080f01060f080c0108130609030228022b05010501080f0c06070c0b030a020717030603160614070507080613 70
    0xd04e85044909001e001003c0714002050543c180010403050b9402c0303124801c81c5490840c05014050f41404100100e01c4544070115040191200500a4010000241c24524500314030f0b540054090410340c003d83c9600d424420b6020115885800303040041c0030040e103560400354072034001c6d80d5920080000d0100315802c003074011a800c2113403ca800219508a801400c2840c10000150b500e640c3c02002c01c1001c9107503034009808038029001e1410114000c0c1c024086045440c0d9540c4001b0003240045e07079207400c040c0905401a00c0e0303050f51910035501e03c1c4ca40c51900b03027100c845481c81941d201f4080e006600701400461001c1c7c01180c00b52200062404882d52203107a4018003800e030054107405840500c05450800c84510034900641d032103000c03400014a41002035071958180f031091404140d43d61030100400c401420704011010402c0c92252258226900c0d0280040221405074041900b2120219021040000c100141e101420341c41041d01c48505d0011702d080103907800e1107400d0ba4115082 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 408405881 1250 408404631 408404701
    0x703090e090c01021b121603031b021f051207020c01180b0f0702060706020c0601060338060d0e030316050301150e1503070e0a050301020a120b04060b03 67
    0x40c5042d0000e4040e0044c00c0e507415184807030342d40f031008030b010f9542180103028088402d52044c05442c072204a0510118002400c41c20001c0140ca6903404a8040c0c0d411410703030b1805a40c80103400d02c0100b404400714401032201a40440b25806614803480c8900225814002020740200d10040911000c0e80c803000004103031000c0e0720361801144030301c1c106003004010710084140c2d41d4004051841c00034117802d1822203940e0702d960403607101807046401a00704000522071a541030150451642040c4080514404400c91004c0080280342a840025a100b80078070240e860315801d45d81c0f50324000408020000038100e90588a5004403001001c1255440ca1f140d01e443c050001d99040ea0a0940c004440c5c03003030740c802a0f50320300c07540882c3c42c0d122045501007814038190360006c2d4880c10310307550341c03000700d0002c102403040c43c42598005c0c81c46a401403120781c86d1954051903014030340403039040c0030a8000d6503d02141c000d0a89411401c2a01ba0010800001d181c014140b40aa801000517035200382d008 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 408407131 1250 408405881 408405883
    0x2101050c090d02040b03210d050105120c010f11010c020f010e0708190c030605270c0303090f040b0d050d121407030906060519080708060c04050d0510020703090e09 72
    0xe030707914695000c4081c081d40009810a43c5c0800d07900f403c00307400c07103061152810003400f08040c0040c480e076001c07400080300d145c120924069107004100691701c00780202138072400c050f03c0381e03002440c403810800c10500000b041132052885d135015420700b03c003c2000d108036640c001d45070420440c40a00d40e60901340260003c003000a00c00d0121070303416000d440c0480300d0400c0c203410118850b0069401600c3c214000c03000c5092481018012203106c240508030000100300d403240341c160950304214a420807c5d9031a0a610084110b40003407204550700000028203000140003015040d1556820244a0940c081042030001e0307070f94041d80c041d84031000c9152100500e8815628401c05c4402c6561000300451051800383e084a00c0301403145402291441e251000300f03411031140d800950450380e0b141c41c1040610300070b0004502922030b00300600468684034500f01018403561041e98004d0445883c2082407006c00c3c011700e9855090644217550701c010038240109541c078540200000400240d000c40c0c8400700c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 408408381 1250 408407131 408407137
    0x80301030303051b0c0d261b280f080906010501050a120504081e07051005041e120f02031303080702010c0f1b080a03020a0b07030b0910150207080304090513022101050c 74
    0x6032414240e40c0f01d0b588c40a1036103802000e12005074000c00c05100c0da07662000c80844d07069156410782c900c408190f064003801000800590040e40501032002f0074850501004225030f41540d0b03003820b0969640302c840340701b15400101d030306d41c94840628241c1440108a4441c0081c03610300750402d002d44109072508202070051244d00c00003440d40d0300100301c0c0d841c92149a003215038064000e00041d15030040c0c80314a000d10b0301d085101141e80c1d00031110b4a41d071a070342001e082d400a00007807005509080226802400b540720701e010117440d20303c020450000f1a0721854070300d90020740c04004001c60601e81d20b40a07038100484146150300c50310f54440425080c500240d40c078901501351340200150f580d640caa459400c40060805410144c4038005c101e10b42c2c070340e011642c0c000c2c20140e82d410721040c5040500b494142e50000c0312411074210302c40c100a0148008190303002c0d580261000205500d034074840b075800c1042e600000f900512b000c10100055150140a0f5000106c0c000003401036654079a46441c843c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 408409631 1250 408408381 408408437
    0x1602030301030204050c0705100506030105090109020a030f14030d1a1008071d040612020f04181203060f090b0f03010204180b03070314061b07080301030303051b0c0d 73
    0x2a009000400140c90240c0000d40c200c5102170045140c504a51039160800758042981e82c69503441d581407285904003486103aa1288000c8020041c242c0b8a07030000711006c0b45440040c0c110032140307450000b405550354508083d1a04141280e90311184000b55501525a421200c0f078201c030400070640712420400c0c3d01002001c01e581c4e61003840d6940c54000c0e5107205000540c6200350540d4144d43c0100d856034800c1c0400b418600000d0401d02100d441002004240b500c43c05002d50f041c203a000d086158241d800c0703a20a035010310002d139408540a070840040400e588046468110058001248109980032440c4000182e40c4510b1500c00c0109040c00d0f441540704020759035032805070302e080c10700c041c0c0e20443e801000242620602542c03901e9454601070a103215182c69088402417150744558401080040c102c2c050b41c841c14031005449051290005220190505071200006051850021043c45010303007080c103a80c2d21000c59101e0195101484407004011401c60f4a1150241c0140e6501d0b1800c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 408410881 1250 408409631 408409633
    0xd0809010c06090204060b0909010b0a080402090a02090d08070209070e0303040909020102013b01050c070209070309021009081005061507050a0f0f060b090708070f020c0604090605091602 82
    0x2040001101d40c0d40e0703401d80941c0c015907100003400040c0d48a000e008000c20302080c0880d11140000e0070040d1188060748901e400c000700704166928641c00868483d801501143c2c0659290781e00d11541002e03205500c0c40c035500002ca291201c041280e0301015010a60003503884101e60f83da55103094038a152005034103a4140e0050204002c500303019000345080da40b046c400071482c2c5e030380b61441038605080c448031042540901c00d450020031100514032030305614610020700c07803820402c0303001d00340b4071031884064041d400e81c7c2c00045040b40a9041361084a50250258480140700c5000408081c264003c5025502821400c1d60917031002e070044500a890007042006000010340b54410f0356401b42e4022a068010944e901d40842c0302c0c2030032600301034003c141c80a0124400c1c40d080040320036000400384078031030207028400d00036030061803603a2000c00340c1000c21889818807410703803801c11114030316a445200041c001c55007480790307041031017141c0c000c0d142090385446020a002d450060b0030030781c0c801 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 408412131 1250 408410881 408410887
    0xf0106090e01020c071415030906040224030402060d02040e07020a110a061403090c19050901090203070c06110c0d121a031b0109180207150e0309060702060c07061d0d08 74
    0x8444041c070921928846c01001c3c61200c40031116800703001d8204035408111500000200070950a0a0206210410406005026195009050b02d482d40030141002e4000c810104144115a03000e0381110050601400d11007000c0ca030110700255120120b0078100d0f0158840c035400505410405d0085059481355220706203c0d5103040800341003a080148100101c2c03003130101031134081d191b201e002d5030b08c40e0980a010301802d0820301030080c0e03882d040e0f11030041c1510400030440b1699000e15800780040c0e1040b0b02003500340c90220b42684a000d503840b048264000d00000a01c4140c0100075080940d18040c000c1c41000702020700740d5801c81303d036038420350150800328245030504020b200310070007604141414000242c551381a008041c8004508030051640000c0000c1482320002054040d000b8400c2c060040c20180c1841944900508000d05c0c05641c0120b1180c04642e1004107480329822502c049403103007680c5203001850041d040c02410034038400240004064100410564017a64103e031000e4a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 408413381 1250 408412131 408412139
    0x90901090209120f031e12100807080c01050d020a092106050a02180108040311060403050309060f070905010f03180b041a0606030403080403020a02030a05011a190306090f050f0106090e01020c07 85
    0x4901c4600200d54846c082041200c00340380c5069a0f502400380a0130340a4129090414042515001e041d40107403203541d0100d1a0100c00d03a9000c0c0c100d5800c688410000b58440717810303040680d2880341a4000c0350480c01071590f44880040784c1d24019100b140100814001511500d101c8422442049000c0408001d503001c054583c0d406010300580040c4240340c0114402c40350b10002c0d01380842620114002035001051103840c00040014941000b50710140003c9801c0034680038090f0742c4207100c4e003414000702414000c0700030300030b03802000d034000004080c0c50540e4481c90074008010085604880005070382110000c0c3c036030070300b082c14482c8202400c29455521151415a000e05005100310308601c50030300983c2c01600c00f807010300e1360305128500110b071146036041c007000315400e0f00500d01d004d5140420351066022494841c0c608603034104500146985d03141c10803003000c20074000050b019100c5c10100b140c80210541c0401c1c01c0700c4003403008210440c02c1c12025400d030310800d428034005500140d4280 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 408414631 1250 408413381 408413407
    0x8010b040902070c210303060501021b120313030f020a060504030f080304080906160b1b07140c060a0918022b0209040c020a120201060f150203090901090209120f03 72
    0x1070014040d01c5210132055440702e510501600c1092a000048810014a410103806004e004013400f0b0900107802c04000b140d4003144070908003210a442042d141cae09003c0c52200600448007808440c000c0504625120b0401071507140d4100012401060901e00004030300b072049041e50162a40084546109242625100210781001d4002e0350103031070401c40740c8000d45c1c840340208540f610701c18000416048604050081402c005c00c1d4403107011601c0c500c04001c0c4010b00c11642e40951020032580302010754010f0ba45419001180c0a0f00201c00144000c80140c00040b000219081811450050f09408008600364081c0100d642c0c1c0d8002a0040510390a102d1500d02801c00c0c00e43c90f0041c00c008445000800f511502882000541c104170b1361001881600607048400c907a250000340041c901c1d0920b104502c4e08030340b1070302c014024280c4203d04214030a0040740c1c00070030014064081541c4a1000c030000394000d00c1041d101d0604590715581c6000c000c542c02c4540000200070b181042c5502202d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 408415881 1250 408414631 408414637
    0xf030a110306282406120507020303010b27060c030c0c06090f010809150c07020a0e070c030c1104090809030105130206041a09030f01020306090c07021c022e02070608010b040902 78
    0x10749180e0010300c00a0083c88603136507402c001c000070745d02d1986c460742940c508401c540d006403c000454004100601100c0b140c40308980070200092010104a1041c03013180502803401030300380b640031400045c0c1d03c0300d51000002a08071807400b4420f40705814840000c06c84148220321210350802180a4014440c0d0b000700c0d1990307840100b00c0256040c20602d000b0541c001e20f41116280750f003040c04620407040d8240702c0c00040240100242c0000b00703003000400a000b0a1890200070104803902043c1000c0151900c2c400507001c10280003400352116030b1408030721580000000d580250710b45000203807242c44848010083c0c2e600074195070700d00b40c03c2c04034101624800e001c007043d22400401101401c0c0d1420020480c580307852000042e103a0500e00100100320801400030145004180306060250f50b4202840c45041d0500303002d5801800d451021a0001c0d101c40044040d071030b8245070212b15080d075240c0c2c035100781c1031940c241c4a8031509e07246d00fa99140070a02854503503000c28841400051150303401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 408417131 1250 408415881 408415901
    0x1906031511090405010303050c12030123030a0f0507052806050c0f0a0b1b03040503120a1d0106150512010509040204180f02011d060304030e0f030a11030628 69
    0x5003482d00c1c8440e80800c00740c480030383c1300303d00050340003c9140c010f05050240391134821210300198659498008066414000005050f0414008400381c010135501009403003c0300d644943c04902207000c5040003911407000e403280380d0152038200e0440941281d850600814940e000c000141880e050610489291704505840034080c4508403951002e0304003004a1050144541092617541c80c0c0b01c6104140000300089005901c1014001d120020f217011040d103a5174440d01541d008555614130000020304000440781c452590441d4030340d03849d40c1041d001102941e441036114110350549203011280c81c800e095104039400001d0b8014826843c00000c2c1d1a041030009001161103002c80000f86003441134001c0403201d58450809070401c55030451181c0880c07586621a40c100308c0420b6001c907200740301c014002010000344500b890240e603540c62580555040c050102c81c0300c21602c3c03130300a030b45c0d03541003400d0341c0329229070000101ca00301c2801c4076403603078a110000300011302c02d641d0b144c2d070141c140302007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 408418381 1250 408417131 408417161
    0x212180d180513020c0706090518060a0308040e090d1d010c050c06030106050a080606090906010f0c0803132001270e070305041505010e06240a0819060315 68
    0x7001901e0794402d081d4040c02043c6040050756240460200d502d00800c507440001445124002000550340f8001e200c0071881c01e95181802c0e681c1d41e00000b514801c01074000610b001404a0f012454040092000b0300c200d1111007112404c6036200410780d01040c401c40050b0300b00c8000740c0045801d52051002880c0039100b801282e6100c2401c1002440e1500300343c01c0180040c50200b00d424006a2040d0b039160411800d40e00e280c5003503101303004030b0108000105143c1c14400486061002d861050014030503203034106c12680d8136410405048501c2189500c0b0603502c0c1d4140c501c841607140c4002550108421058482c60117401100500300440442401c9500000c4c3c0e0350a000103041c284031b002035114180c580d4000900d4078042c580301184000039a0314104c00351500c001803028006c8001c00580180c0c04480801c40b50f466003000c1010308504a00b8004141c0d40814480c80c025040f480740b502400e034095400c0081401409031104580c1540b0014003e141e44103009141e00f0001c0d4001c04a01240c64 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 408419631 1250 408418381 408418427
    0x203160e13140f0f06010b03070915020a050a03030b0301110c03040311060f07060504030917060606090a1703040608090a03020c061c15030b0711030306042403060212180d 75
    0x100a64101022203000c0d004079080091004d215810031321041d07001d8100c2c49403943c01c500f09891300604800c0c00307000e0504a50364000c1382c120714a00030400c45144503408022106002d580c3c2c64010b002e0b15038501e51900960030840c080711681e6500f000d43e12208243d800940c20180703103403034a0400500c010b180d55040f2000b0460211400014002480d0003030180002284506240c81d008003071009a41c40790907010008101246e81100200c0c0042d0011401c99905456401c000002076410049520030100d08095501a5121a40100c060001c0300c150ba220241d483d0f40f0480411340350400c0c0d80e03009005800242d100e100300d00c2c100b4003412203440d0300081200711050003803080048a284980002030201d00180410802914180441c2d0215042c41d0030f85207020700006c1142d90b0700018201c144200e80710825014000b114100c40b031108414080803035421543c90500200075809001118151181d207000507000c094280d402c003210003e41c0c4000e214a0340041811600040c1d058540c0a1202444d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 408420881 1250 408419631 408419663
    0x3080331030c110d0f0803061c020d12120f1a01021f020315121011190e0415060f090e0c0901032d1a0d0302060105060307170c070203160e13 62
    0x141044c140c046121b000303401c0e50b9060940402074042e00c080040e800e102c0406194600503217030602c803028a190b01c043c2c540d00319034001c841513441090884008021070b01d0402d0720350b018449904962151543d020f81c0c10003881d0044012a21440103c040d101c0704800040c070b28201c0b0849034002e5511164032584101c0c0d1015400010f000040c1c909100f604613401241d0760014580588601070f4100e000703040d43c91910115000e00c0904110740940b03002840740e4441c0c40c0b407181d25035810208a03001010100c0034055280c48025000c4e1301b0306084030b000154110300c04510100d0341e400ca40d010306255040b0300c1c10099400c004402920030f210f642e000da181c1c1d0070016011100004540e564126410030040b808000c880380d4040b034034005203103003032043c55003d6800000c6900815240d06680c4240c035084e95a5407001400c0d210000340c84e903054882c40c0300c3c40c104282012100b01074000315100705c040c0c0300005040c40e00c03401c212010303000b1a110003400c0070200e00c00350300c0360b04800e12652080d846100c6110301 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 408422131 1250 408420881 408420893
    0x2040f0f14101e09020f22050a060e04090804031a09030304150b0607050601080d0e040b0901051216060903032606040e010f1401030606050108092503080331030c110d 73
    0x12010061a10b4100410407070751f1203400d048094540b412940914003428908000100d94074032920492040c0154403c030056182c0f40d541282015541041c459960f40e5541d01c0c209061240c2404080d107290724400c0440d0350414044110f0340034640180881901190720380d001c2000344800b0641c41c0e80100d00f00072001c005502484214000c00458010304000002150050181c05045014074426881d0900002155980c0e42450307054560a84240b8110003918120500e80110000c9400407090105000107035942c4c4034003503a054074803d1703440c4802c0d602d03100e14030103102d0382c202d92140d0090181c1000624905040c0c1c012141412910004900da4042c060070074120384000c0982c58074003900c00018002d12901d4081e80e8002c000030300c0c00b00340d18603080e40036a0711080c8803892140301c020b1204110038000e1822103100c001d1504061415500e050990503415404a41101225200b49584440403a000d070032005030041e90301521400b80301101e6a80d280e9242c1650ba580c00e0380b22a5070554433000c64a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 408423381 1250 408422131 408422137
    0x20405060f190501020f0c06120601180f03051903201011250b130602210402040f0c050406270312021c05041203020a02040f0f14101e0902 61
    0x39102c0e00300b244040c2448002401c081105890039800d03403060130040c400791918800c85280941d0305241c0b0310075450740001203801d00901445422400c6010b080441c1010380c0400700e4085902c50b100300c45844c0b0240801c0f2080b00700ea8130020b4041801c80031800004202c0d10300c040403881c2c85c1002d440501c4800c05042c070450304d00d0703103e0056845005c0341036518020b8603400410f80288407100b4045409540d51a9075000c1001008040c40040f07003c054001c1004680590320351101d120208100300444140c5444001d804175000d070700c00d90500c101c641e05a0b002d44104001c4119a40c3d4082c5058108042a10016002821340c0c000c038909103403013400301c44c0c076050301c03005035205803440c14800c032030000020b20b031003510080084000010085207413850382040881d4111000262146075584031820268103001c0c1452005e5007003400d0030019040002ca55000c0741c01851b03600c07810000304110400c040b2403803c04640f80048c0320404807041c0000d511030820507240d207022000000125440d000304c1ba0503a0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 408424631 1250 408423381 408423409
    0x50c0702060c0c030d210204030b0711010e010c0c03081b030c0702030313080307122a05010e0d0e03010c0305090d0507020d0512041a0a090510050f04030b0108010b01020f0a020405060f 81
    0x103940000c0302c1c1c1b40b14045000c04030440107815415401c040c29900d844503d040064035001c1030002c03030080c90300c070038a00303422002034058a24020012402d003e00c000d85102c40810003140024602400540402103200820f0008034514607018210781d580110910594400c0d2000c2c0d9040c4010301c448504011040000c0c009000c000e4040c40d11203c0d14503054900c08002741d984424003070380401c0800401c19561410307021980904151142509a00b0058010907003d488540e00303000714141c1c2201d0540203c1c80c01c0c42088150020482c242d6401e0085045074403c0d2810714191300100340b1003081074410005082013030b000a041c000240440e507a1549880d890044000d01a840487c04101d44410140814040c41e5210280303850f0000303200c401000c00f19240140c0344034031034680c0b90155403882042900c0010101c004026038880d26410400c102c51401d00c516080c541c00c12030010328a51020542101030080f050080459410a60801018007030045c00c294014900b01c90304202980c920b0800c0e1809 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 408425881 1250 408424631 408424637
    0xe0c04020f2b110c0c1012050a0c090801020702010e0904050c090103060504020901050f0306041211030a05090a09140a0522030509010807090b120604021b1c03050c0702060c0c030d 79
    0x9124a22200b40c2914181c0114202e482d00c203004c49000114040340324549044226035922114103030400c1550744c07400b01d9460b400c40510b04801c20050344d1040e40107694040c055118480860345d1000603a0a0b8414410020300145503070030b400060b4109102c0141e040f0b40700314242d4226440382e00100d00042001da1058507096120024041035040c01d100c814007408007a600b00a8880f03560303001ca03944c1d080144c030052450f8081480042c00c103114030510411746151906980ea10344003400010026005640c0462140110020000b074110304c91090039004010240c54040b9540d45100c0381d401040028a507150000d0703949540007032807060303200c4503440501c41d41700d0b10b032121102c50006003c42e00060a141c14080c10070b2003405581c0c0103a056980810440c510160140c0d0b40c030300841c1c0a80511184000c01146100041012910100d2445481d240c20702140d01e540603e0ba80490544006861003001d1031002c20416000d41809001080c444402c9011140700c030607844042840c024402c9240781c00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 408427131 1250 408425881 408425947
    0xc010504150509070302011421010609170c1c060603021005030a0f0c050316020c03060f0412020d140c0c1809010b06070206220b0a021f0e0c04020f 65
    0x8101040d00c50b10742c00c01000c00003045000d00b1030f40040d007041010b401c4a0a08600440c003150510300e810a95900b0440801241d402c0703503514840588010014000c1c08140d440845041440780c0c5e000404a000c45802407c20031300c414160380000e5240010031040d00c0303040d00c944021000d625415684106801595103055880c5072100091049405d80d091380034105040c500000030b110740c80819203420500d6000700c400030440141051b032800f4032034907146815001c1c01c0108080c100e05040d015200e1070044103000d03078828410104984408141c61404007143d440c2c0d41c07054400c0c007000050400704103100d04881019079408001401498100c07407000842c0aa0340400032546000c1c09400304103501079400c90b0600b10390b0f030b0004095000d2030220045600c08088000f10003c07046800794001c110410646680d45d1680780d0094650804070024040302c2c9907541c1c0714007420002d00c0740d10180843c0c64054103002501707a04100207507106ea41c9001d016001404400d00b203038035030a403d9419100052000c68 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 408428381 1250 408427131 408427163
    0x10c0f17030123030c19091b031d0a0605071b0f021302120f060d1e11010809060a2004060e03010b2b030302070c150e0306010b0d0b060c010504 63
    0x2003040159080c802e401e42c0c2000f10320641e5280080e03003c9268a046645e441031100e1581985044c2d007442c1e0000049a040080194041110010400920080d50b070240318104c9030000032080c410070f0b01c50b100601d900682c48903000c036602d036000a80010080c9000e0071444402c90380d40d8620340d40c5c0c3c0d101307417002001c2c0307800e0740c0841c5040d0030140a0b510324000d06500b1722110040380403080000a01000070300c026500040c42c0d965900c0d6116061035480409081d84480071420007440c0c4080034401c89640c12200410101503001c0da48851062440000a01080d5604445100034200a40144144a0604003800284205480a00701400315030703039440481c8603c40c0405084d5182418420f009801d0000803200c0e030b0041856212000842da05604030b401890b1034124024030800802400b452020000801e010041801000301900d680e0307034000800300030408240e266902840f03010768041042080200d10141c0c0d4101e41c680080092043d401c0045000c5058251202180c040b40c0e5140440b803204 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 408429631 1250 408428381 408428399
    0x603210a0f02010618020f0903030403030801290702040b0d0b070f09140d03110a060f05041401110405210f0619090312110d06030c1502011a010c0f170301 68
    0xe0440d0340c00b84024400c1c03038a007240000b101c00000c00d248008980004440e0b074034911240443d050014080c04880d030b100d0340c90500804200b02800f4103114610030806034040c03643c0340042030720002046442580b80913030650030000103091548280d50000c41d0b856810000c1100c40303d130340b07101d5403081d12400300101c0201401400741000742c200e03003030071080c03000e001c1400c0d29100004075080e075060410303040b40e04004481c5071500f014100d00825843c2480e0030701c403c0c880150400b1380210b1180301030018bc110760110b003609075078124040550003103080c08100040d04d486012508101c840d80740049890422511050810804504421595100e5000d01128220b481001e20800c246a8000c02c00c0030030b40c0e900140321032000b004a6001d070340c4400c24015411030ba54112140341019482c00c2040030b5685c54000f01292541c820031610b1021040003680150041c0148400352581610241200144034015101002d004038140c41c442280c11940001403040c020f021f1980720f003141c3c17403a00c2c0e6240c60500 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 408430881 1250 408429631 408429647
    0xf0109030f1b1e17070501061a0a12020306040e030f0705060924060f041a01030b010c0b0402040c05070b0f370b03011808040f0f0b0a03050603210a 65
    0x30100c03444401d9119010801c006a42542c40f5100c584100101c0e003541040d890040c0701e1075031000c20560002d0214104a4154000001c4410194401c1c509080250b4014070341c0c0541c4c1030100202d150a0300c2c602d0110b40a90007158012801000005d001101c681c600d403441d0410301e610304800400190031310034400100030a660015246009005442685078035240c0801c0c540301401810083c01c002c50b8140da00c0943d03030543e0aa010b0010002126001c0382d02007616249c1d550036000c40d250482c810115445140c1c0c0307614a40e08103012079040d0b02c4540c00e002c0103003240b10408080100900c80e0b040002c0302c55030040d00032401c000c2040301600300316030101d0072541c800308400c001025100b000001e003458480241d003400007080000a60720b0000740441c0c09000e1030340d041a030085c1783c0352143d000c10081c100500305075005c0100c058105600c844610500b11103034010a16400010b0141c102168403a03003002d5405100134099170701801c1d0303043c2060581c40001402092441012071070701c54036a031050b06 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 408432131 1250 408430881 408430907
    0x304020f10050d0906060e0f0f0a06140d0c03060e0a0309050904031b0c05031002040608100e06062209090302010f06061b050703080c010c141c0209030f0109030f 71
    0x41c1e00c5810000350041d10521a00d0b8a41485a8840030713500280310300343d480100181040340c81c1e000d040c90903a0303090740791503c219022803c014440c07001c211007092610400c8199016001690700d0358030b0380c07400c100040301c0950089800d9100c07240c2c01700000d021805054003070f59101d001864800103518010b00030500c0c03500141e0007a8014030410004c00c0e40004e260b000d079140e10035402401d55190624044980540d044070ba01807003690006094820306600400c22510310360342d4100141c071100c994286c640c15034410003122044e2040401e8041c6049002072881410b64890720f04007520000003002901c1c003030f92281690760741e03c0000805041e028001e6080048045204010450030880060b241c0e2000641d0a25514504484042040001c11800f03007d55001055280c850354a8840039020340950302d203100024070884a01c1da001c6102005a40004514003084a4210341d0a01250000c0d001441c260b64948280c200780180900288079054030f03140030307980348c08098403c3c40c80640082d03c0c0302c030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 408433381 1250 408432131 408432139
    0x190f0801090908030c0928061107030209040308090304170309040c1106010b0a0c02040504050c030d0207080d12180302060f0c0406090302060a031401080f1e1f0609020f0304020f 78
    0x405007000030780c42e101300c0783d01c8140350300280d44461019001c13440c04074504c1e0039844070241c41c01158030401c64030344082c01219a25a2184280002c0e41c4425454140500c4021342040340c0c5004140001d014a00c155802500c1d00e08030303400d096031600100c004601c0380d100c41c0c406800009600d00181494040c4440301a92030900200c9004004801d075601c40c3d0507c100703000406e000c551080002d10400803040715980080c024040c50615090190b214407030030303003003d20901c10704402c020010300101d10035088480d103034040d2024503041035060390242c030b40c0420b44805566485103120294107580c06040514000d41c014045880c02c3c100c200b10712503001d41400f070200c2040c4030821102e40d1040c0d141c1d042ea81d040d54000c1d212400c1480642c0a0100340401604500750740001040a40d0001142c8071120042e50407500c9242c00e0725484074458200e45010341d0031f40c000344030040c000625060400540b0903400b40014403207555240780412a004103218a011320b0001007404198540342d40e500c400340034105d03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 408434631 1250 408433381 408433391
    0x30f0309020d0f0507050406091e0c050d09031e020105100501021f0b04020c0102044101051b1608150c0304031103070204060605190305040b070c0602190f080109 71
    0x500060740c400e081c040002c2c40e5100c1c41c043d500820009000c040024078028006105664032014401c02a1804443e6501c580d59041175412903405c55000e24548400a03441c2c1c0c0b45005041d041034409041d250b03a05030103100088044445011b050741650744640c58a500000e802d0400d0f207040e50040e40d5507448107045502800c034004408040051400140e07569520002e82e81810b80086400f07401003c0342074070320354400719000031059400500018950b40748003034054201d654855205144074446002e0b549174040ca03000c6841c40d40140000d001012905210302d0386a88405101e0349001000008210110042e900801c0711880400280c1d40c0c0800700c560034040c031701c0c0000d02d0204ca400001d00181c20495804803481d1070200138801c40b0300454019000780416a1201e0024240768400000b2220b40c020701041035450324842c0c4503581c0600d0780700d5100c0380b81d40c40d1044100c8107500c1ea50009c2d0307419942001485000c1c1d80396106c03007000c0f1125440e142d0804c02030180c0540180300c142d00000c80f842c280 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 408435881 1250 408434631 408434633
    0xe0a0b0301090f0f0e0601080607090b070b0a3c020c0c040b0d0c1d0c0304020904061e140603070e0c090136090e030a080c091503070804030f0309 64
    0x362070554841c800c1c0050010800000c1c030700540801c03201d030381129103000340404541c14041200d07030682d40b070b100454041c0d859800c011a5050813511815000500c240110400520090311040d0006900307180480d001280354102e02014011144c1c2e54081501007500c104c1c10b0203242c0400c0801604400e04500b080c48640305030b034540c0040b0740c1a078441c070740d6107903001c4242d500c101395002e0741034200204020b010b40340c0e025407844040700d894030940000a200025001c548400c100c03446143c0c003030300302250743d00ca07036445101a0800c0d403880c00e1140140d01c0030b12011501351140258480109015030510306000b001d040c00c150f4580c12402d401070841c400c2080240d1000103e440c074900c20301c0c243c0440d455964400104e41503c00805000c001d0320781c11141665010320340c01c001d0342c3c072001d801c10a913200450102e80d03c0c840c400d04180426036400001d10001c6007800507043c81c00c03000c1e00281c0c5401011402d940964400c48007880820000360a100902d54000083c030748103009030404201601e4a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 408437131 1250 408435881 408435899
    0x4051320061815030405030d1d033411090f040f111801170111040515030c1b0f0d0c0201090312021002030703090215090a050904110d0b01060e0a 64
    0x10382d90001d9000c8044200c8002d042d1107103c68109804141c1440030b44030f00f01850131603120362006031540ca204d0b04081c52500780445800d8048002c1e00494000d40c82c10b0301c07170030840d140a090209075090103515090745180e6542650186502c4038440d03154075006108100c10400b54580c05402423109410726010131000559035003451403541d8100510000d03407041500040d00340b84114400e034081c6400803000166940418410302e414580c454000c0c44908940c85481d00e981c012481200c0d8480414071800107000d009600458101c41300680403894030011910040003112682400340441e4858599028450000d12030521445400d15115141c1902600000d01e00995400050a11000f0840b1402018020422410030321001c10080d03440c2c0c40c00510180040440c101e050b4003c503445850f041e44001e503401107841c8910b00801851200e070078101480340d800c40c01041101d0111040c0750b00c81d120b540d041340408425100d800401229070410704000c00780151907600c9801020740303090501610f60 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 408438381 1250 408437131 408437137
    0xb0406090f241809051c081608070c1b060c15020f0f09060903010501080d09170a030c03020f060a0506040b0303070b0c0c0106120503070309060206150405060f0405132006 75
    0x3582c04041c10304400100c03c41e4014165030400811a11500e2003e4884480c55000b070746804e149a01c035049140c2d40c001802c1907624a4400076000101c101c40012015400340842c00314503401810b43c81650080300100e182d50024940203480410354410f000c00401110800c05000c80c1403500056003000159480d2000030301508108410a004c00304d540000c42d1208000d0718032034400140240700c00c0d41d40d081002d4689240c0c40311a400103440b2800420000345800108241e00701e060001e1600e031429403030803540c0030b031091011021401028140101d01100700004d600814803801d0004090429408110440d28110301090094000384082e0000c81c400c1c1c0c400c998032182c90064141c0d25000c0321201c1d40100860b0300701c0c0c00500d40901c280780600070000003821145202e5200c024006441d00c00a03a44c44004032803401602c40704821401031401d140d049181c001c14090003919100b000303c03000500b61a011251403489100601c80502071100c60078035017070b8049007110201c1400d101403010503080c0c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 408439631 1250 408438381 408438389
    0x7030c08090f2d010f0e0d03260114040b100309080c120d0608010b03031b070b0f0d200d110405060a02070303020f0705060415030b0406090f24 63
    0x3900204100c040c1e91a510421524854010100d50300240e08080b0700d82c1145a001d04100c9802c1c0f090b034035551650040511502c000301daa220144801040c5003006100c02004404034100444141c15001001c03610440708603a030320700c0b00525040e40c1404129000c0ca02c0f003240c1d851245060404200d400c0e25241d50611a4070320300e03d00450b004415003480d40c090f11908440b2091442424403482616000501400200d46d2a80e002e00c0f05c145e980c51203900341c0d03d40610303580e450780040101d8084880c0143c242da0b041040314080d40c2c0e030035175107150031003032504100c042050410740005d510703402c25000d10900c19143c114420402240a1250000c00180071300640450b026a40b510030714a40300b01001540c0c0140b40003005603030f0b10b4100540094031120700340310071005845070303045110349102d000c47c4210540d00080c0c038060815181250307102d48030050076041d000341a0f44000c81405034440b8003c001c05040022008940e0000ba0107184080310a0400601d2490b04082c0f14100d420030101d007040300326 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 408440881 1250 408439631 408439643
    0x3020609060c12070908070801090b06040b0a06050c01150e0103060e120409020903010f0f0204030c0e01140607020d0507060809070f0f0303050901141c0c0e010c030f0215011706060607030c 83
    0x1030382d07036802c113480342803c6030440d4130701f4850700b500000c0381c08054003c01c48143c4540114091900d9981c1071000380c0362140403244d03000c807014609004aa2180014100c2c540c1c1640011450311080c111401404250340c00002c0303950034a100500a020300f5008101d80749928200410100900040d030301d01c680164000c03008103a40002c1d9005151f038094000680d40c41c0e140500308401c90812034100000c0d442480700300c49000154100051029604903040d04844800c00040d04d0401ca10b004c11415a000800403a440f0700440280320108508102500c082d002e280c031440e0351401c040c1c017a9413401440b58440c0407040c8541c0c0051008032f0280c484241101c0d0b240c185a80c4515403080140d8440313887c1c41c6058044000800d54415410a029008240c6465894108810349a44604544560b800d509580c0883ca041e162140068400c0500741d06600d541d01c180e620080014003a074491000c00e03440900d8100d00010010351084090101c95009601120554030b05102654060007460904030702500d8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 408442131 1250 408440881 408440917
    0x70c03080306210304050114040b03040303090204060e18060108190b0a020f030412181d0a110a02010f060e01080a0b0a091208070206061e06070512120403020609060c 73
    0x78a4640402000340c440d0f0102c100580b902c2d10f0003c055a941041c810580058040d42c52202c0f10103600d4129010b5440c0310301003602d150380d50b0300c1c01e501400c440d4008a0b08a0f42e04c00000500c80318005489000b00001002c450403140c3d901c000c40d00d002c0e0306800451940d0044c0310641031500d40d0b0341c01496030950201104541d641c440351464000e01078801400a0200004200f2080051500902c4980c5003a038131005281400c5012520312450346008000c08000314110300c0108502d514000d9600c0b0000302c1001c034401510016540140d00051500b0300583e454200303206041c0c070079000360b002414038540894410f615146001d6079421750120040c00085d1003070042204ac011a802c4803890b07035000b41e004903601c011228020003044c000c0f036903100140603032004900035113403c40f070b101c040710100005003010450203800c10900341e02c00b010442d01d5104800f428080c00e00510090213038822815143c00e828605401d019049c0600184200e08035000300317042040d4800d0342c6c0d09840415040c1c00450107 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 408443381 1250 408442131 408442141
    0xd0f08040f12050307030c02030f0403061a04290f0f01050a11070b0304110429061c06150f080112030203120c03101403030a0c0f240c05070c030803 65
    0x500750324441e0000c0c1076800d103500ea90b8502c0c0d40000056000e8150340e80c04000c0200c60340c1003242c0381e004200c40303240680303810002040440c1064000c140401e0161185041c286010400036044540241c605482510003103501ea490103244107002d01c11141c1a180750700c844890900040c04016140c2e0343e64180f000105800440c244a2201e20031400c000500f02c1e100252034042406080d001118100c61000e0340240440031400c050081c03458059101a0403c500b0000454090342810b00040e2190404010300240e84102421100021507128211000a846040c003000c40c5844d64012000e03400e2040700c000581c111640310f0517081c11542c1003c001e9406d0002854100e08511510b02d510660000003400d00103082c200d1801140940800c07080c8140f4181d6034160b144411603400e0899900d0b400500036140d5050144e803d450b5182c0c03240559108415007641c030b50103486941c404140c1141c5805100c07150780c040360321901c40d51402e0f1341072607428200640c0d662958500d10780802010860b010010507 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 408444631 1250 408443381 408443393
    0xa1e0614090912040e22050601060311090306010306021e03040305041a070204050f060a051801090e1c0908100e030a140c03070b10050a060215091006030302010f0e0d0f0804 76
    0x1e900c5500703c2503555542e84104507041c940081d01e41070525441c20350711400405000c200100d0702e9500c84041c00b42c0341e103810010380003082c00f010f4954101c2d004012103c29a502400500d000e10b1043c0001a1120b000d0f281403040c110280d500361500110400900003c20340203c1070b48c0031548011041ca02400c44480724003450b001d88107000f03400c50305110611149000c0000e40901c9803106688040a8558410170010b503401c0383c182c4011502c48480c01841000096041294000c03140e2080300c400c940c02ca011040300007114200c0000007a0825014816000c05219100c030b01400c201080c8280301095200b240c8030b1103604014403e110300c1404148074038001c041074460018841083d02e0301c808040c2818045100308540107066074004030404101c601d841e84081095840c02d9008100264401c2c492107983c0201400c04100c5210f01004c440410015010300006507100ba400420306a0446c4428800d0b0f610540c01d940701504006042001140d000b03042102d0384a0383c0c0351265542e115402d00f8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 408445881 1250 408444631 408444643
    0x15180f0501090f080702040e06011d060d050f0d0e01090501050a03050a06050909010606080108121608070b0123030708031603031b090302100c0f080d02120a1e06140909 74
    0x4003003d00152440042c4411540500701060003070314140054441d0b801000d07141d80d03090003501d542c0007140001c0e060402c17400c0c4c0000e0f440780025040e48038a005607240e00e460b12001c1080480c51b5404440206030440d445024041c41442c20f00b0701000207800d240c0080c00394006d03601a08201980c610019a0300b84581e00444000e01000d0412421400c00e240702c2800b03041140a04400f0900304000043c91100000718054440c69201d2140d00785100d41c4036000401d45141c406485c021018070913640490f2403a0951802003031441110803e0911502c114113005000241d501e100750000282002500c41c04003c450001e0000c0d40340c445c00f08024501940205600c03008404290552511000259003104058040d28000c54402120042c0c01d1350446840e640c444000701800e50601a0900055280b07014050030640c02c40302501b0f0640603011980350700d80803101340c40130302c0c1c65100f107030310302001301408090045a2110038040c9900b02001c4442a01300c03214160300030b100c6080040c45407041446030b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 408447131 1250 408445881 408445883
    0x30b0406232a091e04110f0301031209080d02010b04050105030604051c09090603050606311805061608062d010c020904081e1204020d020102160b030415180f050109 72
    0x601103c500c0324640e40c1440100050301e4000c6140084003000c072501002564a07d01c00080150319503829541d901d0a13142c2d00c01d4407542403050481c0b02040030241485040c82c14207e0f81d00015100c8900d1041006a410680c003160080d0000c0e0184004102c02064040d04111281070040e034140d04e60100310b9510304a603021840e0300385031442c00310030000007180090043d4000c031501003000d0440d0741807034108a0540d9a0010102e03600014940001d01a004a030300382d620b01980d00e10010311a00c803281403800881300052820034040d4284239141d08a41580c0d001407083c1d9140c050045d8059007501502160780406031401c20581c00000b80b0380c41030025008069000d0100c0c2064100b600e08440c081d000410844c9401e90140c0c600703004020024140e41710155601200e0326075840e5a001d20207007d98010303042c0d0450103a1081019500c40b18400400241701000c00e995a9240c581015007242d0014242001030600b4150301241c5011104a2001e0240d013003450034607100d03140d1500070f00411228034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 408448381 1250 408447131 408447139
    0xc020d140c060a110c061903050408040f120302011113030303050919030203040e2a030604060e1302040f0c0c080d02070c060806120106030b01060e0307030b0406232a09 74
    0xa140410603500500e0100301d503a50808503a50052000204001800342c5203103807c80f440120410f8181c0f07072090b008180c000340100c42c0c403403070305485040440032807200f03401c00c0c050040020b000c4010940d091150140c0c500d12003a105040c141c551030000c1e20100e60f84805010952108081202c9000900c240303482c41159041200c0280554030f0065240e8100d071154a90041c0407500007000c00800c0d05950030080d091246901c0b4030607404118a42640024200c030381c100e03586000c0400c10140c0c004030075011300c0c801c5900308180a510310400060f03548041000c3c40319424031440c41c402c40e4020501100c141d80c82280300c0d03107841c02c41e0311080c000d000b0350001a00d030101030302001400e40c1e004401d02c0e0082d0015550b0320340d00d0442d010402e0a075207580c80000e00c020280d10040007010b10403356192140002002c0d1040182d69466200e415441039500f52403c60fa0303400340741c60300191400300111407a03e0102030440d514000c104158417100035142c40e00040e4002000215013422042281e41e2258014 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 408449631 1250 408448381 408448387
    0xe010206193603091502210702150c0d1805060a0c06181202010c021e030702060c06150306040302030f0d020405030115051504080c120309060412120c020d140c06 71
    0x400042d1100c040c5a6040d404500d040001099089144800c00800b00880d0010041c5160f2038480308070549803124501c840301c0c800d12010740140da4290052604086240d2200e44899406460030f081600d000801401d100004840f5a20050300c20104400c0325022140ba40d160500400191101c3c6441d04004286c3c600e8a0101c805080740e42c0c010600c598052105840005201c038420390032184400065000b60380603031810031405550503d010044200c2c00192030030011590301069a076005065188925001002046000c03646104440e002c807070f04500a00f00d80c141920040d440344182c0e14280c1402c1800110306003c2200354040700d000b0300001e0003c009040c400c440390780c2c4102c040d0041a00c54140201820b145031030f40426502950755200c0a4544405060104228901969401011801f082c0443c08140d83c0316006000240884442c0b141c40d0200707031520346004101b09050f503080c007000c0c641d100c1c0561140d85554450a5005001580300e401180c40181f13003040300d07688550b01a03800 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 408450881 1250 408449631 408449711
    0x9290301180f051504201504060806100e2b02120309040f0c020c06031f12030906030903080f042102030c060907060503070c080408030f0702010e01020619 68
    0x2c840d2110090107401039a9004040c0d006203110a1429600500401000c2142d070483c851080e185d1049036800030582d40310034880654440e1107820551240000c034400108100031303810200400c01c0003503590f11708072500c0703096800007402000c1142030304c60101008600e4141080c040e20704659050750005c1911071840c0c80c00d85070940d69846201d2090040741007010140d2030300c190740541c118121032500a0720106904d042400401c0d00014001000c6503504132219041c1c100d00342c1c1c40b10143c0381500e0041c01140c21418042c1010b02a0703401300702090f1610b148840070a5024841c0b5030001810350500c45075449a080c90600e1800d0354801d02100c03800e42000c0c5400d00c2c0c0000041120090000580c8d440c1e9640da110140c4502d00d520841c00030860030070000b50054803e040710341c0500d02c155001c030706140c0c0342d8403114a0341c0c01c005000700c82c10000041c6032040d583c0044c1915070114091000302290301c0c1c40e6481c0b0b101d008003103552011803604c0350858500000d204500000130340000300d04160480403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 408452131 1250 408450881 408450893
    0x605041503060c09050a060c03120e0c0a1a03070302071b0f0513020304050a0f020a080a0b06040f02031902090d0602070614060303070b041b080313030302070929030118 74
    0x50341c842118440e01c2c00450880da54020721500c3c08949004001400c494a0101c06940b81165050101c0c200032020880020320061442600c00019205000f05000309400003403041419003030b001852003500100d9207461800b40c1c03504032079204e919403030091385810851810480526400c121001c0b054082e40c0c0206080300e009411004580d1304a4510b100041d02d041001c089120503540540140c0001c010310022405200400b043c952010784100d20099943c2d42e11418000d0048040303807002c0400007803040c9841d143c000c4c14220300040c2000c61035400c0042c45040781b50f980d4a1036040c1701d60041020415a0364400d1406074564010409554945a03841d01c4401400c40a1410010302c0901000c10101d00300002518690395014948203040d85642d1620484c1c048030616079051208031103000305100c44240054200d80703021001410f401c50851902909089803604410002440d11005150f041060304030100ea040692140440e221b0904010070701600e5a0404207101c2000c4116160030810 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 408453237 1106 408452131 408452171
    0x906040c0c051509010c082422090212010204080607110c04060618060f090306021e04061106070c0201050304150f0f020721020a031101060504 63
    0x4070a9841a151802601c0c0d190035802c3e0900900558950074003d240d2080141e007804a15403510044403412003421945010900c1002d03141101c1c00c0c2c80d444075003c3e074400c0301c60030b6507480389415003140003502c4c0c00c5104038051203004401103c00726043c400e480c20f4802d0ac2d0058501d41e00c5001048171016042c0103d40040d00802030410740b1583c0ea48500801040d40391074800314206042c030195a0111603610003c00e001e080b03071000a0055011605400782c0c0e60180d40180c46040e0300c41c0344540b01490586d144020400040d01082e0340380c02001d46015501d05100302c45260744e80400494002d20034190080c0411018008500080d0a41203480541221260001030751141e43d503a900685503118080d208259000600d6400d200d6400c48024919085c003142e800d070b55182a800070b41e60501d90303801504020410340c00d4a1407034401e40100300140070040c000e20904080d6585a00040 = true := by decide +kernel

theorem cover : BRFrame.Cov 408273381 408453237 := by
  have h0 := BRFrame.cov_init 408273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 408273381 ≤ n) (h2 : n < 408453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
