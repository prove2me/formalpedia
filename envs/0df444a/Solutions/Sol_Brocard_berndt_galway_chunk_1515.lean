-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1515
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:21:16.962508+00:00
-- url     : https://prove2.me/submissions/ddc1c9db-80cb-4734-896c-3ce8513f51a1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 272302158 ≤ n < 272482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 272303408 1250 272302158 272302193
    0x1a01050603041505070936060501020c0105030a020d09140c0d0c090c050d0203100f09150b0f090d0c050f09160f1106070207150c021003151809 63
    0x124a1030502c1c0e40c43c010844034440240d43c0ca6603e1301c000505541c0a440a40010504100301d4182e4164a0603502c500c0003481c0c1902240c0d007001a4000c480101c50300c00d100964006800421180d41803000544643e0001400c0c42c104540800400140001c40d02982104a00c9501944551a4028401c1e4202084034601d20300822a401c0101d02185451038514222040e1070000101e8840500b01107569100e4014070480c913600020620290000700d01400049415001c04041d102d40c41f04246815030703a01c10f1548540041448060010300c12405c000d00402240c540c8980c905213008000c51004c10044905a4005807514002c002c81d0070000d201c411103900440e0b14808510b40030015a00e1040d440c8017440c02c2282030300e8203600ca00c0c0070b20031481c80c00c0b4402c81203407414946590000e599135914001c01e81840c607004c0030700c040640280c02d0281a641c0c014407101501186000440061070768001d010080d061010b4001250100650542e205410000010944121a00340390f60b07001000d1100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 272304658 1250 272303408 272303419
    0xf030209040c170d032d1a04050c130509070c060203060604032a0f030b011203020313081b010c11090402131a04061e1202030a0215070c24030b0a0f031a0105 69
    0x303240e004910240b0540d54a951b5000019104249003640d0503900200b01030310740051900c4103200d0540c00c004040c2c50010b180d10240c540d03003902da9050000c0c102013900c588010038170580e24100091225009103500100c09170120341030955940358004000f040c011602d032606007044040b20507900c1e81d03140030701801d200354444401a00d195034000c3c101d541441a04640c2c1c80b403c08850416200b8070840702c001060b8400c00300e000352155041512149482440000d8403c0e048010f48194001e0171041c20300c0e0381040021094070858024022000c5000304201d81c07155030194032002c42100780c4a1100f91100c030341c1a0103450aa00360a002c00c030360f0075030005443d0030490090720541d090b0340c0c02c4030002c6c2d40301c900010030b8404180c40420305d80540b00100a5001d21804050f071440006034002c0c0c80164000c00540311341039a142901e040d540d00303141804014420a21808148030b000360000c4c00c0c0c10a02600c80c0c2085a5119016681458503420427503081540350358500c0f04680d680310503805090304440 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 272305908 1250 272304658 272304701
    0x12050906070b0c1605062a070210090306110a1b3305040f120801140d0c08010f0501080d03020c19140a030e01021005010f030209040c170d03 62
    0x64040c01140c100a150680c1100003c400c852183c003500d001e03007080304035824140068906103440da901100c110700011196509036510f86000020001c03808007126000b031805107030740c0a003c43c10130710182c1001480071345800000000c10512501007440695404070340ca13191800b1004140f0700700d25a551038021034403903502c0d02081c03a010350038105002c060309580c5041411034404011074606e9140440c0d840c81c000810061007a40c0d01000101840360301180d28a0700c03000c4050700c031110207020b000d2203454444000c001900308030708070303950703031401407145881c125901c000007400d40c0d9504100c40e007079030f0b165401042003160030014142c203040709003000d50074030303038081c00c0c2e543e551414020f17910702d100d4080c0c25202400380203005502c8981002082d00c94044050030044e11800c2004601401807007601c11008020409102c0d0f64180c0e843e0f6a0b0490341036285400304043c40e03402401c240d4001e41100000501524045144079968465001408803958282d0014084844a464000b007902c224113 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 272307158 1250 272305908 272305927
    0x3091d060a060e0d0503040602010b090106170a0509010902061303020f1021020f0a0305040308090c09010b09010203120112021e1f0e0a030305070611040308030f06030c090a091205 79
    0x1c0c0c40c8415949140740c00c14400c880a00024101e161a0001400324000003d0104800c2c0d030640104000712011745005000340d9940701f0880c0d4604124003130094000480000c156607807002e80206800c8080d00002043d09586500020103c0d84204c0c449e20351441c0703045080003141020362802810f030000f2502134a0000030280040e000000700760a0003840c0c0d04010205806450a6041e10a04100502c000c1e03241d80196601030020002650198080340141700010703c80c01001a81502000b00030b810800e00764a852420b0900341c100704282c0c0e0650106004151000c40a6461503008140f0341c55005801000350040c0401c40c9020407420000e03100c8050031444a03120040000c00b03203d03900600060031340141270308690a00c50340c00c10a03171140c401c44001046c1607100c80940a8035014903010004a40d070866210341c03521643c41300400004040c80000e048020341842694460000780030707540c0c031f10b131413a00061904100700d44a8003950740c2d0ba80d400c000c1c0800183c0444901d045803d00a01c1c21200c107 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 272308408 1250 272307158 272307169
    0x80f0f060a030804060819020903191e050d0e0607020108060603070903080d0c0908010c1b05011e0203042603062218121b0204090f020d03091d06 64
    0x808160061a80401092464030351561150045810000c41a103c0303860303084c01018880c00751184140c032a501501e00082c0e004920031260a6074004004004402c21036690304408041108252150711004000e9003441e207440c40e140c40414440c00c041c0040849030710014000207120111913008a50a012481c01030340c00ca0040d5810081c05c4030309603141d07a544001200d80032800e800040c280130010a805000c0107803a000321a145000340c0fa060890b030b886140d21400c035106003241500080214030b05c3c403041103c80e41c510382c805000703000102c1e00341c07200d52151141a504005243c04694004104401c7c014542c0c03211620b0b4400c807011417242c1415100c56941d5001c040d1189100c0c1e40103102c161400b05247c941018850418002444801040340021082080705a41a60380c001007001c1024994416002c0040038089104040c100000f83c0e02804000c002c000c40403600c0407940c001e0ba5000d03079203040107075044038400d954940240e0300f48004152a001c1001610100280010911000350b803034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 272309658 1250 272308408 272308411
    0x906101e2115051b0702060904060305010e0f12030705031f0b03180c15030907031e050706140f0a050d02070c03021c051f09020a030303021e1602102c040507080f 71
    0x40c1611035251105d40c00002d9641c400c0a0980d07034458681034002080041c1900006541c00d0381c0d4003a10101302d0803842842e01c4083c82e081c0c071380601c0c00c10000036070b00a0190016681005602d00c50900000890f5070b59000300e01250000810180048100000791140e5040c2a0b405902900940f001c41440d00100d1f250301014440054102e41c003200003900107804009900c025a0806252102c210201c0d03002d00b050041e140f81550b032800390200104a403030258540340140c000782252145030880c102c814045903040030100300200710b001c00401050b011140003a0140c00d008503148060103207548100074500c0c030400d40c6182d100701590301c004049480442c080d010f901d1440d016640f119a8804048001e0070b0502c0004e50010500303101209255040d800b601315a29090710002c400c400490b01c02c02e050103070440d00002d2409044826005003014803800d4800d1500381400c00508028281428180d0660348190104c029404a61001498580215030300204517082600340ea04201c0788001c0110340 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 272310908 1250 272309658 272309701
    0x6020d1109090403030c030e07091a0303190c0501151401030b01020f0304060509060d0c170105040603080a0c030201060b030703090c050a0e0c070f020904060209090906101e211505 79
    0x40c0d6604246e4034038080e030880400240178005a4500b01e4865900074000c01004081140c1c04003011080c2d070681c100041155501070310040082e2003915003040456500c0c40761001100e495486214828503640550f03210006020800420210300841e2000141150310030b18140d4119440108624100440403003210143c86c4c1918010341e0b181203560200e90b062107401110400c140c6044842d40125034050302c455011880c107503484190366618010041901c0460102078082582040481c08207400340d0038985d0000d11078000494030030f6664184442c40d800c203c030480042501e602c0b0200c1000348540b844005445c045640d0240d9508181d020301c24040000d007071050380f401c000ba200091092090160a1703642e40100400748034a05460300c2400307500300040d010701a540d03040c08504007030804038605100c0c490190301d215855217402002d40c001070303485801030b0341414510b0000c0744a003542507402c00054221114001600c540b86084510044010f4400e6003003451300c000e00428a2500c0140d21828a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 272312158 1250 272310908 272310911
    0xf0816291b1e04030302060712020a0e1c0605161205090309040e10020711040e0c01020d03050604091a0403080702030a090302010c0201121d1002070f14030c060406020d110909040303 80
    0x982e6402906564215100e001c2071215010a00004265002659034030550b000c2d42d0310143c6142c00da4104040c2c0c0684500b420102d802d00c4284031190400075142a20001480f040503c1c01d41607486a030b0031288259011641890500c401e4548581c01000341454092414810081803a084080350b480340070f00401a84519100d0300120741540080200004104070316004540e180c01c14508090101c580c802860300481c1009800003410001080711741c5e04940c10303000b8024520855204a004180041c030255201e6681d40208020a255810002810b20802900a11404d090801510700340c8020540740443d0300403ca60350507190301c40d0040b000c0303d41c2800d020700710800c1ca2006840f104d040640b03010800d8034107181021403000d5450344010700c00d840e000307407800380c00300040080a03440745201c00382951000c110031200040340c4041090040124106985c1844484460701d4100300c41030314241d4400b130b0040707401c100102152017020550b0b96103010740d5142000e4600440c0c2d000300020300c00740606 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 272313408 1250 272312158 272312167
    0x50f04061104050a0e041b0803070201300b1f02240907090f060e07021509010b0a05150c0d08010609080d0c0312150b0c1002030402030a0f0816291b 65
    0x40c0091f001c1540000c0100e0300e180054071828130555a400c8504140d001641c600a41c6c1200c200c40a0508981d4000c010041903198130041580041c0030010541030300045209076103e80060001814415007100c1c3d80513203c100c461110101031820340b001c0f0912100b1000c414001c02c200d0000320b82e01201e0801c0707000f081001e5685411402062558091400c184900c4200029070354003080721110768440c50301e44403132034036011419400c031409024601d80042512400380302c203260284c8040c50100100207020702d49050640803d003443d10f843c0c411008503a06030700511446401c1040c44004d000000002c0030907002400b0000c0c078a003c50b0401a091100d00300c02da03212001140c00205045221a81c10902207564100025030f56200c2405100b0038003400a00e010500858022a80903640050090000d14216100c03442070503c2903000300c074a40410400040d05000a40d00458018065600c0c1d400b0204640085a62400e0710740c4080616054102002840b0081e03540e070806081031182e045446 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 272314658 1250 272313408 272313413
    0x90606010c030912080a1205010b040909050703020a06030b031e0303070e010201092406050301090f080309190c141c110a080106030c050114040f030b0403050904050f04061104050a0e04 81
    0x183c41141c0082140446043c4d080c4140715103980103104213001a5210401410980840422a142030051070350f0010300304000c110074030854020181e114090b0060f83c1d1440e03500e500003924985158012004a07446403546101c07071038240250503400205005181152000c41075482c0c45c0d210061a00d824041842030301002a4800d41c03040c1403440e03200083d10400c0500880781c8120511103014001440d04041c40413400381010301072041a1580004003068107030b140c0c0d89103803850308001d000c1552886682d150459000c03504179001c92442c042c0d038141c0307019070800921180c0c16801c0b840541c000d000007600103440380740101042e80340d0b9802c0039a8180198001c030003d000700080c1e5210032855820242c1c0407040c004d0000b0000100c5400b40ca4110310820040c041e01d07054042e034480d8546200841404102003400c506019500500c207251080c5005101000a02240d03026039507005031268010411040218ad40324a48070f05034114445401c00e4680b400140b2540803c1c094000031654000105e400c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 272315908 1250 272314658 272314667
    0x5030a0f020423270423030f0703080604020f0d05040804090f020d1a09160207090207050604050705010503010b1605010b03032205040203150d031202030c0a030e0105090606010c03 79
    0x140c0b8400010403055240d0740340000d00340c40c055411030f110b419803e2440c2003d00d190300c08950502c0c9030500d004c21599590310780120005440c001c0305104048000015070117a42840117202c0b03084104c1200740c5402c8d00f07040040038480f00800c080c0c0034601c10000195203c2025003078502180035006e02142d01c0e0f4441c0303000b41142c060750303015495003428a15042070000c4ea40d0003500d4040100c4a003003200c0181010130000144120022540045001c80440d001c003107075891040001c5070900444044a0317441102104a9103e01c0080d683c0d40c0005060008020050060400418091070b1550465061908489903840f4021501e945900c08000c10000c121003900302140784580102500d444620281c5071540c3c00000203280700c0d100a070f421002c02c4038502031007a030307029510890701041410140c4080c40b441c40800c5030300750b080c0114451113518400440c0021403044d004989220380751602c6e00000b6090f03a50500d04030305103034140720402c800741d600002c0941c4d01900c01d00c1c1103051001581000d85 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 272317158 1250 272315908 272315917
    0x609020301110f07050606060f2215111009030e1002160b04210c0909150c0509040c020a05100c0c050708010506120c0102070b0d020c070909020315040305030a0f02 72
    0x10001c0c40e01180f00303050700c84100090034a844c0600c1c107a030401d0750394408029891048160602c980c3c1e01c1403103a524480008603a1110501d0b9103482d042c003040e15440110035540104e174000000907240d494030b055510702441262842690720300705010308142650701509050206500c0e03405840300c84d402d008000d01c2041003403010080060840a400d4540c14910026801405041c100d5505820701c01400858440000419604060901142400c00300c0e410b0141c000000141c600c460710b9094040c5450461007056401b0a190300c43c41c0d9994501130501c41540c410b810044c1c00d64000080e0391020a601240c101075a40020070000307520a11040103950061030080090084e01c103144022810002c15403155000b40c2003100c01d44034940034a100c085e41e0b030005010150045e003083d8001c01800d1840d00c05070610250320200942010030308940d03d41340c40c1c5154000219507880345844425400c0a0045466a2440e241c0300341c01c4c2c0c81c194601900078403002c1c003503014083c0d0301d80c0c0801c1140c0807a4180e4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 272318408 1250 272317158 272317181
    0xa020c070915030308011a03190b04140103050d05070b0f060111030f0d0f110d050a021c060509071107060807030906020301031a0f01050d030311090a0803041a04120609020301 77
    0x1000841c21084890b02244250f00046010a000340f0000c070f20700c2c44086100000c0c070b11502c50700c3d00c7c542c1c645210400300350006003544000e030f480b0111800c55a94a000c4d4501c0c501e1316120b030907102e62442c01c05510b42002440d0020500c20b0400c0000046080e01a00960040e64010408410b484407401203600c1031807000c00070308600011074030320807007505480100740d25141500148150310600f04c142080f2090921802d004031010040001e80e0a0550406584085021001400c02101440301401415000c185407040d0303903100350502183c5418840c00750021041d1402c08011704580c0b1085030758180e14010003041c480b41d1000600520302c2034002081d40341d4054425902d039696442c00480d152407491086010140050015400041880206040f1800107051940704845a28294020404481c48903400ca90810210800303483e4021050000d200d00c4008540c0d84c0c0c541039140c80d94207442802449656402c22080090441180c0301c1d40d201500014006900c0e04a0301c0003038014125460320 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 272319658 1250 272318408 272318411
    0xd02090103152406030903090e0c09091b091e150324030601050f040603060207050c1206010f05010809030d05010806010f060509060a050f0c0a0605060a060c0b0a020c0709 75
    0x40100048030000b0160001241d605004022500c083d4012025008990103a0012251410480075220760400780502d40242400301059444d001c0f4020560003c644808100c0000642c050341c1c5e041003040c0c0e81d030001e000e001c10080c2041030413078000144101070445101780001d500410003015242c04c103121000300204000205101815107010b035400484003c11b1550402680d1211700c0001140c1d00308400303000b4050900b5a00300000c02c58800c20403078075240c201ea40c0301c602000280c0a48014072049006100031320741509540c04002c101c001a000c1e44400d03130802d50040255440c56079004003560000d003132540551f6a1281c0041c80c1d1b0180741039645246081000006e0407803030200701ca0741070f43c00b5051908051900d44405554074810003010755040300c0c0030804c00b00000e1080c40542208046440521325002c1507500462909450000503101d05130b03240b050003a645401090600240650f00300b500f50f05146450349a00504010207101d1130f00d4002400d210300c80b80c140654805008010f00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 272320908 1250 272319658 272319661
    0xb03100b03070c06060e040b0a0c050c030d15230d02150a08040c0b130b0906120108010b0f0a030503031305030d0606050316170a0f020409050a140f240d0209 69
    0x4141550810f4240c03603441c41d141c4085a0001c1c0d0b406018030681d004804510140c90b5504120014112a040c1604000040c4413403081c0041c188000c021600c0078040100b018218020540d1409032549e21464400c20810104c4a1800040709000c800d804122041d068100503400494440e4000038084008160001070014819401c005654091405600c05880464407001c007110203204032005011b2a80d018081000306840320402401c40d00310103440039051203985505c4c112803181c20b80210706a40d46030008100705003403405d860089200c0496050203001e00c1d603155907440384806440600c2d000c802409410a001e0200300b21200f00c140395408002c25599480d004249400030340c1d08181120810748a040c52078490031941504443c1c0b4400001a915018070240042031541a0080303025020f001c00200803560b8800c4501c141150300b0041a070180400f240400060000c3c411820340c2d400d01d0600150700721868002a840e5010044811041d010900085400c088040002c2d07001d0740100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 272322158 1250 272320908 272320921
    0x21090302031213030906030c05160203070812030f06030c010c0b10080303090705010e090621150a06090b0907090b0c010207050303090d0215090307032d2105040206040b03100b03 78
    0x4201e03d036202d0183d5102d803e0503132258170032015104100c4205000038801e110540000f5407040460f1200d610080407600c4243da01c2c402603003410340b040c3d160001070300088100032410000c5106141c4c071140c124090500c4100001c0041c0c50000f4400c0040c01c14039001000230b084058001d23440021301a104102c1c0e40741d14201100c25900d99003401480d00141da01c00407040c05080140415001d064000d000e040c110511201403841c4c295621150901c0d4820414490360401e0f080490b54052448004d000c2107290038a05001e050324200148907001d2034802c0c1c10401c2a03a0300207481d10588100380700e41540c0368041c01d0041d019000d2510060300c180000000e11958038400195401d115480b40c003550000669480001200031003101c01c0300d81ca400400c8500c0001e44030702d40b2444480650158144000d40c4094171a42c54120385c1d9519020034981c20021280103000918103010010541090055141590224865005520402c404200040007158101d00300080c0700b806405d00a0007141c4915000b03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 272323408 1250 272322158 272322181
    0x618060714030a170606030106030e1006090515010c0c2108130e100e010302010804021c11010306081605060a030b0303030a0f06090603050606280803070c0501210903020312 76
    0x36051100441c41807104810701141020226100c5d66000302403c1c1161300c0c2100640190001c0118030220740100c003a4203030000344510440000e805840c8001605242001d40c0b0340f2002c1d00400c18034103104603103001c43d0018020301d84103030944884c100580090400a9800320f03900000307403001021305001180b840c05511103410888100c81300e80781c103000719480c0d036410320900345124040c41000040450050000d0750080307080e80d8000b0f02c094420000031803451080f0b0060411702c8412200380c8941c41e000314156a040c002c0318082d0645074040c01c0400b0152807a020802c00300e100e2a07010350008180c102c0014040d5204110b95030700602a03035605d10301286c02c0401049400300c1e48203182d103030100116400d4814401c5409581e400300050403143c0380d00c0c08100c5155000204911100b00200c3d05c03481207038107581e4400084c208100199211041e500e04000403820603040641000240410004004900d0b61521a648801c680c00074110103603090407401c601c10714142802c03030003105c0e00f40054035001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 272324658 1250 272323408 272323417
    0x21100b09060402090102070317090a0b0a020d0f2f0706180902040605070201030f0b03030c01020a030e0a0305030609100e0403170702060106080a180605090105071409061806071403 79
    0x8940d01041655448200001c9000340c0d044c03140180e200941c1400010080103103900008034848106060031407440005a40e102c2e550030101c05207501040300c3c036a082c1c041040795000025401e000d030b1200c1301504020f03d41440408000c44005500c020352045000001c1e842001080d03000035125000e842e44405000c0d5000d8000e40e59042c00b441c0400201600e692003a40c003a988103654481c60459590011406440c0d15101e2803d069641c4805540c0390341c0800c0180012130841e0300141c0c5400341c082c5c000c2c0c111003280d11007200c0f0703400844003080026031050450f03901c00360880e40f800c0280c0307030004182c0c6900104d420500c1d002c03148400348824560001e12044412590015803803543d80c45950498803071100784070300001705246401144e03502040b80c0014803c40e02c900d4260045050545502c0700780c41064034011a181d548509100c0c0a99102c0410055012910891464020a0300104506109100800446020b001181c01407a9248011103011903040040c080340000c0304030340d0303949a901 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 272325908 1250 272324658 272324681
    0xf090b0618011401030b0103020d0603120e06040308040303180329070f0207091d0a0b391b032217030d09051911010813020f2110 57
    0x1000621604000300090140741030b500c80030016601c41d00f079580154098481640c000e410f25400740000003242080b48100801580160f4144010452240c030142400c3c0f5401c9403039015900c100300a10201d4921022541140e5151078031101c030281c9404a0340440030b0300d406c01041100c0e120424400008019052150209201c1040e0303c940c4501340190740d05079031680ea450151f000250101300900a50b0b0002c542c82001c01003000d110001d8504031810b00071803030022144041d0300014000c400c45011050380b0021024009500b0844c60b030004500e0358048290448800d050008041d0440a170b9040a08034103010a07040b2030f1282e0440d03041d0100c00b850303001041e50b11220ba0400046c1d04c462071100002280d01d08024619081c81d001000e0041c04a2440659231741c81a1590640c07204200b4900494940c00f0b02d892044101c000c000040462101424020a6208810b00c000160b921149114080f040c11100d406000034100c980c800c0904031404450300a00a104410070000070541054007040b0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 272327158 1250 272325908 272325919
    0x90c12150b0a291b01050105011806081902130b0403050f060c0301170a061802040b0405060f09040c0b0307051201080a02090c0306031f0b0405090f150c1303030302041401030621060f090b06 83
    0xa107014642b03411100d10070000082c0078000418000c1656002c5083c2e01e590400c405454000e2140101c0000042035104e0100302e540001c040091110a010181c203100040018000c1d40c1000070051666001c10b004500f03040f0100c882030b55001e08204400a541948602c0038455188240c0d46402250140003003680507508041c032140c014901442100c4c814a00102541040c403030b15402c0c00043c200050046a02d03034800500411040800710281d4483c541c2d40c1d8a281d52006920178510941206900021003688100da452005a81c0c541e0030f254420039210040740c8941e11040003c0c40e00c480d408041d202010034400c4c41480c01c61f250400c2c00c01e0503050b01e043c081d80d100e100da80342d5644103100c0300404a1701b00b04040003810381580c2ca20b54201d12014015030a0401c0c84401020220880d841100032a500140070401c0c140a613183c1d42c41c100c0c003424104061403404807036100d0113046004c40014100007981071420800280d101e0f100844445500700b01d5100c080c9040f00d4004801d46402e40b01c1c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 272328408 1250 272327158 272327177
    0x8010e072601051e0105190e03010513140303060609220518121c09020d081c0f021603030b031009050c0306060d15090c12150b0a291b0105010501 64
    0x58040d4044c288040f003042c1e41e25490302d944801030f002d01e0308441c10b032903040102c100740b00001ba0307809020b101d000c2c414440f4a041c0448030317480c01c807244148510180030f9940080c000c010a40e40c0c0c8034240e0301001811344400d0158000456100f09a102da00010001a8a09014080c101076103070b11a0000e071540200311740881d0020300300c0a0183c01004d4003c108000c01190348180c0c190240c11817500d00303102900c0c0c0b525040300c80d1303541c00e407641001e54542d8401c80b40d8030402603070140c540070300300c1d4622418000b1407418928000252801d60400740290916441d10403c00da50340701003041004c14200040c00b040101100d103041c0f6129281c1c1c03114140f03c5d100d4080415000c0c0b0380403c08454440c0c0c802c1214401c0509082c0320320151104a4090751110364680740018811b495402c54090148105010a0303902c11071195a41160b0300c0c02f9020f40501268881031116840001051040c040b4440603c81404030440d402015032103410592580c03507003840c1601d890500150000c038141d40090f211038644 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 272329658 1250 272328408 272328439
    0x1e1b120d0f230d0f0b031507020d0c1208040c08010e010207060605220c0c080f030702061501020d030e1e03030103060b190311030c19050a0902040608010e07260105 72
    0x3081076409558109904101040090f1a03d900916035440d01e40404103506548500281c14800716050111a090700d100401040da581480080d4410113a82000c580b90100742e11100d01c140744001903c0184112b20022600307000d40511004010024038009104510040300944c1c00303500303c2c0c0d0003140e18500302400401c0d42e203031100c48403804c4a0010707442010240c0c02002440604401c03480780043c0700d80c0085180c08922400c0003070200c452100d11003603072400c0441000789048001491426000301c140f44030ba69030303a404140088074030070520740402c01d8041c0707015040c00c210b02c20194040d040c05504034070b000c184011010b141200c2c02a1410055039101109218070001c1450348100c0409614405000007103905d0340f000f4003010094102c481072a0031801052112282c52881a44030303600c088100b2081c44d0080800000c0e06940409600b030038607000b80030b89107260600a1501c6160304000080780184603d0a5a900c828480d41c041280c02c10080d041f84541c41c2805541c0c080c9800c40c068040307 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 272330908 1250 272329658 272329697
    0x6020a060e03090d33050105120d0806060a030e0a050d02060a0506060702010f0c0218240d11010516030906090801180b0601030608011406031e1b120d0f 67
    0x100c100020f043c581c200c4a04e69036040c45140c0d00003c18035070307030012249299046851a412041c1652007000002d80d541090304008050b0036650820200d680030302062036002d40d100100e1500400c082c0c60050b10b8041c00c030001e601610f40c0386018440c0780f00d04000300d03062000001c1d542c0c0e514442c94003554059190441c90000740c4004840c3c480d00b0030300c10000761006510503c652460341a20f0f141c0ba04603a030b425400180710031760242c03035040c0d80071104003401218003003c0f0303242421000852010701d12a103c14040364800d2040400500300408805240340581d004030120f46150302001d08550400d20384c1d19014140f0b108500a280c00609a0580854180c805115060103c0c80c0b07490240c903140440d41e1070300a0b881006081904150301c40c1d0001421075400d000c0e0510500070092810210700c0c058052616207044d41240c901d00804007803120940c040003007244951441581010300400503c800440e407017100b04080202d82d07100c0e034040100715560001020160700036650782ca46022001a02100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 272332158 1250 272330908 272330917
    0x615090515120d0c30020d030605010e0d110f09040311060c0903030711060408010e010902091513050408070c031109090714010507050a05071214030f0a0e031606020a060e03 76
    0x70803e100d180001040d85940514180b800b902c0254200030044c62101c911754032821485400359203d0340d200c285082d010301880010340002e20703001c50950381e00000074006005010300500f40014000104005483d940e00000c9000000303011030072079041c6403800401408130900c140c003040c082c9e100440c0c00c1500000c100c8008290060041d801e00c216511003c05012164480513801001007200041c0c0701e10078091840358044410000854145500500c01d60840003070010113848808400115290748a10050905c104400400120f561311858441e0440c40381c0c0401030481c00c00341000004200322540e1903a0303040300a4590200035151800f406950700407901034030700f5085a600081d04c8551080e0098041580664101e40a00c0c43c10707107517241000b1840d00880e211450615034401030010051000d0240d18006005500e040382c4210940e61500a002800c4100541030b540c0d103615940c100108840f0316020070400e42120780d543d10280d515554160200c0e68641007a0012182100210a88 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 272333408 1250 272332158 272332183
    0xd03180b1806032e060210020307050f03040c050603040803071b0b13030909020f1e0f030103021c020a060f0f030207021008060d0506101719061509051512 68
    0x1010070304002040200b141c00c000c0007540c02804420883e0540c50300d0301c021556003031031201541c03d698102040241000c0d19160504042c40c0108240140140d01c1400c844a031044241c55503260f441b20301c2e160480c505694800755110001005000c24003149100840c001c0c1c0302a2903200c0c05010b4001c1d400c240e2810110017070300b18120030001661900e00340c80e40007a9644646090b41d0400c4c1c546100d40220381102040103248140490f28400c03407001204026117811804440e241040c40000c010b60356840b05010080c012010034605031108001c1441e400a05540100004202c13a285c0700010241e0860350000700c0042c1054a00021141c024401c441103250042d0118208036501501558550310203040c581d00105074044103800315100b407051034007400d14980e840078950325203095500801481d10254500307410000c07c01001c1c1c012614500c001c0b0781e019401040c051541c09034104121840d9008240c61400c02e0704204619000407580d800b0342d00215041030481c2c15480c8240d56a50100c81e10 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 272334658 1250 272333408 272333437
    0x20d1505011d04020f0418020406030e0f0703151b0c0b060409050a290103030906080604060e070e01090503030c03070b0c032707030f050607021b0312180d03180b 71
    0xb580d0060515400a040905600824a260076640d103200d02c00b0214070366000ca03501ea4041000d00c8095814000c481107141410014030540f10381540440e200d559500c8020403841e04000104508642a0440d0b4014920400c00107405a100403000d80300840c042c0c001c4420000c04c2000032080c2c0307003a100350255035400800400706140c00c1d42e501c0d101c11030344250040380000c40340c0550038030030407400046010b54030958030141c03010b14003280580180c0000c0c01e428880c0c0d05001d000e02803440c604801c07d5000301145070591454400703000507504003400c0d03044640c050000044840f000c240020082600f1071080c2e007000810b035190410036285000589400700c0b41e601c1c3c401c03444801d10034029503d04401c20700094541050f41d80d501d0f40ca0b000100203007140d590300604100900c031078041c4080f0180d0a0108204200f1850300302c006900d40303104194548110744003058a885e5140340120580c0083c1c0c003d1b008410000c42030401070036a106001841e001a09003100102c0c501882d4010790f1541404881ca = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 272335908 1250 272334658 272334707
    0xf02010b031902090a0207020d290c19090b03090f0613030f050703030608060106080405060f0105010f140c10020c070f03020904020909100606121404081209030d020d150501 76
    0x700b0084a4002d00503e208640074000347c005a0344070607110300c49074803d20710381101c81c02c10407030340c0d00840300d1141c0300d0000c10f50030f01040341010704141101c2148400289050541c40030359410341e425039540d0018640c07a8004020010a400c0001b0707004420307100d0504071080e13070f07580c0400c1c0c42d1711031b0000c6001000900d64440c940d0b4038070f0184014120161080c02c0100b00345458451a910b401c50991152000071080028041440820b07c0f8852704140400801c014560611001070400780c0d03925850b2080102c10901080c5045030f482c242c4004400200c151021400c1520030034000c0c3d0840c3c44481c0b980c0c0162040050032424500c80b4008499016102109c1a92a502004036401c0d00420300300c010300444108c600e400d800d80c031849001d071070961507000c1c0c032a0111100d43c080790070944070024042d0a1005000110b4815000d40321b00a03005481d03164550388000c021401d500580001640170350020a12a03203500154012955801c4075030500c40301190303500011076601012180120105404d0381 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 272337158 1250 272335908 272335913
    0xb0a060603060f051008070c15050609130f0809062206020c0303040311040f060302040c0207180902010206150d02180406140606030a150f0f1409010810090201020712030f02010b0319 80
    0x2412070350b011f0b486040c540e04041080d202d84a64035602d998440d81c0c640c2c0c0303004004040c075281181d2a0410303030004440700c0101c025030b50168542000d10014050140c00305031156150307980011505045e45461a401004000144000c041d0045000e1080540160040e40d0441d04002042d141203d82080c20b0b03040d10b992020504c0300910b42120340f580e01948030f02010000d0384035800750040e001304640c01428010f01c0c09544540e0500c200380031002d064200403241c0c0c0540c1e40064090b8204888c1c001c0c40c9880022100083c20404000a000750002c1c1150218603014101c01c40092241e400b5200a012140e103025225140b90760443d04250302003010b00100b62004044d9000408007030142c0301000119440e102c1d03003010700900c1d500100884d40e00b20700a01c00001008180c06446c00c09841419480d4100b6200f80e44400a40c46007903140d80d80c030308003601507a100308807030340c000c00603201841c80c0c4100301c0c00c00a20705031002000300003544c00c0082603051f0303050000c3c1e0308540f08100c8041da404000e07150f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 272338408 1250 272337158 272337167
    0x9050606161128170a1b0905040b0403030f021e03040203010f020c0703020f030102040302010530130201080f070e01140f0a020a1214041406070b0a060603060f0510 72
    0x5401c180c0340c036003901d040240c0e15110b8000d82000d044104940c0d115842c0301a03069030762040603400210141d481e801d00200c0360f0f035000503403040803a4048585607144952442e00c041c1c081140d4420006141090284000d200303503008028016802a90180310418540c111a400d038410005e00386a0200f654450f5190b0b01c40301c9000d1a081440100046441800e0310200420b903000204000e83c0c540190004000718600b585103440b80c1c140540081d41498a10340003e40a8025184440810416101c058039004650a82c0c0003000d0080c1c00d60040c41c0c2802607160781c104410100490205580001084c0180d01022125100d80910b68544818489280044400c91008000e91101e103005000d1410001c00b031102038000c0e1001c6a0050006071401c1c1003841d0807600e0041e0f0030003845940040c600e0704441c0e240c00c98050b980c1c02055240b1568681c008640c1d58864158045c0404128000380461205150018001c4031101d607000d004075602c0d01c1c9094440300203441101d901c0b940c2c031207054881c0e5006 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 272339658 1250 272338408 272338447
    0x130c021212070c0f06050a05220b01090209011110090b0c031308090604030b041a0708090a02010c0819030605040e0309011e030e030c0604060c0f021905030906071a0109050606 77
    0x1380a29071041d8102c0d60b0700c5040c0c0301c040e82e543d18107544942c00c002d000100e010180c600d41d000b00304540d00103046511507a03140340040c0200195140c0001d0a00b010307034081d8400c070400d8034054040390220360760141c20600a2101401c00c440681c1d035a8045441880520280c0e030240c2c1000c110349444140c140d0300d00103954081e01107190001020311001021034030764100c0b01c1c400c0f0700030400f030034280410703484402c2440c50081900062200403805d0009090340090401c40c42c66080c24011020080d0303050040d900d010700d0007054514500c1079256017240d81d00d504151700320f0b00151800c1c401c42d41e042841c2900d9004588990740080c4c010700a2280c1c900b083c4052400c00c81c071a00700020003141c400340c0b46041da88403446024030b035071040090000b001005c0c0b06201e444010b41c41c015801504100000752108038107460403020549001c4c0c50b2050080500840b80d12000c001e1080d55035204030309d8001e101d070081e1011408070481e154000035812049000355813103111300070034481c50080d501d400040035040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 272340908 1250 272339658 272339663
    0x50402010306081204051908071203200c010207151407020d020307060f0905030c150711030118060609020909060d1104020d0504020f0d0309091109130c021212070c 72
    0x4480c840024500d00600240e07082030f0701c2070401035445e0f0510084c400300d29940716603182841380c206410025000045200c1d0152041c540c008061080203080448034a044520b580040721219000d10500400000700ca006440080c1c082e611400d66072002032000012110b500710104200c2d900148405240d9801040101d10080585031940b56540202c2e20b046481e03000305000c030b00441d40c0d40d441581c0024803c3c0003000202c00a0292040d00808a0242c003001040c2c07650202c0085003d40070410400b0502e5071052018000304105000c010400603c00080b0324280da24a02d82040880e4000e818001c503101d140c1c002d0000802a140c0d402805841140f088040d19004500102c0d000c541c0e983e8001080b40941c18603011410341024010408419200c8901901c11000301c07582000094114015004460901c8800204042d4100c28a1494407802185075880b4544451451442285900c00c40d0705003400ea080314842c4628060000746032003220360040701040400c0c0012400c6204803940b040651 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 272342158 1250 272340908 272340911
    0xd0c1509020607060903020a031b0309050904021f0503060a08030f041e0e040f0b090606010804080306031e06100f0b04050f04090602070b04030e04180209091203040606090c140a030504020103 84
    0x211a504c454045440228081300160003900c0e0003c20b140e40220a08402034082d100b80ca107040030392b44c024144020034440c90707008010030800281590380d101420800052022a02c3c1c0c055102e541c001800e0340d004542103449010801c6021038001c0001064880e0820303480c81691406c0e00340801c004902050050306010001c0c00b0f48045032000e1440c1c003d03030103030b031103603004114692442c1380c61508590020321446169120000f0056a60303845001c0540080d000060340307680c0d03201c40f80480c0c10152070303421580e84010048070068041e1400104c080c03141d203641500900341e40d00e48201d044800400c0c4034983c1000f000340300a11a03880c080a0b0420040801000004d00700c6c070f20380d100c1003a600044000c0e900311100d401000141070300505001410102140c1c01c0100e2100c100102410001c8146d01031700581d001c100050905c070040101c00240700400e040c59442345400e15003040500010b00952081d42d040c800074443e01030003512000403107000008400d0809015030b03011001054001d00c01c0e810035 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 272343408 1250 272342158 272342167
    0x2210d0603050706110106050105030649050705122e060b0702040605041e0b03011107050d09060e090106050307030603080d0207060614030a02010f120c030e0d0c15090206 75
    0x3910803c600d00007000303544c50b45038178180100d525608560781640441e0510504004100c03a81d030325500c003840400b940c1d1800220100b450100c00da10a000c50b4a520008800780e1a006010284854081e0800e40701d2000c94184a0302e07882072208000700540603080c26401858150580080c04c1c548035a8420104815070800e0450041c41c1c2c16240c496110024641d0002a01c0040d410140100c8011305816036042c8146400d00c0040c03080b40c10084290744000f5a60b0940107083d550039040300404100003040316483d4800350800a46907681c00c0300c0c00021030300784880043d4260190740d84842041004203884456823900344c0c213503410b6200034649001c040d41c40c54084002498a40641814100c0600040e00ca020350710f088400c0ba0758135000b1008c0415a0740d01801642da0008032179400701c0e820320741140340c1f05042800761807542c0c41c9018114044c5c100210300000c55490f43c0040c04c0005000b08450980d00082415601400059005087c81420a15050601109030402680248040c00ca81c2c0380 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 272344658 1250 272343408 272343413
    0x11041502100c05041805060109050d03090b03150916020a0b04031b03180e131205040b18010e06070201020d0305070e1801080106172815090201030c02210d0603 70
    0x464841e000c501010801c042014020520052004c9404c1100c1242c06c120340d0400700c001a200c07543d58030802e071045560440500825108080344802070001048081e05c5e41880700c103460b9003880c003110040c060700b01071000494240002c265441d045040750060220a8081d892b082c11422000340240d00344030742d5840c20704182e0344121600342054002e40c0c40ca8540c0c407680e10502d01e14104c0d584204025902e0a0070301a036500c1440c0e210010700d5010410103070008001c10300303071414003c0c1d60017075122090124a651240d80c0102c80c616078100240e0390341d0501c140200030000f40707005d0900c0c003a005902201c0144a42c0740a039000740c0d000403180c01d01c211100a1203002440704aa0204100c039610909001004101000d0140202500c079003940700c0035001903101341c41e82e10b5030714920f035020b0746030340b682c041c01c2d440c0d80750300324004458200c00c04070700065282c800140540711118040b0300081c5013000e50f1680c41c0c80800d00d2a5500600c002c0c0e01450380f01b448279818690000d984100440d90b030348400100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 272345908 1250 272344658 272344661
    0xb0a03270b100e09100605010e031509010e1006081507050d091e030201061e0308030c0f091002030a020d090b0a030509280308011a0f1b01020301060e131104150210 72
    0x120f284d1541c014a000e20703000349200185c440c41d5009074107110081c0d041c91050783e070200e0944001c0358038104c1841503603654010350b405418180703188441030141c1b11a1444009030354012109032010001104d80300c049410038001500c07002c8594000003072080c4600385c9003018039000080500d020b0400701e0f0315040c12003400007680c000c122040740943c0d56141b04000f09103440c000c8010906202c20a01a03051864482010f14400103020343d0040c0c02c00521421001c3d402c2c01a0b490751a0064541d1310507140020020b036482d030054000f02c015208081040b407105104450150a40b0a640c0085040941407102a00500005400c4407698040d4404030300820004808841d403801040306031550030760742d84c01c01518403001a00b150203101003200144005140290894242e00d9000411664031003084015a01e201e4040156040d994000400080d04981c0040c10a80102044601d03042000700760341000d04480200c410001498010312080115110444a000c42d05010b40141c40d0301c01c1c4500b81000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 272347158 1250 272345908 272345911
    0x20a020603010f050f1509121203010f0306050f01060e010e032506080c03040506060114190e0a0803040e040602090a0816060807030c0c02090a11040b0a03270b100e 72
    0x30044690f84104000514084600150626080d40c1c1c0000c0c521502584080d9403080700441c0d4010441c6400c403880c802810880320404d0340120701c429840f56107078400c5802c896228803003a1211820880880c109010b5890114101e440e95194000841c000f180150340c0000c0038866103606004910344003039480039500a4540310344818001d4050a81854009000c0c0c1c000a4081c0032014400e05c00c000000d400018000d40064007420b080404031410024038800788203c1d2171841001402d0420488130f03a130403800c8032400c1e19044030444050354850b44040c0c0d0307a0081d0310443c0303404d001040114021a0090b030003480a00300151080085035103581c550345c07030080325000790681ca01c2004010440e095001c84940c5d042101c928040c0041c0000c500010b01c00313644010f001c5e119848520100345919003c0c0c0c807005c0780008080c2d6203502c1760740e030721400c0046030050140d0f04086401c1208055281c032040f40400007040034010910102d031f800361950b1042080040c0801010381104c0004182075040e1034495 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 272348408 1250 272347158 272347169
    0x7030201180905131412160206041203020a0203071a0d0e0309032b0c0b040236040c08070b0d0c0302090904050313080309010e0d110d03110105150d06020703020a02060301 75
    0x18586020713601d04001440c0d9485280b4800b0780200f080880100340c03620844811030803084240f01c400c40c40d400043c2840c403aa1340201200282001c00360201900031440d800818000c40a480441c0d940e005501c4c11107608860326402030b00c0800040c4030040c8140d005601c4e070000742d41101e08011166010a203001c1e50008004a260311404024038000410300c110030700c101d4245000804410260f1b1070789002000a8402882541c0c1d501c1003000404500c1c2c0e1302a08a00350f007090b41c030000c00413100250b01c2d0005490a0310b01518800010500c94000100503040b1124001c3c82450503402c02e1021004188000440081580800000019903100308140d80140d0003480595550f4002804c1a01d00c008158044a910b0b0000c3c405100c3c05d83e00130706d6964458009845100d1201131301c2c54800510b028001c2d07000da00c4860300301c60030103142c0e0103c4480b40e80b402c5180200308546801c450000b00f506e8120119901031040c13841d140c0083c286402030181d02e231003401140c08410840e400222150400d8108 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 272349658 1250 272348408 272348431
    0x10020a150e0a0b15010e100503042406060305061009150e030601060809010b040b1e0d12090312110606060f070b150414010e060603090a060e0303160e0307030201180905 74
    0x604c1582040356000c01410340c001d007080b850740140e09003c0703483e41084203000400c4c0310000c800542070203060b07450b9099200c04074400e085041012891240100b20900600380041c0c44c000c00590a42400300c20440c4031006a169a425a464a65000c010084c10b0b07000d80c040182c02c00c810300c400c0c1c80800989000c0e142984824400b4034000c1c17107407402c44040302d002d28416030528101e820241c4903501d400c0451441501000c40c014490408281c140480c403100400e070340d548a0000e010755600451039401c0d40d01c9441c41601000d54440202d803040b441604542064102c0742c042650b503e028401400c52901910b8503034203200c80354541c0b500c1490100c0b20b00c0050300c10300700940306502d0148100004407a01020543c2030394105010102000401444a402420004007007840600300b0421882c04540c1310030240f01c80302040050580320380013a203041040c0102d101860308614000e0b0391810300f40b140600140055491038004481c2241005a6000e01c0c5028400201d040d03030725806814800c0703000340030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 272350908 1250 272349658 272349661
    0x6020307050a0806030d120b0d0c03050105011e08030301050d290103050d1107050906030106230109090b091f051c02030f01060b07120203090901061d10020a150e0a0b 73
    0x10300900002041c26100342c0025002c6c500103a08400c403408a584040da0014062561034049440740b481c01c5400740440360180d00000400805400650684400300c2001200f00844003038800c00344018006d440050f0401d1005001c0340c10001302842002307005d500103810883c2c403903072089041e00d046032407070b00040030703160040c000d101c5c0400c0086110a19072410b40c0081301e0110b030903510384000c1c1c01a244203103034910108610b0f6800350481000f500a000000401807844841418803c0740d10400f075000c5440300000040d03000c3e0501c2082e00c0d951024100c40059981c0800c003841004031400c140c1081e980181011506803281c0340c110341c0503051b18682c030303542400c1801058606100352451010680c1059420301420403800142da80107540980c25003540051880c09034258019480072642201c00e80b0000903405d5880060000600309854284104040d0030041c02100c40c14034510f400541d11002d5010001503841c001c21460460340341c40068a00845076006080c5148898260b071040a00c40 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 272352158 1250 272350908 272350927
    0x323070c0306020d060b090a140303130602150105010201090210030b12030a09081002072301020c1f0c022107020f0d060902010f03061d1905010602010e0706031a060310030602030705 80
    0x20400e001b40a851071594104081000001c01017200c6004200d580b035110440c00307403551010001d548000007440d9080d5803564690030003d42da05441821220150011030000809500611900c486545c001c1c2030740740035142e400340c140c0184c58160100354001d2100106030b05460380034000f922015485d80d9803080042d280002c12454a42c250078040405403042100c4000214500c10f014120141c020b641c0d01004101d02d6058024015000e00385824000d405902c201441d449905a0480301540c00030003501c7c034104400c0307a807083c240c42034100d45503020384000164403040e409002c049200038800310340e40e071203000410f0040702d01d40011500d568442221804568004e581000340140e14a4100030300c40c5880c000320010340d682c00400e4038801d2410082005404000d00aa500c4103158005210a580d40c0100070b000341403d0603c8030403401403803c0400c1b4540f090088480c031032008684210304180c0702042280a9001518044482040c00800000154503001951081d48d8a444442c0c440c003800c0d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 272353408 1250 272352158 272352161
    0xd03050924040204090203190303060302100f0f050c251409090d052a07031506230d0c09020405040b040501030b13032123040323070c0306020d 63
    0x4620744100309180040c0a541088012032280e4040e0b0103c40115100b01355002007820000d1901d0071400480190501209043d05900090201d070300c2615007001000d01007201712941107005807050b0002d54804c1d102031002c1c6c880c0e4040e05810510350141d9984a01801400032003000b200510814803403200402c22124091000c10f100003d001c1c0ca0300019454442c00c503d03102e44410f6849018000d0120300c410440c41d510307003012405204000080c3c0c070317401840022a910b03002888101c0711480da481e40900c04541038001c6204440542e0035086100410b0300c00c05408525a41c002a0002030185c240d0020451250098004004083c0c005907103e0415051000f61842d40640500840c00c00c1d0040000a020b284921392008004600903d0380707015142c02c03074400746074201b811301003003e041c8202c01d03942d095840008054580c40044240303140703081454041c2c0c4021034011b40410b030003001c05206c028200201d8000fa01c05841124907001c0190ba07000f600120b16081683e07119400324a03510640718a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 272354658 1250 272353408 272353423
    0xd030201051807050108070302130308120a0506041b1115010b040906080105060618040b040c0f020c0901062111030406290a0512010b1e010807170406020306120d030509 74
    0xc503000e0f00700c040c10500007800b100401703030481c0c0c101a800611489400580452000a5540911090707540c100c41e410b4042045815154482c03050303e002c01103421403901788078440b000207011800381c40d410074042d4259200801c1381c5099803079008070820300101c042451042400380211f03114094849040c00d01c842e00722641d5800040890380f5120501145966500c00d031a000c08449140019090b40d05c0e0201780a050300c0451517400904004200102e107800c0822660410348d40d07809c48004030500340401403041803e104490100300c041e030310515554084154080c9250444902003540070742a4200300840c1d108540c2515919076541c81055580f4603400c0581040800600000000c0540400209003019034070070340e40702c4e00c00030b00f4995103660b013908a9203610000500f04100d600985200284072110b0300700c007a000400c0310001403a001d000c0d191203075442d40c0c0540c800c9002ea95079507400000f503001516065001040954080c40c22804010364440407142d41c3e0301050030b007800034685180045 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 272355908 1250 272354658 272354701
    0x30e1917061b0306040b090f011e030c031419080a0915020705060d18080702030705100503060402071e140f0703030c0206071109010b070c0902030f240d03020105 71
    0x2d0005108000010a81079401041c10701d6803074403040d00040003030580d091003540003540c40d0b08004011104118842c1212403180b030b1000c41c03440b04032024105d10001e0100501000e080c030300c18030104603542c1001d61050094012500c101c683c503020b48114038080c1c101217802480000e1404c40d0154862100d800070028582801000405001d0107503d80c44140500b901594012034031a040b1841794000d0710049000d18402c1c02c00c041c541c00c11050580c00000f040e8040d00c1098800240d5040810203022250350070750b1284d00310b80f02c210412000e50302000087d0341d90b0400a40800c80c2548043c0390300041449911803050b40f442d203103000c07070074610600300c1e510030b503000310318100003082d0444000d145840e0304030740c440c2c0c1d1041c4500c0d005841d101c240d00413542051680002241e01d440100040c420305004001100d07005540ba8080c00c2a448200d5254420713401650100b490f40c00d5140c05801c0e0400181c2031140c20100c9140030a40740c569001090700180c0d142c0c4148100030428100c544072020 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 272357158 1250 272355908 272355913
    0x60b06040501021906060b0a031b11030a0e0303040e010b030601020727110c01060b040603050624031b0d020403020405010509010f0e0c090613030308061912030e1917 73
    0x14a0000080e458000401800c2c1300903040741408410031410b98852000303410425031f5203480d03c10010380207000b4181203e41e10340c61000b41d1803072042e160203200d10180f80c018a42c011890000142000c8403101d6442c4070003030b0580300030300000c2a58008070404a0181c100c003150b1640380e140c6040024503102c040c0d803199083c40102c0c06d00c808488040840301c04901103a44020445071554102020309224000d40c4000381d528002c4040344084800c00108104e0340296014000c68a6a00c00c001c0d00040302a80c480701c1850300c00302000b8402c6204041e5034800403c84405030400b00d1200c2070000c44c0d102c80e848100d125030020f070500843c40c261062a000d071500f070b201d80e04198140440c010386810140146031100204c800054111941401280c000500c083c02582e2101c429a2641140d14001e000842c00b02e01d0400028051742840505d56100202e03c0500e14080c910301220b942e41a8546a000d50420152031507a000984903412035198040381400803016840c030313000740701305161082c800032040d64 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 272358408 1250 272357158 272357167
    0x5090f0d150902010c050d080103051e03030a0e01090c060e040c03020711090615072409050c150405120607020f06070c2409030801091104030510050406090b040609060b06 75
    0x180e101d2121148000e4661000141c1c03009034001650b100c402604010024440c0c406105e008076800558181241c0c0b05400300c0302d007403104100c2800c141d1102d400d09030040d070003800000e613289019007222010b01e441900000e030075074031600d031004510302d00d8010b180031440c0031000c04580d050034490000821007901e021030818030aa51124503007104900414801c20204020030055907030b0050b84503030b9141e00e41002e0b54400403840c102d2018600002000740c1020b82c0011700d210414035005820790720307a00c02c020302120440c040030803104d4004040c15120f50751092101080076140e0380f84c01d80c03842d5400c50003000d0a2901c0301001385003440000c00203e00d9040002401402034120640310b40c616403001040b0003141540c949000c1e40a201311010000b0f03400c1c20b00d10402d05030000344441c180c400703502081c042e00c20f114000c40c0d414410343c44000d04581c400c0842c0d040d0050320b43d20854000340314048c0070070450220b031552402ca903019070302a1071141d5281c2014007004000d2140c0c440d881410340c0d507981071 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 272359658 1250 272358408 272358413
    0x112020c06011e080f1c09080606010804050c120c0406050d0b01030b1b12060f09160e0301020408071d0106080c03190f0c1808010603120f0c0b01030305090f0d 70
    0x4a000610540e03000d1000c00d4108a5000c203d034411101070f0408a044912548800c4016940e48415402284c2611101c0311942d034118460351a440680e0801c0380104456156a40115402d910041041e2018014844101000e40d50101c42043c911445002440d0103142007040000300c50859101d40c0c840c4080500080c0003a05010340503044a0304840c80000c82d40c1c64140030140390400c4c0751641c801e40d500060007c00201c40311100d900801040d2000a680b40090741030013620101901d004140742a80390f05040c2451041d0011042104064000f50400ea41c80d81c41d54642000ca400508200504440640c28a003808000c0d40c0100441c1c5030419480c2401c0f02c0580541c8401703890b1404510503c4144903001c00070383c01451060151100400800a50320b01c02000c0c0d0700500201840343c0c3c0110f00005800205001d000b0a41380c0214040300392107020001582c1084803440424188030300000454085040340310640c0c020f6009840362941c03040706804000503006400030b241d10481500941c20003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 272360908 1250 272359658 272359663
    0x102010f0b1507030201020d15080d080702060a0e0106120317090c212a01090b031e0603120c031b1f0b040b060c01140c2502042304020112020c 63
    0x607103408040d00c55944400a003000c030f01920480b04023410260070881c3d0004405804600e044c2200c00c200306031003903a442150201c80341e900540c1c0b00340046e4003000105d90b0f441405d81c44501412007040c00055000d6903000b0021401039010000d80204408040d00c0c03010245408016512507181000b03060140d02580c00640090f0913082c1403095181c81002084100348100701c20014012021141c0444d84a0000c0400d403840805030071078002000d17208001a5080101c090300c3c0500f0050000c808a890a00041c00c5480402004154148518140c0b4008244180010180e041c1c0c800082c1d903655550000d481c0c400e07034010181004035030010b00da00302d2120784000e000868445028000c54204240300c00900903101c29178402c1da01082c0042c00c080c803440154804581c019140d5412503299850f90900e440e0b9005522044000004e0203031900d100c02c440c041d000c4502840144001850701ea040c3c4015070803d01403000c5021059444d062000f59a00701491402c0044060742c05d51401548140d41034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 272362158 1250 272360908 272360929
    0xe0703050d0f090b030a0e0705031203060f01030612050606040b010e10080901020c03040e06040b01050705100504051f09170316120e1504060608011503110109030506090c0102010f0b 80
    0x40400541c00b0750100300e140310b04004030041005440e0107840e03040c141d91031001402080c1149071107210307414001405040200e2401e0056041c0951a0b0940d940c00b402d00c5511440c0004150406503149030200d06070200c180360706407480c0104020500c610301001448201c035402801c15040c0024185400d45540e19601310840010a07841c1c00a0140c841000c098007a0041d809031004a0201044c0030a411b80c403000c00510a4000302c4040c8103a05140c001902c4502c2075030b501500b0b64020b4003487c0410360b8980c1100390428490421603d0030f0101c0d26608041c040e040d015106040d458205000500045000760345c1680d40c00a000c40c40c50904584080100d03082854910034000a074600c01d0300d2076000d511002034244404c1c1591000344200b88a150241011207080b208285417410204441c44144501031110581d8460140441d0031925280f060701c20002c22107041001350000480051000e10036031780140a210024440c84115400182c25030302000c4115452920b05800d14840b50f45025144 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 272363408 1250 272362158 272362183
    0xf0301030b10150c1113140f01030f080304030903021f080915150d121e02010212010509130c0e06010e030c0a050909072111090907090f021308030d0e070305 69
    0xc8850356514608030309004548000c5d60383c401070352801c5929944d22078009180f150040103031840e07590344110000750710210a000141004000104000008640000440d04076000781081c000c0750380d9a13070008680340345161403401841d21040d640948250030080c20f5401c01482005420a19407010342c903100100c0003011090500d817101000071158880c0348901c00b5480c0c008200c000311a459202c041c1642c290440000c0e9200d4550b003100c580144180300751156245c5a80c24031b10140d103050100105540301a1091200340c0d030311205240002d24210100008000e07020460b64545170440015209401d0000824000d8004588080d496a1980c281c40162101140d41907195110070061510740442501310740160040d441050810135044172043e0125481602c0c10741104007001d09203c4a0380b4140d07001008ca5001c03503028401c14005400c5000a00c1080d5401400c2103a0007038040c0b00d07100c056116100035000011014001942405a540065000c20090203242e18542da0b4560300d64082d04035 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 272364658 1250 272363408 272363417
    0x3080705070f120e0301090b07020d0c050d0311091314060406080304170307120e130228140f07020a08030c0a0303050406060f06020f0601060e0d02010509030a080f0301030b1015 78
    0x1614505018541302d8480c101c000c1d00804c4101154070306440883c000380c8017200944201510000c01c00e1140d40310880e0994030001801c0c01080c1c0c03c00c20b4010304811148034240200c184114070158840798410132140c0036119020032070142c03000828403802400350000380194100407044c07260f071074000220b07800c44403612081c2c6143d00740306036954118000c400004003030707a4030481201d13902ca034030031146050b0380c01c200c9442c0e903442105a4030382d080b48580200c8881c200700f039034484581c000710403c0f10354000c100d42c02c0c5005032055407049411541d1220269403403407140400d00c14158200348281c03002400c0100c000f140780c8214080e840742d41d0b024030000101010b0701c50001408110311600f04a005042117800c0b01c0b0300b9a02d887d406510342080c0003042301e043c810311000041d000e12030180320160480162192021084d01c2e001140c4591100807801e401d4481e180890300090400c0008142e41c00034071f48466100e504610b0011012940507015000000e02d03140c060141d035045481d51507410503035040 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 272365908 1250 272364658 272364683
    0x61401060c14030904050103141c270302060c010c030509030403080712030609020301170d1706060d0905030a020303010f06020d0807051c050a2403050601060c15150303080705070f 79
    0x2c0c1c1865486002e001030b0b049400e000000007000304c039009074071b0b003118034605039450312030001081c011640041c1c1030000011440c007030018900c508854411507144000c5031205c05503450381c022910b0360b8019160201c040c1c0d03407044407500c0d45500d407041c99000515000514905441c503100c200041c0105440070304001e504102c00441140607510440043c0441c240a640703940c1e654000720400c50a088001035580a44d11020021500c01c0c03070002480b10b8a480c540c2003688a440a206407078200e6103002103070079600c00800010034010006040a66400d90003107a81e0740c10410101c1c2e400c08541d201100f9507208000092005402c1100240d0056251504646806400294980b180ea20140c01d824403440c0c1010310002000d15000303a0101c00304040c078401c4100246150340390020080c80040c10b80e0704030600510500c2d00c100c0c250304016000d07030140a401d032280014007088440f01c5c19010090061107400b0010035811182c0c0650100c2942071150030104540c0303c00305500c0c0c00a40041c01c80040c0a07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 272367158 1250 272365908 272365943
    0x140702010e0c130b0d060608060105010e0f0907081306062903070503060f060909090a14030705030d0e0a0b0106020604021509130c0908010f050108101e09021804050109061401060c 79
    0x41c001c45e000c40e00301ca0241310f0b4aa507680031a880b00005c0c025280050031206600d40d0604084040300c02c00c54014003c1d41041c1e596640403103000d00080d041c0d240302404820b141c4080b0b20140542000350204d11f0b0f4907600821210001c40200d503012070202c0d40e80406108101c4001c0d04401500c0e2300880503250008989221070009800344034064403141d101a00c1c07010f001e106440022035016440c0b1811200344ac01689248090341c900450304011700c01d620030401080190682c4c1c104082c4440c1c6c00086030012903440c0d85485801380241c00000040c1e01c203030100b1003945055090481010f454004091400c0801e0380455609660407000707615554507442d02c517044070702c903e1031070b00280306190003080740584914545019040a01c02c442880c07041201c1250891010721075a042030401c60409013100e80142e081401030010b841050f83d20a0303280c80027200640c404841036205610403400041c0c4401c0d54a461011100d03004030550b40c4008450050200c20380000d211640141c0051000380340c5002e40 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 272368408 1250 272367158 272367169
    0x10801150e090c1803120a0c11100c030e0406140609031204091a06030921040803040e0402010206070e0114070c180603030f0c030e040c020c04140702010e0c130b 71
    0x4004941140011040100040b0940040c0107000c681c550141c1e15135285404165858803010a0210158010028004440d00a0300c080103598030500d11416118601000141c0080d418151440403510b845150410103501403032164001004540c20401d503828400704c010382e00580f002c0340f80100d60020300440607503410803110f009a104250419a100d45035000301000e850040c010700000b904202c0c3c000e80c4d624200c0107592084480c1b1004000105080d1030303190b15110f800d44543c2901c4401c10001c42c801d0002c0c001000905001290803140707080c01d100080c5807442c0180340741d080010149107072010307a90121001b494100d061502c40d40302c0c50181800c00b100541e99000095014002c01e991811607902e0700404210303402a1500044241d442d1020b440100200300c00900241c1c20f03018840980c0b41036440205000d5441c41210110210075001c501290741c150021380040d5031060400c0b00095090240210030103510025010104030000810074000f8a000b4042c50603898040100c4d4a4580703 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 272369658 1250 272368408 272368427
    0x1050307030b0904060605180124170a061d040f080d0b0a080d320a0c0204021303020307050103020901080f07110d05040303022a09060103020f04030605010f1401080115 74
    0x1c003c0061800c1902d05900102241e11403180901c09a40100103d040c01c0e80c0740343e040b03811031220b13034510741c19034900c03048101c0303868a801007405090034115007003615903400d85200b4020714900103515418110406030119826440f100d0b085081e1041000291070040c4542e2500d5004106139140c0c400001d04501800c0f00500b025000400660001034800001800c2c420341c0361242c40300d002000381a810080740f0007030030107426840d000e4201c0c610400c02c603010040140e00864a07210402100d43d81c000360aa0f40318003084408120704103028030540c5000d220b8400140b1090030308510b003204d5140042d0845000800040540c100c600000300d08030f00482c232044070006068260382284100f02c00190043d0800d020660045c400e64648011420034800010115201d800c42c1e2605042d46e40b08000c80410000c0584d81015003c0c4802c013540c880d2040940065803082402051030341c18450810400c02013a13000310b82e8440d4040c82c0301000d907006884103055440d80100001610414103054401444 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 272370908 1250 272369658 272369681
    0x80114010f1d040c121104050d12121b0311030105010c08130f03081c060b040b1804060f08010f0c0507020d0501021908091c090611070305010204030b0f0a060308090105030703 77
    0x1c04c034150b480d05922848a04105084000410404002e68440f184500481c01540d800c40602068040402d040ba1001c500d00c00c131a10b4070103003c02c0115000e6080c0c03800066a11904020300441031400e5406003c0d20381d0a1301001492030641d85041d000800c507109082001c0c01d040d00004c0e0188803e03510300f010744040e0100c0064011259540d00e040300140e0b01044000800c1c0034500210034100185014041c100c07154403180a051500301640348030140d0180c80a8100605c2114016a090301da5004180042480444410026180c814003a0a4030255159500d002e4600910910281e410209450205405a07141244200b0903d8018020300c0b401c80300052140c419060321205a62200c60244954650019200300c280c4103900070b0383e40d940c0c1e02c6003803000c83c04610040c8950741c0f1614900b094044d80780111342036030382d0741d444440c01c90740903030002e56425081c9002c005060301d440082542080034070208001ca64a1610f44244601840c1c070003904008000000c104064825000760340150f6 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 272372158 1250 272370908 272370911
    0x50304030b0f010b0301030f080a0201020903120d0e0102310803130312050702031c0201060f031b06021609020a05070212060906010b0a080a091b090c080114010f1d04 73
    0x54a034109495146002c60703941c401c0030320510000c41c60388030880c01d80c0c0c1203070303030200e04031560000302d684106490300030040e600110740d404c0c021811241d03400c008000070b01c48200206aa02c0e900314240310141d039203504945152741e0040110851042c00c1451003201b40040d07a600b038072660300500021030012182d51104001d03220219a22603020b40c3d01800004803441003014460481020a0594441c0603c6c031010f0b5054101030301c1c000c0c2140483c80d803034150090900c00003a209494410101c8501d065400c1075992100c000c5114000d441c880d0304c3d600103001540010032004942c094004220503003400350038001c1d03401140e1114083d01500607110000d81c02800f400e03100c42d00e0042c0740e0361070301c00301c0d1103107058826180000380c110103020403503800091039542c680459803407100010203480c40d503004030340000346041501401c19507035009802030310411001290007101043c00505d08601a0007180000e04019000c811b0743c1e80156003001d14402c41d081590200320349403000148070400c01e880300d4009 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 272373408 1250 272372158 272372167
    0xa0c020a020609030a121d09090c0d020a09090506100e060d060c031d030a02010c080714090a031403030a0b09070512060111100222260307050304151e050a0c0804030503 74
    0x5030b0070609856901c401f8031440c01e50311100c1c5041121584003a80c01b03805035005882c0281c0c050400e42d001c00b2030180090001040303d90390341890422175514800c1039070913800400510145000501004000300f0500c2c8900c0c1b200d062003000130b0b00515203100024003031030355540790805290180c3c002d24000c40258440d100384400990010b0744a41c000401c16006501c0c011840300d400d40240d072140d01429055540507251001e2025004a940c0414407035580800b0341c80e00000029860507010310300d080035901039602da00709460312109449880d00910302c140c82002c2001422607026040e01c602140303440700925140c482c60b0050700c641d086114401514021200c1524600206400500c562801c03601c503124045240c4001c424038810074002e8405000314010032240f005c080d050050410300b000c505070f82c585056980c0c5c145c40c1d80c0c010780c0301c0c03965003c0c21080c5011003070304800000c0030103c0650380754500c500c006400412521462003128244203051444905020f1340350144c401959000f021650707035 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 272374658 1250 272373408 272373443
    0x120c1e11060f040218010f0506070c0509011410050301051008040201031d06070e0409020d06152304051e01050108100302030111030115020304080c13020d0219080a0c020a020609030a 80
    0x125002110141e000301c00d1102c03003440b0020a488028100c50704548494040c0d41050108101072b80410000c2e1414042d1a40120320382d602d50415074001d2402c00000c1c10b41e0354020060051454003070000c1d00c24030500f07100400076074840c55060510503d0300d01c1c1408140d0307290300c0140c0040a090001c00b26030342001e8160808001d0010307549015200310707200c03003107a50300d031004100c25520b50840c000d4011101e25540740028007a9003110f0b0b84908415a0402c072503403a00864440c42280440035211f148440310100036904041c82840e404c00314406c40c810716a03403045041000c6036011300c5068100105840000c1c040c4001c080040c0c051a8020001d20a1169098216120750020301550100500c0701019400c11400041101d0840d00e040000d8045030f2008410014a040d400900000321078080080c009007040320303c018409036600c02404482c8071020076004100400041c00650114540011340250b1600001c102246039411103c4940c0c608291022034200908080300402208045507920382 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 272375908 1250 272374658 272374681
    0x70c08030711031b1807050909040507030b241210020d0f240e070201021903050a0b010306050a1404090501020313170a050a030b0d120906120c1e1106 66
    0xb41d030422004ca40f001e5040c0064065a0f40540d424954001d001e241603007071600c039164400c4c0d0b1080f02410300e1410300141d10007043e001403013258102ea040e040440c05100300003060400d9500080503410780012000740c3c2514003400600780300c26911428202d4080541c40c841000160f1054100c02000d43d00c0300c0c8548080030280c106588081002ca00301904210205803a03400314040c84014810000c202d440c100d8614201d00e0080c0000702155000c000c1403401d80740d50705005218011035600021186010210f030740c1110b00380800d80c1c2c101410024100b0056403000c00c80b90598641588a0382c1412090000030000e005071036008005500200c2000340c3c0c0f51003688200c1030300d03000f80c0c050f1214078540361740b0007402d01c10b82c0b181130082401807142e0000e080c401c1c0d0216144450281c1141e0081109031250040071000d80c1003000090100401400391030b03031040445040c4010400d042c45070144009015201142103d05011601f102c072103030801151054078a101216807280039039001e824803824444 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 272377158 1250 272375908 272375933
    0xc1b01090204021606112b0905030703090608060d11010f02070905090a17031012031206080105071b0b1f0306090b15030604210c08030907060306150f05070c080307 72
    0x407001454100d000054030440001c803000b030b452000352100806007c894001c14803076a000d81c00300b0555104c0070b000c0011800c00c01000054040d485440c2414a409002030102c2002440c50303000c2d00d1a007901d9000103c03041c003144440b90f402d0070026030701000743d54120701d0701100e5031194034450b00b810f061042c500408500080308a014100c01000521000d41c813801c244002d07146410a2001d8010820000044410f10081e4038486d28001406050030000c1c942614441d42211102d43d6594080c00707a00340c1c210110031240d07000303946220f50424080e1038201081c10024030000c1540c56000703180c0b40c10700d0001030700303400785622403810070000d07480381071411314140c08803a06100300e00d105101c0101843c001400754401c980c00086080303000ca0300d00c495035102c01d20081d04e80905c00e00c035054a00042d11907001d10f109201000044c180149050380c02025244664401e4194080c082c80d82410154025028184c80c01942410703030340d5009030b2a0408140342c403684900b00750f00020890b0400c01110f101c030b08 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 272378408 1250 272377158 272377163
    0x501020705010507080d0b0609030115050306130201021509071e09110403050c2206030f0b0a020f19120905060f10060905010309080702100c0512030c1b010902040216 73
    0x4030600d54840d00103585a00c1203200c00f40c10501d051101480c0c00526401c41400060701804d441d041c015408042801d58010701912512090903500038001d0341002c0140c80d902441c0c105e0000d2080324540c0002c0e488501c07221442900034410000903c0250301040702c200203191078a60905050380002e00c108694016004402019090031240e42143c0c0000c810307141035075009405030450f80c5e640020440103081004500d40d0b4044070050565501290344194030085020b41c2d9140000380561030849440c0c00024080c1e1041841841102060252801a50320340c510000304503228124541098945511421404940c58144160101009008103030300b802009000c085204e5500c890034040c01d40034050003601700040703290608004a6100e904003204890082141a2828089030042003441521840e040e000c1480d4114070403c1003010486100d6170884400300314111300b0701045128584c49110040d0144110050310b030307090040b00b9130000d0300c442d82c0140b0441d03031420386003108800c041c84020300303 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 272379658 1250 272378408 272378413
    0x2060304081c052502011103011202030708010c0e010f0e2d040603020f041d011d0f011407140d0e010f15050f0108041505010803090928051b13050102 66
    0x42d216400b0b2034001c807806645034031081e8a00e0020940340c0600e40d01070319000340840d0f4071042c80340c80c001c4c80c2c0d60046000c0d101d00381c0e0310280700721680103052814140754020125030789805c6584214503803190105200c07200c2460709001da02c00c0640c003151b04250141810394003130140044981d09130403103107851505040c00001e954500a0450800040384d05500c0003030342003407642c9405442850107a00c14801c03801e0303070221200b1703406502c84c0241c01c64032030039034018440440380101c07400b4050030484911407001281c024008840e0b420305800c41c0307002c0075040c202030201d80250501c10b2001402510100310400c1c00030003c0c03030107001c1340c14080c0c020a600c1d8030b1501d00d090500204005110711110503100701400e04500b45a03110011603012200500030303681c200310301c003030603600403014092103000f0304400005503296800c0c9800c1002d0b4050140a514400b102ca400b031401c0a141c910046808d02020000003c00b0b684542c007400d980584040444a0401c001510941040010048606030340d070a03800c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 272380908 1250 272379658 272379697
    0x90a12050a0e010c0f0b06040906060b03040203250b090105160302070608060301150b0a03150f0f170d080c09030d05120c090a1403010609020d0b090c0a051c090206030408 75
    0x15100364160044c05402500140207400219068424854100001910010380312102c0e444180850388076800c490380e455400014081545810441c00300000c103105038602c170705450602c03c0403070b030100ba00c9090000c0c0720104000000d0703802a416100000000514554091400e2074002c2d1189c0700c501810740801c10800121782c01d030505101d40c10750780b002c410206800e64140003114450340c0000004504041d1284003030b0300745110b451910801010a1600d103c1458100003151513024000d070410301102d0550210100e64180019000701c0e034000034208100e098461190840c0740e1300c9600d52050b0544101a0140c400590080060034681100072054040d600c0d842e520402903c036480c030035548008080014031000d80706000c45440c110004000042807a1f9801c0c28100b0f80e0040a00c2d008180c1da02c004841d00c50a02141242d404400e0070010341c50801c6282c005496406001e080d000000c0528907402980c0d4003ea0141020715001002075440f407a141c40c004000c0d900010030b0445072803601c0e8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 272382158 1250 272380908 272380937
    0x305121326070605040c0f031a0705120606090a090507050d0e0f0703030f050c060f06040b030601080d110109020a0e1023010804060209040f0b010e0102061509090a12050a 75
    0x1078051000641565429103420304a440e41d4010f40700151040d500703c1c9151800041c0134400301d0010340114407860f0b800d41c0324405481c607944a044001c000000b13002080208506403804c6401c29644540c00b02c071404d0325601c05001080c41c9061642001b25201e1420052142054004010f00401d1b804000c040c024011406202521040c0245c8444400c1c1e105442c00d20010f8000e401e801c10307542d01407501c0790030f0040c0303191018945602a544003c0710341410741800014107050240552040b800d034014100ca514140e038030390381e42068020040803c60988847c0029038400c5d007006143d207800610009140e40c84010b1031001c40c8041d02c2d1b51075000340508000800d480140c400c8400490a44004050070300c0f9400152100040108112003d9508101004541d503c5100d00f016901141e40002889103552002415040c00fa000e294150750025081040130003c500700310382441d0041e50100025200c07003481e40c1c603051058500401c800f40400c2e100c511640e02c00b0140210300540e0f525000000000b5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 272383408 1250 272382158 272382203
    0x270a03240e0304050609060c0106060c030905100f03050a0e010204080d080906090d0810051207062703020d1406190506040501030203191410050a0507180e0403051213 73
    0x10003020b07030018002000b003440c151000d006d203007802505031840c0c4542581a00d0840d030b0b140d00214045003100038008281648030000c6800350005032501440072007400405424031035618482810561580c00052070300340700342c00c0035058081c078000035501c0d103856040380c684801440584600044c0001c00040140100040b41c50180c1010700c0940380400b1004021101d20070020111285807140d8880081c50382c88410041010203198000b800c0e2007130a2110041800b0000d407140d98010078203101e010718a09017060032104980e070448507020514400c1c40c058903019604c49952419015440c2088038007901100c0701e07240e6581c905400c1160760780d98410032040740c07000c1c000a50594844454801f07104180c13080a08454001c602c505000014104801c0c940310343c1c2014010b00b2501d60092110704205030141c2d540284060400d000d8201132022420107d056500c01c40c0c00399203221300820285802081100e080810800c101c1090b4a0a07481090948030114411200c052401103010b90b1400071 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 272384658 1250 272383408 272383421
    0x209041713080601051017130813062006060f24030f0901110412031808030a020102090102060f09030910140714060a0c0e04021e13060906020303040305270a0324 71
    0x2c11984420030744510800f0b51888c461381c2030882e4807103810889215445240106075000b403200b07a440a87d18000880d03003121181d04c0c0203540780d00f5031054050020599846910300042e0005503a4411561040d1056001003031002480d9560308c240001404101e00c1c217500c03000d12841004009002e400c07444442400c05104600c00e14014103032000c20301001920a240e40781d400a0718032041028140c0380c15100d421507014098050160394001400c0c7c0055806110031170b440207068030042018904807405984170720412112a01c100181c490442e9001c0c000c0384c3d551802c184c5402a0f90320740c106442e004544150240c003601c1144110b01c00070b0950302242c011100400c07242c6d0b40b410400007101003404080e41052251401c40c00c000100e080303801e0080c5000d0000203000d149481c1c22680303440000f916030a55a04400110b40041040102080d0002c00300c0d140001d400441c0105480d045002c40407010300c1075100c40e4000000c017400000c0c440d1079020104004044a60441a0048580c240341229103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 272385908 1250 272384658 272384687
    0x60106020f030315030309130b18160e01020f0f06011d13021c080f03040b060d050c06090a18060303020d0504050f0f0411030a0603150902090417130806010510 70
    0x304002144e1404da00b0f0941d000c42805011070741041005000a980010540b80302c0d41881d42e03542d00c20082c1c0c80c0100d1246110b9411001410950500a2114032000b0b10580c40800340301c008080304545034420080d521207265154240c03050070030300302e45d100d880b840c2c03e02c24072902100203040d405454264041d441e0041038000082c03807801c0c80070390034004200141490030302d03820740c9140400080340340343c0c004080040850050740e5981c0340c00d2808035000640601283d00828005011400003400051031852810302110a2504c1c0e4103050300044080240d80c004054803070f050500820f141030241c000c202664402d0702070ba42004407075041161240518072400e94070183d41500075421b4100f010320259540b80152000c01c40c4007070340da48414254029a80c91510582c2d8150030414010040e8551004410100042c88201d000780c000a01810000d030015100c100805142800b0307001940856192001030b401e00c5c98a10b580c0c0300200e0b00c480c2c3c24402c06020b904444980c1d00014402d91300e4008002 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 272387158 1250 272385908 272385913
    0xc06070906080403110f0d030b0a060309020310020d060b0c0a12020606030c1513081507140706050a06031e1b0506030106050d06031a0115090b0901030e01090221060106020f 76
    0x1d83e1520f04581022030044582e0720340c018006946101c0000b805400c007200d58984020403407a50f844144192880756600400c205413400c0c01c07500050764082001c0044140503e000350315866001003c8005202c598030441c040c083c0010a43c950b41c0000c00c1d0100c207d07018000156441461000c16a2555022501d6a50540000b52009070307a02d44030300c0b4001c4060003224460705041c1c40c0c0c862210704109175000792115901503807074003480781010a51076601400a140007151b4030203188019a55000f03549000301125255000078584001d01d601c031030003c50b0040001e41c0050040344038050180fa094405513400c03140980784100342d5200003000f000b10365020700454690b0307291640840350340e0451000ca103500740d200c00c0004041240f100c0075010b0344080704516a0154076010301000303001d00e40103790003848045003081184850a4055921138a820f00700480c22850303040e0082d004040b0654000e520101c0704e01c1445000c00400101c60f0070001d0b40040b1200c80e40c0759981039036500c1a10380d0071205075 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 272388408 1250 272387158 272387161
    0x8130c0b0c01020c19050d050408030301060c1104090b15060408030a0c0203150103061e0e070501030510090603060b420c0f01140106030209180c0c060103030201020c0607090608 78
    0x448820010119140c07240001800d042c00c451505050030400c0718052100c0160000c601d040c48824800420420603508065150a2401541075120300052080b0000d0001000da40c8040c001a022003803a2501c005104000140c0c09250a0021400c1540c41c81855003016401c0f803e14148901243c095880c80c1005500303240c50902c01701c50700050703c0c004a80500400c5640c0c41301d407841c05091400303180f05010100d0f42a01d84403404560040c1605c141008504100d1460130015002c6031f12401d030b890030701c0c0108007541c0c0c040300d00c01e6060f4203030711403034080e03280c2040041805540d80c42006610000c8612101110340301c030550322400f0002000e910b0301468940240e40e07820b21442c04035021001100035600700000c0507402d07824400540c0103a00240d440c0c0e005440c2c4807007510750840c09411107050071400d01e058540030400c10746254070310640c41e4540c0804505240302e101305544e03a45a02c003080392a59a101e10f8028040d4001112550003032040b000400d900c58004c12a101c00d40701c2603501e02029 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 272389658 1250 272388408 272388419
    0xc05030f1510030515060907031b1101110a031407050a05030a05130807140106060f0207090b03071511010c0912060c11030c07031106041d0a1b03050708130c 69
    0x1802400030b1022068664000000030740a1080e00001c02c400580c0441e00d152100c00d010f850100140140704043c42c06c10800c5100b000502ea081a017050b030315003c4058445521034070b00500082c170121860b8040810050500c59142d04240e51003403c841c08911180c482280580b07150089801340c0e00424003d000081000d401da80c48560b20142000c12004c400c1011b4944a40e540d204076825204102010300c0c902806800740240001030038249081c00221204030700003506c0d0401c900a026813261145910310443d60108207034406000c0a2101e00741c404400c41c0c001c1e103c1415445006a15402c0040d444882c2e802408031000300c0b03149030805d440300d0b00240d51b500300400c015248482031200015414100013420030103080550b1140001f81440e038203508040c40c02207202c1000502c188020003082c07001c100c100c2944060326501050401c07854580d85000800b0b4066022943d07401d40c3d590001144981d4190000b030301a0702d40f07895140b581e8079501560030b0030180c1000c0c00791240c195030004002 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 272390908 1250 272389658 272389693
    0x100507020325020603011d0907240e0312030f0c040303090b07030512090c03010608010e0c0118090e100f09020f240d140603060103120f0323040c05030f 67
    0x80360b0400e185206442c80340c0e0009101d5002a008030b031010b4110f540d5a40c0f0040e0f8080d00d036400201c254000c10401d4540390b03a2001c91101501c4941000000d41d0700c409030180551448490f2400040c26159071600a40c94144180c00845e185031500c3c100d4808141804032960480303068903010350301d05d20f0240c00c00005000f140c1c48640c0c11801c000c4100501050112030f4203646000d01155400340c034500510808040c2507900d160010440d592510246241c400c0b40082c5c40084203201b820b010200c2101d078080c512500c403240c1d00415009007010752294203041c0101d240ca0307100041000800c0220301c4030311144100d450b80c01c0c0c001d410111202005c800c80c608400740080c29005403080051898108015284e03e41081c0300741d081c00c907182c1c4150543c00b07601003145c0780d10403800d4008003d45c3d80b4603164158420000c003500c1091040021146a5103842034004004000e421751035028032251400320b00940d070030121010360341c404000c40003141e1071901140710841d00140318002c0c0340e00d0120b0035a621 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 272392158 1250 272390908 272390947
    0x10306060804031202180301050405100e030a09050d020301060503030c010f050112051b060d09030503041509120c1b231e040b0402120106020604030e030a08190210060f081005070203 80
    0x4040a5006c4802492a074003401130a1140e88039101610399085a500004191250100594044d800070b01c40440a2507210031040200d4000315500010305045001090041107941c1189425010016400c0c007508015003103040d4034100c0c1c0d00d082100d40c0e69140140002045203000a0440c1c0002d04500c80f80748810700d00040d034010080072503207400e521030921022030725000002c40201e107000c020481840a50707044891031403240f250500081c0c0e01c0782d0311441c600c1c1c40100b608007413100d10f41507030040c003e803e005a0b03940c1e410f4151003600c2c00d88400ca0b52031652110ba00b240c4003403040c80d101c50b05500384005050040d149540c0c08082c5412000100800307850910a0035030099403d0003080000361590007428001c01c002d4003d040303681810304000f40b10b6064500d50078020381c0152418000180d10000710707603031405030a51005550381c419604900700884484c0c4494802e08100c0c01140c10b140141c4070a046032600c1040722141c0b502045c400050704d1003200c688016800c1031004030482e5041c21b0526 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 272393408 1250 272392158 272392177
    0x180f090d1b0507150f021203060f090702070513020c0f1f180b04030905010225060f0c0c151106060a0302060a0909020a0909060e040f02041d0a060506010306060804031202 75
    0x2182c00603100c4a802d15a840d4640130107002039191030083c400310740c0502a004024018025951952070041c0200341c0200e5a000c1040c041c2448100042d007203482030000c030b4082c0c20003c0400c1c480d100c1c01d0200b00c010f50481d10300d41e941c03400741352325800e520315001034100603000003501580807071b0826110744d80060801c80300c01d454030705852014400240c540c80c07059104030300c82d441b01c00440b82060002468001114a1480d02c0350000101d000080c54000007041100c9203840d00c0c0c1c10400d0420411295640309000040c85c2031441500403421005d40d10120909050556030720307840c242038615213aa900d000b9942590003c4542c0300500c054200766000300061543c074246290990340d1502105c2c126403185609400140c9002024400200280540b4004106017444450f040c1481e44400d10560902c0c003000744039903941c01d0a542e55240002215408001030340aa90010506003030100142400315030b0107000034648031003c10344601a11015029a8040d56014211108081900002d41c0000302c036 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 272394658 1250 272393408 272393413
    0x2d0b150405100e0105220c0c050f0601061b0803130501090b0901090309060c0519020a050414100801020c03030c0f0405121609020406050703050f09180f090d1b05 71
    0x1a406103459a00441c1d02440c80c40c401481d44a00d07001100040308410b0704020302c40d4480c1c400401340c148401c4601c0d150503503401030005407160014001c2d2681052800020242c0c0a0707800c1c080418040415071a0481d00b140e01e40e2440d0440e41c00038a40d900c1c0000f030005107450000e001252500226400d810034142c420340000404072001d80314842c05090866030240d5a80d180c510090416600c81170307c80c02170486003400c002c000e1300c40d40c034240c51380030084401215803a1400c03108159a83d00c02804000d009c0504108800e0f802c03a1100e5031981402c9030301800d8040d000000003210401407003215041c074074440c0518159196118462883e0b44560794200d4002c90078000413609980340c01e5610054080e643c0140048040c50340001c4100c0c0481c0d02840489105000030007246d83c00030100c2d44216810314100381d440e440580101d102e40504101190401001a0000402009804800d000b03101244003d501a40c4201000303a841d04814030100010b4400060a032030180c0c0e1b00005030019115906 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 272395908 1250 272394658 272394691
    0x60903021027050c0603100f050609090a090f0209100806092404060902031504050c04092012100c1202210606090d060c0f0c02151b03040603092d0b 65
    0xd12540041c0d803009451507e601d01080301032910745031a801828142c8940b42400a180005020700710002c010178000381e01c81002904100c442c00f03190903041c0c0c1c000c10f00044e03810326902e400c00002240c000d81400e403051001081d4900ac0000d4100742e44692250904100401051400380d1184040c0003162465155650000141d40c1030164031028401001400180d24042c20800e01c0c1c44a0032a800b030107286007482d1040443c810040340000e00ba40d00f810100c0e60402080480c8070480800d0780310b0124012400c0308580901650442195810035590f00020b203500715413154102d224500d903400c141410400c01d4000c11a856030443d0b0300c4080181000d091440800201e002c1000b00b503030481e050342ea100c0822001d40d400110030301480e100c61803d0381c1d0b80503c43d4040303a0000d403105820282e0380c40c041140d05090820300840c4000440403002d694270340c0d03560100500a0100300740b0803108404a12000f80d038000018003c1032041400c01e400042c60602c5840340c4400d4100a0103182e0302e40f80c20007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 272397158 1250 272395908 272395933
    0x71202030705191106161202120d06080606010503090303070e061207090e0c09060306060c0106030c0312030606030c080703090501020f1b010b010302090618031906090302102705 78
    0x3100c04021007003c018500c1e003c01038548540a1000700296620441c8180a54240c00d20006070702c140342640108030041103d1101404d030304e048006a04c4501e00c82000450040200050300007004841c004401c440641c0c80301d000640c3d450000315901c5049910900004030300314850940d4000017803001c2c1c0800e00e041c1e00500e0300220f00d1000c60312080892401802000b800c0f519140051b8884019210903041044520004216201c080c244034805c0001140c054401c02082d44000c00840d481001c0f12a100c5e5685403040f5003815086212002c00e00d442c03800183e20380203020310f0751007111550310b000d01d0360751700e83c3c00b030b4010035421f601901d8540d824412030030425459001803040809101c8010101c1100042c601c0c01d403080701520a0406005000c10f14080d2985801d0f80c412075000c0c6007602006424602003881d0542030300107403d03942820700d103000a212180e0302000300c15002c1e03400d0300d49603010119000d02f80c900030891034980794038a181d180455036002040b0700d4400e00c184296407445110b070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 272398408 1250 272397158 272397163
    0x303181401050f1f12080f0307080108010c031a0105030a090822090903050306120c040504150f060305070b220f081903050f03150301050c03010801061406071202030705 74
    0x280003107030354450500503c06040050140d0100802100c148104114503451650108902c1580b40c1403820141c482e08010148081d1000410203080d59030b1607285c080c4006100100c2032040c8241540790071342c81c8107094801d00514521313600c0b80d4400d40c2e05844103401124035510007080785810360303521714140b030005200c88000d0240004d4046028128503030703241c92400c142c109601c0403260910f080b801200180d0040d050702d44c0301c40110b8a13a0380c10790104840c14109103000300010341c0700d032502c4204070030003c00b01910041c1a00c2284c0400c00e8140403003e00c411150306000c0038100350b01103001000040c130007000501066240300f1841c0051002010107003110981508428494000b940082c08001d900b007049070502003140c01c007645074140c140c401034210f00c80c1341c5141403108030000003d07800c0304240e81c26075001d1b80c0c040c000304003a203048600021650000c1c0103010ba0383d400c0880c001000c00c140700e2a05403810700102860314000f810ba07160340d01c80b11440d00c0c180950009001800204409 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 272399658 1250 272398408 272398433
    0x7060f05090f010e0706050903030c01050a02030703230105040b190b0a170f040807020126041b140402090a12120e010807120504050c06040b040f050409030c030318 72
    0x1042000300303290a01042150902218080304000c40c3c1c98400d03d040865400140501222444e060465581c8519401700382140326000c03000d00e00358203010500400c1e400c0380e4011841131950b65010801810540000b50381c4540310990064902c0b410001400b892a107075004c0144904010a03c0310b036249020140b1281c03802a5000e110491030101e0200100e5811010481d960f04100d4012091458092541100800d01070710181054601055140459000e0f0340e0a141105511544c402d84120318002004c059600b290100c5075a20644460454401200c05090585511062101c401880340046c40000d4100081c40b03075021080b100700081e152903510800e602180a00c0201c1c2e03000c91142c0300a848040300c2c103059810405090204070b800380e401521009031300400c50011440b0b40342c90800a16001c50a407000c1d920410014001440e080490014401c40d8404c0d51214542540d850800c4201c82245034045c010420007910b000c0024829440480502210040c03100160010b88808520318203 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 272400908 1250 272399658 272399681
    0x9090a0b1011060f010303020604030c05070906080d031103010f140a15081e01061b06290901080705180408040b0a030603051b1311220501090e040b040201080403050706 74
    0x142d040307411101c0364041c07110581c0014000380c00d4119524681e4000d648980c000c0c400780070001440a00020094140014402048048800d0201a48908080d510340d010141007101107850840c100740039501076030580e8100ea082b690444449407800035040e1800c00d0f105082d96115502000202e8070703080742005036000c0e261581c0d84e00303103074500004500c254403404136400110421210042110f03650015420741e04025204203000100d000d4904900588442071031102c00c184c0074070b106501c91491048484140c1400c0380e09228a0740e071028515110b45032405074940140443c00700481d22079151142c2c0d504144030384109071505a8a140718440d6410505c0281c0000e91101000c20901038104400202c001e12640e1406a03404000f00040111152440d203c0c0c2e440d480e60486030940360248291101441c0344d03031010f16403901c3c89034100d5100b2040d0042902041e10608007103108240f4000980c4642d605c03903030300c84540e00e030303a0010755011030001d00840402504000050000302da501401c410f014 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 272402158 1250 272400908 272400917
    0x6030c0e07081e04032708030316110a02010f09090c080a0f020a0e01031802120f0d05070c122d030e01020309090412050412030f1d010509090a0b10 65
    0x702030308010030a1002a04511910241440e002d107441a00418550020f41c10b0030400141d1000c40c1d54503090b02c40b1440801440e04c0c000f180080e40e1000440252300ca10b41040c0800c900c4509014261182e01101c010034980d0b502c00081c040055006001400340ca001c907080141c0c01e2680c4207200e0b015a01e0b130340745000014140e85c0c24044a00080e000d2500d8003480f0705401d40c20039120707150003010b2014126401c0c0c10141c50b803d4120588099042248105401800c1d103650254020465540e07110160b8034080c40d80708031100012201c1c03188094407069a8021100380c0024a40f0300e01240850304200140c07110510030f115090000c000c2064401034040c15114520340407014207002d0300c03101201c1080d90641d0010400e03406103035203000902e50311581c002e20032480c190a01e8800c80d118000d98000101d180c41020856007415000b0751480440a50f542e03901161031800000b603420f660340c40640c10b0206100b400000c00d43c0c500310801c9079010001040008071003d40d04006039203080041c0c0600c000c02d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 272403408 1250 272402158 272402161
    0xc051e0d0c0201020c040b04020c010c0c050d020703030512190507230a0c0609080c010203180c030c06030f09010b062b1505060304210e130504050c1306030c0e 70
    0x116028418200142030a061212039a92039800107512200b80c01d854074400e59070f41c654607070155220fa044e1001c021013070000700000761007010302415025402800b614144100c043c00003042d4400074081099075450360700c1606001302070028031416000a4100520000c112035106240803541c0300b582d2180d0807694800c400b00025a0408a004500c001e011071a600100300744105260014440440d103075102400103111083c5060851850040d00e900302e52a50000040c4010410520040b100303070203010f0706907481c041d074650826646003007404200e40c002c5010700c0001d240c440550905580041d0f00800490342da003042000500030b80c01a80c0103240300c0760400040303550a1440300404c8025030008810810303d21a840d10450002161050300c5c441c00c0f000000034200010a403005007405040600300702d2000880300040d040021300b40260380240018016800e804c4d080380a01d038003864108000e040c2c1f0030491302c28488405d0300c4140b107411660701c0340800000120100d0010b4024903041c1480381ca030303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 272404658 1250 272403408 272403463
    0x2042102010f020c010203090d0302070302062d030610120b030601091506030203011a090613090906051e1f080f060601020c01020a0b16030b0d030e19061e0c05 70
    0xb0180750020401150301c040036241403660008100c039201c0c0c00c1203842180c1101949000c03450003205400081d00b009002c100e08281d4148400311560003509034031126005c2004ca442014280011030f0415030003541c404441c80c0303860141081656405100c00d000ca03c2c991682e0119181100a0b0701c150481a500c0d0440e035801d0300204c45400103844241360035851545846501440684400b04000e00c004000980381c50076920380c4100c03119804981e101c028000c0c2c0d02d0313464070010b040a103000c4c2d54490402c0e000510466035400e4903010341c807550988401360389400c040b9007000060503030320726090701c03c0290128521104000d92400000d54400030807061a05800090070049001078050556008012039030018820100c0103600444652202c2030b00320413030b0801c5002d00341c0b8020268120410418200031305a0080445845000a032050000e0800001e9058080c81d1544180030014065022581c1021030720f5240b001c9800b0285058002041c0c1500c5141c10840c0002610070200c8640701f030b0900 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 272405908 1250 272404658 272404667
    0x2060a0506030706050913060e01030812011a2a0f06090c0a050a0b16230115050a05090604140f09070b03010e060f030106150518090c070b0a0204210201 67
    0x2071000058001d002614070300b68018003030780185024980b10754400d5241141811103030b0300c010002d000542144640b540d5905080489901500030103130301c0c84c0c1c20400418141c00d0040d8400081214031106440e01d40390075844012400301d10f80f91084802080715402004030100038901d03804c0001d03c003408003414501d01807482d1902800900d8040c00d03c54000708019511200c4600031034000c2c0500c180c0d22190210030034042180420010a855044280310301c0140302d1441c0c0c45005488400200082c102010601c0000c165910580c0c0c1d000d04030260600240c14000340d03940e04108043c2020845000f41c0c0664010740340d0456420000c8081c440420450401c1001084014a0341038406880c41d41480310850b03101c3c1006001c18013030100005401400c2c1c03070035802072000b45101041c00c0101802c07528010700315070020038445400e00c40100d00001c1840c0c20ba451600500000f00d480385041180c7e503402218030002040408020743c20300c00042d18060000609840b8000c284604040004900c000760 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 272407158 1250 272405908 272405911
    0x50f130605090117070e13030c21030e0606041b140f041401080a0902011d03030904050f070306051207060c08120901060513091a060a0308040b0405040b12030a0c0c0306050702060a05 80
    0x80c5201000303001f01410304031200c410098040c50b02d1000c0711580d080c4002c0c54501100f1840640c44001001c441260307150740030110400380340f01602c0f516240c0c5420042039a12811017040210f00900e0040c450b0350044144082c0c0c034507031642060a0400c1d2224600860f00944d00044541a1005c100200f540c1d01c0b0080561129000070100714140254000130411454007031b07824603490141c8400340803a0340070001e076080003030014028405841c128030207040c91542a030729000400d060840c0400c40749407801000400c40e05e0310000b000000c3c94101c04031f07000b5607050741c01d9490540801103240c644900e5010503102c0c044060010407a24030344001d2110042c60021204006858800500006004444c1c01c0b1620703103e1300c03030a901a840d104006907008981b0385c4000c0c182000001c000600c0d040280207001203c4e003c41d8100000c1310715000340a500d4680088051003a0020004800460f000791002d000f400c0c0030b649210704407900c0e40e403604200c81c0d00750380300409a4041c0080100f07444881c040e55 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 272408408 1250 272407158 272407169
    0x10b1305120c030c091509060d05010c030b0a080a02012c0a03030c02011403010e06040e12070b040c0503010203040803011503022110141e04180c06090807050f13060509011707 77
    0x17104030303240407010114080789108031544503240b8600802c03180e65a840d9020445a0840300030048020704000250040c082003403958003408030700c44009018400440c4484c949501038540a482284280203850440605020100c1043c451030003200e40d03440b2031442d04051072094a80b81071046c200d0002402c20390b142ca51041103440108010320500425002098102c2d0040c1c3d40030440061840001d4184140005401c0c00b246010824409010042d4200c0c0c1c003a6029590b4000199103810516081c2d12080310080c045040400c010055964440c2180d01081400c1c84c0060402c05600c1041254034002241007120003030035400d2110f0500f543c101200207100d101881101ca80c1c844020a4006044c07880e00d0600c1c0168082c090840c0e203864002c20901c4149100d03043d10440607103061820f400c054000c172400180326180c0071481c01130005081c4103859009040c00035841c04a42040588601c440034001115140c02c4001015104d4420090180c0320710943c40e919800b104c14503030700d070840300d9001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 272409658 1250 272408408 272408419
    0x8010905011a0706020c0a060e0d03110703050912100603060e0c030a110402090103020d0204060503093a020120030915040c03140f0303010308030f07020a020108010b1305120c030c 79
    0x18507011102c60070071640040e90280b005600c8a0003a45824101614098050550b500304003040f0100c50340803400c5010143c0e5072701c08102d0b000000c11020b8180c0140840200492070030000100c3e035261540405005c24490001c4410002d00408004207540040d8400c46206844500b00e1640c60350074030911440d070300144c2c003c0c418494152600d070340c0210700d0003c41c3c0c065680003c1ea0175050344240c0440f03000b004540410f554031030340c44030020038582c401c40c6c00d51101c0c000c1200f049500140c0c8101686540c110140c41c015141d881920041c2403040c01c42000d0956680729141c0350011a065804040900500d09032038480c50460300150420503024018598900c50404000010b1000d11b1400141d0307800940d10300ca1500c1112080c1c2c500703040c0e110700c2002c9d4130001c0000002c000c170540085200f103c2103070a841160320354030b501782e80d44c0f0b0780720000a010595131001031140d01e0716030001e4000d240060a058080d280d4803404a822540100b00c0c0f00d859402418610b01c0c1414200070301011010181e0703c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 272410908 1250 272409658 272409689
    0xf060b090c03041203020306040b06040803090102010606090f06030b061c060f15020304090f0212010b0301050f0d02100c020f12030702100206241909020c010e01061a03180304060801090501 83
    0x80341030380c001380450b610041c0b65001c8089001615a58442d4440b104050407159507030340c5840d00280c0c1e84d04808071090056080c01c0e80418000d226a1a070002c8520084980300d5440c1002003d85c0600f5000da859904500c007030040103a98074072060910840c4038103c2001030014149000642681c800c1c0e00241406c0b000100b81240e403640c0001245c0441d1004800011380742c04080c9550081c1c03180300c031b00002c03028203240045101c0400000039812920103ca044c0140000394061144100310350801a43c0001700d840b55584045c00b0380c111040131840280124101d020040000f100c04641507041c0b4110303407010907250b0840c200420340070181b036402c0c001044149002822840310710158a00885044000c056043c102e44605c4444120b6001082c5c209440c50b45030460900250020031248032a9801c000d18100010010f02c181c0007603510840204030030700c000c0680000c042c2d0028100380c880c1c03924a1244a0924002d00141001d032089039100c102c40d514185200d400c0d034030180c01c8500e64842204 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 272412158 1250 272410908 272410913
    0xa1103090a061b05250f050a05040b011112090102010b03030c0c06071401020a0507030f08010b0f090a0302040f050f0a0c021905010e06090f0d090513050c070f060b090c0304 76
    0x14200d0403610b040c604140303520442e10011007241c4600c14010241d1145458800e544040581444402041e200401081a5842c04400000d017000c2c891190444100101403000c0d08050300503501c040418140900c489020001a030300e08011000090180c00d40441c40d60403541e4207002c1e5209000c41140114103000785050301ca0b80380c0c2030424403148540c9000404104100404155903400c480d50030007151a0246101c0c090826407003d613007100020b40240003011800d005029542c103803041101424108400c50b8140500c584c0851320b81030707000300051000001a90307240200c171103c603101c0201141504110744201d82c400d1029201140c064201004258a2640024402e0346403000980e0000003072140e08025004208181b812001c3d4002c007401c1154002001031070ba102854001c0880b160004540130448819a0a02980358030480200c040c071603020319074100641003c4004403031440c100751a034507400c4e400782e82d0f8001c40b58a5110405100c0500d080c5604952000e10442540d01d54545135 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 272413408 1250 272412158 272412169
    0x31b010e0f090708070c0f1b2403051801090623130f020d0204051f06050408030f0d0204120c081605060d0e0123011404091205030601030b090c0a110309 67
    0x14001c07002c101e0b0100c001403011b48201101c011550b080181d1070030300046420403800401d01c555901c10103642211000488070034001c400c0e8554680032140b50302448041030b0884c00b42c80c02501c0c84d031040c8882e00c48104289020300c684030106110b100e00103500c00200c488203030003c82a400000f0340c04100e1007000300b80c0f0400c1d030745038058039403000660401c0091880010740704492480040c1d0400d1030042041259807240b0184690241c890550b5500030356070704005c45061140e0b0094401a410610202da5410325450252040c060f00d100054102030701c80341d200901d4483c60784299550480c41030200a45c030400e2110a9655035129900250b090030000469842d1080104500e0450ba54182d03030241c034138081d406240e103000da03100583e200c000d2418588050003020b014118526100021440c2203241c81c1c414207402d0341c0c0c08001e0205d8a403043c03009444582000742814103054903803603004450764858190300c0c8120140040c050300c0d941c040d40c00414442d4000280c0480754420420000a607944 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 272414658 1250 272413408 272413411
    0x4080f03070305180418060b0405101a0c03040b1606060f0b0301030b040f12170115021f1524141605030d051e0907051f0e031b010e0f09 60
    0x3940d0b100c00003c4902060050a06d50080d0040611280103c010884030760030010711030004503000e2100380c075901a01006610a0303c80d0005a0301000002d02075901d943d00130380304050310101505c0c1441d41c2c1d1343c040c200d140e101822580303905a1402d02202000540e02ca900043c000d180100c10340c0606000074010984018003010703000c12400320000342040301c14071a000341560320010000368484101d80c003804030402d40d54420b04400b009000070a1a40c60083d0b0400700000580c0200559900200021048440507004241082c1c03034279040f000110101c01a00c0080002e1580501110802583d50a501c00c000d11440c0812060060080b001c220203020303210001c10b4584003051010452501c07a02d0741c850f0580f0626510300744000c0040c40070040369014100e910101e101d400070f5032101003080d01c0b1f04017806150351101d94421b0302c1c0d2742c03015406204200d40b070407820580170780040040005c4c0b600707080441d28282c641b5228001d400c0c5503404042d840350464191403824076410901e0015044610 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 272415908 1250 272414658 272414677
    0xe120705191a07051c02060601120e060c070f0c0303020a060e1605041116150c09031a04060b090f04030e030109081e0f0d0c080609270309040204090204080f03070305 73
    0x110741d0f0001d004041c86607100c0c050b006507289100b0401408080d440e007004032081030110304211620f8100c01d0181c000c4c20002101070300a0009a51001690321854210040a41d50351031586280c0c00021800700122010314002d40041050178801d15140c030607181803030000e01e484c5d045141c0004030a1080c252003c02c4c0c1c6d400b11004107201c18100200140e41c01030488003901e001038014400f0030702c03610313400312134840f0310440050180b046100000c0d03030311200e01c0c03100414454411401030f840c0e5034083c4c0031642062103030f503000c01c00c0c820b040002a040300c02608c020780c10050345403d1108054102149041e007000980c0240012822a05c0c1c040f01401404081204c86c01e800f15404a2841c11404841811540d485001d880349040d200d0301c0c0c01482c44415407030220b40c00e4808202c45261103202075104103a11829a213802e210000341c200f02d07094030f07461707020711744002e100310300d16561140044e00c081c140c10040180c480340b41a000c146000e42d0b00141d0b110700d801c1001030310003199111044031034008 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 272417158 1250 272415908 272415959
    0x1b02010c0203010e100501031b05060d02031911180406080c12030c0a05030a140313020d050c1e01090b0405010906110703060c03060e07030e061302010e12070519 71
    0x9031280042405000c04101543d094000ca810403820443d095000d681a07a001e00282d0043c40c1c0f131920f402090780800d0041642c080b000303001d4403103c0d500a400440d0700140c101c05080c18050944102e006561280c00c2e11070024001040e00070381d5640ca0700030701501701403c54042c0038036480d0002d05070f2a03405006c0309a002e4052103401c81408002042140c83c1c1000490032100d202d0720070308169440781c01415039540003410002c0d40c620144050300c1681d008070248407c05444c3c1c41640c3c03c10120700f64282084459015001481c0c1c4075a55821a500c80c000c11542c8110034102c40b0f42c0010000e2841d0713002005014014003040c0300907607100c5101c2044e0703202c0b42415801444110380b51454404c85900041c07515082010311408258140c1002d003c0b2401c0714216505521064016802c0c9c0b0400808080c2991041002a1010071165028041140103060402001d0344080128101403000900c01c501a448240704000070300300f580001c0e88220142071181511400c02040040c0150001c14090685 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 272418408 1250 272417158 272417177
    0x705070501021e04030506090313050409060b1005030117070e06010516081c420302090a051b030403020307260d0e060601021f090c08030c01020c0d1b0201 68
    0x100354101d50301c9000c03d44100344103040308090305070b8551090104680034050701000c25503907100001a160394220900c0c00c0291141000f0504c4010b201e0140b080d1041904d1b4141720300691602480c1106000c1d023552961740d41d6042c404d02498450002c181442107600c0740d1002c100c0401c0081f000c41d00900c1c24a0b180307940d103040c100301c40452007001d0380191400a00195500c14a411302000030400d00c550f51044c041810384031307510301050b041c5041080726400601d42c448040314040240c00b1140a07665010161140c8030b030003081c3c00600481302c3e00b2099a82d50306102c100070041d420608e07076000010300c091441c84d01c0d5070001c0d26402400b00060900c44800c5103c01d4142c0b401c10392802d02c682080945031544003403d2104090308503080d2482a90041c0000305519510100c0e18800c20303103020150f201103e014000a600918482d001940c1e01c0500150200e000003090005103c0000f03410005a122021210b42d5800c0030301000120f81405040b07d5101e00304003007240815507413502400c02c041c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 272419658 1250 272418408 272418413
    0x1170f040f1401020c0706030b090601030e07090e010f0e03091e010c02090901050406050c041a030c0904020705030a180f05010c060b04020a0903110405010803030610020a0f0c090b03060708070507 86
    0x2181d2021000780400d41d40d12441018020550242c0026001401144e6901d6510f00c01a001c98071664403254204000d8400182c00e54080d0b080a010170300a00301b1940026030301c90445080b2201d0441401250351600100c90400909000b903035610311249026500e409002000160703580040d442461600d103880b81d134141e55a000714081c100c455000703041c08141e403a00c801007600924040310111403151404021610008504081d1020340e142906d8422117603034001c50710495604018025a00c0740c8080000c01c90b0398445001500b20a8481c00082d5250311405c2d01c0604081c00e1a4400014188000701c100f04603100e05c400c840c202c2d103081c00e158010075040d0421602610001c035519800500021710074691540c840c0d100c204585c090003444140081c20420001034410030700c40c1c500c00b60710600104142d031502814100d00c1040d140101c40d00e140096079405a00020b4160654049040340c004001503002da025800084000f00c0c0030b80380a1501600203008800040c0c44641002808a41d0408 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 272420908 1250 272419658 272419673
    0xc0c08070605070c080d0e100908010213030b0708090c06090415121a040c0e060409061401050a0501051204121101060603051b0702030d03050c040b030a020d4d0d0603050c01170f04 79
    0x50b0ad19a4001e6540e420b00d46030ba103141d11810311080b16021030303610004024034820481140600c81c0310b0094074940722a0000c20140750844504558807665980340326221003022007061000301102c44110503000341c1402d02480d284880007941410030500b0b010040003034200c03110007090315110007003108582c94003008a8018520390900820442c0751565002c41e031102c4c1c2c07040c0c50490320b0480f4202da240380c0314401103500b40200c601c41300c80c0c482c84201240c00289031441042c030b540c0152608141180301d00e171019007502c8190348007401081daa182440301a40320f280c0e135820300d406218901841c1010941c0402c3e6030f410003855070000c0581c0e80011912007120541101c2c0100043d10941c1c1e10790034a01c45010003544440c0e071007207007185460560705407095032006007200d210035150841e0ba0120b515130401e030035110b08088004403180d5017007090900d008100182903030940d40600000c00318203500d059442c0c0407603982003905002c24410305100000b6241c1c1c08035840000344909403801d4803189480311 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 272422158 1250 272420908 272420927
    0x1208250f0306090e071806050d0f02240307020c01080106080412030e15010e010e100303050307030b09010611060708011a0f0c0d02061506070f02010c0c08070605070c080d0e10 77
    0xf0259410546014008003000600e032003a103042c818090700f442070505414040354580c0c411141c1168803e2140700204448072030741202ca03030000d480c2008030304002040310701005202c6810343e03084002006002c0380c87da0400014481030801e08011036694101040904402c0d0700030002014203090f2240c0943c2c0e03a200c0d80140c41179100324411600d420300c0c59650f014040c002400f03520813a050040000403019003000d0070f42d01441040318040750321400e40e2400c031001d034030052511090603118541c45c00361b6260004168020002c0d130360740a00c24080c14010504040000c1c1a100403c01d801c1c0c014440210100031320419104181a21039403551424040d510b907018000d000582c80c001c043c22040d9103500402c01610404641c1e004416000741e07442009883e00811001605601410090000650040084500450050f4035140308103a13501141440c1c101c82c0c0d042800002d1000c2019020041c2d0303c06d505000c0c1101c40050408003110410040c094502000307158445e440700150464a180a0307880348 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 272423408 1250 272422158 272422169
    0x7061d0616020f0705060405090c12040609022d0d02150a030b1f02030f03180615040c02010204080a0209040213020409150509070806120c030a1208250f0306 69
    0x300c49524140c000304601d07450914000d0054010080c503151082c1c4082401010340740c0090025080504000510103d080005c201c080c403900100880140c0b50700b03800d0320910942c440d90011a101ca01441448036a00000d01c081d140303500251680501042e0308810759848a03c1660142c111706824000901c0d040c40d0380030905e00c01c500005182c1c801c141c1c50781100d5000c11003902c02d039000102d101c02d9926000000c405100c016001400f0582008546070000c541206010b2003015012079001ca030300342050410b070703003100e50011280403c0d0a54103280c014200008810f00003141031500e0400855224405210000c0c4200d0700c800c001411035840351404542d04407030100440d100d03503e4894450060044440f01c020a0100171000030715071819a086034410304056884a11646440060000c0d618041c0c440341414007460001c0307207180d10200300d6540d9a0340690040b0442840039130000d0700021004e405c2c08400581d0302c5c190078a5000202c0220404a402d1070704034034214400c0d904238000c00054120703 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 272424658 1250 272423408 272423413
    0x90f070504231906020a15020f0d06060e0f0a030210031b0e03150433021c050604110a110705040c0c12030b0f040b061e0316030c0507061d 61
    0x3490098000044910030701c40140e40306600d41d01d0001c6400840d8920b44101c0d0300586c002c400090001d640c10342c040100f010b03141c00c00340c14040d5030400d41c00300d80c004080128406544050030442980d0100c0c481c40449020313241000003480c1c60340810070690b40b9000180c02488200340480c907051090b444442070f0091040c40e01050309142130024172841040008a22038416182160700d00150f0b0b40c035050040340d00182c0003200740d0001d5001d165403c1c3ca40740070544031030444400e100d180c01a000611744089120300c0383c82c40d60300080c1580102c1e6070150502c2d001d0b500e820b64104800340600300310380c058920303410514207030060100000e2078030714640c120a400030f0900719526501c9401882000341c1034852024030030007a0b10303034204400f100d8001c0d42055101c405050f04d0316050420b940301c8000110007070403503480c0140303000344041245064441030800d00c0000040104443d400031b50301802c00d906180030f00000156001c010668000d0380e1001c0c1c400c60340c1d51000e1118480c40d02c42c6120380c140300c000303 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 272425908 1250 272424658 272424689
    0xc1e032019020f01050c03070c0201140d0f0e0106050a061407021807080f040c050d080403080a020303180715050d0b030706030b010314061c2406061b02090f070504 72
    0x4805252400304020031025100e002c0c81c140c03c811040c040d0070f1041d00903124580c190395500a08803002c4840e4a41039060101c0641c0e01d203490b81c0305000500c03684c5c40510300424000f44800c1c08100f00d60700c2c001c0000f01645041001c0c8007981c2e98404500481d04035107041c400300c1c1501c0d40d00c45420301c10000003e50201241103142301c1824101d101c5441070f0f1071a1988002c1d5910010400c901410444009100c020a010140303d6450709001c0300e0401da0058014606250301daa43d003002c01d174070030f15040015a10101c02c0000b8020003040d551074608204001d09110340c07410704c450384102e19070a0305074144070003c038a61103811880e03030005d05a1280181142ca040395284c0006d0b0080500c540c0c142d00180c2041540700000c4215070010780514000f42c00c04034190f100c030f14000c4040d41800c0085034031951030000b0409800d510341d540c0901a50100c40000c9092600c44050980e081c0c402d64a003c41c181e0030020000b41c0d50344140a03500c91540c607100c1c04c040d030b14010125500d10854112030300e540e05000307 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 272427158 1250 272425908 272425927
    0x91006030b070807051204030807110a06240605030112080f07061512050304030605040809150325020d0c06061203031b2c15030a02030405010c1e0320 66
    0x801e040d00898007900d4503443d644404608443e81d12070030140d15484513200c00480c0010784070300d03e616841803c3d482c1460040040c08015401d00d0912081135071959215018107903441d00c80c40007420030341d01c0c08607030115041c5820000f90450005104d4150480f0550070401d041c0304421041310307d01080c11841c0f45d689c210030b1401e44002d01d40c1c41d015210043c1c0d050400b00d0b00041c07400012511030b400000560030180b441d81e50700054000140100d03004082442265125120015101c100e810201c528a840b80b400d0a451095850344640c80e8902c41d08100301000281d07004210ac0030900c4082c945851001ca07503082230f030080c01043e03100121560350040c980080c907038598007c1d481184d95808410f0718000d1030200700c8001c0d03141d50051001004001c00c1000014564a404c04074100141c0b00000076860010388001c1a041142c0c8001d200d50000108410008c0030700c0703400455881030a02020348400e1410348100c08401c0040403091564580c00c55030348503500300b002d007240c0d140d4000080d541c80da40c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 272428408 1250 272427158 272427173
    0x110c0616020c0a0314010b0102010c020709020d0204030203010207140105070504051c021212040503070b18060d0e0a141908030601120f060f0e0108011e0c0e0909060108120903100509100603 83
    0x210505c0500e51811300011b100d58418010208050300d01e90040c18141e05120060000350720100700110700c56800c200010068500303002601c020b9010f812082c0e900c0515407403850079184001d001c602040300400048c41190f852184900d031001d010151803500148900c0811841101001080d1840c4079503508144a10703c00030080c011b0303c0c026026240c09a684d40082c8004e405030018140494640441411040c24040b025011810310a00d020038812920407400d17040965003c03058400006210b101c2d62074000c2009180e088400c140004210700c18180c07500481ea00020300341d1070402043e5901251203202540115151000b0391904003d030f079942d40c0c041c49100b82a4401c861803014001d00006660790180300c0c11700039028408014103406070b00c0c1c0d400342c003e04c080311600c400c1c803201009200302074407464112403051051100920495040002c501c1c0740c60758281d580c0d01840d000304540007440c4c8010402c403200c400300c0c0001140030b0701d941c44528280303444660540c107518900300b000011710411 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 272429658 1250 272428408 272428433
    0x6031823010f060812133c0302040e03090d0206090604050405090a0303110412230303070c0c05031f0507020718050f06010503090c0d151e110c0616020c0a03 69
    0x44c04100c1d40b100320f8200c416080740c006c01229081c0c3c4158800c0401c40c000440c0882400840c0c1c510000c1d201c40c200c4a81e2086000f002002ca07011038401281c184110b0070144112108181ea6400039420544060b001032410504014001e004200208041b032507601ca00058134080c0c00001d109010626140c4201c69903081162420740000b410f04032000c0049041c241213405880741001c4d800c03110b59032600e8686171b44511009032100d0342c0c00b8443c40d00e660001031014501035401652400c1110300f180c1003144140b00746801440c403d41140410552940101e689040e0340082000040f940341d0b5840010707070600b25164044000406009200e035400a000e502080c42412420b018503010b4640d54011540c9000c112501c02855005540c4205545841e01c61034038010300c244a21542e0021034001c0b83d0075903440da0388000c000340d401c2c440442282114000d660f10350070000e055506019644a00d40d560700009006072407a0040c20202040701c510a01065451074005041c1c0b0003066520314104844408 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 272430908 1250 272429658 272429669
    0xb160c08191e030206040b091c0f02070501020d0504030201110a060905031207030902060406111e0109020a0914040807030201090b0c0d05090f12091903050c030706031823010f06 78
    0x1044081d01c01c0040d02d051a2201542c265004003440d540740c0e83c540f001c590303010709160528403890310740814401c9900340802e5204495079481c07428243c1001c000c0c0c46c010180c0c1000f410f41d000103040d10f07502d82c0d0050aa0f400c507502440e00b011282c82c04500c080c1411034581010386014101700c44401840700000041c0007800c003075104d02100d5564120103d00f2601d20800084d80410100410069a480f906284844081030804e4a00c480044101d40e2421411001c2440035a51504120f20542c43c050030240b00901c40d1450a0000d0895422950484000202300a041003004180b0105040c0300f54022020264420054691030034507000c00c1d800b5410100c5a4007045081078009600303004080744d80c00324910400014541400c0d003121286180d080150407a07005a60303100c81d20740700c49580010703000079409000505001000c4c40103141c20089241c100c1c41c18142001603204020380c0d0309a400d6101c907000303052a1503114407031004400c00e80d000c40d1204000c1d030901c028140e010701030fa8402d004460 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 272432158 1250 272430908 272430923
    0x20703050913140a09021f0827030702010c031b1b060201021801080a0e0703062004080703020d03050d050405061009090201120c0513030305030a150b160c0819 70
    0x2c1da039003020300648481190007901c90080d60302240b0b4107585908550b91051004043c3c1c20309418156900300c0580070b0300542c0000030455400e01c081000c2400020403428407102d1500300502c285883c02d941e80c401c050b8000d0400404800348020b0511942c003d0641035250b80c1c078170b108040141844000d000c02d0040c1424101b010101c0000c2c00b0b4014421500184003143c4801341c48080c903001900d0042d0000d00d000d0003d601c420b07405010740340c2805a600554441c90340044d542d00303035110b22940b890b4000303a561040381c42084140002c07400052100f0031241c4c1259100580001c030b140c112050300820075040ca5407401d00b4144000c010000c1a00c42c031504041c0da00b80540e66440408000b601c4441c03001a020070303458009840d07815900d4001c815900c07000d0a1551415596980010326424140d20503070014001100307002140c1140d000d4800b9100c81980700098440c05c001d03101d00a131150444010300418074511030010882000d0380d1100900c901e00c1901c000041c2c00040180003611001c08442d582c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 272433408 1250 272432158 272432179
    0xf140f0615010f0804051f0f0603140705030703170304080f1801020f0102090607080702041d1605060304020a090b030703060c0203071b080604020d050c101d0d1101030903030b03010207030509 84
    0x82c4180c07910b40c8117680007401000c0a15025559003444a0b100a4100c0c02e2915840003146482d5140610401148180407201501004051403030400000e40c100e980f0a4010b000c040004c41c008800000d040c585500700155030380c8a0f441c210301c162181c001c000c549100302191600710f854000d5000001c1110a0b0280d515078100076000b41d080344510030b0340680c45082880741c54080346600010305101d80c03000d8400115582e8808640c481c40041800081643c0d01c14295800c040c400e40d440314004160070b44810b419420035a0002d20f485403030b4000d00340f00940c0c4220301982682c08020500c001c5030001c00400000600300030080d120340c49040140e80070f10000d400c116402a040145400b01d0b000710000d484641c072158200011841144400d0f03480e4450044910744507980c410983c0b0304510641c840000316107503030f00b4600850f01c10380e00e101d11400b0003a5200c0d0206d600c070000783c0b68000003460001540219841d060b002000c8640f0015010341c400305130a81090b8011000f0b0100d450704480e003031604c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 272434658 1250 272433408 272433437
    0x6050c071a070201120507020715210902121f02070f12090f05010207030507031101021002040e0105090f090c091f090f060506040308070219080a030e09070504030f140f061501 77
    0x6d449050b294036005a0000004000c10610080410091003240c07800303080d00720004103810342189100501c2c8104a5841c01d00108500d0a808400c1c68038030020050401191035440b01e40710300007017110100178141c0000741c540800201c0020f64000580c45204c60030709000d02000145401e8040c00f03640804004800d010907298000142501203a6104008210303050640d510101400610b0700c200b070551090b0000740e035690b0750b54006440030b014101c10204d042c1d850320342000015940509a401152841c0703041c0401858041140d6001c82c1c000c1d00c16030740c1d5071035040319401c491503079116001c03000700312007000b10780d110b066005002007034100b80c01401055262020840781e807041e807000601c520000c00c1100c0042c00c054080d4030041154251900115986018860502194007011000180c1040c2d281c0c1d201e14010b140d09400000600d010b0381000d04541c1d8144581500384405482044010380341c0302c446c001000340180c0f42d10140c040c5c2d001400c1651500741c4250302c03940c2c09e0b030100d80000c0d01c1108 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 272435908 1250 272434658 272434661
    0x30206070e0d0804150207050a14090c121f0b0c0a0209150a090506010e04060e0a050703020c0705010324060804050f060f01090e0a0210020d080a02040501050406050c071a07020112 79
    0x1a043d0300302c646280342920780507012254103000580750b01980540741c000207280c2d40710b07840f910040907000e102043c0303000440200081d103030008202800c1001c003402410035020715075000503030219440328100b4403607015401508020100c1ea0068615410000e001524140701083c80c00100d4400d0796403407296101c880f00201e2404140d44015001010500108410055500980c1d0445410304041a03118083d0001c10f003580c600d508015614184041803080f41e20044c41216031042c61840d0447c14001781c0d0304a55152030540c4079003410561107030b62281c2d110740c1742c0280001c00c04a51006000140e55920060310007071080f20701f41c81500440d05000d18001000c1091845280c0926481c42a6800c0682c558000c4c9110404076541e40302e02d03c0c8500c01601c0e102d000003229641500200b01c4501c541c0303001007965400400d40c1000c64018402001503036005030640d8207907102e0f0b0030310315100e00200380c441c1e1034000c46034006030143e40d0701000200740d001c0b0b003402400c40d503000381d03550b080c0d40845c51036000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 272437158 1250 272435908 272435929
    0x501170106080c0607020105070c03170c0d02060702030d0c0e04020705010510090b010912150608071503090f020904170f030a050901091212091a071b0f061a0301020304030206070e 79
    0x5130050400c0140d0b100540c07168008000c0c4902c1102070382052130701ca844070103e80340d8015140301030b00c100250440c441c0000300403c0e45451820301c01420940340143e4000d40b640a0200c00707613035060316800c101c0d460500034210541140350141c0115110001801c010380641016101110b00210768a00820b20030158000c0c0d5070720802c1038440d10011840d004088000300240e950640740e80050311000c52202801c0e002e458010f0420900800d1aa03040003200f100d4000e140300e544041c580f4141c5503c000406900b8003401c00b41e01210000c500380c2e65801c1040903003c01d9100ea1007a20030001d000c0c0c2d040f09150b0045c5010b003803030080130012a5113280b030b1942200c0000344040c000000042e03501c2c441620800041484494104005c0341c0d8800713558903000490b00d940c0a5501000b59102003028065100804001d034100c0026414000d005603140c6c4140094610000341c291511011b140560001c154078810b29800090001c45d034a103028100291502d0054808174005102455001020b282054460 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 272438408 1250 272437158 272437183
    0x9031b030507080a030603020d030e0a060203040f1403070f0807080c04050103020d060b0301021b0708060601050703050a052805070212010c0207090203130506090601030515101502070801050117010608 88
    0xb40740240b10740b50b040441e04504849410513441e200d011005840359a0034010f11442520340ca240f583c1218104082c840030750b0400011944117100802482c42c00113003030400ca0f5001030840541a450002080c240101030f0805405a00e60350400070701950002205000c860707084c1d040d03c007864108800c00080e500c080c4070103544014503441c0007000c140c05038081c5144140003000145012035482c0320713290081d184410b15041e40c0040b601084a924140131403580a582444c3c01c6180070030740d640290540c000c102100003000300205104004502d4000316080910300d503c120040c8040c00340e401051603000c000301b28019000d8800b00c203040c0b801405000310406903034019206071810721486600942004040d8080c001d2850000c0001c1041070007410b000e0808900078000c01d6044d4207242d03141101031040e2001101c00340003040a002081821003090702d00c0f4071603521420407020000c070b190030021742044006500c0c0c04000240340712100500c0611a201c18028400550303a000c0003501e80c800d44240 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 272439658 1250 272438408 272438417
    0x1008070228030e01091701060303090801113c0a022e02210a05040201080906070804021003140c04080c01020705031209060f1c05090c0a0501030c0e03030c0109031b03 73
    0x3440700107800b41c1845404a207041c5024028256100b4100201981c0c000000091740d41d0745006006040d44522010058807080d03000780816601d04040c0005440741040300c0c146c000c2403405002c0101e20203c491500d00e601c1c41050540320035070103510005988011403407005441580640c14000320521034294852041c04010701c0083c6c502d03c0f1880c0a5072045907005502c80d00c2d01001603d14070910344160240c9400c9500141510301440090a07081002d40301d9a0143d210804000c42154400300055200358142d03815144800001d03425070141001400c05501403810004000d443d14400c0041d000722015001250454001c000040e07858070654015990140c100703c01480102500340f00800c0000d502401c124580010500c150b00c89800125682e01984620f41410341180900d014150f00100018007411030710050800107800040c45115440c10b040d1200c810802141c042c0507034410b0303284040d059a990b510950b0b911130007800321020841c0070444500240c06021300755101c4d000e4107a4181c40c2c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 272440908 1250 272439658 272439733
    0x2312040f05090f04140f1203070206070513060c0f121e030c02030f1b0a0803150f21160e0f15010f03020c0309040609021209030a020a030e0a0510080702 67
    0x111700580d03840110a400c0c140c892400800130103c070400603580c82c00c4079207442c103031a820003100c000c0c100407003e0403001c1040320a0024041502c88aa140822640d0038204020740c4005813500340c1e40703800412000350112070f9141243e0007413a0030803841540b11009e4003603402403003840b00047d402c407058172403040010b0384141300742d24070800d402d00100260481501d40510b468102e000c0503141030306240003164160750100034406060782046a030202c20000300c520511510822010400c000c80d0040401e1280380d40c40c600c01d1110800380a000724188840d51a90785854a500300c488200006075840350030541c2039400900c0d440581e11041104050595411841418035001140039420a4403440030f83d00040042d4960790b030b40c034842da07030081c46180805a1102002c41081000f1040144110700c55002000811202a40802c045641c0b41d031600b8000301c40403440c400306142d0252a0403403500901241c4284904980059100d803040d9000e6007200c0c01440c07220008108801100c410740c003803044028 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 272442158 1250 272440908 272440913
    0x702101d0409020d0b09030a0e030111030c030712020d0c0806090112080a0504090f0504150606050a11011506080610020706021e0f0a140c0108132312040f05090f04 72
    0x4001e481490f000901c0c84082280341c0e29403061168044d1244601c6900019610801d1030300300b134080c4c1400300700b20000c00c40101d14140c1101d091100421022500100100244803240600504c42c08110300150440d125003d00140328010003c56104401092a22001541d94613101c40b80c6d5050300d2825400b0030a003206503940c003640f0382041c100070341880001d100101d80b01c00c0c1c0d482900c4c0b420045140c04503082c00c027810142a40c022204400001c1424200300340030140d045000c03111709507160b2800b081403451054085004150541810401e035840b41c10010700700794840e810b0350084600b204ca04092101000f02603070341d03030110701c1050050f0b0015242d41501148070010511076030607075410355148a1a0603586410541c595500300c510035800f0102d02d1100f00100107201c0b14690a08107400e9508044e41200c00400c03041700010180301ca24201074001c6024154050b000b9045203080f81e040c00c2c816400040150068040ca420f04040312400003801e20f0a183c10f01c3c090360154000600c81d480d00d4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 272443408 1250 272442158 272442161
    0x90d03091406090d0f11060f09031b061509010312030207020109090c09030c06050408210f16122a240204091404080d0f18080702101d04 60
    0x400341990403040c61209614501000c1c041c1c203104034400d02c0a0b2000b4070303d0700030107403a0300b0300c40300351000300302c0050200350619000140e2540c100c020700c680590300d640c40982427465441100d460407866401501c000c0080b4000240082c01204960b900003c210311080074049100024440500200c0c0b01100c0901c00c00d0003603000b0100c9900600d004c0356081d842c0c0901001b95808080140001070350507904106121580c1c49407005403403e441c005213040d141800c01550340030311050200000c4400b0245d030f0200c4442d00103e40c05540d801c61130a440e03900d01c014050035001112016207030948002c50f0070180394031551490215103407038007490b00c0c00c54940001040034541c03100b04a4070b854500740c8682c1c003041c02c9a030928414140100140c2e44504103034161007a11411802d0a0381c0d050781c0e0b403c0c48009030200d410f96142540840001541e1002e48820324003808084c200008445008a010000d11054034014031040c0c1c000d881c80c0000e42041602190f619541100b42510000c1310100e41d480c03443c16 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 272444658 1250 272443408 272443421
    0x150c24091a040204110306010914040207051e100c08010e18010216030219080301032a031202150103020a050618040c050304030f02060403020d081305160f090203090d03 74
    0x8000004060899a48080038610940d100c0001030070a8810401140b50501400700c240015002590844c00c242c0c0020f001526280912907850220f07920540f007585039030f8180d17082d47e40c109048070328003004800076082c48503540340340e80024050010000f601c10402d0255220024881e511600c06a103081141c0e03d0354a0f02804e8103200483d8070a59041402090000d07045480004210304440c43e0545006441c00d460201488010302007545d080b0041180701007030f40c0c11280c1145285241e410019200c940052441711403000c10400d055001c0103115200e05802c1e0082095000c441108100050261b0340700300034400203500c6500c501003800340d801c049002e4100e2610f10425090128605000074054401c07807090040020b0010003080705050f8007054145032290140042c0c055404c05403402925a144210305800b440280c001003442410800c003441c4126400c031064910f01e0076100980a0151801d201e1005044801d440114501c42c45208690245c0c80900060480030405201980074144 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 272445908 1250 272444658 272444723
    0x1603260d06030302010501210b06010507031205010e1806061e010504031e0218160302070f0506040609060e070602031206030705061303020102100e060a0506150a09150c 74
    0x203100e5611605200c0c050900998441d030004192907043c40d018414010f1041380c80183d00c5e4246201c0340100e00030200050704030400f0320f0030f990b40c0c40090030705580d14040c80000802d258503200001030003010101c0c01034060348840d00d0000110718000c1006a0b01c00c810b0301c9640e031000340301044100070340541c0e032103070290030b010705206040580c0c0703449840c0d2001d003c01f02e50051723025049540c0c3c00c40c40d10130041800210b680300b103180941810328900745010a203000800602d0f0340041c8800a00100d888440105d0380c0c000300b141c120f4585071410b007001c1c100c60441124813a00702109005092400700d84c030700644076158015800e14a52074082014000d007c0d001d180c2500031594086240c5e200d0400601200c01040d44980000340303107100092900f4020415012010316154a00ca031320000890019040300d04c03200301107601c0d211000016040100c19003141d4103030100041c0e215046401542d004100d40c202c1014a41034411041c041d075031411012401007100f00c6440b08460b1800312902400030381c15 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 272447158 1250 272445908 272445983
    0x2030d09150e0a1701021b060c0a0e030106031403070b010501030608031c061a1902030304021e010327030809031204030f090503031602130e2107060c0906021603 71
    0x39502d00002d807803506006011102d17650005a040d15990190403446035081c60000100124980428940443e000d50320400307041000020207032180f580d007504940091504000e440f080103203c24049a542d601110007110591848000041e640d030191007024200d030a008051898a184191484948403c00c0c4805c1c200e0ba6988001198035088000758075010003080546990b40d003100340700a542c0d040200395100455004008000c01610f07214010401c001d051460324042c40a000c0c016406402c44240e11098482050010f5150380099a01c0c08aa9030180c1c0ba4512151164220345440f8402c500e04100080030000114001920500004c0000d1071286015551942c640001a0544d4882140034401c0070200c8660020361416640c01030b621161610100300c41204504600c0d291b502c981c030031100e0441c0b12042a4190400282200ca24960012080001c607402220140500c13003c0d0190500501c50f031f040881c41740c0721290300b01054940103051a80c1420340319103012040e440c0f03031490a8066 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 272448408 1250 272447158 272447179
    0x5030c0d18110102070f08100c051c06140607080307081b0429070f080d150806040302011b050d050403050c060f090d02030a0915170108060402030d09150e 68
    0x9488200e41c8034042e200300302030340d00345180300c000919040380c2d9007204410710680c0744104005480060b900c0b00e502c7c844035010031850040f000039500c60203103003800c02c580740140e03080300f022210f05e80c0f00a00380c40111080c829079409880c1486000d01a1580041c1075440410204090b1409400e81c02d83c4032554480c400750840002e4030085554005602ca0031101221704540e08a404c1e0180210b0f1540e240c003981c0f103040c41800d450b1036082c0386004c90054030810000500c28104501500f0030780d86607035000b1900c035025568011040c1d40d00301c100d40a5005501e44807401522205100810b86000d09940e552820083d0030b10303920006100c043c1c011014000b00b04803140d9052018444035119104c5060604907502d0900c00303150a01c0e001c40d01050464204100d010310158204141b4420303603004c01410303e6055070b8004180e861a8030403500032900039000000241d618030000d6114070807442134007a40d02000c0c9241c015070b0382c418680034000321170307030305516402d28207104078510301c03803079500030030701d0038035 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 272449658 1250 272448408 272448431
    0x200d0905030d0b0301140601021507031514030d0e01080a05060d021f020f0c01120f020d09200603010b0304200405131b1a0f12100e0603010c05030c0d 66
    0x216482a030606210a03142d040383e0034146070a1040341c40c034006062424010385000c2d40002c0d195510390000d41490600c110105a015200b61b208211b064100d0078070098603925013010040d0166030888140c0300344036551020240b544942e4071025a014181c4440e03005d6100d00429001425004020340d4204803468980f0300540c1e100d030074580304c4442000014400401ca44070090070040700420707000b0140d003c01c0405030542d0740490302c0d4210f5085240d0009500801034103a4000c1e100d0700480507001c40c1000131403020f0000b0b20307404a00c8009105c442c03050044044040c054517010912030071540690070b000013004075500406d9120300c51044210303030480c015038200050844206072000d09400b866480300f40e04001c0f4483d40c3c100c1c0302000303c9465076481c1c0b030501496180004a0f823345407046002c00c5218081e0420815100100100102e030030700c0d4500317500526038030009132107050140c45c440004030380b0341c1c18188605075000400d40d0b5034600e15a16021240300943c407079605044403d03a10070100d4070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 272450908 1250 272449658 272449663
    0x6160602161118061e030307080a090e0403120f0902090a061401050322050f0d050307090b130b1b0f0705100f0f0e060712020105010801060801200d0905 67
    0x10401d14003001108100c009003003800c4100e1441042e94010000c0080d08150006850040ba5010b0804c5506101c00090785081a070204040000c481e0148404a0900100703d10f04000c1c02103107080d0756039201d1150703607009048545a0156400307400f061140f00180c035003281c0c541140650744100708010a12500c1070380403031002503040b141d80d02610b503222001e210300291045101100002444e0241c11400d103e01c4001f940c0d41542e808114a250aa5100c820004140b101442d0900300c0720a40d00c40c145900006081644212120350001d00c02850100d000710b2844141d5103014a011246039031941000155407031a80111110b0f81500042000d90b541c0d890100003242018600001038040780346450b0070710210790302c03081d00e19003441103240c40c2891080e84102d02c0c03800031241d890320b0318041c0080004229244540d0301c01602003108820503004898054111a040b2510940204502561440d07014200d51400e29015007401030b501c0503c4c510741d0780602505400c1050348001aa80300203680301071 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 272452158 1250 272450908 272450917
    0x130f0f08090d06141506040e060109080d260103030c060b010e0d030905090a0203090a0f061404050105180313180f02160b090115050d0311010c020a021201021806160602 74
    0xc81090b1a00c0c000c9040f0040c0014040d00104102d01d0805c1d01030006000643c140128001c60042130384100c002030541c1e21580c0200000c0c2405410742c1d40034024008024001c41f501d201c0c480814004282c4010044100e40700a4102c0e5015511501c101026544040161502040749030420450002c01221913440101c1600b215120303845849815143c0000d201c0820001000500858414001c0190180c1c0c0030600c550704036841502010540c0c020320f800c50050010f00034501c03184450f5070030002001415405280100b01140c400e60074103103116801d0390741e0301c522005c4440150615a003008002031400c00070014034824a8040384540f4002c107907004981061401ca200204d254900c0b00c00d1103490f844035a040034040b0024000d41416041c503107001103440c42042d0050030000b400606161040401ca02d13202d1340100203001d5000074402c020760354039011340103038403564000c4000002c1d0070052003103d170104840a001041d0050010400041da00f04810703546411000701124000184244001e0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 272453408 1250 272452158 272452163
    0x60c2d0c020a090c08150612040501060315091a0408041a12040302061f080c0906040f050a02091305060901030f1b080703030f0201021c02030c04090e1005130f0f08090d 74
    0x61900e01c0008024801c02e801b52042c1c0704a441200304000e640c4a040071102c4100060981c4042a00e03a071600e0f42c01450950302c0981004001c24030108082c40700d03040130035034a000303014025240c4078007410164403041c03da60080c000300742013004204509081300080c001c0120140038070300300081c0b024901309262013164100c0040c8c0024080104e03105846141004089583ca15045001e040c6403003282c4e15042c004915205041400c00118180d8581c0c204e041e402c030781c0100a2000e810a183e03450080c2d00704980c0b507441503600590383e088000c1c5911800d44941c030010300e04a0300740d2035078440040d10405100c080e0360060b950b5600c0303004601e0b0142d503080182071840003000a149181801024568448005011a40100505044541d500d9100768a400480f000160b41c2e407544501084684140d500121400d401c01012180698001c00d4034040a8640d40382407180755190301401901c000b1000b00141682c0a201c010004107080580d880c03180d51056010303038900b038a0040090a60074661104 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 272454658 1250 272453408 272453411
    0x191b080316021203030108031c0f0e0606010306090b03031c11070c15031a010e0105040807121b03050a1704170a03090602070f0605070503090a0b0403060c2d0c020a09 73
    0x808600b400940c103c0390507000c0c0051401c55040560080d01c80c401c400014000005040007202400000d40c0b00121441682508000c3c040f400c0103c2501c81c1011155280441e10b00900003595801c20700030070b0007070403009024600c0c0446100c958122081560f81c40350304d1650303891070700b0b21150080d401001032600811000310100c0c98070710f00c0d00d0203010319039008040600f410480031a6000440744480c0031442403e180440c0c07000400100e078a406680e00c242070034407484000107801c56200c044240d00328000d60382100c1012010151021281881c800208560300c5020401d01281041510000d61580c1d010783d640380594805803044500500d0f59200c50b541c100031521810943c00c1000d400007403295001811030145400c070007810060b0035220b24014494001000f004024081c400c80c4c075500c00003000c0e008410348620b0340c0300450300705000c1112000c1c43c00f4500051035010b04584178403507000503200c000b810300d502d80c507501c00304c0407141d840140a052410040103907a4016150081c000c803120 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 272455908 1250 272454658 272454697
    0x3040c1703030919020607032303101809210c0f08030618070206070e0a0308030c0705120705030f1b06010315060f150c030228020f0102191b0803 64
    0x1805044c54200541080c0b2200300d0400b04005031119425a198180c02d030900c1760003c18068061224500c0700566909801c8000040012440080c10400d05a030b0100c134a10080c1e20100c43c4920880700c0c015000740400000065240c6400b05102c0c0b42244080c0038a80014085540c2d6500c038111b0215800c1212000000300801c19242028100d1040c0c1072108641d6000c0e034103244030702a4403504c4c040c01d4203040041c0502d00700100d40f2a002d0300001164005e5070596a441c0266207044107810203c2d0481b003d000301003800f041c1d68142e0342600c0749540c002d4095480c120740403030b415619600c14031060051031900315140c82211400c0c00450b009600654089443c3c02c0c24400c41c1c000c490958100d4036680b1034031042400b08071003400f0018012201418010321410640c2426464043c440b00702c800d428a4000714242458048481e507601719109a646520104450005a8965028244c1100e10820310b20303149002c640003a082d42c81d02c0b0b48200c4c0d584810b42c2c84105090440c0d0140800342c210310f242a1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 272457158 1250 272455908 272455921
    0x20304150512061903140c0a08010903021c050315040e0d030603170703120b01050c0a300e0409080c10060509100e04060c03110d0e0606010f05070803040c170303 71
    0x1c2c0d07072a0b4000c40c101c1c1d09824000c0003005480300002c1d01e00024080340000224034464800c10007020100c0100140300240380c56440303589502801042608500500071a100c0880c861a150510714140c1c0300c54a0307c0c0d003981c2c0c8003403000d008440c101d40311541c0b0a440c5d950140b5040c0e01405955040301c101e50b4045101429400c140c2901a9007408400e095041000900c000c07983c081e1008000c0d003c4241e0100c1c0c440c041c2c3c001220540210303140c580303079805442c00070010010200c2250008641c0c000000c6500100e05a41000b10b40c40c2d211202d0119080740303416030180c54241d0081c0307031280c0f1541c00a0300308241c400c0d54518115003100e00c444c0aa0780c48100b4840f9107003412002e68401e02942d08011814100202440403030000340006008940707810040385010b020380c201001e00501e81c9482c40e00d5898135503c41c0082c050a48002c001030150501050295100e506508190603968031194a0203a807550b0f00071035903100520652f2010628940482c62440c04841e41d0900c103c40802540c6904112 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 272458408 1250 272457158 272457187
    0xa0e0109050604271103010b04060f1d010503090a06051602070e011d04080702092401090602030301062d0327240b030f1c020a05070b0a0203041505 65
    0x50304114450b0205001c20440d02c40209140070500c0c049a007051404034940c0442c1015201590000d010900040008a0090929405002120030a0360b52020207040814251200c5c1c58800241c0480110b001458800e54000d030021904014844d045403240080ca072641030485005445d4202e41d420502a11000c6a50401501020702003e56850074a545444055802010807010b4002e1030014a00018140b0a1000603a50602d8015107404403078640201d5500e03c440b5840800f04128185c103121b0101544201c0546054580b550011840d507401c01d2000d960076202418004070a0b10340c40c40c1007030b840000261500309054561070115114001072203415203001000c200e004800f0900030303040041092584c00842580811400201018030f08522102904040d450719405100d0f44036038079815003000405809080d2100072103420342c200e642d012038840c80c0e800009823855214040500c10802c1c900010309501c80e850040300e00d003540d100101c000c50040c40d084000815004150021b015199 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 272459658 1250 272458408 272458427
    0x9010c03050c0703141203090d1b050105090105060108180606040e0118050c01110d0504060e131d060106020a170310121a01051c061a0409080d060905040c120f080a0e01 74
    0x82c0e4031541107203411000d10340c4ea0b4103c109d8020804c15048032001da40c0364002020300000342c10800a200c54604a0001c0b4041d081c1a0340d2540095050700001d050100026801c0e100304003007001601980d00c0e64010032001d13200889500c041c3c0d540c0c0d007841c142a5100f45d0703002001d80d84944040d0802426182c005003132411007800051854100e10030500c5080d902804450640c5c810381801c224022100c40401e043c1107100407a020b00d103190441c8060070f4803002c10380f03020100030368080383c145a0329201c0403070300e400003004010010b051040e4000c42c01c0010b1001346502843c1400c03019003999036880310000c4070203030010507104240c102c1c0c481e9912106204a160140c03400780c80c0f919801d40c00e2140005a000d0700c04001c0c06087d650501500c210060811941c1d4501c001041400348401d181410708040e4004800521018034000340001c0d17100c13103401041c0c1f045420a0740400343c2807614140001c2e0040c100021203100d45011201350004024101820301a051a541c0f0549100702000140c000c0b0130 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 272460908 1250 272459658 272459683
    0x306090c0203091f020a0605091f06050319020301270507050d0f15060504020406050a110118080715050403050901020d23251a0c0f09010c03050c070314 67
    0x30001250f0719202c8103450392080300b2010110070080400c990803070602c40c50310310080110b4242002e11031940310029494900848240c3d04454003140e01c1c807100111075880c0318083c2c0513044204520341f440c4550010048080c0050700100c1c8511940c1248403840780c4080341c1280d404840c644d41811b1010800c000c1002d003805441d4010034081545455200b9400c000004200d6500e0450306500444242c01c10001804060015511b940c0c96440180264004038030a1000941c002000101d0799014001d00c08924082c140040c600911601c40104030b0b4010b074004e50f0450301840944003002c54070f11469206da8003a42c0c549417190b401c000028104001c030424242000700d08214503103081d105100c9032a0701c00000482c2c6035101c00c406a1041009002280b0a4510308000d07c540d041c81070740c0055035003c85401400d110b0a549d80c1100f1040c2d07000e4003070002c0340d07104d051180340c041c1e5000700884001039009041c804e0412004800c4145041d13196001120b41c084559030b84044d8000070000c0d54041030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 272462158 1250 272460908 272460913
    0x70b13090e030708071a07050c1b090411010c08030109050103060f0903021f06030b010f090e0f0307020103150302040218011407081e09030717160302030a030c080412030306090c02 79
    0xc200006180c2e8a010324a0058002c040c00a0a2810412101c04001d00000c81155404541c545810090243d401102048085028000410401c0e074440c480c0c03103c60060040840410f511030340c40c0c84012064226040341806040038080c008a02540091802402c000d4408a071540c10b5240601c1075805003091407238400e0420402030000394020a4541101c80c640d8429400e00f150480440701a0034141d0000d0420400c540c00880c3d804640d91291042d140c1000040c0072301010380c000c0c9035403a140300e00b141c05990011b101040041d8440d41024100403120f50b00d178106c180e00c3c0e400080c100c0e40000c2500360200c0b411400c090b0b0b1941c100c5d444040d141c640c5900305040201c3c5486991080c420318100895a80c840c9154402c0c041010007625000703c800b50894044989400c916000f0342c0741c0c142400f4541c03107418003044254600e01030580503a81d010f00a072000c119680c0d0f0a0b034203114010700c11240d008082c00081100c1240c40340b420b201c5030080c1d13008a04c0c81d00c0d040816003202c584d02c1c441c00854 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 272463408 1250 272462158 272462171
    0x3090112060e06091005060403050a0b09070602060703020a0509100c1103010b0a0302040207020319031706060405011d0d1502040e01050a0e0f0c09040203130213061401030c0c05070b1309 82
    0x4400102c1e41c507800340c1c003500c00400b81e036a24070150b50398681c0c50b00103d5101e5008103020050000c009103003419640b00e09026421500d07508455a600e618510405e4010b07400240040d4030079110307070041e0203582d02d5410a14141a18500062917801d84503401c0d00000d000825400140a003441c01040c0c0d01070705800801072104100049181940c16000280c0510b4002503036008545041096070401c6403400821050140246802050030104140c9039508013105004100240b4080e401c5a0844205031500d419004001000e100c0b060441034243d40c0c400c400d061504045802c0b90481d410300c120301c205c0181c1d980d04002c03000070003007070617080a03014000c1c20702d05012803102a410140c01244419141d185580c44080041062041c80c44960300074ac004404c1c085c0c011100906c15880920031102e4080d001580c00040c01104c000c0d11603a00d5400c566066101c1a50003584113102042031894600144112516150b281017004e81c40480c80c4034000804020040b02c20103020003500d080081440344 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 272464658 1250 272463408 272463419
    0x190c210b1608070f050d02070b040b0a0506090a0b04090f080a09080102031b1318140604140a0e0c041a03070506040303050403030f0908010f050f16090b071a01080309011206 76
    0x70300004010b1414442c4074030780001d0503070062086d0b41130b402c1c081e10b065598052510301164040000d80713045504c0c0030700001082c00c50305640680c0348143d102804c08122507031280400e030041c1c442c2d034004941041d80c0750122004107549803200b0b03140c2c90241d09aa81d803044140c00c010080205039000305000e9205000f405450804c18040c1035050b800d0f280c46c940c45000d6001d07603110f200b100d54040d900c007000b4030400005c142c2440d001070b8004c11801c0d201c041107a85031004d2205403802495000c5203041002c00080c00080154030078011001e0010803249ca0035103440105048850360841082d032038042c08607400c0ba07441d00b000400007034801035841a041a203195409052806503000050a000119a803907110611806105c030013404070b42c0091040b40415900300004250550b80c1c1d20030400c00c80001317000e0000100c017122604a00e640c540c00d07114940580700c0b0440d0805081100c1881d50801141880700446074564040c01c1d940c0051580c071850000003401283d601e04400c0e2546041c80400c005 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 272465908 1250 272464658 272464667
    0x403050123010501230307021614090f01030f0209040c170604021e031020070b0610030203010f1a360d030e01050304060b130b040f020903190c210b16 66
    0x703081d040400021b0b16501d4003041a0b0409a0520003c07820701258000000e03481a6400140002d1801361a030030807079222081c105294500034000a401b0750050941741c0014101000c03402e5100740507142012005440c3e4411800c1502c1810100b8901ea001905100940c034101415240820708a20324003400d207091390100791a40d07046181c0e0100c5d2591b038000740541f501032201d044422000b11510603510402d0b0300d08181008426100e0034001c1c131005641000c0240070f03208990582c2c85810140030301a00e0700c290300480f0004182c4082c5a8101885000c400c0c1ca241c04c42d090075894030780c003003118140c0d1054801380019110001d0030701c90b151964003840881d810400b1010400f00a10300243d0300e036290304116028000716404160040c41c151141c01016a1a074483c3c20f4030401243d0a015070f4882c0c4c00c0075805d0f40149054254150480c0301e00c2549800c0e12040c0090a610500039110082c3d0345900d000c2c1000c800c8140c03103440780b8a1045040c10800040c0b10795a110346c850b09010401d040e004001071 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 272467158 1250 272465908 272465957
    0xf0603020306090c150a03090b040303021210050a0504110403171207020d050313021c0602310603240602070303030c0201090507030b09030f1b070e09031e0403050123010501 76
    0x5038105c0000318404103a209411401c1480c2c1c000d800fa40c2c8a0816240007002944861003504080c07619601040e114920300c803130b5804070b900080250102c5400d001c01c02c8002c1c00d40d00311102c3c0e044000c00000000500c40190510310310690140141c48408004101c0070a600081180b4215004440c0070007242e80c00c0070550b9005a522070030402e040c8258408141036011204c100c1c42082c43d101101020801584c0041581c1b035005100d00c00e10801d86440c04da07034a101203000d4010034440300300c144182d9110350f00030702c18032950519060310001d03680b1421103048175680001c0c0050700221b40600030b1540600a00b50826103a100030828510340d526803544490603408024041803120010402c1c184e03041042d03440320320918203080e9440303400240c0808543c0b69a400b8038940d0189690015548078140306191040703801c0ca005d1840c014004c80000c10030300f0701c1c642e9160105010321000c0080346003407048044003201d16031158509940040c4804006a0581c0f019041142c145d038005c4400e600c0c041c400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 272468408 1250 272467158 272467189
    0x9010e0103210c02040f0e07060c0302100506040b0d08090117011d0c0c0102301009020a1e20010507050a0c1a1006111903120b040f0603020306090c 65
    0x20b01400c2c01d00300d8003035002e0b05000c3e40c080d0911503c01a150642e90245900c2e0010204450107140c0c0d850043c0c0300954070b0300021740540c03c40c18078041914001c0d00400da00c0f0b10001c100062018507d00000d641e20100364044c0c852884c013103540c0a4071350300012540508000e00c625030b0050761410401400164104042140b03445401c0c020405520b891403c1e1411a50382000075510b50200b4603a8035100450001011555203550400c0013201401340000c5004000c41140e1402d4541001030101c0a54030001c0d07950200b24100c0303101804000344071003460391501c0c82e6881c00e020001c1840b803101416001c080210050740b40c08107000025403c04100c0f040a000c90030441004101c40c103103504000d402e24a03407204200c1200411092445190411042e12401c1c0c40740c080d174002c2902c01696420000c1d03000181b035071420b4012004203019480344420308076400004107120084c800801d00762000020019925500c44c141402107144c2031120a5000300500010a040000d00c0300003214404c803030a40 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 272469658 1250 272468408 272468453
    0x6011a0c0a1502120f0709170723130b030c210d03050412050405010804020603060d0606081006060e0604052407030c02100816030e031e040509010e0103 67
    0x100c80200414844850740e40e4210b01c0510500b042c42002002a61050031110b106404035000540d6401e183c00020b8000c00c0d1950b0307800c08090034042c035951000b01050001500b44541d40c000581c0341040000c0c5061100c036034115418a00168090002c081568401d54500600b0041c50b2000c1d40c400003606000d0103000c5640f003180e800c2e24400a2500c00d45203401402e180100c4940c02c3c22640c254000c07030f00540c440c0389100c607181c1141800b111140107078060f8500003280c11000c0b03000741c07406101841d04483c0c004c2041c0b040f9000c81d5245400ca9981d80d1111225420291508600102c54402d51008160504007248081c00303450002e44644502d00440d0300c5143d04002000d2130101e000324490081c120242c0d1a40d99035900c1c200609440e0000360206e00c10000b4100724100d05206e03080c60f900070400c80040400c4a4060b8800350081c250340150309001d880305000219400c800f00941200207085199070982c3c6030705000512402c03403c160008944218154010030018416002c21810f950f0802030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 272470908 1250 272469658 272469667
    0x1091b0b07022211070804050102121602012a0507080c04020f090d03030e0f031c06030308040b220c03060c020102030f130501023604063008041d0906011a 68
    0x50303c500404403180941002440440c0000030030003941c00410941c0e10980844d84002d070f03840d00800b070b03502ca18414011200c0d03500700d5400c01540140000755440d1001c0e0f0301c4104031104901c40c0700c40075000907015030b40c941c0301c088204032004080c4042c4400b0744003510103501e881ca206c0a841103600c01d070700c0c50302c0c044d50307040003c40103241c42680090368500c400307000d0b1114803800004555880d0018496035101001b03d40d00420220748a01c05c40040300d43c55140d1030311594482d2075200c4140c8004254003200c04a5550080c40c00d4200001c0c2c0d0302692145101c0c1c00c00c981141480800ca883c032107070410a581c410401e00c03601180341c04405a0220203a030360404e100419103412406030280020301ca41c0c82602d07405003810640c0e05580010b58002d1154030164030071140c030800c4260303145c1d4450320003031180203954690010490100707949000c1d459400c0203120104c95a603140c283d4000d034000b0b11068003006030b800c04403400404d003070341000b500d00c010f00790703541840652403003008410300342c0074001c20006 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 272472158 1250 272470908 272470969
    0x21203070501050c0a08071812030908010c0306030302060606160f1703250e091302040b0d1101110601050105030c031f03200303130905061201091b0b0702 68
    0x1080365103580c1c0c07001c001e0120f030a08101001554011034054408610800c0000d4034461260840f500e0268405048502c002d00d0302084140120b0300c0b0000340c0030850315180104906500340508650400359a0340000c1c5030340703917007030003420a10f000e03103228031800e4100103620788096440015065190061031081460100d032801a11456030f408034102148004810480741007081a03d03409695248c40c3e486101c01c0301c9200c00c8038034102e2210345c16406032401001c5964140890004908244050400145560749800042001000c400c04962440740000b03442042e59002d407503000800b1800307006041a505220003e412408020715151500e840400015544880403091030120800c00d0282d1180545a05200020003992030a801c6503070500d03541c0349900d040001c220303155440c80f207022020017424010001c01901c0054079807030340911a9480c00309074540a04c543c0350054494140040340140c44255541c02800301d50011b040b8203410310a46c40503803500e4100e0911130503201c800d0480680e100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 272473408 1250 272472158 272472163
    0x100302090312030c1309050105011b0c06140702040204030b010f0b031012060b04090b01061119151b050d06150203220f0609030606090b031c020703020d081b0303060d0212 75
    0x14403585c1c1c08190b000e4000032400100c0e400a4140d900c00c0c5e0724066100118004480080c1c0c070f0700340040c240c80a01500f00400c0d44039107111241d19101d1158186411004d0b000102a80c2103904103481e038480100040000e450074403070a00051070307000c03409803e500c0e08940900030440d1502c60329201440ca80480b500300040359201501c441c0c0e00030820044803865090000d0401e0017401030700c000c079440c02c43c00049844000b590140c55000c1400d084805112075130303006500c954440e4107a0016490b400c9081e034414103086039036085401c655416889005100a0105550482e802901a01e17035000c28039000d19800300c201c65035050450303c03501040c682c04178a25451500c50340418800d442000000c80d40660114004040320701550b41441120345801400003210a15201c3c0c0b80c1c540d1048a000680340f504407041d690442c0240166001541d40c1d8020074a24801d14070100e403800ca000643c0034540115103040c00c00030300080021419442d05d10007248040964801c06481070701d501f501000d982004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 272474658 1250 272473408 272473417
    0x20304020609063010121716170301140405091c050c0c04050c0910030b040204150206090607080c0f1b010b03120a0507030e2805100302090312030c 65
    0x150080d544e400c5503001d0103203d5001d08040500450401e10001854040501c00c140034400c0c2c642e00070146841c00d0005400003600780c4044444010600600e00d00d07010040c050454071203d9400c02c036000c8039920742190325020000c104825504140014451141e10230f0604100c06020303540000c0030344421001038540700044c1c480e00100080c0022650403254464080e102002001081365030070042003040200f40c98040f20f400c40ea001080c090043c8500c1e02c0409080b0340a454100004c5002003180850141c0c0c2c000d030441c14509401080f50035107150b04015841c1e020709400082d040a05210360001c10b841409414200464400324848000100b810708640b201000c200003c040707864005a60b0740039041c104410b600c2030081c3d04000301a0580e044c1100c10000705030359107901d400c900e41c2d410780c2d05e0101c05c194240c100c07181b11464082040a003000d4054116910320b003c1c0c0551801e41040042e00c100d4080300d04043c0144080092902c0004212000000e20209030740c50703079980032801c0d405010307 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 272475908 1250 272474658 272474677
    0x4031701060509010e030c060a030c090e01030f0b0a0b01021b04060506030f100605040305030d050a0e0f0105010311010e0a0b090d0c090c03050115080f0603030f0c010b120d02060a0203040206 84
    0x1164400014042e810000415074444203803600004034914100301a110180610899041a02005000841440f0b0b0f07020307003054002ca0901210103510b8188010241409810456038120200d2010080c494807036509079004c10106010301c2200c0481c00000d40314490348002901141840103500e0342940d582e00310b031000e004040d2415440f841c000150b502c003c2400d50b5903020300d8040c041c1c04030300309206008450669400500031450044601d030300c00c0c000e002c024440340d65251741340031248044c00300744070490907042d40100105595040d030800c15801c81400e40c0741d505002401c0c2c4100304584840403480211030381800400c0e124559680400c094684401c0700074891140b5101c081250f402c568000c13443c0c800e060340c0811183e80c90301b444c1824a070401010102082d0020002400d070182a507810b5404100541a2030500c00e003441c034480b00d5080700004402507511070501120506000b03941034402040280142114004203101a44490014041c02411070b0004002429511420708883c010003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 272477158 1250 272475908 272475947
    0x40918150506030c0a08300a0203190c05030f090d060c030b0f01081302090a0e010903050415090605070605060a0305031c180b041202011b05120a051504091401020d09032303010e0403 80
    0x82c0e480d02300035100c0d1300000c1c40ca4019a0f481e0b884240923031003001c003c082c150b40100114501102e12100228a4200300348240e8800300600c40140007403d980141040361000761800b08103400008200501800d4103510181008010000c0000d4a240402803407420f54040c0d07401e0011751207440e0a08050b06032a10b241240e58203041d0381d03e081580c043c000b001107619030800c86201b00c010322811a940500c0e40f080d2000140d090102001055850340503c4e00403000400088040b81d803070350b580d402c2d03400900300c0b9400a541111580b1004d01c1300d010380074803040786021079440120306654070710040c50050005009071b0181d856110480d8000d5101c00c43c4407102c1c5065903c00004074400500a03441f44441c40321070211400401c2c1c0360031035070154501401500340c0d0741c1c050004803000e00c0300030a10107206480e550960500102080c6083c0700902c80c0c003001c10b0000c00d100240e824090302c00c0ca4074032440070207881d509828070170160f20360b0103480c151107080c1806045510345080407545048400150f01c03504 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 272478408 1250 272477158 272477167
    0x1603050c070e0601080f060f040e0a0b010608010f060e060703030507090e0907150e030c01080703090605040602090f1c0f0c031b1e060203040918150506030c0a0830 72
    0x620b00c0390358144074407000d0ba0740459954510b00d559001c1c00090f1605504201c1c0244034000d10300d055040800c90482403411260321280948400b4908902a03110f40c01240040d00103018690101c1c907004081c10726810807503055040c6002250b43c600c1210310248c01c1582c2d880104802a20030342d00c002c01490603a00440c2d003405e015000c540c452515110f402e00b101c04150f00500c41d280183d0840079403000043c003030205020080c006488110004107103c00705551004000e000812500c22036000b01c1c02014016203d4040e0402d01071760b034440000403403244038650265401030864407961141c1551004415002144074a0088040c03001504000c150721520f04291040341400500c1a0071158041c1c4200036502c80104800c2110006016940041c1c008000600039808a42c1000012100d0001e0b0303010100d0240d00c07451810103826100c070080c1e030b403100140110741c0303800c10110842600449a10b6205460803886d1640c070860881c0040e00c03005d00d100c1204c8911031800182d45910201c54009956 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 272479658 1250 272478408 272478419
    0x30604080d0212151311030601120b2214010323010902060d0506151e0c0a06060b03040312050609060d2d0311030c03040e130204061401030e0609031603050c07 70
    0x1201100c0a81c0c0100700300d80c174144031010305000b016252103217644058070350f446140c01180c420f0103001c00c640306991103088030705198a96110b8807240891424425840000a00f003001c01d80364004101860210313910014008100004031881c442d00f16500c210b1005980c40480c107000d07045d1144007951217040401c50f003074102d5550f000f20384103040841d16100c0c2400a07503404072290203600080da02d4160844e004044401901d0010901801814102c4840f10b085035103410590307001d904245004070b000700900c410143c215000c0020603000b548213000c940351640100794549030040c8514410701013200c5c01c00600225010a506203240102242d0b07075010005010042d01c04184030480002d081340b184032030117041c003100b40d03a031003c80b0201035854245080c95a03070000c00c01500e594040754801c8a5030b40103a03103e200b80750050034000034100160080c0400501103d01b08a4440d0040d00408108030780f1510102c1201c610b215981400040221a81000c44683c01007410300e02181c0305242006c1903 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 272480908 1250 272479658 272479681
    0x301090b06040e060108120d110c0d08070f020d080604140103052409030409270b01050a050607020a0308030709120803061c0b01062010050a0e030702030604080d0212 73
    0x4034040c1078070284500700308503c0e002e94410007440b404d95507803c6003007400b1f541c00e01c001c0104030032001c3e4000400c01400260700072040d1b600440310510503a01c007020b842106d54000c1071040e4081101d00741101c0700503c1e020065200e4242c24210700400041304000350155560b5482241c48040ba83c5105030780c2d60712860503aa540e0f85219041d0540f0f50280c542095400721400864452900b0700f0203542001c2c5007504040c06400c424400d11640c0094004450392002c05403104141c0900030380284c0c04c15450441440840c2c0704613003216009080800c032000158640389284030440c0c0d8010035842d941d5641c02d1044030204015000f91100c0d910310b144400500c440003000e035020701c104a400e840902c403070320740100c858000c010f0010320f01c4480c840100441401880207100100c1010702400d00c00d0f01d16032800f0b003420070300c0321004042c0780e0300d00600000c05144d110340340306d5040800c0103525103d00b5800003607480380f000340000d011090002c0d8041c80016190160340071107800c0000c04401d410650050700 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 272482014 1106 272480908 272480911
    0x212011815060503060702060411090408180604090906020304050d11120304060f020c060f013807020301090b07031107020904020f010e0a0b070605090d0e010507050a020301090b 78
    0xf4151414805d007403103040d4550281c10103160914043c444806044146130088102c041000b0020704500d003200c0b044012800c40c9545405005c00140051189420034401103003419400341c200074803900a940135521810664074455644901181c03150006292090a98814070395a048051048021034202d40640c00206a50f444002010b00b0307644481d010052540c001d500f08240321850341011405001c00e240c103040b0110254044181c030791a2b110380f210748030201080180a4800170401c4170320b6240d01038000c0c4042c2200d8240002c22210850b1120b011908002580802d20702281c210348070254010005a81510395409201c05c0302d0004440034148544512070002ca5500d00341000004e040c000c2103140c0e902c4c00c0b85001d205441c80070b03050441030780c03024401c00c1000303130005a10540c0c1c400a18100c0d0303c40c840350800740e1030010100f1029405502e056a40f0042c05020310805 = true := by decide +kernel

theorem cover : BRFrame.Cov 272302158 272482014 := by
  have h0 := BRFrame.cov_init 272302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 272302158 ≤ n) (h2 : n < 272482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
