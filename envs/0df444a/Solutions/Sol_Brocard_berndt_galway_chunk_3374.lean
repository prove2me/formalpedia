-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3374
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:28:45.265186+00:00
-- url     : https://prove2.me/submissions/8af0f700-5cd2-4f84-8d42-3b88dc1bd1d4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 606654676 ≤ n < 606834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 606655926 1250 606654676 606654679
    0x605030a0807140106120308011a0f07060518030c01020c0601170d08040206070b04061505060a0905010c0501231b030105010e2e050d06150804080c030d021b0f0705 72
    0x1070802c0010703210000014000700b42003000f5507035035101190105841d01440d81d06030007955001a20341c10725660306803000c0314004044000c0f60500c100f1203203e042c20103c40c07030181c0c041720100305615000083d4844d0040c0c0418012503000c00310300f11144c4001503001d81502d040c1d450417200140d030703292211000307140c0650348400140c10000c0c02c880868042c4a09a801c5440a41300524240c010b40740d0501c5803a00359812101d041e16500c0a008644200b00074602800d030403038083d0f04d408030b8404040c08410541c81214103010551820409024083d4096159401d41075042940214022070640610904035405070400b5000c811510310754114500f034034181c81042c2c61708840c01382c0140c104408501c40c030541030078001d1080040800c56640000030302070041d25482c0c407502d40c0c1c07111118009450300c6801c002e5886a00a50740d880e1141d10101083c0c0140d0082d940c907580d41e50313181e8142e08602c02e500c1ca5104507800001c0c00e01c9007901d0f01110420000d106010b8030700c51074030f01c112151590a5445480d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 606657176 1250 606655926 606655943
    0xf0c0209181e0325060221090609060601110c031c1803020603061c020a0602031b012c0a050609030406030b03010504030f05030a0f110904060812190e031f0605030a 72
    0x6144010302c07032504d8022900c1a50302030507440140d07446109036400181819980360714120035051501d10203003060b4000003084d0250049140c4005401c0c3c1c2e40d00c00411007810851400ca00814240051000344008031000c1d00340c0315100e240000720352810b854414002d00003040c02c1d25520341c0e030b59140d807c802602e9008007082d107035031200310800c02d99584010b1072110b80240502c04400594807803441b030300100701940103151036000e03031000a42c0f40c0107035507207850300c0da41401c1d100c0c24241d107044821030780c00e800191940100342d1016040c0d07250070103000740102541301e01d00c02c1c8400224000080c0044800b16501845410764034418142610000d0700c009003c18801c1307905c0b40712540100007541d400b4150140014041480340c07040b2054540a9596008090f00003485000c181400c0c020100a09251401040426820580d2035050704c80c0103079840c44a0b0247c010002014410b0300d01c5a0110f00c024200c400346003e010061501203071060035400401c0c41e1403800100750070003244083d09560880d151 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 606658426 1250 606657176 606657187
    0x6060603070801091a12060601020601091505060c0309030f2b02031204080c0a03030203011d04051207110a1e080d02070515071722030803070f0c0209181e03 69
    0x1104c020340521218811111128007024003541c94035441e441c85041500024042818441d00190400704113802452085007000d07040c080500c42100000d085603410744005a0301e5811503c41821802110100340d0700d4000d504003603468041c0044c00070a02c0c009900b8880c2030002e2122142440004c20482d20090303042889411000111210451340c49405080d1017864140f440b2205810000404002c80101e40c4c040014001107509030f0b0001480103c0d06810489420151100c9555a01201c450310310440c00042c150204942c8031002c007030516025040369019074403803900502c800c082c641545954544500d0001c2e483c42d00041e81c10808942e03402900d17605041000388100c00c021280300306401c1c8000c01c90300300007452143e01d5010b255501941300340c5862200c0240c164490841c5001c004040b0700002c00c1c004101c40c00c04898001000f42401d062b4080c042c10181e40104085c00041c0d8040050000c20a042c0034905180b00c8100000301558040c40d03a00c8003172806c6007503880e0554070b81e40c0280079 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 606659676 1250 606658426 606658439
    0x414070807020d0c031b060e160f030f0f0f17191805060901020f060a020c1203011802091c0b15040504050307020405191b0806040c0e0f0103060503011b0206060603070801 75
    0x800c0045c20604021403900c00c4596101e010548408e401e14031402d03480a20321032002c005060141c4090007800d11180222842d40d1904400314261342d002070402400d0022142c10403001803004000694080b0480c016041290705115198114869034406c1440700400300d1001403003030b00b52180a4900c865500541030500e400c0c041c40340c1103031591605501c10084500e010b800c1c1001060301c10f54041c480560b131115501815410030396100341227810540107200510219256646100d10710740c58600041c1c42e1000c1000241041081e44502e500302d0b85082e504070b09002ea08082140324140204201c145190b4002c140000c80304121070241032504107000200061805800c01c6030440b151807900340740f17201201603181c1156409680310401c9a045941c4128498201c41d016a11000450b020405001280000382c9880400c4007124402c070f401d84121102c0da800707940054082e01001d4004c110620605049a922800c00c0c51503401601c07402000844502c0c02c0c03000c480c41100e075907840c0d1740903918080 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 606660926 1250 606659676 606659687
    0x40e060d24020d020d051f0e06090a06030b0403270f0b0901024b0318190605090406051f08100b0703120501060504080c06090d020414070807020d0c03 66
    0x740c8035000903003c01c074503038502d109070002c0c0c60701c0300b000c0c20005000c0c18024044803501403540040a1100704c0660108043d0800740710195015005481001c10359071030201c00c07002402203410003054100000203000034581e21000c0e100300e0841c0400809a013110f0450152031040461240000f028101c582c1441a10f1802d0301030000c0a60600403108560700c41c050755980b01784c0004098a0b0b003002c11100f070889294140d1101404038075164801c502900c039615a5443c0d00c0f0340c020000c3c07282c1e40d2090b0482035881ea400743e1040075118056003031449441d443d0052060b0b00102c0f03c20710030303400c0c40804115854107845100003139050201a4010316070b80b0344180c44071030000b850b8522081040c107000454510400003002a01d01c01d070359032206210f81c501e000c0e04480c4180c00c901c080100900062041c101c001580c1c1c01001c40488400d030b19403800030006100030210400c025041400d0807500d115003004080d0060103104c07151102402961104401c9961345e4106814000140819080d90042030196 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 606662176 1250 606660926 606660983
    0xc100e0a0303020706060503030403050d030c1e05090d120c0312051e1009110306030d0c08040506070c08011a091311060c0109021801050a050604050607060e160b040e060d 75
    0x2418082846c6503940b0001c2e086030010b500035030706600201170307030900c269052084458620060910070b0380ca090001802006101055510007031000c001000c2c0d40c00d40e03441088100240e80242c000410309100e40c0b00a009062520089000c60721040c000200c03d03125000d158030900742c03111a03144400c0d0b000c0303103240381c0c2030050a1721000506104021031010f141c7d0044401d41980321070f0041d602c0c00c003001810b12b0034a94040d54010001d0f04140c0300c0c00a412002150f0882702c00300c1728945c80f1502d07402c103002c1c00c1c001607010741c540d98a0b1000506640203c00105107a1040468030326400b5503c039210507030603030701520700107017a00c8411080d10443c1c07803d0f070050008405158000261102c0e01c0c0c0c0031070701c0004036600c0608030080e140e00401c4035160100456014290545d8440d0620b03180c4400701d0218010054010126070302c03214440c9400d00f0800071100038407440b2000710850f660315404660140d100c0d000b240304000950001a20b5401c104544001a980c000104030004400c2c100707210140044 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 606663426 1250 606662176 606662183
    0x18050a0317160501060b07021806090703230916060f020303011206230103201305060103090f14100b010c030305060102161403060f040b011403150a020c100e0a03030207 74
    0x840d0741000490002d10402c001780c600040362640d82c0c000c03401004040b00100449c070080d0300450041000320b440b10403600b80c20081900780851a040c1989203901e14444400010b8108504101000f8801100048a11181c02c0c41c11102e8080ea440d090200c803150a103080400140e8410001000b03950801000400004d010300d1000824103090101000f034107401e4951084040b07049401441880041c18000d07a110056019204201a0b02d0011445034101c01f050345880f15035450002e00c9a900a420009240f0340c48424000e80321401d18007032821144000d41c0b2a85885080c0c2d615031304c0542071084014251050f1500d100e4950240d030103d000d008002c2106046000c0c0743c1c0c1d404210030a8804d080f02601180d0f40220702121031390180740c5030150003080d4603260002201070001090003901268195040352881d140610f03040c00100f45021203001c10240c01160760302c05c11003903075020f5004d00128100e0b60150340100c05004026015030300035204601c0d883d0448202032000034001d82c0200103c0c0e11 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 606664676 1250 606663426 606663457
    0x50102040e0a020a021e1f0e0708011a0603040812181612020d050106090507050912011404080a0e060a0302091806060d0b040b04060602070816030503190c02040c18050a0317 76
    0x80104000880000c01f00210070494840d209070f81a04028400b12000e044208020011703282d51100600b9030388008280d413402404004041014080341c10120f80003140d0b10300c100401130819840d81e6600011740101409a4024038107091000d0001c02c002904480340c0c086440d48e046800e40070400300300c40f0f14030116400c0d903031001d00060080450041d944188a251181c0b40c5a2400c2010b1000074010021102c2040c0d250041d80c40400810a10907508142c0009080751200d01541040e82d0148440c0e0646910000c040b038a0301240e82d1580052441c01c605503580301c0140e284228840200b0b00980307040364441418090340b280c102c1264448080b60100a00c0400c205d00c101d004074044501f03540241c0c0040c0c21090782400300100402c6400b20341e0034405096011140b03107485107501d0780200655106004034a4004089581c41040481001c640081c02080904025800540f0842c401000711081d02c55050740040d041ca00b0481460849411111052a068101101c04529444021074803650407 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 606665926 1250 606664676 606664693
    0x140a0e040515030706030506030307230604060f0e0c031b0423041110050706020307030603060e01060e13080306090c071205041e1202042007050102040e0a020a021e 72
    0x5036240541c038042e80c207070303a509a240041841414100059908031400f410704020504c4943d0301c0010440740700307641080b081c845401010203100340c074222814480c811441564144800e00803540c6c442c004031409424200441d0354004082500d41c031421050726819084160131302c41800310b5100c2e001c509140140001000e48a281506201d03544203003540b00c8130941501040200711031200789048008003214111451005803000809a100705140205074540100100300f0307450090701700304051540640f0a0103020000050107008261601c01c3c020324100c00c1c0301151443c903000500c07008080d0400d4440d4999a89d4101703019000f40c02404210744c0d10f600300101c0e40071480c550000c82d0081300c0d9036925542d85190210b001204080310349503501d40300e001c0d841007003044400801c00041d191305440c046075a01c0b641a00805929a1002502d6103100002d5084108035040d4010002e4643c0c903c0101c00f81e80b80c500c0f19404a00805140c10007691000c041c401c1007030240010a0500d507580340031a05040e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 606667176 1250 606665926 606665929
    0x10c1401240e0402060316030f050103051b01031104090930020c0118090b01140d0e01051003020d08071106161103150117010e07060801051f140a0e 65
    0x450265040d008030400280c10310030401201c820800080c41164010030040c102038000032101d21018224040d1000a00440e50410707000740c02c90320840780c1d00d0400b08100e6949040a54940e02003082026a215101c082640d1540c0244900241e10b10700c1d4098909090030300030290020107440b070381910041d0b40743b030000b00342001620344d2102603902404481d080c0304404c8006031030015009107503814000ca03010141c558000b100922412102d105401040c001209401a20b40304056200c0c002400d000068003a0110140d8000c520a40c5820008000d00e54540ea030259925540f400025407040581100c03c1c040b52510018000d424002d203070f10898030704c121000585990150802c4098044a0740e481e805004c0500380e5a1307030425050b0050304010944178400c107030700c001c140102c015641179124291640070003507000c02002400c10045420203911001c01428140003481414424103001c14102503d4000c2240300344030301003030b03214501443d00c03640d03500545411440100003001002407a50106 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 606668426 1250 606667176 606667181
    0x2040c0504030212010b0108040312150303030516080c07020603060a1d2e0302100c02030a0b0a290d02120102030a0f05060a0807030f06020403050d0806040f0515010c1401 75
    0x244809625510365640c03661040c007900002c0c00c0d1070800035926201e420015641c1041015a1055240c42c080c000640202c20200041c04800503a0b000c0400c500808010560590320150040c121082c850503d020100000c8403140f80880301c14000b04802d025950050400001444e0044c07002041d01e2145504c1e00c061003184811900401b400803243d078184154408100c601e4200c407030b420000500c100c030703114204200040300d902c8001d004500d082c820501c40c84c840c049088000c0c0c2d0040070785540a4040c201100084000c0d40c45541d940e1505000e542000305442c20155950405540250000300040c20031100c610b1054080c0d0300210f040b200459440300078401140b10341c441c82000680800480f200800719080201046e008014000c41800302040000ea035104903680b00900d0b0710300b100702d840d02c030380039005980c4010583e00ca00d1305180011034200710b01318890782c000ea40c10000c075410740d51140c05858094804074008140c403041e0700155482070b000340440600801c41001d0720503d24181d03608 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 606669676 1250 606668426 606668441
    0x2010f2415140c1605010f08060d03050d11120105030604020a180f060b130501051312020f091003150903170a090c06020304180c0f1107080d0f02010f14071b0204 71
    0x15078000c142c0d0222a080134407010b00c0a4102071910402043ca18540074106c81e101801c000e02c04d074400d606450415100b0021144040c00e207407014400c140000c403c00300e02c0e411100c2c103000b408074140700104250a001134890f00c5960000c0018000700c0c6010410702e10580c04e10382010f4025280c8240c0040803c06004120040806a0046580302610b001800c089186500807a040140800040060380d083d140b6040c180d59800d0a12008002148001044003005c48110f42d00304a401d020410803d50004402c4100c900a01523000344040c2003c1e1641200c0200100501045081c5035020100b000118150380c81b040f02940000c850780503440340d03601e01070302ea0300a0005a00003d42407014180300350303024031110540d10080c000081100005070000030403080c04010054403da400d1a000380420001005000640640388100e0380c4d05002003032461402d04202c0958200070380c000c4101d402c1d104800700040013403070580ca1610382200880b002031100c3c40103070645084015038000b40c0e8a6104461 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 606670926 1250 606669676 606669697
    0x406060f260f07091503061407140910080601020f01060306020a0f050c061b040e1311031614060c010f09030908030315060d090b0702010f241514 64
    0x255000381d01e0260490200020a5041600240d04071160088001503100580b40350420104025000e44800006020581d00240030300e8100380303059481429080c41d050041c0c3c07041e5a03428580c203040000d400c540c401c020307800307070003402e2100d6988142c2d05c6049540d4111405106840c80c41c203403d1480c074256501d581003900c690707030b00140800d00d068205820701d81100072400c009080060000155480d20402043c80c9003c661041904000386002c0d000c50f0050001e07016640c8150801c4104508282e040e000d040b900d20100e000408918580081c1e0100c00641010800392044c2c00c0016000345a40c0c0c0c280702c0c5400a030305100f80e00d8080b10a000e460b410b480c145800050880303084c200281030301807030341c0000c126030010414010300c6a18a484001010401da5086a54884175030a0100a21003076101a2441810109004400340d06401403081d0300a240c00c03c1c8012100020400c2c40325604c0011072105c071500c2e40c000c0107445c102d620f09a54610560030700c05038691f80201c03c00d1150b4480007018 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 606672176 1250 606670926 606670949
    0xc0d02180405160f020a240b0613050f040905100b0111030a0201091109040c150210060b0706050f06030304060e0609040603050f070e0609061e041a0f100806090406060f 74
    0x52440300d0340813003c0c001d400003c0c8001c00c40d0080c141c031a46c8400c94008890350340e115a00d960003113251129004543d4200c0051300e40b079601c82040098044041c8103014080c81560b203444c030683c29140c0390040309042a048009800c040c1071010703400b0000d040c48404113050001504607001c0d6604103201410b130b0306441c4d80020800710780764980140403c03030481a035803003043c1b140c05000c080789401801c80c0981e10407111040b02c03108252426440d146804140c04d050a081035400f18284001d0701c040c1462510954040c0085d4483c58200040c0042c06c980607601980140301c10030190f4441c3c100078220040182a0a180c40100004503056411582003541c04e6405494603004041080101d400200002ca400b0300f03080c148440001c034101005401184104080044202d61820065812101c004010020080440b004e9862072403401750899103407040340d207500d081140e400c001079100d800c0b03900d0b99114981c5981e860708010300e45c200a4401d42c2d01543d20103000c690340d6402203800010b012214040c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 606673426 1250 606672176 606672211
    0x7030b0a0c112805030c03031023061e040305070b0705061501020a0b07170f0105040b030703050a0b091504030302030414011b050a140414010f02060c0d02180405 71
    0x42c0c807501180c0040040359108100d214680d00402100c0d9105400910f80d038600040281010b62441c050b1a10102943c000003050007140e1107108415400c803104503660a58001080d5180d07400c1c2d00b402d8403040d030082020402d4215002d0094000d002c0940c422410701e050540381d45449181018540025601c6076001450310180034081095540c408a13180440c0040380c005070000703450703640000c0010070b0b5041c0140030840c2070380034044402031041c0f581d0685d0030ba0315003001c904006420a106090040d0300e0801d00a50504000c00c02d001039942060060080074011341d94088051001849107645009403454941c054540881c540c2c0524065a000358032801c0a0420020b55811582e103414160325001e03110a10600c46030b4004010280340c1411a1100c21103181501d1045804d1720304485143d000501044072000b004598501c142c0a98902600014001043c0c0c0c0d100c90070345a00040d03110900410b008039040c1d400414200c5041c40c3c040040c14110310100381926403c0c0c0d10340c030f100880c1c40d02 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 606674676 1250 606673426 606673451
    0xb0c0c0102060c18060a120c03050412020f1e0f0a0506070e0f0306070c020109050a121401050f0a1109040c2303270a140325020616020307030b0a 64
    0x10b0f4102c00d40324400c40c03922107446100030000c1c1c80c0c958054001c05000c502518503500503104441510b140407401c0c850000340800c020010401140e04484c4031200e4140407030003d20008040441008803002880d644082d44500007182107482d10301c95051040406e07031030b400042848050080380c4640300038803d6042c001c2020b41190150080d19004203862860041c80b07a400140507a000340990601003800661800121222003154010540120124400140072501a51400301c901e0080f00100400001d1298490170b0f51016a0302c001d800040d000400c03c00e0f44a54070242c017503902014224a014086004a400d40f2100040c00012910750041c001c158644030020000e9440908882403441c61702c414800304103840300680c0d40780c0e40d00214042074420030803c80f20502d00d8000e48000300046883c02060740d01c0e03001130203510510301c0714508101c031b15051250900080c1c0d4001d04990521650000b020766410f5480c0003a40d051045200020100e040d284c8001d014280744580820003090184 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 606675926 1250 606674676 606674683
    0x8010506060f12060a05100917150105060c03043f05030307050906070611070c091107030305042301060510140301030615080d0206100b0a02060c0903070b0c0c0102 72
    0x10300c114000d900821411144074110340845809100c80e01443c0c00c2e80e22040d0101d100e805860300807681100b00320014202040c1c100f0324007411181d82e0200689a4405d00c114180c603941c1c8150902ca100748030000500c480c2c0381101c080e0400c0c564043c1168100f5039600440700c2c91130315000810596008204205060a031303400144030781d03204112a40d0114000035500ca56407480300800003c1089004188520159698406c85003030325002501801b61030703c0142103120a501c61541182c3e032100c07034880013851402900400c0501c042000c481401c050480e00c0603400351030010b000f20f80990b281400a218404882040c2080030482c1700001801c90030801400351301c00c094140789043c4141c00c005070654000c1c000c100c07415254000d038045843e08198400e5040d4030026003203a07205000304048011595400118103100380b02c1204064926550341058800c903100c3d442c40d40d001030b044000040c42103070410000341172420740034048501442d903640e448081c0342c01546c9211109d80000340c82d2425503a040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 606677176 1250 606675926 606675931
    0x31033021504110a230f03070b0f0a0e09070203030f0c070b040318061d0607050102070503030109020d06141c111315060f12050402060d060306021e1603080907080f07080105 76
    0x590342c06501401c040d855800040542c071745106000081450004d51000d01644008203202c4082e1a1140050510031049400c0100b4000c005041900c150929240c4482e030740e40943c001c0d402541c80c544441140e100f0308500203041418603c1c04018810015010f800c40da440350307010707a45048000544050f440400740c000d44c05107080144c401401c003024401c145600c0303004030b003c8a115a68181c1890f045001e8040d20074054800d01001c800051030b0019500240400ca036a03401c1000003540f1200c2000040913138207980742d0008001c0362041c0300c86005040e01001b0a000d1402c8040c4c00c64030400048000c00580750801d0f9554031044000d0101c91080d036002c0260100b070608020f403030b01d89000200100c800031500301071551504082002c1d510383e10200c1d030721024a00c03814062a600d9003818006980080303c52a040400403a50841c0c10010406440e0346003070048500c14250807946080f01c5000780a40702129034020760702d002650503801c0090101d07407071903400038003445490081c2c1c19007103e100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 606678426 1250 606677176 606677189
    0x80306040e0601050109142b060605090408031f0f08010e011a031207080d0504120816080a0213090513021005040f090c0216060302031033021504110a 66
    0x4800501c01aa003000c8114287c88110309a1b000404450001422090100071f4010541005a18000c4846006802d84000c180647d80c00e1050a5541d024001118011140074107650010b101184004540545500d0004045449840d40c6034907110401010fa2003903002404076950b6585020340c0b040c080c000d501c0c4001c2d051015031104501c00000c170740c680c0c21043d032145001034001205070401603242c040e98000d8000400400c0140303424a404d40917401c064040c60040740342c120000c0c0c0054803c100d000c0340001c00d680c401c14540c03280d07100f200107900700e11219000e501c94444045440a0140702d080d04c5031100e40c6040961004030300501481580b1002a0780c1000000c10003442140320900140b4102d40100c4400a203186154208a08201111012414102d80701c17100240195041d0040c5000d20522107070158625520306510344170b10358070035640503561001800e4151500274130070744031142045401034600d11129080303102c0345424111811140c030600352540046600349643e20402400b031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 606679676 1250 606678426 606678433
    0x8061503070b0a0513090c0903060e1911010905031207170f030402190308070b10050a050a0b0f120c03040b0a0b0d0b100b070309080d0306120807021c080306040e 71
    0x80c100c000859110f00c40c440c00070f008000a516015581c0c403000301d4018000c280f070811044401d604018200e00b01440191040c42c200030307040c4000340022600720541d101c4030441c1d40140206644840500020707600141c18881c1c0707000001807070740741444000c10000101400f140c0d01d084c0e03882d01102c503c0301000c07190096001848074401d0311502404a03a01b16804a030940e45134003c4610800100c00c454100501980300030485008200170341044034007a44450103640c2420b03844905000d80b20201d8400c1d0707a400b80040ca030402081c040603005113100c0d402120014903244200061940f05c0304142c80d04450b5100000030441808042c84115400443d44181070207131a583e00700240c401d15000b80080c01030b0750f03807101241c4000c1c0b82c0303990000144005041c440d1103104904001d4003691851180d04058003581c001074154074840d104200c00c0d030340c003503150084a080c1c980310012a50800402281c000340c25070410319103a5152100041000d01c03c103007480e600c5c50648140420b4940118824590380d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 606680926 1250 606679676 606679679
    0x40e06390403060e01060605040324020d15090b030709110f030718060201110d02031315090203010b0f031c0509040615030b09040c0605220603090507080303041101050c01090c0806150307 82
    0x5e50003170466041700d40000c0159581c585600c551042c1010344034092459a20004101c85a83e800e070b0410ec07c01e01c800700c000c0129034dc0c0c0700c0c07160060740c06000351244d04d90400002070111034010b42c01144c030081d42c001c8241c2000020a1092031036030042e02c546000c140c200100440c445507400300300f0007400b2144001e0145e803040c0d0350382c4042d500502e400c019141c0c1c2c0101c0003601e904002c2c0c0f245109540c001c01c6178070740e602c049080d1070010500d41005034029403c28848000d60300700800c1c80801510080c0c02443d00b80600011742411090703040c82103013000410807646140e0f583d40d0107000042c201c075401740000d0603e607203806004c444012181c14051400001084003042a0702c1c1181c0032103400d403c00650343c820900c04000c507110300184d008a01e114240010031141c4d07043d405150030790301c540304454200740c5aa039450fa0300e000c1200d000b4004c41c0c1ba0b080c40390311075100350064803179a0500000407030348075626601c081c0814015004002d00398407620800100d02c03020501c1c3d40318114203401070117015 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 606682176 1250 606680926 606680939
    0x90803010e100608040809011e030e010612050c0d0c030803010305033a02030a06090f091205121303110a031107052d060405090114010e040e06390403060e0106 70
    0x3c89000b00007038806e0740003103140700d4180d00901c43d1400003007404014502882c15901c000d402170036805010300182d0310f40f1801083d00e0041008114840b600000101221901d4000b00007940b62200801c46550346500e00c000005481c20000d5800703517103c0c10195480d8a0004d030303044401c411240d002003e940c5284103a070658100b90058007d107018001f40581d6960b103100b1104050001030388580e02d1030346002165541040158841c440140c4a503185454074054000d003101c03980104000201614011404901d4a00d040325294a00e2031082c182080c201c001c02c00e41c1030901e900044180d0118814408003207070000140140c0c13018010894580a9031007001900007406000f0039020280711160f034500141c2e41c0e40b84401d441c000c0c000103082d80346941e110118071066a5a21491602003180c1381c10440d211b00d0709016161170b19405100800803642c5502041d01820030040d03d19586403030041c104070f40780d80c100842940c10742100c000c09660314654682007080710140d501d01c200b1a45403a0301808107 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 606683426 1250 606682176 606682187
    0xf0c11040c0203090d0501060f0902032415071412040f1a070606030807110f0d151508011e090c0b0a020304080714130c0f0c15090803010e1006 63
    0x5a0068500040208a03500140d1440c440d03840d50907805150861202c0400505421440a450781f210070250007039940c0901800b640411f90342203010b0289141100310585013000041c4014500800c101404454212001302e694851601070b80d800d000e500540c03244100401021003903401d81c8114524051400351f1500010780a0301071240c2401e103254036910010300990a8462131500300b40100407580c1d5034500491664403c080807940082181c498a07400d28200022460502c8083c0800c07465101695550b5402084010b13803d620305d6480d04005121010540b4441c080c15072180000f401c2c1410700358480f52198000e240391440c5051400030390000d0b107410081d03821910f00c3c01d2826152484044160700f14000c81d00080301620a0160000d408544c40010341c40040c0152021130b07103620000c000c0000d0710030300d08a03040410443c61b2084122482143c520510300e014140c00c01d2424189141401690212001503075454004001400440040100756070800c21581c06925082e1811101404 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 606684676 1250 606683426 606683453
    0x605060f031e2b200703020d23070501030e0a02060904050c04030f0c15020312071b02030303040b0405010b101403061302120138090402040e010303020105070f0c 71
    0x401c41c00d5503545010075074200440186280c0e000c603c0b07010548000112004040c02003144000640b80d40061030724244121050a10442c0c0e14000d44600ea017940c0038010f8001c2c2d80c4508440d840001d60b400c10202d246000d46940d02c40e00c0030007510507140390500041c103603903039090480c1d1150030444015005035142412a80c0c0b03810180d50200c3d00b9500c6520051041c05140c2c8040c0c10700303211072801c20404c940401240d05652168500c54504541a101280d50b0f00171090f0150448540b540442c00b1103000316847c04005440c540b42c00031741126680806d044d500140da04a07041002c1c0070034041000001c0c016603030b00c50415621794552200001005000030401145e0480803a00000841d01030744480c0b05665020100d00810b41d5903901c2c00c904170ba0640024030480e0704200c2d17110301461041e01e500403d52154a500f007403465101001d8051140e1550210f444940e01542c20400010382013010300c40e460080d40260000201468000d001406010303281c5d01e0b03075040040e6100840001002c8101840 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 606685926 1250 606684676 606684703
    0xc010c0e0307080c060910030b030303040506060a0b070b0708090106050a030b06040c030e030a0c0203101b0906080c0d0b06070506070203130b040501090e04050a02030733050912120d06030605060f03 87
    0x70994207d140040d00105009840c458050000004000502200041482c055a0151401088255210b20605140c0180c2c3c034010180c0600c031000c80c00c684e00c144a203c0d04065254000220300f030340c0e100011b00008142d80101d81d0421b0440801440b40703098415004403001504090001c940c000143c251244070302000101802080d581a10941d1002c112404030160418010040c4140c16207003d083c103a1104a400000380300742c880413410070301c141215405400d0074404e490508010351f8036000505014482990414002c0c41004d003c1081002001e0185641c3c0d0091035441d95486681c1c0d1100f0055000841c402e0340403c020402a47d1183c1c0301ca0031108070025071513807a2102e242103400c140c1301910195062142e2540420a40a1618550b61102e44e401a80354000b001100c0701c101000d01348801b50100e1400e001d00e40d094108000b0040c0440c40e240701361002c982e1a800e01e019035400000f1030308603083d5164003d0003005060300c12030f074102c07c040321f0381d81c480815040040e40d0b41041b181101c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 606687176 1250 606685926 606685939
    0x1027050609010c2d110d120e190f0e011a1602060d0c050c101a0d0f05010c090302120a0b010b0c03040308030c071b0b040306110c010c0e0307080c0609 66
    0x180500100003001813003e0b031400440000034102d280d003101001c01c9400151141e180c202c1c1003260724900840c0c2003000360350001c00803020203840041038074400102c00805800c4001125080d030120310007140a0043c0c44030040d028102070505050a06039007050308828100c400d01ea0406e8003210f001419901040a0480500e00340b8070f540c404248580141d44041d07400500700710001c400181c010000d814009000c03421608403a10701907060b03050312000c4a480b05401341c0182220103d0a254140d14192401405c0c10450640c01d951102c1c21200c0c001d52203000140320410a02c01c502d0705c1c059200404802200234101d01c0c429031203030030440341c040c480c0036443c40002807103a50000f02401510019500241d00c41e4aa103040110140c8039440000304071754420b610b8a03003042d40788001c007041060305c40c103104d428206825076540b00024204041c00345014070043c42003a0003400240100b02c0b0300c091a0790340e1064103140d8014540ba140c92500b04504e25040510290b55070380740c410954420550444a4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 606688426 1250 606687176 606687197
    0x305181c0306050301020c1b01030b221e050405070b03090607080919050102041d010320040b120a12090602030f090d0807030c0519020112020a0905102705060901 71
    0xd034000c0c882c82d400283c15500126050090100204100c1c1020744e0f814000e0b1200304030704004404540c914400d680c0e02c010000c42d9070503910010802c00c10041c80300640020341c0000305032180c4000c1000d9220341ca00e9a243c000b0041080401d01501c0000c11641855a04505080407420340b0b989005255008020402d000079002110130420185490074818050741d0710105414a94040d52283c0210b079a00c6c10f1251524460340e840110803812a074200055040e02d20b0b5604242c2c0c1c84405a080c101e52058480c40c11007001d1340c0303060004884411102c010503000e03000740f400b6070600601101c10400e10610703450400c40d01c0e4000c021a0700780d84042c02215500c0000c1700018240d03c56056024211001c0400d86404054215150b41c0c03c3d9070203001102c614280000f0400703040800d50400900050809078041e13a2401c95401500090340b090426428560b102c0c00440c03408880060b0410000701d85a803011002d00d51951040c00da101948420040c00c0d0400700071400c1da1099070001e90400605840 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 606689676 1250 606688426 606688483
    0x603111207030e0a0c091410032a0302040f09060b0f0f0d0f05010204090518070f050d061407020c0109060e0634050304051008070e04020f0f1603030518 67
    0x191481329481401c5140342511100030000804891400030400d01c00a408a9442108421500c0480c1c2c8c0c020407010820400401c842000c0d00000410020000000404001130380d850241801049035244001092032841c01c0c0279090b00c400700030180c0141d003d62030084080d05d0707000c044840b00c00b06985242c0440c0072460280c0e49040b02001c040c09552000c6000b15480e904e07604201d0040410782c1d4284100c040020301c181d1168040d105a503011200c02c80104081d0600015000500f80283c800142e01c0f640302c004110b940c1c100302c0300100141c00c1102800d80542e0483d401102070034492410722000000080400ca4034807845040721042034180e030801d200d449050302c107001000c14401d801c0c1440410f915140e592608a4000d440c480c603049601c600c919480707100c071544600b04681d0b40454600085052200a600048444d251a00100910441d844401c00145559202200c03075000f1020307903090003011103401600980600c0b540001c0c0c1d003810b5600003441c070171030050299043c154100005 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 606690926 1250 606689676 606689683
    0x203060f063006011e05090405040c12150e0703030c060b0f030703030905010815100f02120f0913020a02060a2307050a0f030203330612010603111207030e 68
    0x20395a00850074128210501503801c00003040c00340030280c0340d8817030088411000820140504241e00d00044003440210814540b03038010f00c0c4c000d409001210750041c1c031541c2000d00e0800d0000706070385045000b004420012014400c01002c81e4041c40030341011810343da40200310300403840f4054031550310703400d809540b40c0d0358458010b804a4001d0072100c403180c1c2d071b00c0e0240485146210b4a800315107948005459004100403411003100c00406480305540849025203030060803102190452040d0311b413451101d080700b40100801c0b800115031684625980c8101702d2040c44500c0000324003801417210580309500050b016802486000300490104900f07050600b40700c1024810610092170724040c41100f0750440c00034080503c2d2950381d07030601e402d00300054040c0d02c01941d985103040048000d13846070b0010380c00311580c2e41e000710b558507c007803454100084017504070348180c6420203a0100104031050301841401c030b040c00807041c13590a180003661a681c2003580103000100740f54640010303000d800400d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 606692176 1250 606690926 606690967
    0x1c062106020d140a050c0a1407050a0501020409090c05030a0305040303110a050105180d0306030b1609090c050a0f080103080306060c01020c0a030306090e071212140705010b010806040203060f06 85
    0x2c0003c100902842c54440381d0340000703864210a8038901404603e0480c20801111000d00d03654480400300030342c3e414581d910346d210000907946402403001240002e10280010300050049490200300181d803800c03c02d51104080d4010340c4643d021400000c002a00b000a60b0121394041c02c001c0e100003040031049040c06a803500080881d480c020410107c0c0340c130044004812001401168410f5034070600a5040390660701000c2d10100d200e40c00a018840200720f1500010881d24011980680c0c0f10018400c0d541c81113864404103c011840401c815440004128031918510740a08035516503180e4004501c80a44018002c6000251480141c1401d404540143c09120101c1d002d086003401e004004010034010030006a0500341203c03242a40096480240c840f0302080300d0030001c031955a22092629041600184800052018143c021250140c28503500a000101d01e41048500050029100818452040340705005225007512110064902180e064902e03e070b4840c00200c40710ba80c10f105 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 606693426 1250 606692176 606692197
    0xb1506040e040f0611070b0103021c050601030c05010825030b0402070b0414010c050c060610030902031005070f08012409120f05010c08040f1106040306020f1c06210602 74
    0x4040c00104030060034440d00701c5014130720801024850302a001090b01c00c050001d040311480c0c600601c00b529029910030840c84202c0c040e0f51060609030f90310350815200f60b20607210300746030007001c000658200c10050390040c051280c4550040300c0007065522081c0b400e03524401c240c1e40d100041880d4a840d8101c5117903e030030800080c0701d1314292414810255503020b00420650030003000e10901070290055511070702914016101c945e0fa42e00070b000d0742d584401d00301c4040544a54003540541c505001c0c00c0c1580100c80c101103990706d0b1075030b4068241c40e0b0740700078803040200000040066040d9586115200c480c140c44030000314010000031912240349400084003408801207000c01c00101826580802d84602c009000c0340700e1094050b14040d0f4201e030054041d8601850301e100041403180c1915090000a041c10b082503140e494003000c0f0380007908091f00c4610005803085845100c0d071000c0007410700440040c01501e060000c00e00c0f05014005221340f04021001400040000c43d4041e0f4504811 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 606694676 1250 606693426 606693449
    0x20102070b0c0609010606110a110d0204020a08070207141f021e010608060108070509011205120a03020403050f0d1d0d0510151703030615090901030c051504030b150604 74
    0x2804210702d512980251144600382d80303003440001c2c400d4050085946c011450300080c11805140c3d4448004000c030002c0d00e1075001140d22200070060752248041c0801c42210340d00da0026250155000c4c0c0303002d10306e8104601110320307517415100c15039074004c1c03044075405c4015460320702d007a85000c1079140403060f1410490700108814001c040260540c001e80407151540116022640d841d4495902c81d040d43c054250012001d0005004440d21002ca1300c08651180782111001c90071450121080e400c0034070040d0000c0d40014082050120801010000100700d07030144c102c1c0b079503c400c05030403c411a00f4000b8040e200340d0301200300740c1d160001c43c021203070800d06550941c00080140030007401460841054901c43c440040f481c80390341c802d103056680d4010700a40c40c503156001001581014001071030921181088102d1481e01ca0001045c002c602c21592284120f0070f207002c003c0c0c001044088401c264105000030000724001c450380d1a0080c280701c070b08030441e20030040403c3c41445960001b119004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 606695926 1250 606694676 606694687
    0x306210c0f0d0515061003050c0d0c0504030501090b34030c020c12070608010807080a03030b0a0302190f0504020a17090a1b0510140706050718080717150f04020102070b 74
    0x448140104e0300c11042210021524890180164103ca40a440742440f00100307120b500900100c0e079101034110f0965080c99400c0560340e03a03881e803d44420b00001c0b100d0ba40444140b00c000c05401c10840410000c812246410000c08a4034055503404000d941c010141c444803d940c000780203004010742064041d0809030707010440d00c0e89a5642d4010312959000401c02d4000140ea024045100b83c292070000c8007030310f10301c1c010b40c40840c040c2c001c07140c0d400c0d0b002c030810b0700000050355610f180781c0c03d010600d007004814918040441400e41c025600950041340104845100941d005041040915071019052003a8032039402851829901280042202c4646a192000c103407802c0c03441011200100c49071800723074000c1030003203e00c0280f510b0340b41424030092210400240c80b60700b1040d0f11803440c0c03401c10044200c0c0950049100500c0c0d02070305982c4c1100c041888a1044030322401741c1c1c01c011304009c1c540c40200c004e0348010742d4001440b41317a20f41e44000114046a2003403090788010060224040d4459 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 606697176 1250 606695926 606695953
    0x161112010504020f09160302070602160f0b0108073b040b04120e10051b030f0c07050604080705060309030705010606091502011b0f030902040203010b0306210c0f0d05 73
    0x806040e6010f9100d0840c4c026440482d10704010740d544038400c2401c00854031303c4010410340103900054000c5907015024020060300000014142d100c0e00d00900401600540c6802d1504404406810801c0650401c0400b88500e101c00c03a07003054404442009502905003803842a500c1409008020b400642004240414001030040d6140030750f008840352501d42c1c0100f042615424203040780c59401c1103801c2184200d00d4000c80281c040c49001c2880726007442d00c9444031500b19400750140c5140c0e00400b04000104550411404010309001d5801c14905800d102d88141c1d540c54a03c112846600000001208401c09000b039a00c1140e00c9002400215165080501020307003e009035000d02500c00d2030110b804d4414080c021880b4031141c1001c0c4181d2901ca0b003141c4115079513006406150b1544190780c016190f500c0114001c0c48045480303626400d0003020005096a036040e080849000d02e40300c2c0950a9011400440640c2c007110391a00014454000c2480183e20810250150103000148880e0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 606698426 1250 606697176 606697181
    0xa030f1503050d031407081807151205090a080906120a140a1a0415120c0509070c0c0603021803010f06030201030e03131701020c0d0509010f08010b16111201 69
    0x107481c8207005071602c0c82041d1a080382122030b5000841c00b481500d401188125005c3d40c10310703400ca1070031400d5441c80200904802c4c1381c9003d81c3e000c3c0d10486070345460000303c3e40c0d00003110340c0f1841d55100c4c28030030750600c4140c00e40d03500002031001d02211800540310403596a00d90884003400740180717942c000741c038081a0400003000da02003000e08500143d03001a03003800703261203004a100070401e105080004064180300007480100d081c404044c1030440040b440a00c00c00c0740c408010b220b07601c054001802c050a001c0740b288040e000e203062000b81d1445600050440d0013840585400d40b400689a180c203000c0344a040035400c412917015440e01840e07a0310f91800c2d40204054900030f0328140241d00061450f40c1daa0311403000c048a03c864481001d10034601c801240300ba00c0e645010026090046407040c10303003008204002100882c0d400242c8808550700100b4580340d0f200c0301c3c20400400d41c54140c00001a10840f03800c944241961070100c010003901e001c8055542401915600802581d42d016900 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 606699676 1250 606698426 606698429
    0x4030e010807171306180507080d0c0302070b030705090a031401060b03130b060d08030907140d0b13030903120507060e030403031b0503301510050a030f15 68
    0x381c0704200080115001d6540620302c2d41c031081e00f2680d02c1d0303522a040d070359241102c0700072164140ca0310074010007892003c000c400301c58054000b03001e440340752141d01490a211800f02d501480714003900c01e00032980103c2d002044800b070350a0340b03030745e540c807400115064820f004880e43e002401d07040110a020318a00c1016034407500300000c01030300b078558041c03000380d0004803074485c003200b004030760000040e00c070064894001c440500380f8000f1203040d560350010b6030800c80387d218403540701c00e904110440d140c5001230501e11058408240040f60f549411600d880010803800070f20040c0c61300e44c01051302c034188401c0210382201c54140404540040181507601044041d20003500300b54100848880100440f811070782d15444d800000025440c03010f256502000040d5510700040c0f00360042c0d800581d140c1d9002111600202c2c8150f02c82003002800f5490141c901c014903a800c0ca04100c040c0c651000c1e198605146040041d100c0500340821070240c05900030b90101d0509000074072030314101e044c20703810 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 606700926 1250 606699676 606699679
    0xc0305010f1a0f01120e0d0f030504022d13020c01060815010501030b15030703140f060d081e0c0a050c12030f030a1103090c210307080d1404030e 64
    0x1541d603500a6030075110041d01d2a40100076000c2444803074644110340c80a100d82c18100500c000c0607410300e0308100d400311500000346401c04184078a0b41a41303c183c20900d44840c1c1010840c50810703070040f420400404002c03c024070040321010000b070700c3c80079201c8a4034800904001d103400032402d1100107034028103080347c402d42c244100820411404504d1101c00c80c202050000c030340c0c0ca800011005451910100b90300200d0105034621a802c4e07850085100b5050703074a0104104105d4280b88080b01b2004001007001d10409050004940c0c3d408065400035402a80d41520303070816030f1001d86089810a003500740743c400000d909648040229228007454011000c1d41c009a5030300b01030282007003407001d10807001e070020841c100b04110a40041d42d0410014500011110074510303d0302415801910800d44580c84016954400c3c64494601e0710707402c00130100180340103004e01e023040d503178002c5900c001d0400758046898540128240d003c582135500c203184009040c1868100542100d0003e400396 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 606702176 1250 606700926 606700931
    0x6410a0c0203240415062303150c0316050c0706090312050a050d0507170a0902040e0d050d2301180c050414010f1101020f0c0609010c050703180506070c030501 70
    0x83c490300b40c0d000f2429109090100858080c2e03500c1e584c5907410391130f0506220b01029507884020444c50600700c00c0d0080714600d8031008819040c0c039000c051410421240103064060000c04010152a01000b0b07242c0080c504200c803414000403600590300340c02234040340300c03e44c842c094001401c00d80c441e494008590154040d801039200c0c0e10011603c034481c022082000c5a4104800c482048886c0d00031540072085203400e000c16507541400312180c020540395489415166000311055282074454800040e400d14001c4c011601c030000701800758040e84140d85105580c0b00c2c0d110b0110740c4904080786118600c10713001d903025a1a14074280c0e02d004060b000021079403500200c1c0360014041c404403004e6480750740181a17101e4800004480c565403003022002044411103440303101700f60034005880b40340c04568a907600e850f03104e0601458404001d0213184141c4c1023808015020303070880c0c100c0721041d8041c81d00640c54120b40703045400c034420a902c05900310900088139000d0011890b02c910136030788106c009 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 606703426 1250 606702176 606702193
    0x316031103060901050904050c0d0605070f0f0e0f0a0504110403030215090613080c0f071503090b0f0c130e071d01022a150c0706410a0c0203 62
    0x1461680011030302e081d0402100310052044d841d00b08011a8024420390031108102d01900100d00b40c0c039010241250307642e85507030038003000c0c7d500884010040340580c502040041c0203030308000c0079a000010524020590324610110503156000716074040e00c800b51040c070030760117441d204100d668000c1c8400da005001f074948207445c01d0029641306000395980320062280340c44042d40070040c0030303021000301c401074020041e42c00c3d01034040c0710140641c41c10744042c00055180000040c0300c600c11609141c01c040c50200800300041c2c1641c3c0e1183c02c50322468030118560f59600142c03165114070100085076189000002414008003801c0611500031607440d4000c071140700e0001007180e55156545805a040070380b03000c1c01c030040403d0895600d0308240e03240741510f4000c802700e1000f070b0580c074004540e0b00d07000480d4481c030441085940c000704014a02030b23107000b07481c080070407184110600700e40880c0003c0240b03503625103404194500c11040707076189075940d406070900034000f0241508224001c0c002e20700e2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 606704676 1250 606703426 606703451
    0x40b060c06100f03080913181208090102040e0f09030417011e0e0a060b040f0903110f0f1c170a05090601050102011b081b13080c060403081b12031603 66
    0x105182101d0784110110f040c485043c0c100320303044d0024030342174202a580300123848400b40204c1e6852011400b400403a2001d00544000038000c4c00b000f1300110700f90380100010007000d103000740c0140c0d0000e003030341440e58580c50381102d00c0d00314821580411112000f01c0000080303a80107511803123010188101c0410840000344502050300c91441e00902aa00000002000300d1552b4016003640c42c0300a1001070408502c0c2d042000b01e40f501042900015044100c524107228104400c5101c5183c00e0024007000304428481d641d10082a4a2407603a40b550995454000780a001da0341003c0c60002d001c01e90700d1605d858687c004003c1210340c00c40e03038030406000080950042c45607908140007003d02c031000c603003e504141c1c0e5145000d498084141d10301c072400031090110002401c01729250f058110b90312403500050501d45481c0d03004882c40394004110400000d50542c0494014840500031162000c40c071030039141c02d00c645022442c01d00300380042006075000d58107148800c0c0150b1610108104d80c8500b8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 606705926 1250 606704676 606704699
    0x2004060f08100b0604061b140708100b100513090617010b040b24040f060f111513050c03060c090114041202040e030d020d090c0602030307090311040b060c0610 70
    0x883c01d500050300700400d01c555440350701c200310f28a403448000c040c19000c0e07a070350b4000f6180c0c0f8007903401c02784c00031642804003400500040c10b280008034401e02c15918010300142081600810040500100140295849804800001c02050b40500400c21700395128210090000e440c050700c400d551030b201c140c85044c5003501c070320050150040e04001480c6449125600400017000d0115030424060000040c2c290b9804118800340105a5503a800c5a02c0c24401400c400c641402c201102c0e04003540040e00d40600401441d1305c0000e10401d802a0f1800f42003003414908200c80e0140c25020340c4041101e1805d204004050540081c0ea807201c1c440129841000365000d035001d4985800b4141d040c1c3c03009450180c00c84650b45c5002001c3c0c038601218120700034220790201200396115034903078120740203101c691001c0fa40140a0381c000303940382d8501108014a2444180001030010381030002580141d11103520071042c2d058040d00e01540c4043e0b00d030500340d980c3c00c1142c0c0c22042050029000c41d0503407a92 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 606707176 1250 606705926 606705941
    0x7111e1f05160f03060803030a14100e040201261e07050a05040909022719020c0d11010e0304030b25140708090405040812010e10032004060f0810 64
    0x129620310b5160380300400f10b400100c4040c0c4036042684418012486a4041c00254002d8641c560300107804240c0004a1060f207a00034911291007240f41d0003042960032015016609c15424a03080111100d4000308a45ca0320f501c2e0480c00e541c0d42018100b18284100705421192480c503052118007a03034030760780111160305c6126101d03400240107101c10803403131900d0307008550301f50f1005068640c5903400c0941049047c0109809842035454202408203142400712580c8510022140541c038010001c14859524414212404104400c100e0341500d540800c6d884480020a90401d4036592941c0f420701d000303440c0d002c2d600d800d0007400311640c6044440a08030b058410980da034a0340100c5d24100300d03568000360881c600a90300c20004210240700c03036031184200d500c100e101d5900c080d12a8807140c00007070041016000780303080c80c0000007841000c064000b940c1c412698402c41441340003509000c0d40381c1641c20382d80241d42050038a0008604000320f810014140d84801040300c26480480352200140e580301d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 606708426 1250 606707176 606707191
    0xe010b030c03120f07050d050703031401060f0e0f21151501050f041505040815190f060e040303050103030809071a090607140105101d07111e1f05 64
    0x8030102071901c480078004d0500807000050341810800700d0380b5000d00b80700000e1880e4002800001d1104100364061158641e08015955900703681c0d03052140c0507120130a40c0301171303d0910020664103d80e1b40d580c0f1b143d045c8181c0c80508946611a0392168450501030280d420b4400ba005d20038983c103115099800c014428005a0100c408000049005413419030003101360b003060080410002c24032000d4200140340d440340c195500c0340d0b0350b072030210494109440c4829082881c400c5030103100d0064010781442141d0500c14100040d60101001c00030001c04a40e800004d2660071201000140f45c0c050381300504036406919855440d60f280180140c81d4a03550261010300301c110b0040010844400d805402c0030000030300007518103081c58840e03068080c214410749210707a450f40200b059010703a40300340500901109069002c1c511070450084600440102010100242004903205900742007040001440348001242d29402c0358544003500c465040300440c1c034601803190070050125039032044603c41c828 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 606709676 1250 606708426 606708433
    0x30a06170303060609180906010e0c0a090501030c0201140a021e03010315020d06081603031107050a23092a16060504050c0411090f0604031205030a1d010e010b030c03 73
    0x81e004100005504808080c40e0000c000244d411840d40c0c81b0f4500702d0086840400800aa41c0341440f50014800c008181c01c0214405000411202d80c01c108514195682402c02181a2002d80400c900401041c0200c950075000305090056040c0d1640c0201011402c4450f010301b03c192442c00c00c81e00340f000f07100081c10841c1682d40c81039401180e80c003809010b81146004540c0c039540c1c2e9015450016070fa07800070300000501208200305604000100300c0300714498098a40d15142c00000b482c0001948658850711002603d10700507034010071740322192000000c01113032240c00d1421003201550381c1c03400e07d034418926184140b0302d000002c0c01034508900104500c890200402e070384031700c007520005d04121030074800d00c0c0e2142c0c00e0307956034050100b074802c2c01581c0584411030f6200300180705908460032805411304001c01e02c085004080034426000e800c0c103040c1d94a0302d440d150600104a01e0318405068500c0104500c4000e5043d0060740010b502c0c10000e0001e200440c04143d00c524241c90807503071690 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 606710926 1250 606709676 606709681
    0xe1903020d14070906031110091d0a061e090e06151002010b10030e12040f030b070c0c03200a081f021204140601080a0308060411070215030a06170303 66
    0x8140d8071404031012400d038141e981c40c1c0d0b59002040d00b0781c5e070350350012512403603130103458080c50502c40e4003483c68101616200310541c0c50b14014403c9000c5911041c0f01c1241c2040001c2c05c4a80316421080040513000100c032080e0141081c0c880302039005001e6040c2079407c141688410450005059001c0d482c04100c10504d0031001c02007140c10000100c805041d5521500520480c2d990390581f284004000e4030017082c0c616414461500340340b803000c1e0b11201c41105010a22010811012907000e0306c0d0322030000b0480c2d80f01c0b064203440b01b0445441c004c0003809600d601100f007289611011280d0841c2940805081203070104002141001c0c1c094101d84da4804522220328081280800640130103010b001850200328078113603214403004841c141c1d521000005000c8041c1c008200050040034144044d180701c505a035001802490302070000b40c856a1203010041d41408408200c0ea59181d008050003440c031403c420800031500121001c0301258504038000541a4940780002c04441c6001e02952865 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 606712176 1250 606710926 606710933
    0x9071e0e0112060f150c05060c03040327090501140d0209060406030f0c03030e1905010f050c15070305090a020105032e06050d111602101e0e1903020d 66
    0x11001104060402c961212000e800310303468400d280113400e026030122401c6090003841004401320720051030070032841141000100303001280312600500c007160625580d40703035424216040010310342c2105001c0241c2c50b070600c200003142d15240442c3d58800b42440140e9071503004243c14800050710940280001e0b64090051500c0c00050350700c07080040000601c02e46139114800c928401ea442150401c060040c02d10a041d004801d10100e0743d0304442c819a451050312001d4584043c0d440307041d0604c0107040042c21228090705c00e5425540d5940b040f034034841e07121004191001da0235500b9202080c40e080100f0a014004202208103c1d01078548910356200c4d4602d05914050545070203400041518803404100056141c1e80020302c0c0d20b6481d0350300c650807500640f0407205600c4001108500811400000d10099071401c1c4005804417490003d014500800362218200b9200603802c8800000307114030019001401c000c9d85071003d03115080450340000d0742161040f801c1c00301035400b0500c02001e1000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 606713426 1250 606712176 606712187
    0x181f0219051f020918130f02060405060c0109230d0806130c0f03050f04120e0d080a020109030806090702151e011412150106030207020f100e09071e 65
    0x1000c1c0300c1e00c11140409080700300b0348880c8180909070202540c0000e5985410f18000607089075103ca0189001e9050403c00d100e203038221030202c402450141700714484d03c01d564a88059500800c00034105956508641e02c5190003404100022548680f440c042c0e15805007030140c80603032051988d0700030000c1660010007500d0440700140003070341c07142d030111003110094891300405202d0501603c07034404c01c40510300083c0585400922a001c5c50704c0c50301c02c101c00704150584019007201d407400d00040110004000c6048405a030001800210002038000e0700160305600c80002c140c02550798003265100c0c042008038002e01990300b240141d212034060480f0280021410350019070100594071901c0a40d00100a0700c18268055030082c284c0ea0703030306142c6080407907543c858160303104082c20b039040031540445600601030062104059001c200e0500310b458882883e041070000404201100000442c01000203c1c003924640c02840990040b8180901546603002c0403d00e400021241413602c1c84201c91 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 606714676 1250 606713426 606713473
    0x510030b1f03050d0201150806160c080706051009060603050f1506300a020909011e050306010b07291f0314010506100906020c1e06181f02 61
    0x420901e000040055400c010310040201c4c260004100320800c481c1c00750380160107522051080e001003003080b8600e003020454000e40e200781e0826203d0104039042c82c8506002d1101e0080c102c0c1d25200c14840c3e1090b2996103202114030801091105a40381d1a04a0036140252041680b60811340d011611b840b0716092034520071000500418202001e113480c070149410000d40e20041d880910000c20300308031101d0317030240d0302c031510900079450480003001289040c40c05100382112031a00030b0001420309032102400006050080032100c0340d5850307242010103681f1000c41102d20310f8104041d8940007c104907030490f0384500b1035000031996509001400002002c06413030650880e50000800003076a1000c2c01d4520000c21000000d451802401380512b6812400c1c0000a0041440040050310b070b0001300c500b040c020039a01070039914603840c490315292042e5050a90b01100c041400000c29031070344400c145040741110b02038148400d00d0400344043c49450000c10042c2c020515400300b0305010309882c103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 606715926 1250 606714676 606714721
    0xa060b011d1c0813090b010c02030a0b060102030c150105040b0f100302031f090c081b16050102040b0a0c0c0515030103030503130209090703060f0501060917121b010510030b 76
    0x18001580c3e105200d500c140a1200d00303182e03502050098640a1150304004039007801c00041e19141c54001a586000c2410018290006540002c0c4076034801d10551341b80040310000c40c0d518440c1d0f181c0c0441010002d0280ea80034a00c1c1c0842e041240c98449486e01c20050003906900c0b2509802c2c1040380607605c0100002c1c1c9035010447c94401241400040c0e00051500c0b10000403110b0a0120082240102414248451074a0f00100d80035100350400c4404640000304c5010124519242650180c0610f501c08009000301107001000e90b50420a070a4030309124600080d010780d00d03001040340c410241c0c1d61140300300c1030600060001900520007580c009910320410320080da8694005001101d040300d180a050b0030a070302c20400c101c654040c00c4840580078500b800150f042c40e00c0104007100300e10510420020344d00708464110014002450100a03080c400c50b0384920301b0076070107820f4030f041842605942c83c1a0004070781c104c40e140100d0561764000309070700b159290031241da8080088051040b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 606717176 1250 606715926 606715969
    0xd12050106170c070218070e030606030c01110a0b040c050108090d091802071b2102030607200d0203040501090503210d2c010b03070812030a0b120a060b011d 69
    0x1c4d000340c2c0d1810395202080a6081d0b074642c062800a40040ca00e11406020703500a50220f000c0c440250f50101e6015031094007840d2180341c038442003c0040c6000348140e0094903000245c8240310038405403104207815903c0c2a213501c0d9154449541e155942c200c0491300200048079910103120721007100e4820864107084650150501e4a140c03154400c0c41d0150307011480c00c1c03002c04c1081154801d44d402c032800020705694070346214030507600883d0316620014120010404040603c16090103000300c0d00c035414101000b142c0f4410030084020b0f5a943c0305001d558085a84100b00181c01d1500013502507015200c60a00d213600380070507040000d0358002547c3d072414141c0b0b034190590f0b01c240400150805003e50f204104030092155102800c607180d01241d1402508500c80910041e600000c0441105494000051350390380c2d42c4142030024044051100d078001e12144075013440302c1d00051182101c0340188410041c40d001c4000565924859100f18402e810140c0441500c03403601d0143c5054100d802070f5032 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 606718426 1250 606717176 606717187
    0x30f050f21010f050402040807030611190801060e0d150905101a0405010902030601020a0312022106040507020d1d0a080601030b0a0609271b080d12050106170c 70
    0xc0c09440c02000010092071000004004000d01c004003440200000d9a04629240c240042581c1720b1456000241089844006c075441c1aa0042c2c02c40c0c22501c40c100d070240110074820300c002e00a19080c400c900014441619403110741c41e003500c2103000c103030380056250109222000140098075442d20195001c2c02079090700e0041680703500481541514180c0034040c0c0f0594001000216a01a0012580c16205008000080e40c0000d900d0300c150703801d801c1c5903040188900b0014080d204066846100408110070540300140d8600a54081d1078100c170240629034808508903542c9204c0980700d00015007040d101c41c4400b5002c0005c2600380f1026000d143d00300d80b24400546040800c0c2d0088802e0100c00c07080020509440c0300d10009404100000d000c4c3c09885c000310310350214031007016551403003844008410004d4142a9030300c00701480e002c0d11004da50394000103880d442c8402007500440c4c1d4181c444240c189031881028144c03129515400001840d41c12000c1c00801d00420100ca420010440d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 606719676 1250 606718426 606718447
    0x60e010216260a17090307050d120e1006150c03090521030310150206070e010305090f01050702161d0103060507050c0316020103060503030703090308032a0306040513030f050f 77
    0x308803601c015125080301302c0a1003205490501c0052050302240c10502c03800300055004165080001c00750314020031f0195000100070001c2200d41045807152290081050070701c100d50b00200102c0324110448040050031400c2900c00c02c5a0b0040103000482c031000501c058a420004260005c46034981c241100841442c0c1074610790090700c00c1c0c1400030460394100002c1a540104405107541072001e04400d042120000e010403071042d522a040c5600d500001e842c1687c01c1203280390351076001c002400a8200000003a44902003030200c206462810200032580c1c0c40300300000c0880342c4ea090030b0040940e286864600c001e0502503c640e0800600b085204d12550b030403c060b2003902860310340e03104010b48603c0050103c1d04150f01c0307180207400c140403420100e604200d40300704580c1c0211803246d4943d2503107041e8880c0081c504007200da0001003100e1103081003000f000742d44100410396042119444101c0e400c8030007200c200c001000100384079860b2081600ca40040c0c11841014821282071482c0d418 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 606720926 1250 606719676 606719753
    0x5090a0209030714031c1e0311030412080603030c06060415080a050706090e06130b0f0406060507051e06070f1b0302011b090803090609030705090c07060e010216 71
    0xd01035824450b60a11625243c81c0c00e10286488640c0c0660003001b00c40340403000351103d1042e103a502070540ca50400c501100380680c01c8060410340920440b9035030700d40342c40c01d0509003c040a00900188031440050f0650800000b159003200b41038000f0900f0340e59400403c030240018072140031420711500f40c00103400100b0000e130071341c00e072092020305100d906000d0001c0ca40c041992100468156050501c0500d0300d0b035100707a1286840360000810400190004031700c0700150000082e0b006441c000000507150740c000b0240827040d01c01c1d41600c8040f0039004000d62556440e0700c5a070860b420803030104040d6802030749024a000c48505145d0a4a05c0100201d0707480301c5079104c264003503511901c529070715101c1c803040103003011003600381800c0076420b003800b0316030b81e00480c0b280394001c2600003003504450750100328090080a004001c030007545028030510355130707402c140070890f00c5030704103203000702070724810300954902c0d1214101c080c2802a85440c0d00ca40c114408208030041184446a10207c10144 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 606722176 1250 606720926 606720929
    0x8090604080a0f03020f060609041b2303010e010b06030c1e0403030e01021507021f0608060109020c100209060f2a03090a08190b09120d092a05090a02090307 69
    0xb401400f40c01409414080c4c10710100005030b5256801601c1003104503604c1c8980160015084031101d03112015040004915100a030042840010001ca1481403103201940c3d906070140150020301094000325440750030398050082c059030090341800003458100040026000c98a5400300786226680d010119250540c02508240c0c00100d6284001015503010029070b41c034550f41c0f81c2109a1031601140094071004800352140440b118214010120b000c1c580003e00601074000c1a2070844d40d5482c940b400a40c000c61030740c1a107015017060800e550416200361504441c0c09058030b0300e0601e000091110035401580150f10b110484203120444011042002c000c0c040303c2d10046aa07060004200003e107111503002441c544d1040e0b8103170704040305564100c146640d21800001541d01e454507081c3c00c00640c7c2044100e000408610420040115005500d00e540110440d4001e81c0c400504c0c0d45c00424514504100c40c21150320400250610a03400e56001d144540010b05001c544000070307041c14584d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 606723426 1250 606722176 606722183
    0x40213050108030d1d0d1214090d020d11070302010516121205010909030e0d020319030206010614040339030506090c0603040201091a130308030f0105190308090604080a 74
    0xc982401d000500e0301c2810405048007185503400445c0548595035284804481010003981c0c00030215242c085030000200d030001d6418160162901401040d42c0701003480085005126001c101942140a26001d14401c140080900300c6035045400540720340e84a0801c2580540007820000b0101d1300041142d0a0044142d42c1d100702400301e00340c02000c0e03510680104514a10303000c141d6000030741141307000761300d044252075446201100d03000081c240b00803070326401c4240304001001c1c0c080580c00701d01c041c107076a80c644841c443c82040c894403440034016800300902003105541c01201d102460205045001c80c3e0342080542c002e070040e5102e0800f4856407003210380313074004002c1c442041002d0150003031814041d6407071411803806400080200007184030b0036044041e0308a55141540c01d80040b140004007400401d01440c0d62403074403c80d1540f00300e43e03000b4800012400854986030101846030500104501c50480c1811074544801036070010000300e90241c020400010300440500005030785601 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 606724676 1250 606723426 606723433
    0x70c03142208030c1f0e0303012711040b0d0b040606051b0c060306060c010b06070f03030510080616050c010c020604050d11150601050c010f1d010501030503030708040213050108 78
    0x207000941c4068428240c004059a40040c4184840400000ba50741036030485003080d039409843d00310b40b000c0106948802c0c3d1480b4040000045012000c14251070840800c111140f04c240d03844014032800c5032050300317005103002070802080181412070300107000c4070b002d4950006200703003030080050106e5089520000c042007001c10309600c075411141b1150b2040322410040c08102405e44001079035403100500e0a8070900001c507904000e4002540603a400d00300c007070100c59072a40c842c01d00c00c4041d810150100c00280c1080005903015010484100c103c614501c010619919400b15515440b0004041c1c41c04000041c026580c0c0d840003406003040d0140141c0140c041070605051250824040c0380800051007111a01504011000034150152076500c4102d0720f481d0b151f640049901d44140e4444050301e60801d54400004815540003c0700c005480400e0303840650141c42c150b090b42c2e003d1101411941050000800460091a50381d070320070310040006002c6070941841d0000c0320402e0300704030001c1d0b1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 606725926 1250 606724676 606724717
    0xe040e010e0708070905160c030504090908031b120a051302090a020712021b060901120e0c0a1409010e0702160303020f0706030204082a030f0c0310050f070c0314 71
    0xf000740650000f400c00e20b1401d003d18901a03c880701c00d118900a894108560421280140344c81142a42c016100418091000e0350050078110700c903401c20b8509540c5201c8011440003800d600108481000010b98540700071a0707594100d034070007001c00601c5820001e500740010300c01070382d42c01d103460b2007450010380050300c0d8801401e0008240050b01d03400d406540c8105a0031030044c42010301c2d18032803142200d4807651007107040012a42802e4495020402c281805000c2d4000b020100e510b02d003900c025104c07804403035518000c41035001103004005402c000e4000041c0003d4540c010810340c0300780540103c0301c210030105408039a0454985c0241c0050700018809485c45006000d102c000b0b1031240381c1542041c0c1000661902e0b40d500d209514401c083c0e01c0c003100c0842d140c44645121740c403002000c4e10760403581014015190505018050f20234003a265004603014040d1041c1e0b409843c0380500e070511035403030090955100184660035424405000b01c0c8003000741c2444000c0410140e02880c9030100b1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 606727176 1250 606725926 606725939
    0xa020303100608010f09052203030903120b01050f09030715020604030e0919020a18171516201b010f0804120311130b030f0a02190e040e010e07 63
    0x1000036410500801c441c1c00f0040244607050350604003a500000d01c00259600c82003882000c03151a00c04d8007641000700c0b2646014560982d1166502a000f80c5440004003110790020007211400004076000c58802c0c81090706410f00a80a030174168405011582042e8540004600508040481c80010703400f440800080503801071100000d85420740702d50000782170685603401540700ea0282040041c3e0b020401d8051184204a1108001c1e03851a001d1452921b454141c107090000c0640240c0300c1c402d0a14a083d06041044440d1040d002d800d0907001c01d5800340c00032155807034810640383d0001415410f8002130f50f42070002e200200e0350b502e102884602500300140c039402d01d25209006001d40341c020000410a15208510030107003070725001643e5102082c000b049801080860690b8000c2e50034081a038098220065001d0880c0400381a07a036641e403c010410b81c0b0131000400c00041e41032521030100d0380940c02c10852180000c20104440714508400c1e400c44811417184040e40d4802102003005 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 606728426 1250 606727176 606727201
    0x2130e0f06030d0c020303030402060a031506020105090d14180a0e01120c0e040b01170a0605040c050f0a24050d021305011e0c1209080601080a061401050306041b08030a020303 77
    0x4600795410300c007100c4c26a0350002034403400018030190046c4000101c01180074884d600000391b40701d0b00ca01c0380e0b04c0e403a10381c0c00013030080c1030460354500d9a100369011044001c2c01404e08000384c940c1094418900913000403c1c0c0c08000c2e01d06207440c2c01c90391500e03001c115041401c8001f406001180700d82c0188903101c2c02e040124024951080724541103034014000460b1096403024150707040480c0160f21010128070591610141135030140c00703149803000780010002d00c1012a03003101c400319012a0032982e600200856a512403180300d5009040681c0c0c03c24a403d00c00e12000013800d241070640c14100310707079110743c16603000c03960a2101041c20041440a0761f00042e21801000c4005040e03c6c0003400c00401901c0900302d1038000e000d543e07003c1c1078103c4280c1314480c0030028082207426504103507900c5c031206136120560f10b0221070150600030704d014442c0308450210f040341e90040043c441501d854907802801c400301d2503410401c42018a0100b03072101700301300821240090b9401151b481c5800c0003900d52 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 606729676 1250 606728426 606728443
    0x30408010209130b0117040c26010605010915111906020c120405060906030a090204020705060115141c150f030b0a050c031602010e01060f0302091006090902130e0f0603 74
    0x40c428500004c22840e41d038031206e441010303900c80d980c07034506490303600700321100b9031207030f1b2100088076482c0703131050110328000f1401c110541036600240507894450006465680403405001100c0040030704d68041c941c820010f040c240c2d0000f10640304880e58821244030b0014011805540c85a000203900316030702c84c00c004460b00c680b07070404c1d201d0900d810400003400c0303407058a620501c500c20100104c3c01e451000e034011900158000c01c01c640e104087c0c0742031030b1900b10034410250805104050500040d0041c3c40319640c4200d4220007503c1c128501402403d6407091114601e421941d80f9900341103441804401400341c0008110030354140e00d14a044400c10343e000780320290440c1003806001141d01c080c402e030385e01b200341c07070100d01d035004003184049004291541682e641982003800005035000c0c0300c0d61240c140c90003940c110815650b54500c3d0348038401213100ba440012003910041108034015805808917000c02c42c005924140c3e5007400310b03d0080d0540c0d2000b00740c01640240701c1c03686010400e005 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 606730926 1250 606729676 606729709
    0x3020c040606300905060403020d050f03010e071e1808011509020a051c05041406040201080c09031f020a021c02030919090903021b120705061b030408010209 69
    0x690900b0320050540588024401c086000951498642d00031480180e6105600382d0301005003560b07608207151b031118140c42c2500940640505001d11318407550481c0e00014141c2e001928507407070516034005001009043e0400c10422002041007085501187c41b1103214031350702e69403800300c0383d180030007805030540c86081180c0c540000c070200c03240040c645c1780c21503440d4580142c5880785480e0641e41c6100d92542c004600001c80e0032400a5a51684414052805208034100040031964455900c0d841a50043d0224405e080098030700c01c600b20041c009105c2c00b4080d00e540300c40c4640100284103840d403c1d1002c050700402e01035255030341003200e501203840d64030900207041c41400001e500c070300c5001c0d00c03c0e0042c082810071501ca6800804610028200c8000821004400d400d0003501c80300b180745000406064011032407001e1170504520405180f05101a01e03143d49031604218059100340041b44581d0348010388407000c00c0061002c1c2000b080148005a038a85c400340c20425260800560308 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 606732176 1250 606730926 606730931
    0x71706010c0302151308070c080105010e1e0702010f0f05040b0f0712150b0301090504150b0a0902070f05070f09050106090608040f1401060f03021f020309010507030c080d020703020c04 81
    0x30004280d0000e404080c241d803448410790241c40b07181e0345204c80300178020040c0c40b11400081403402c100c4100c0c035413811180614020411071341c0303800d68030f40c420b8410703110b110810680b440a0f400090080ea6465000302c0c960000103048180b050010701640c90420300074420555940400003445502402650700c0b4180e1703048500e1034a0300f084003502544102e12203c03603c1e692034a62842c01c55043c44030038082c0c0320482145071250394400621000e0901101d084ed0f054810518105200d86e840c0034071450508014084400d0038180403c50009420100717060340c0d5100b00c1da40c04c501081041c00100007a14040304d202654a080200d03290603200c040c2e201c003040100009041007201c0e80881010382080e4841c0d01040920a0b900340810400f02d102ca120b400c55290010025010380030b8100202242c0c8255500900b8002413441c0340848904242020301580042008d080c40758840d500a0808a120742044d2000d075050ba121040340f0703045600c440111030381c0000c4032014150100a8440484402c41d410b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 606733426 1250 606732176 606732197
    0x603100501230f0102280c0b03150f010503130615030302030c0d020601060e0d05100c110d0c050a06091a0903070606080a0309030303230907030b1b0906070c0305010507170601 77
    0xc0d036030504086d80001d5441c408900b07080a80d907551020311015042028810b079141c80d60301d109440e034030039144015280b41d607103901204c50801642042d1880c030161540c07420f40d41c0d42d00308800e0101ca2068111800e50ba907040840c00742c81e82d01c0315072028500990065407100c8030084003a01d00117001d50b081042d54810343c010088182d01c01d40c404c40e60345003501c82e040381c0715140c50550700d001c82180454144504107030344d480300c081d800114444031115000c00c85007100b000b000142e07400307034000c00040d10542143d5081c0010600360b402801d80c00b84900d48515061641c4074000540c6201030b20201a0ba400000c1c02e582804058060300c009005030300050400850603030b5014050201a110003000d05031102c03140300c1c410b400721b10280c60701c404044045005140446800d0b40302c43d41d42c0000c84490310107038003142c00340840484401d5559002a1070328a8600c0040030828180c011403030440ccc801404c21004000104207000710f50086405071112090409410529165a04001c2c4002c0c10010348008 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 606734676 1250 606733426 606733429
    0x3080301030204090f05010c0809060a0c080f06030a02030a11090a02091e0a080d20060105061e19031d0c0f010804060e0312070210020406050a05030603100501230f 72
    0x21281140d60440d03000071800224604040060300d60035014200d54079100d61b1892060700041d410b03118843d00003e4405950701d0600c0d03242110400b07000d050000c1c1c03452000500e001c0e424620141c0101c0d00400f168040207142d4002458429030a000310340310303503a04113180c0302410300444040d040070b649007046d42000c1e4804080b030805104401e44548483d0100e02102107902c0351403500018140103015a007101b02105800351194520300304000011004413034840648c4004aa4241658002030056140c401d0810f00704a06000d41e80744088201c0003005020100e001d4680ca01d801400141c0300403c08003d401110b0140c00303040c400e00c1036236400c03050307880c45965a40c4a04071001a000d00b00400301d61951b003090001000c000c0d80383d009070f01c070004081e40b032001c103210441e1107165550300b150120021515000164003483c8158004180188400c62055000300c01656200801a041319100d5685d6254601625002e0b40001d4000054180d40c000005420420842e00b1100f540c200508068010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 606735926 1250 606734676 606734693
    0xf1508010518060609150a020c13060305121c0615030c031a1e030a05030322020319150c030b011103030f0c03040f200108010e060d03050a110a081306050403 69
    0x61203140310340c000151032041907503643c05503540d02580501060b07d03440c0f20440650b46010000c0344070b102d81d01d0150000c041d40c019000f46000c1e00c5e8070501501e032001100d040c440980e0440d0070858150403501959044103c0303184161300041c100e2505100c001c400c0d8060103002c0790541c6000b9800c06080182619819a01640c1030f0035150003039400081400c42404003c4118144580550b0725008031100e0344248034001010b540604024108441214001120143d4051903810000c0d00350704041e0305c0c0c4155881a101501c8001d0140004400d40040e200007007080303980c85126070020a036031700d00d03c0c590303542e01c0402d00c111440e041d8011895810710540d03040c0c03540d000074010100240d000000404009014203002540f581c00311a01154860514003121402e240102190000704c03ca40000360b6107002c00b06840c020070015124115a8034039440031103060740403030408024020041c13540e2881200030821140414044c84404c1c0c1c40b8151100d00c01703181007440e4404c00401000b400240041075004c03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 606737176 1250 606735926 606735931
    0x51606140115270b0408011d0307050d05091c03090314390a06030912051612020f0d021b060408030423120c0307170a0201180f1508010518 61
    0x4111a52201078110502041a01542004500348008140024051b8054011088018034110151720400142c55216076074061800e0160440d4485240100d40e240518014034200101610501c1e4503601d00d001c030000880614822400a250880c0c20000c1c0a1401000740d184411384002c2c00d0001100140032700144050005043c000c66001001e00128034110008c4401c0c4902400860500d0354a09000e0020501c00790207440c1c1c03003048100ca0380158840e400300e6205400855190101003540c2d2590329040c0100c1600c0e109620941c62040100302c0d04010107400145180c0c0140b241e2000600201c2c40d2a4040394082d0150f00b0034042408040c0010054400365104086801c20402c611042c2c904044200b00403150460080700c0071100215000c01e083d200c0d22030903000c84d440c0c59601c600340441c0403c05a08410306401c0348608000541c814034404400c0c0f0783c115040414075485078108904104c141d40100b01050501c1ca200b000250046070342401000225007074520b09a01441143c0e861000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 606738426 1250 606737176 606737207
    0x3120606270301060911031b03161808060117010f0513030f03020f030c120708101401140a050a09060e010906030e0a0f0c06031d120307051606140115 66
    0x140c4641c240c094800350712000042400d82030a00004241100c0154030340c1c0160740c000008800c8000300513103e4001d008803800b1701091060302211082d00a81202c5980d10041000c28210300c010001a20359820411103000c1e042d99404c1110540101485a00b19030b5074210030700005041c03e04000e000c0c0c80340d03030903000441d41504204002c82060348040b0b00038030461902000700031000c030038400041110317405000b41003403840c100001c64075440790640c2d0200080300c1c1003080b0078036900180301c40b00858610005042060400352039840c0b5040e80510300b44c01403130001c40044c0011500360140d56000034144004c00749410040c0309080107400080c81d445070760103010141500d42d981d03150b484800b0086111090f03000b08000c40310150300e14058905507c60b10070b21001034103011400e1303050131622441019102550009060050000c83c0001003038200510580034850107000320501c4682c100c101541a030301c6480009143d030a1400c051002c0c0406070003841c1c3e8003074000002c004658011a913481003040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 606739676 1250 606738426 606738487
    0x204020c07030b010815071e03020a030605130212010e04031202032205070807060504060203160c0e0a0f06171b0a120302060105040e0d080a0213031403120606 70
    0x15400109481d265469000030320f542e410100010b015880413800172040380107100c0c1101305440b08803040312520110140510190b50030501404030030700950050424803010304000c41e6141d501c2000403078000359540b080c1710780c580010704c000004442051040c050030765030192231305600309510000c0c030300000c00901160655001011401c0040c085050090644418600e403c0c0a0558079005440e405a440349103a18440c2100216084d400303038090f2404d03528168019400c00c031240308002c0c4149610302042d0340a400341c03000030a0500440441030301c1401040310204422007810a00d030101d40c255030040d28074040103101140c1e00c0b0004107254404200d00d0400e22a8440d00300000361803010b4682c005602e2101000d41e01082540103d03400781201d40c22641004420a0110802e0302c400d005811040015040000220140495030241ca41d0b04030300b500b1402003586980d1a6981c80d5120b070915806640301160320030700c0b00540c0701015800901a10074904021203408001441e140035911850b081c0c5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 606740926 1250 606739676 606739687
    0xe1203040606031203394a0307061704050c1306050307050303090607080a0c1e060b150d09150f060501080c0f030c0d0b0d0303020414120a020402 64
    0x10960842c0020b103401a0010459114a09010300140109081d031400d030044000303408510f250302c15140e000210807844a035034500c00b1480c00c60f0405180555014415012102c007160300c918000201155880c5140d0344411901700420b01c2101483c603c0118070a0341302030b00034000300d036005400b00c00c2801194100e0046c1c3d281ca1820a00b0300d607508850316080703418502c403141520090b800000c11901e0541c2034440050f202d01c107160310792040310f01147e04000c04008200000e41600011701d19525a40380a4a2840c1c0303d82c6e6104980c0001408128480d9600c03030703282c0a00c46071780301e2032600d20780131141480350440311034481203a03011b80060420380da0343d204450000d01c03941e0544601c641030141402c012071050340359464014005801000d0004000f00300007155448014200e074440320340c4800c024207503611a41c1c1d8440c00d601018141162584a401c0f40b2000c3d140d443c0d600f00140c0c0700e83c40242c0c4550424440c00d4000c01480b03074a0341b00300b2024000e000c3c25400800c8a011654040d1809603490 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 606742176 1250 606740926 606740933
    0x6121b0318170310081c0c02150c0307060b0f030d050a030f0f02030703051308030f1008011a030c0a0f0b0306040e06071d09011d100f120c06030e120304 67
    0xc01107903002800709555002e8200041407820019131040c18480052400a80c5038110595920451030003601c041248445000742c01d80640e000c0000f03284020100300440002d0107580e4015000681c50085030351000c030300b120812441c0e0284001c061002d480c03030305c030300f07850030001969482004c0d1000061003400181c074100f0341d129400a00c042d01c00b80b481444070400d0843c00700000c1d07008580550009240c240400c102da00d514440c400100d8128509074103584558029441066002d800f15031800351094000803200b07400c0c0103408600900200a0380240034075424542008003445400740314012403141481220303100f14a05c026101c5064581e0740302c0e500c2001160007440740849104580c41361000b0864441c1d440101002d01a0b075010304265101001c0051201e000002c7c05000b4100004030300c0504003e5110b0711096000300b815000c486020f607200040c005400381a00003150707151581c0000c00501c0701042d400030040056160400c040000d544015440c0c650402c01105001e03400000b04090 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 606743426 1250 606742176 606742211
    0x20102030d091721060303073f02030309300c0a020d080c0d14160302011104080c0a0f0605120a0b030d030f0e010510050409031e0906121b03 62
    0xc0c10040790b52aa40c0311458441220380e0368248040c103e204c0010b400090042c20301205a9186070342c4100310b400446c020510b4188034141c0e00c1d90002c510740d8400901c01015911403001d861400407034001d140c3c2d90030300f00b90f518144806416640000d80790443c5150306282141d9002181c4051840400c0e00d40c412490900d041000c1094080e5201c100040f80b00240855980204050203506007101d9480340460000e075210302aa800c416200b0400b40003000a00c000120f40e036180500ca48000207a00b45041101c001710f81203900080001c2c0d104000d51115810080d03082c0001d0030180d40340c078544501c7c09a000348103112b12a01d1600c0031090700d02284070811190003100c01004000c0036540920f14130080100200051841203001c2420400142040001072040138003a00500ca050f5814a05000600c4040e0001040071410000740604551070440038500c0000200e4840d03407200c030a549895802421809405400191140742c60010000d80c00c0120361039450100c2da08020501e4074a00c03040f0b000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 606744676 1250 606743426 606743453
    0x9010b22180317010e1302101b080c0c0d0f060b031c0216050d050a02060306010e040f020d14010f0312050705012c1605040209030304080a050a02011b020102030d09 72
    0xc030440c040241002c064000030f804030318503016000380b0b6a90780c0c4c8400034548802c0c01e5540008400c00600c6190150078004480510f02d890350400c0b55440c5004211002c03c50704041c41900e090801047c940da50310003e116060351130390b003110300110004017501d40b0844e2040510700201950740d01c0103d840b44c0e481c107109000d020122400c2c1c01c0c14901046c0c201a41718948503042c014403d00c1c1b07070700105032440c2035000000c010750410018281d00000340d0078040f5591020340002d0512050000c41e414540c1d46000710050b580c1c85804c0503031030b00701c102c02000030f035403030503c0c22094110208014032101c8120070020707084a4010720820080c51b070184083d90542300c1c90390003400e2075090942c1d1440440300b50b640008003c00340000d6020300e8100e02451380d125220000c24002402e591082000740d0b2401740c021b0141900d0084c25a45050750b00c140d42458441c101c2001c5540e034200c42e400105568006804582602005801030000003140e80000d44900c1074040c0ca21a20340c2c0c1303207401001e11010000070034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 606745926 1250 606744676 606744701
    0x6130506070c08100902040b100f120b06041806060309050604060207110607050d081006020316080d060e04140304060f0305040309030611040828030c0f050a08040e09010b22 76
    0xb1110744c280591603004d0003e041e02030340250b04040000b4101d040c0511888140b0a07280d440101c40160400304454822240c00c203504915290041484a903035602c00810042811001450108217481030110903161300d03610100c149880c0280100110780d006c00e24940c025842070006948904034034014401c1454201401c1d001040400ca002c00c0000008004981c00c2154640115503aa44042c0441c00000340c05843c0040e0401c0c40000541c020421510703100314412038071035061480710583c010440b922980000c00d50000c2400b40418001e2030b0700341b02c0413141c024018529050400c40040c1c43e20200c03442800401d40d80b80c0001d800e251051310000040d580c400c02c207100c1040e16540b041c0b403640040c09600310901440c11008000415400f03031030700803400c981d0569102481e60b1808e1b41c141e034000f04241d031010850980400000c4051140c0540b944c4241c1942e61031700c0c28102c0c0020884001080e8a81c281e02d098200010b03651003816003000c0321484003050b0308400c0d556007414054501088e020 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 606747176 1250 606745926 606745933
    0x901050307120f0b01031a031009050c04050403030b10050c0309060a0c050f0f0c0a080703020f060408030d0203010f09021c15030803180d0c0c290705010e0c06130506070c08 76
    0x520102210707410144e949002640c041c4441104103a00d01207541a170003089501d50712910914182c4011500000049030092064401800c1c803a000703d402e640707046074200c0009584903c04000b80c502109042c0580c035140c503000742004000b40ca003660300d10840c5805403140b8800310b5040100c0f40306180035401940d001080c1c82c5000400701040e9640c00742c4881101450088403140581420500070f00004c4483c03101c0140a090728580034805050100d8802c82d170030020801001c1002c0008000815200412040c016521b40c50b00040e2602480c0745e422408080d0700400101c4150900e08504060810000d900060454070512103404540342d180d20041100202100b0404c0d2074501e4175010340500201d10a0300c1144400c41002c0b1401c00d482c5200600c2c018400805100c0d40f5446a627210350407100102c1c0c5408810b034510b8440064000fa40c0072102a911b0307041c1851000c0c070a0003071101c00001a21203d08055076108003447c030101c1c0c1e00030f15025100c0460a00e040c0400d25030150024036101c2c056 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 606748426 1250 606747176 606747191
    0xb031918050109030207140a0b0f070b011205060610050a031a040f021806070c0308090609090c030a1103100b2118120405090a0b041508070e09030708090105030712 72
    0x41c501802c0c0031281a40580100d40c00090161000000b046d81d003580144641d24480c2041e10016942e0000940c56511017418003c0c100050b48001c1268043d02890245404408003803030240e2034114014a25802054415000e034105500182916480a03d506011030600c0780717840c2d018081803445c1a825846800c04050194000d0f1582c01041c92460007c105004038009001740001c62040c0300000f409140351000800110310380101a009103e0300802c014030709003140000030300160f8140c8030030365180c90000c24025191446c0c812000865440892641145002007028403220880d02c81c002e85110000b80003460f1030420010505488403c110741a00c50030109403100030158600070b011140d1248030240c4d04c400c16050300b920102c40d001852120b40f03903601d00781c80c0d015000b08050590455110003d21030801100030010018000c00310080060b203107000c2c80d001b0144000b50141c04290810040c00c004a51490111200f5400c2030800c590b0381e403a0202c1c211001600c94900d5102c05140c02031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 606749676 1250 606748426 606748433
    0x90c0612041103032a030a02030f0a051c1a010306050f2115071107030b13110a0b0a1b0c0501032a18052d03010207080c01050a0507020303010b031918 66
    0x2030043c640c1e40c0390865002c02d05170700b400e1540d071301c521aa8034015a000f44040e0415008a600908041540c1e15165081c481c0d24a800d080c0ca4003022244000781d03032900c0394141c40c800502503a0f0100c18091809110003407903c00411448044552294051140c0e0854420307065500096000d520500c0c208564601d08980301000048009031248030009004000b8425199000101401600e41100c03155821351039215113281154401c89007207030b80070072100004640b903860071007038001015080882c541d14505190001d04903000c0c0405040340225020740d0310089035015003d0b4003918030030f090019054070307118a61500000c0101c42c3c13442400002d0806202540c0c0300204c00e80603403004d0000c8002ca902c4904100340703400b0313412000013480480700311040c1e114041035030003150344000360006203032542544404241c0c0e40100f020b488541c0d140d4040c810200e0303052082e25401210751000d03500310f50401c1402100c922014103034404400388400c40c1e848180751940416516200483e0580e880d410134038 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 606750926 1250 606749676 606749707
    0x40f090219060912050712020d0f0c05040f06030c0302090a180c0f060f0206060f04020d020d06081603031710150c06050c040b04060c080d14010e090c061204110303 72
    0xb034800040c4903400d00195020403150082d0b51184c0c0800540030590415a80c051014519103040c2c2e0300078000c10804010981d03841c50000400d00441c0030100280c100f00038401a20401c800d8004c8681c505807041000c250316400e54020780394102c4617280c2d80e4641180301d801800f22011b003d1100c0c01920060740401c01003503801380442c1d66040d441c1e11510313a1400143c0e044221703c40c43c40c026070401c0000610510304500c0741c120a5400034801410440d905400208076000000d100800c01e60354807081c49030503400c0108048803420300204140700c0f4155680145a030300c402c05203130035514400c2c003ca4070000081c100280034100c04500e81205c0b0311401d90003080f40c44180c80c00c0e92001d00d0a0041241355045a00b210280d41c4e008048501e054a0000111950b80c0b005505942c1c0f9002446100118032a0b401614000e102d41e004051042d4107000020855507c06801c2001d01c0e80204044c2d0503030307200c4009030381030100c0129840b182c594907030620b416228002d0f40c3c41d992501000402411130341042c07 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 606752176 1250 606750926 606750929
    0x4110a05030108150f07050705010f0608010b0f040e070b03090109050a030c12020105160f0509090403090302120105060a050603040204020d090803160e1813080f0304110915040f090219 81
    0x760f048648a544810980003226000d176500c8800c05040000580703000d02035002080050300c078500004128881d060b040c4d00300e60b01500900c0190751551201003a0b850190f080740d0084a003214100501ca2407070304a07031f0b82d07500144030344501d42c40007000041e02e1041c20b6001c403140c0c0390001c0c266400400907141c01000f14254200807524003003040c005400c4a44140b041c1845148103080c04810700d26a502c060300e904102652900c1044020015943c150b00d811540354025442500d07803c440701c0c1144104880710000c2458182d40742e261070108102950340b0703051481207801c250f43d02079036030319140013003000b070704c01c410290030303541e0900c6e40c5102081600c0d402948070b44017541c20100d42c01044101207861000740d501075580801e0706808054072015614805800c1050304403422881c090a0ba00d600c0541c20503194000c001070044104424422041d124100058080368218041d01e40006180400007548007414003e5a0f02e00e03544540c40304551010940d60b80082000002c2800d0030202c013082c880a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 606753426 1250 606752176 606752189
    0x1030b032b0306080d21060515090328060903090302030105040c080c0409150e070510050a020706260603120c0304240507030f0c0b0a0c1107120f0204110a050301 71
    0x409000044001010401d8034100c000c540c0c80346100d0f44183d40240c1c5213003c1481c6e0070041a542c410006e074682c1c03240c070746102c1090702d0381d5003545840c0341d00105030071f01b000010030b0018000002c40c484a044586001210744c1a8440d50000314100103040440300f00020f03800094141d8a13000070722090019a00180046905040880d011a104075043c0000d88624007001403014200c000c40c00780030607132504800c400c100d91a0803074030160b5450001950580c05180c0b1880400e000081c510100c95040c0521005008c140c205a01410410001d4240e10030384100d00b0541c0750b8a490210b5480d650a02c1459861742b02c0c10f030341588a00840b90040d491394085d01c9441031204003c001c407104a441c50445c681c021072036440d614141000e68505640307e5171440707410020044003c58500000b030344201d0045c0107000001c80058807808007180501b410383c544072805050340c40500100b01040300d807800d0250710780d4003074010000b803400c0744040f5001d8411200da0300315085011031440303915a400790146041390700 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 606754676 1250 606753426 606753431
    0x70528020f03030f090d020609030106170c0406030b010506181e0301270f080708030a02030108010e0f030414060c0f030a020d0e0f0103050705220503160f0501030b032b03 75
    0x507a01c0c201603403480b41c1504200040403d001141c403c3c40c02d07107614000540080e01192401204900203400c668158002c0440001031100094844100300007016080c00195003c01c01503045132600c1251510511455102c0c40c800252001d0310900d510507858140405000f0498001000c0000c030480c88006d0340082c0251720384260501069010810400c08a9180440720021203254a840d105083c90b500d0680b0b0044041050b40005507290000318071072203503100c0041c4c0700d5042070741d01403e6070f880264410071548038402c030108810003c0110350849146403100c04513031440c44080b416500818a052702039028a507013003060100702000400000c80c450382981c0702090040000c0d40c250940c82c00003070300030301000c4061485502a60207181c1000c800d0804d941070161200c4002000503091040312121041100101305605040000c54085801d400503080305505000d031080e001c035014070403141019210803500351a904e05214100400c002d40d50301600880344000100c0403020743c02482d000003032 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 606755926 1250 606754676 606754699
    0xa06050c1e0f0406112e050106050903150916030f030305091f02030a180c080106170a0f170310062c0d02040608030c150c0c1207052802 60
    0x1e00701800c5030320b00d010001031581454103101c0c0c221821500c11500500c2c0e4819014000180d201001e007910380b00300e40200304040c2264071400c4205032101030f48044140941401b04c2e401940d80854448034401c04142080d1803980d4017135407580750020001064907034091801300402441102010803001c00d009840500843d00d4540f050b503a5400048812510108c01d04031a90441e112600103607006280e668000c0340f0202603040d0128540901001141c6442441d03108000e4143e0038000d40f001083e076920502071190043d075082d0b4442d07050850003030292101e80c07164410070101210100c6020040070300035480f481c0004071422181098001c3d000030a407203c0b2075031600d0285a050f160240d002540d0252815014814040c2c20000c1410880c0d220341c65000204205a00304003178450500810700030034070400e0383d00ca030381c5603418081d10600c100c0c0810080d40e64407846c0050322190034030303030340184030356410740341c10200d09141c0d0700100c800780e00721205601081020202801252240201d0710a031800e07 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 606757176 1250 606755926 606755977
    0x40c05121501151e050d0608031308071a0c0a05241003030507060b01030906020c010c1403040210080a0902060313022d01051b24090a020105070f03020a06050c 70
    0x110309607140300001594040405461500c85404442e4040c038a04151b0b046c010303a80020000c0c2e0712241c00038181e40d8030201d00c24200390440030140c801011450301401200c1d0410070321a00d0307101403501c1d445003840b00042c00c2d40a01d100b001040c02243e0402c042c2c641400000540751000900c02000325181805170000c903e1020658841e02d08982e416102c4614260f911780e03c0030302421102020505050380c484404000c50340b80c1c002441400b580d00000101142c7c05080604000411001c45801c84002d00401c801a04d8440280c42c0313002c00e070300303141c0c81c65503541410a0161000c004000e40200d1b0100c14021800545500c1d2400381d80f00320794940f41c00d4424520801d074a9800200e4880001c0e900c3c01901035540940000d01c1912a2011801e080c1841010100c0c949032200c0c2840f503040d4020045180380382d043d01107050704000c940c006881981c030365030002021750040035405041f00c1b902440c04805c060080020141c11a030081c003d00c0145481d8112284e6600700004046460114030030807010b8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 606758426 1250 606757176 606757199
    0x307060212010b0c0a021002010e060109020a02160f140a09020403050307020f04020703090312200606090601020d08010315021b010f180c210b010e2403060f040c05121501 75
    0x481c13006900420003540140c08000000c1501d080d01d0095558800c3c3c04030f03000d00140541d6020b00030032000560789965104001745416050005400d40c2d1103400f80c1801f000760488140750481d20b504024403429580e54001414001c21644004582c51000600208009000c4040c00e2102d008982c003420180600f0300303100c2a03224202d00140058403880050001600e40000c54100750824075009103c0714180d14884c40a100103600c9180c10b034000c10400c1043d01d0a0385c4990391094080c80a854810010100a003500300103000c010070407020f079400041c0b402c5c51581a501040c035801d11020243e201c03c0000d0b40240390082d10590324600b00071a43c9513240e4200c18201e04207a11001c4820403a2609841040c800c0d504624030b002c0200900142c40818400e01d2201d0107020303098404103150a02140b001d610039641403061421510710320441e526581c011940e00da00213900082450107a0350761418030180003054106592010139018030810b0242c00103005120890f140403104074698854480c0d012 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 606759676 1250 606758426 606758437
    0x6060e0c071203020903011e05100602032b02070624050607030318081b1014070c050109052a0f030c060a03140103030e24041211030307060212010b 65
    0x1039480400c8500002040499480d4016045160060a002c0e0703140001e82581c0c901044c0040700702c4840401100f01005220b0079030000c000c00e035035045c440d10300400a03440f801061310007145502034005ea0546107210f0b502c800142d4958038021982da001910f0315800500b00c424008c3c03000d040132212000c0320200b4102d0079094901c020074003414080d4030b6030200d006e010904080388070300c0c2d0048150400940c107040500300607030040c06882500020300950900d840741840c444c00400e0f003044045000401c1000c1800d4205040e40780c0030000011038203003640507120b0380000402034400e0124102d040c0b804126823400390344a0f0714201007209140c00c00c110103030f9803480700c8617815040110120802e2034510028941b018560902280e0001940c40070500385000360300503800f2446500000c1c0040ca0900401c003581c042c840030000141c2000c11a02815010300d0240903c043c00d24150103041c0181c0c01342c0d6003400c49004080f06d80d1441c0703610f4020040d40001004824600700c01c40003007003102d0b6450540d035 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 606760926 1250 606759676 606759691
    0x60c120f0403200304030204020d0e120909060114190e04060f03020913030903050d050d0c08040b0c03180610260316080d021206130c170a060803070c0306060e 70
    0x40d07070740714118020f12050740c1d81480504544800c1100000580300c0b80003030210140c0c51800007503031401c4403440c6810003082c20032000c5007640401c0018400d5551701c0300f01e500070b2030a00c0c00d24403640c20240380700601e01c42c0f42d4071003520707d6414042d0b80119500420000c2045410f4500f031144640d1074101c0d1100c1c1900307020080d8018207041c001250110032007950130b1228001e191000381d4641c0ca4076400d0600c1112182000091000148044010349038000c81050a00c0d600e8841c87c40d10b41900d80c840f01d01009800d103070001d0070002c04140c81102c4484800760449076001601d6407030501d203584661a1030544203103c0040e2522044480d03011482c1112444140030340007075813408c841e48000e6000710141e21000c545882c002c0c400c88070311201034805008141003a0445103882c0c02c1c44030801c103081039000c20540e030700381c200100c00e59025400340f1080040202c0c5140031000752200c03118040540040c2d0002a8503100201d110814412a00d000d1000c80303001d4603040102a071100965215081c0440f00c00c1e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 606762176 1250 606760926 606760937
    0x60d0b100905060717090a03060203040b150907030e010b03010614090a0915020306011e0513080f0c010c02031e06010608070201141302030a0c1202031207210908060c120f0403 77
    0x30740220700102024440104149602407821b8072a800140554440340c000b0f6641d254040704100c1007240d04a00c441d08a1400000b0741038a55910000402200c1c00070114010103032144040d0b1507910007504203060001e0300400030300c00349440c0d13a200242074412880310307445411001c020540240c01c52140300701c1c00f40c01010641601780101031780c3c0082c3d8405043c2c175041218072003002d00441c00031100443c0807800340d500c403507490096048941c184000d030f4001c0d60090b01f00e032080c091040e0700091a0b020501003803c0c44118040c5a0000909084001c100d419828040c088800031059005c180507068900e65240c17143e540c0c6070107400300e00b01c448071420003070380507002c4001c41c49690110802041c3e242c03004049900720f0341e403543c424442007840d51141c0c5452400013024403c501d028004030340328036a0241d002d03080c851213031280c40502a1484c2044038840001401d003a2042c400c0c01520007030540030303003111280d08041c180c4140a0b800000903159000400b0301040190b0119406c00d80504d4059880 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 606763426 1250 606762176 606762187
    0x1409060603091c020f0a080a08070e010909090606090c020a03110c18060d06150918120e030304080a080a030c11070b0a1b060e0d0804031407060b060d0b10090506 71
    0x8544503043d045002c0c029481040c54158032030004025182400d4451441c1c1c0b6100c00e00000007820343c4101074568030170301c1f052a0301401d859a2002c00c2208585a04e2004140104141040801000150420740702d040c105107042864503000035211040e64869510140513a0040c1c02903038555203100d420340d5001e25030046aa420a9504c8059604040020110442e40005030356400450342c0440b080a54154609001c10a802d25442602a6005030015032070701d09010390380d0780c010210300082c1c40c0c0901030310402c4407500d61810001c1e41d0183c2241e004581e4140c5c02030525644640042e40d0400000341024001a9a60301c2040e065001e42c105000904109091030008000c1c3d4001c40100300803c06101c0e921003817a0140c90030b03052098090301d000205843c1001c0190709104615491000703110502050100180d88820040001d54001d05202e4807078505180c0000a00014000c2a902c950080398585040c582980b00d2040a801291062039680300c900050700c00c4841481a01c1d80030303005205 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 606764676 1250 606763426 606763453
    0x62d06052d0c0d0f09080a030e1003060807080a060f0e06060904061b1205070e0d0f0201030f0207031e030509150a0902100507110108042415140906060309 68
    0x11100c1e05030181801003401e1100d8004054500b14044114100141c52680d00341c2c0119004404c5401424000300038080c1000242c80240015407580080740c000c0c0b403420b115200c182d20030703400360000d0900c0c6070030354003995a0342000a03a034049116040c0e40280c84d00b4200c4071070027610b1058208511618010749050340c0ea40042118810000300103032411070311341944602002c508151003408960350b464400f01b91903960300030411180010124000d20450800c80010b5640d409045542c0d80e50100c200080d1069500c0100e010386259811490900d00204206007015081107078540c5111080301d81d4284643d21440403415950b0942d0034081d0b03904800c00794a01c90310b0386204268092548500407459110703640c0816480d0105000740350001c0c9000ca000f004109450425200c108000d00c0c0c200c41c0c9040c40e40b65650700c0e01d40f0010580001351560404006101140c000c0345092040c036180010b0243e030750220110340c0c20f507401058840c6a1050000c0c2803031900360140c0f402205810020450b5645444 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 606765926 1250 606764676 606764737
    0x409020a03080913020d1d06090a0b1905010e06100c0b01051201090f050109020306150a060302070302010b0406080d0e0d0803040f02031507020c1005120403080604062d0605 76
    0x3d0829420000070003081103140c859000400900c02c82c0e4100140d00c031001c0c094007442481f200c0450080d90400024400c20000020b04280090780100c0001c2c4903803a1000d9411084000b2004103548a06140000540c107034001c80c400e00c20a41504d18031039540204c8170807074604c0000580240740032003010041c0414100314480e1443d4018040000503605801d072500f90001c0040101240c0f907030b454030f200304110b00341408401e401c14419032842100107002e000041101310035000785010144d005c90038209243c400d40110203640c002520401240e600c8039015a110921554a00003040c040c1d1100d00550901100071503100303030443d03403260840e00d0b280d841000c1d100108100f031340d0511805903480318a0941c2481c480c0649815001440c11401030420b0050840304d0088040510400b4401c001f4900075501c07460340e100380c0c0343c40c0007951640c2d1600040c0003071205812011002c3c0003101610518601c210051142c443c0c0441c1c28080e41e55a28401c071881d00c10f03030000b0b00c00340461002740300c110b80d00e80 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 606767176 1250 606765926 606765937
    0xd060c083c07110303130c0e0c0f070f060e160b04050a03020f12071d0f0411040b01020f25050f0312070305040506190305010e09031803070b0304030f08060409020a0308 74
    0x910307008000c0303e650224a855608182c031000c0100000d01e9404040042c1042240700a100442c0200c10625000d0134805444c0554000b242d0f003034400049c11030400c02a00703210000258031003410800c44a200c080142e40d000710003940c51110000060110b03000c41d128040e00d044070402000d465503a81036032b013400307160915038644a4228090b80004914820305001c840064920522040800302001c810302c842180301038040749403840c10109120200e072050544040307040065a02240700034072400100e1400c2c880e00d510f00c15a00071640302c914044e004040201002102120b000002da44800070023004142492041b54940e01c164841300040302040003400189000b81010340c186a03480380032403c03030781c080c9a000581003c0c41a19010050b01442a240034082d03840c170002c014070b0503c2125503280300c0c4a22032045803151b01181e074081d580400c1b00102801c2d4035501c85031641803a18010f803119640122017404104640b000580b5400c05100f039031003460300104060581890764031003100a9104 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 606768426 1250 606767176 606767191
    0x5130305070f0b0c070c06090b0a03051807090c080603011112040c210b0a05041e02031002120603210406050a1b030f12020c060f060d060c083c 63
    0x440e80303681d003c074001d4412184201070b400581c43da0f0303805034a4040348003941e5070442818000e02e40e00034003c2610840c182d910b18880c0b42000a0981ca40300071500015404a10710701c86031040c4100800c0681658001840c00340701d9172600c10150b21000d0405003694600110201410701c1444424a059400201190040c0c010f0780c2d8240855181d4101c201020303030050194662402006244003003140c030813065503008243c100c04005a060a564040785c4107402d10000c071700f1f829103641c2c000c19540c09204480c84d900701c2100442d075030700d90880840503906080314034501c01d00071581100410742072043e0342415504c400041c01d1070a81882c2059078130f41c20084e8120100300c00c280c2c2c0c61112030a2143d41303120150107603c501e904442c5030840148498800d8a17a02c001e180148481070900500041e41074001f40c002e042600345a0300d82022800c0c1941d00302c0042c0007142090800c214441c5c00c101c0140c0980c2c0661021890301e02c01080d144008081034000a903064105482405211020140d860f040300c103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 606769676 1250 606768426 606768443
    0x180b040c030f1101090e090619110301230d120f0e030a0f1704050d150212010b0909011a09090c0c0f010204080d0c05101a0901030f0b0a0513030507 65
    0x440703446500c4000a8401c04468002250552651641c0c0280d42003004000c286240e9846d4603144011944501d17010b401c020408503d55a8605011f009405c0315051102440c001900c80d07944c4c4104510b2981480c64028101e011b03045803607100c0c01e180000309401a04500d84992151b880c2c0710813944454041c892404002c403903003d585403aa4240440c22a4601801d042c8207001c0080c104081424055174002d03407128001c20080260b40c842ca80603241c86900014400c54149030100c149020740308201c0382e8007103140210004112041d089010300300552040e18000d095a8965640d00000c011540345202c07502024018135503949012001030344e0001c00b444859045c20801d0740c00310b10f044103207005512165000700c1e0510130b0540400190b03080203040e14000000400e6515000e4540010011009a4a80300c104541002c2c00300180502000e001514004440d03030f40307080c000480700c44030604581840e5810081121030015000e914050f40a4031005941403156980586039544401030031a003210 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 606770926 1250 606769676 606769679
    0x605091e151602040b1f180801020a110c0a0e0a02030402121204050f060301060819020c1203040308060d050706111903080f010e090c0402090102010b030a06020a0909180b040c 77
    0x1e0110000e80105032400c070014011103240c0c4104400e03a106a401039000c0d08243c40c20803010f90400040b914903406908202c0c0d4800c10820b48000020302a800220a0350300004002425503403100d204992074075914140e860742c001c0b601c20461100700307602c240e02d900f100c407502180c8130806d25801950070a1005298914a4030004811402c1c00e8482040c52508070000c1401c1210b4100500741d90070101003110054595030401401a260030390180c101c0e50000e50509440c0511507080c4e040b241c00001c0c07402120000c89405035103102c2540129002c500254003407010904a04024041c042130f2a840001f8000c81c90038158110303601f40145000400a1050706090619180d100d00c4020741d05010782e94101040c6030940c200000d60070181e00031008160303000100400700801180d03e010312613007202c0240e540e5044000407405070030140411541802040ea903d0100111603005151892840c2c9032181d6107503481e048071089a06c1c2098500071051a88a8003000400000c016640540304124141c0c000c0d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 606772176 1250 606770926 606770959
    0x903061b030c2805090f24070f0f0c031203020703020d08070203040b0d0509060105010c0302150627220b010b03040f1203051b180d0212010c0302130605091e 69
    0x10301030803020b0042540005d5041440c00c0c00c402520801c041500c0704401d40151020041e800500961024250400461030604001060002c161001c1c0c00224400e1850850305141d64000490f20049522002c1e812125010347c0c001d00a0302d02003038154010341032601034003d0684071501c0081900e021400304000205a41e4800c20240c08140c0b070600300002d1518240545500d48041a000f01d8148a01d000040c00000d50000315116000c6149007414030945514000c1008008800b41021026285800080140c2100c502c1c851140c0e2010421100c403201110b079034040e101c0703915400307015403540e400144400b900e0301008541091281551025020960f200e803103052154003000350009407114207000000b0400065038003101700050303c0615140e00750300444407a02c000175440303010b0740000d000344081d0740e01c580441840020000007400010f50114004000b54041807804415844400c008100103200b90166202c214014101d080300c5111011283c81000700b1381e0115034808440aa4403104 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 606773426 1250 606772176 606772237
    0xc0b0604062d0f121b050a1d1005091803120a150e13030806060706020f04030c050103060510120b0a0801060602070f0e0f0c0d0c08010e090a03080105100504030c0303050903061b030c 80
    0x810f6030168140c008910889403019070440605a114027050850b0f00344515500c05011a4001ca1007910040950f0048241c59081d4014400b8030068001d02d1030802140840c50f802c001c00c0b0780d00340c413901455240c580351103d49280342134910042030310700042d01c2c9002038000c020958001700700030036480c100314a90742c60205030b070700240c1d4200c980c06002c41d04200300003072245c2c08806082c0900301400581d08200c003248101e8410080314040090040081000c0c903034540c4408003c1034050981c101040d01d4214103406007900303100b4a0b00510035502c0010390f5a05207101001641c060402c0582c0f1a04c0d511103584641e203024017100140f24042002e002d038102c1503c50510b034414542c40d00400f030340c50700e0b450341c5400600401c002042c0d0001e02c00c10000035806544103064a20449500d0301640251004680b0f902031504010441c5a140e4004000c0c19001005003003070a1085084070700c15aa0040700403028181c00b0790190f0740380000c0c004514024104800b6060106c403008107500b0142c0007031820781c1c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 606774676 1250 606773426 606773429
    0x30105390a181a0a140a1d010302162006071a1905071d060a2309150d0e03040f05130e0607110c0f010c0b0604062d0f121b050a 56
    0x340d080044d03011011508800ea01d0360348150b000005040c007001c1d03200500119040841054032010007007652605038040d40c1520840082c541c0f20484016061515031080c1c2981114840c0000c080146e505980c5410001c030380e45107038800d68145049030300000070803200e2409407000301d0710202136490309511b90f0184100c81c4111079aa8400840780c030000b035a5210203c090310b00343d0182d042084115a80c5412125a9280400f46c2034841041c0303851034014282401810203e69220802003003a41002c00210080c040c90b0001c24030411045540c1c2e0002a620f118a01c0742c190102c05204003003190340b90980306e0010321110a2401f083e901d462005541c11b0000858803000402c0c880030030009162002c000001c41c107001a2144500940c40100280c5110b400d607900400000401000403090b4507145c2080000b0300320494800c52081c1a078445c3d4000c46202d14100194440701500007911408003004a0704491119054021480440e181c40315402c4020a450700545140e80000445880e030102040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 606775926 1250 606774676 606774719
    0xb01020a0f110108010e071706030313090b1003020c12160204140912130b220b040e0906040c06050c0a020a060225150c03030b030105390a18 62
    0x50b074a0703000310000f42004e070040e00200c04075003001003003050300c80e0072016400c50040320700f4000500781c0e1880700180c80c6115940c03003130300e907154160301c002900c040541188801d140304580c03c1440340c1c0b051004a080f4064403c2130010b560110000e000d4000c05503005007000c10070403c0c0e0010081861b00480e05403000d03400c40700c070070b59049000c010301198140040c0400034604003c05191005001c00049881ca20b8010241d01103c002400300302ca402e00350032031409010401701480c0705a034905c402003041c2c015104020392554450001007020348081007980c45240c0c0b045110100e9414440100d81c00d411400c0d40c2802d905c0b6a614103405655000759003802407006500401c02100281d21f45c0c41c466000302d142d000e0200030f148040c411400290860074402c0c945207884006100c49090460250040c14a0301da05546004188003600c0c4400011903840c03030390002d0f48410364800680e4191040c2d1100101504240103018203200d05204030000d00700507050010008040f40c54800729202c0000049041 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 606777176 1250 606775926 606775943
    0x60c0a0c120302030a080a470f040c0504090c0f08011406070f110a090b0f030a0203151b0f030103020103061e031709060c060618091c030e03030910060906050609040b01020a0f 77
    0x3044a81d03104015603103038048c404500d00c007101846000c220321207070201d1990710440d01c130ba0084003503a2150007a42c004201c081824442d0003000480513000003046c10135800020700680001ca21100101c0380c00d0a408400741a2038a010200d0b2039215540003101000c541d074103010700709044550365189044002c0c010a0400040383c8a45000300164031854031a2103006e40c0045050801503a4040b41149010042c1c40800103a56200c01044507462400240481d0a0030041140f10001c41480051410381e4401e807020080780e6214025003015401c070410a0300d044880140c180b000811a01d9403582d220460200c403414004000c0c0000c9940c0c0003254001105c1d40900104100c43c680b038000030490008802e2200c00c5c504045207101c0c3c88802c014450307080c050264148400f814800d80c003c1001c00d0800c0c00b6030b51241001710183c1d03111401c0d2030300300c400142048000316100c41d50b07204000498400412240c44d10281c0014040502421200d030f41c198010302061740c000c680000200070100d407141d580d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 606778426 1250 606777176 606777251
    0x1f0305010e012909131127010902041809081b03090406120209070c03050415020f0706050f0702010c0804051c06050a020906030403050d0605060c0a0c120302030a080a 73
    0x2d500644071110003d00c0c0b140c0002d40007503a54442c50030b0140c01813518202c00007808800e060211300c03600c468440a80100850000b10125054281000c0011141980c0000141d981e80c9081050380201c0c0150005c44018010b101400000d0f5440001c959105104007403d181d540c40703425541d00e00002501c00180c00c001103140c1c4c240b07428032640c0e028000e48681009101065004140c0050f0007d09036000e01108030101d000349406001914003c1c168400001d44011181e14002d40399007107000400640c3c800c188000c03c0e040d01920079540e00050440d02c031410300300d041c2c0044501c0f4a08200c1a00c2c4c441d001c210104590b01c81385900c0c80d421440d00354007640b4a903985482c000311280101085000380c8180040d0300703103030b80b10310032650407942514201e900c42082e1050000200342d0b9a0000394041c0f00021401e101d94070110b900d103280c41c001d40302c0e60503240c0e4034049104210182800140180c20802500b0000c60262105a420000c540b5000a04c40800e2035460400d00903900316050000e01c0421 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 606779676 1250 606778426 606778451
    0x190e06041a181b03101b0503070c05010614030c0a080c011b05060106081e0f0105010c05010b090106031508120706021c020a18060c150e10240f0305061f0305010e01 72
    0x170303c0c498a120910100022110070710341500d40c04e01103071404100700000000c502c203d4401c800d24980c240d00000200000b503a203484034001800047d1009009004154226406190070245071007200c1d903820242181a082100440707040711203442666440c048600c1c1e810115004221590180101d912032807814100350300c56140d0f0380c00c5181913440300903141003001502811505c445044600c2802c240501400342e11b000d50140000c00041038201d9000c01c000529268140c00518014003000800d604180d2900816900d5180c8185404c099031000c01c144800500294000e1079403104d1a60784c15400c1c9207008050083e40d1103c4060400142d40c00f1a510400e104420000c0081050742814440c1c0302503a41d0307422450603030344502224182c1c0d5070301c2001e090b4000d200102c0031402c6464200001c1c0c00b0343e0300e0380b1584600300005043d060000d120118851b4600100303c001c1d240c111004140ca565039041d031090722103080030021018842c505001000603400d0140b4049400000c0c00851501440030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 606780926 1250 606779676 606779683
    0x20301120519110906060705030304031d1206150f0d030e0103050a020406023a08040b06010212070b090106030c0b07050d030c21060509190e06041a181b03 68
    0x40202800c1c0c1c20601030140020200f0400c2072282a003a100c100c55543c5200000c4d42030b000302c440290140c0000030400c03041580c07020894601c15140b440300e003484000070003840f00c944071000401803140c2c0490046503401c021140c0c0c030804490b005140949402110001c140c0540d4807030002c030080740717030414103034559a094003d03030350322240d031840850405280001c020b68800c0100781c490b0040141403180c49a00340072884025180c0601c1d0840050446440700040004008840a0740c1040700440800c9103584082000e010402e41240c10900304045c075200d106941c00007400d00d5405641c1c580d0000000343c81e112880c0001c12002c030040d525501e41d420000d040c94200303564a000c01d0300d4696842100d9800035840320380c078800b00c000501200c0d0f41d261100e000b4651380d0007076079109460a0402660f4000010410042c001c0981c082c03202c01c940201643d42d428007900d0041800312890007692401180d48441c1c1e502041404900c100c0c2011900c046040082070080480402c04071018400b440c01e042 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 606782176 1250 606780926 606780943
    0x30902060702060f28081f080d0203041a0304020303091314011203030f050c031f0803070609051507080a020c010917030a0606020f060c09030a17030601030b0405040b061c060203011205 81
    0x101000d9121900740a00180500c200406804801c10840d4111860340087d00c190005024610101c44941e0125030b4065034030b070130501c40c0071040100030340701004100c40e042c243d901990340a00214200941202006403044565801114481d81c60019144a48040c101e4900a080c143d002010000342410000c0039101c40e43d811505283c1800c0501202c3c44000048075440381c41d00503207403011000049a41d45401c0c60381d21040151001060744001e025140c2e110780d20304c92285084441c2c015a05e09950b80c60304044514101240b031050001d1040c402c03d070000c01702c40300460000911644980e543c90400c1c5181c0d068840100c10100c20030000176850b2140101400e42400101100ba90020030a40d039020020b060010310180031481c1d03402d80e1020009039109540c0f2070200b40d0800007198040302140c00403625280000d04000008065007000e101d03c9020300e401019000681c0c0c0d4034828030a42d904203400c07003103542d14a5030914012400e1480a14041c08a0b01c5190507403c10b5170600c0303803400012 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 606783426 1250 606782176 606782227
    0x1b070c0e061f1209020a080d081b0d09060e01090c32100207080a03030903021509151909050703060c0e0922060e0f0d02010605030d030902060702060f 66
    0x4000d8074044045614000d01040b5a5030b2400110350f00150000308040e001c5910000c0d001984c100022071b0550002c41c46807120181030703a07076801580c1d56480c10348400c841c8078603000b400c0504000c648201c03026a08102040350003040c011620740d29642d40c990840b41072100564031180162414070204190004400306400c40b042100d85110741549580d51044171289024443c032000c40f40c0801e420700034009038000f050078105a4003418480c3c140030300500301c1a1000ca0041c000c000d10b4140100301028042d014950410092904800c407148078107100341d01a08204070004211500d80100d0303810b00600c0d610030b11074000303000b440f46545064001e648007040345800740a0761125030241d90b1101312040b0f40c400c0001302644800d178021014000030644152001d0006c9050880203400c000b4001028030514040100f01c4081040c2114200e088880d50b018041d85904040c0200001e0ba202e40c00100403a80000c10080ca0440d8581c00100380d58001103d621118401044520300c0ac0108041103000320342 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 606784676 1250 606783426 606783439
    0xb040507020d0c0f050d0f030b0d030f0f0e030303070906030506030703080f07060b3c01051b0313060206041511040b070303090b01030c1502070305151b070c0e06 71
    0xc1000000c2e4480300469019000c000c1000d260300188943c510f010f401c026003100541d508403204280003810250628500004642002a410483d09100c81c009070650340540d1000c807154403210086409154440c14141040f8064201c0182554140000c601034450b903203c2c1d00390700380707080c002a0a4850040900d4484d4210354020000708400d8000c0b103000c0100003040b156204018a411030080c960280d103d90001003903400305400d0a03100480f01100b000b940028002c203500c01000003d001030b038814060005c3d8040c03224506a03036440655001c460008400c0c1c0c0c2c24074807054141c00c0500e03500d502c140c006900034000c0c0000d20582c2c5040070b0614200c04002d0008140c900100c0c1e4071480345201d031140300b003400502d08050510075841804076580c01000e096440d603407800c26000382400d034010800c0509041000801d0a80006001001c42e03501078081c0005550a51030601a080001c01c6070080c1c806c0c9006880ea45103010f002005010700c01d038201540141004403030700300080e0052502d4090784 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 606785926 1250 606784676 606784681
    0x40512060c03070c1407030602040317211e0406060914101e030204020d0506030712030e0415030b01060f090b070b1311040911030f0705010819021b0c040b0405 70
    0x80107072046039400354550070503a007142100d18000750000c0b20003c284400c4c2c024000c01004210503a001401201d000c0d6050381d0781c01c6101103042d0314902c56a405103503102c9107401001d0140300ca1000c000c2d80400d042c0000e0340c5403082c5900510304030404907411070b140e0340d49103c1884908110b12940c0101c80e03034000c800714545004508070f9030312195402002010051010b401c00105c51012041001c2c641c081c1042d0344442f800d40203400a000140c030240d100c0c2c040d041000c642d00075060718001c05d02d6010303650b500300c0c100004103000090415007900103085e10b5880c404800303e032203941c0c4c031802000e0560311030100d2426800c000b801c2202940007a03211707030402c10000c000300d40c020074525001500100700c4842c4504900d44001c84810301000b450b001420503861009220507100c0d40200c000c0309a05546804002c4004981c44804600520b800300c0d001d1804110b203103041d20440368004441c0c400043c900b007868040804000910300c42c10f0120780c0094000c03415030400f8080c600b011101654144440d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 606787176 1250 606785926 606785941
    0x30c04051b1204050d09031509051c0c05120313020402090d06090f061a0904030e0d0c1401020705060f04031e05010f06051c15020f0409112502030319050c011104051206 74
    0x10599100403403803a271601707031241c1800010710501001923020a1003024507440c55801904064000307500340c0f154044c010b203030300b1310940c1e40b01164450140310307640c69901840c650810000350040801180c2210800f2655400180389d4404d0f008890f0051185c012402c07000d00e010b0040c0d80a80c000d8401414840c1000c500b0340c5c4513a0712030364004d6454100307580031482100215446680d4940041c0c2207030804000000e00003000d40326598048030a0b801d4031401611182444858803402010030b0445c80c080100b000400e6812401c1e01408010001c442107800e05506c8260a6030029840d0640b869501c0800300036629041d0740c0d074010705100001400310800b494603038443d9410f81c0b141078111581c00282290b4991500c0007241d0207080214801c02241d4410070700e0140c80e0300500b44e101c04a01c1d281311804c10440d140360201403c00c6e801070007540b525100000c2403c040000c040c001040c80014851121002c10a0090620741102294115111454041000f2200b007000c000000c45070051001e00900 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 606788426 1250 606787176 606787193
    0x3032a02030a0f0f1703160c0c05191a030f0f0f040201030b0a0b0f04090c05040b0405010c02011e0210050c0c120a090b131d06030c04051b1204050d0903 67
    0x425401c400410700c0701d8441c2c204540056041e0500030000c10400e03140c0c41d20140c40d0700207180101000c2c8444c801f00748120001340c03584d0009801c05030100909110801071494540c0d0098604c000010078019a15900d4005100d803070b03204541c0d040c0303070007001c0700704a428208021050740c0440c4415004400d801e01d000010b070500d801a002904140d150301d1184265220b454424006205560740301d507a0301e4414400c503000390024060341804ca41480003000e142e511070800d407010740d208880c070700c1c0c60903240c440192028201490308034144408d4071910b6940d0380c0040c0120207940f400e40c024040c000a48051941211801001e00248130800c2c000d456080a00040b4411105001289540e880c01086000d44060b205ca60019011440004a2070044c5400701010000c0346c449da803411807403040841d01640c03003c0c01140c1c1240c02d03070300c25101c1c441e141c9400c1e0403042d001090b6a0040c005104403007c00c41c0280d01003606202038100e075009000070000108204004201a1f203820b44190b4211b07594441c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 606789676 1250 606788426 606788443
    0xf080f280209071116081902010206011401030b040e030309010f1a040518010507020d090f1508070c080a030b0a08160302060304060e010c11011401060504180b06030103032a0203 78
    0x10b000c0c1c25000402c1c5601810b000180c5101c100c0844090170070055a0380030101c0c950040c401d00b03000784192160307075481d01c80b1407182c4554142c01070300e0303030783c0c07c245140004d032010380301c1581050b48403900c90034a601ea41c4112060030b50950061941ca01d461507010303083d01d64007028124003034984580c0c03601e00c1c00341c08191043c0c80c0040f078000c6010f8131900d4180815199044181600d94a428140a94103400250000d00b10019850b00b01c0e98980c0c0301d0700f1400200c0c15102d54071100360103d042c1c04055110301c01c4140d02c800d160601648500c09511055415003280b104000400c3c3e4900048540d490454001c0d4014100900245030803c80c03032002040040607407000900462001c40030a003080322030740040111003600701c000c000100d807800c00105800c0342c0440d064510b5103421142d1006c0e0249100c0c46058582644515107058908034000300c4d02800340308840c0400c0d586030700c1c001d210340d2114025802940241c0da008010002280000d40c800781c4103c1c1a001d400f4007420705001a140401d0401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 606790926 1250 606789676 606789679
    0x815070203160c0306110a080a020703052a060c130803070510112115060a09060f020a200f030304060804031809050403020a0308060406050904020d05070f080f2802 72
    0x140400302d40c034107a20300d40c00f15003000340f101e0b081600f0200030240c19800352078460a15682c038651500d81142d844102e1094850140c001041000641c402c51403601d8030b0308540c06842c148140e19410120610704218055030070325070b0792100140c0142c6038261051488094007642c4043e519045030340da40c050740c80e1a00000001d1668583c03039100140307c040001c0c0c5e0074801c5d0400302480b4840c0c1c0c016024141c0c500c21100d0b14182c02000507a82007a007004d40507241c00c0180c40d15100425401d021086d81c51706040c600080451095180d424005800c880e82c2c40b505508118400000140c5901004186413001c01080d000b81d0051008000180c0e0203001c041c0c1081c1c05040080108211002c001d22102e02904540011810320092004041d80010002d00c59402039030b5002c03060b25603000300425508944610342c1d02c40c07901004100036142c801c40e12205a031046048407120f5681d046d1048104000d68003510301a0480701c00d40010007028400a82c0119003042424600c0da89601c0d00c2d84030001815010303 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 606792176 1250 606790926 606790957
    0x50a060611030d2a05030103020307090b03030904200c1e2116080406020604060b0901080d18171e030f030103060f150f141008040b041a0a060815070203 67
    0x14403600c041c0c40c0c4d80010b040344040e11218002688100980b103a4000c0c030003240a841081d03400161036007a1710401310342410003400340d85030000e010700300303c00341100c2074131030306188150105085100a810018014084181c000c0d05207130302c801c0d00d00c504074040050422210b402811040291410b07809021020000040340e0544514841c501894903c25401c2c000b00480400107000c00c0c12074001407403a200f01d01c598020303c912003100c000d000c8600f4080c403486060b07a00c83c0d500c101626014504018000c840f80040391a4150741c4c004450f411010030400d02c1c0e041d04103110030306aa03400c548044041d00344500066240118517000418103120512000c0c0660369200322000005005801c00003800c2d505454447c085034460380c40001001c2140f2943c4c204281041a02c001400e212044542c14810384d1134807509642ca644452100381c1c6c00420841d904c2c45007240e06600b5111116406000c0c0c040207100080d014206040140740c0180c1d1402d4805406041040100c2d80d40d00100b182d40860304049203 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 606793426 1250 606792176 606792191
    0x21010e03161e0c0b0c060709030305040510032307020d091a1b010627060b0d020f0c0f03091c02090402012007291e07030504051201050a060611030d 65
    0xc016403031444040c010f005082d0003034000f408000c1d440241c60b103898218203840b91500c1c1c100301070b036020045100040102c0c50178007007041729280c44203a0f040c80300120f040c04240300000d581c000c0200e00507618241e03580300c60a007e1003800c1e91304100740740d02154181425103605082c4408945e030b02d1403036000340304811000904455102c10351b0b10054896010680240501031b00e0f861403216403015101c421042400039860a5560981070140c0000c0354503081840f4900040c2d84c5404020b50f0103807846012440041018800ea903104200780552916600042c5880c2c6189104000107600c07000500f2175103402264101c00075a49032178110b600942e0900f8215100040c0c4074400d051a0401c00d101c0840c2d0042c0540042c2c101200e0030913050841036814240210110070210360454090a00080c01d0041001d864900d04001c4400400c0d04078040d040031401e080c0c3d640005207002c00344202440c1180d469000b44140a4020f010f5600603004c00c0c1000721030f144a0800c516905d01030900c82a0403030391201c44 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 606794676 1250 606793426 606793463
    0x3010308030402040905030a0206070e220905030708120709090c1b0507080d0509090708240609040c0302120108010516030b151b0c1009061d21010e0316 67
    0x201c00171a0300200b41d80c2c031444a0b0b0b03006506c0e024219144c20102c2c2c0b41741030603440c610301503014403004410440a01070411405030580c006025040701259280f00801c010000f003a90900035010924655034540032500c1d0100004000400c2a40481c0710a0b040c40c5202c82c50365042450100198000b00c41c2e11a020050f00382280303020b046500000150103010103d0441d02e40c081e00400d03886105031810603083e1164030040721012000c0b0b80d4200000701e1101140d200c8040b810409283c140c00030207803130600300c1c040000307011140c042800e400030a0740000c0c07200440ba0100c045a0050200d03d00800c00780c500201986c0550201d40240c01c07c05560f200c1946140d0340d08540741200311142d040c005d1300c0b1101c0707a07406035012080c6400c0c80c00d07a20034180c0e5003071103142c205180c161810842e074513104d52528004042d105440000c040500b60200d20b4030344001c3c1d4584e81c00d80c10101c45140c402c071050719140e61100342140c0110348641110340007000402c0c010050900d01c078035407940c025101040f030202c400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 606795926 1250 606794676 606794681
    0x1e07092307140c0106091103011a1336091709060c1b0910050a0603021b0d02100e070b031602030c01020d0609110c100509010612060c020c060f0301030803040204 71
    0x2002d90910000421116100c0070150300c28030549108010810414001e205a0010b40c0001d10070340d20504914104aa420782c03462003c3c040c0c0381004207004018944540c41c0c00008051012135030b00341307100704141c5240086891150300360184030403401c1080341e00c640c852040a212014080b00c0310000014050400e443d10021101d803007000d8010340d0300c1864038012880c01d00c0748602c4800d1043e0706040104450325920280c150494000420b031a00e1103160410680203900248082d52407a903001c19807038404801400703482c403405100e90103022054280d13250700c0300302c440c2d00514a10540c801c8401b80008280e2104483e084140c09003000143c0044136003ca1461050440030105540003103810042954150031000070f60340716036800c0c440811005203410f49400366203000451a40300540c040201035455014680007801840085601911a1034140c1c3c040281c440c121046955030340c980350b00c0f903410b0090003100001110740074901562400800309501040c00090004000000450219680c55 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 606797176 1250 606795926 606795947
    0xb070314031e040623100306053c090c0f060f190c111008041115040b041503020306030a0311011805010c09060809070e04020f031e07092307 62
    0x20390070b82034605032500101a103021501844034091503c03d4010159404440c00e102d1000055060355a625640f24078019160181c02103403d40d1150f58a600700008450028649039500b86640c1d1a030924548800148030005000000756001245135110700d907185104907024440440307045803100c080ea50760782421311840d071400603620840304800b00c4543d0040d00d645182c5001e071080307101c050a01c6052207104c0d8207003800e031000101618005000a600c004d5420078907000a00500c102e00c207448004000c90b4420b4101d400c60f200d002c5010440054a581165a0400c013803406604600302900420343e204210000101481484501c1100d0048250f224860720344035125a9560140030f81080382c020b10310391080c1d20004211500205d40c090041c003000d40a000c1d030b4401880002e107840a0794046c2480034000b02c0c0c1c406181161440d456404001f1969807400340c0c102a0303d0701c000956030341e1801141d5800700408900300030004001040d82007481c0084a0840500b0710183e54001049400e0f03a440c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 606798426 1250 606797176 606797221
    0x402150c1c02160905040611030106030b04051f030f033b0904020616020102150412090e07080a021c060611120403110d05030705190c0b07031403 64
    0x108000c0010000000c40491240003900301d10456580c4400032a203407080c0320107800c1d4200b6403c1040002d402e160303005a40c083d020b1100050b00b80002c41090071030f030707000ba03001100103522001405503510301441002d4100c00e214400394041e661910712000c0d050445e110240500c80184406c0060500a480801d0408000d14000c2d800c14001201171035600f01c17900c6940d40b140e03601c084c009414149412200d000343e400420441c1005000404141c500711011400c904601511604140600c002213015004500c515028581d074565194004d110b1a001d40c170480351620a28140280140c020010b6508070030403039400342c0d40d070703100094001d003124081c1200c0c00000c0ca801c1000603080c0d402094091100010010754014402d00b0882411a000700c0c04064540350201e2556a070901d048100b002040744510f066034105002d41d2070349428200840c003152031102501c5101010441e507540a000a4040301d00709500746095528014160642c04032020000c0c080000402c58041c82c0c1d6244160b10b410 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 606799676 1250 606798426 606798469
    0x221106072306040c0608190c0504091a0f06040e060d03090308120114030a05150601030b0d080a090510050a030c0905130f0c0f05120402012f0c0405100b030402 70
    0x8201d8000d81d5601e01120140e810000a440200b90b5030300c00c038021401200014201980d840d0b1034409900240b5003005030206008080000040c000034602030f2201c12411401c406c4800301c03642c0184001502600b480c18486c803020031040c0000c11001e00b5071038000c44142c403074100303019052074103844110301600003404d0703064041016000e42c0360140ca8107060740c45102c03860443c6411041896030724003041c1c10081050b0060070698a54504800026500030014035011501901900c0498035080c6030560640720300d1400a0070a001c1a0006d9030b007801884c040d204440c03001e141038002000340c01144c1c040c0382015150701101d00c0d190f2051201501606d001420700c89840c2c291120f0000600b10319481d9900a410301b105003070424017820107000e01c035009845840c602403100008003000c6c440184101d043c04215901c07108005c444200104803c2104401265402c50107110185020351614a040c8205d05100c1040b1641010800600c1106c40052045449454034400904040ca05000040d0340c01c9 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 606800926 1250 606799676 606799733
    0xe01110705012c0c0103050c09040603050d0315140904021503130b0915010e07020f0a0f110f0f06090301020c060a0603021f210f050f22110607 63
    0x501940812480c0d029010064104050041e08205803c00b1403007408040d0004807080155500030303007040d82d1281c4481031a9142403032860006084502a4006684036031268041400c0075815120784040303054050200081d5900c1c0c50383e00e0170454040d40d400c03401081304402103070464450050340e59034540d455007c41e4480c07030541a860541c0e40414000d503400520750000c45c0f004000400c48030301210910500d43c000c0d03070a2250302e8100701c1014101d04110301c03030340c003030120034038401d200e502541449940000410659400d00c0443d00140c11300c0b40f4414400b1040088003075440a42e48001124140e858030386940c01c801c002030080c0140101070031140240c0080000c121480c0d0310040580340b088a000c0c0502d007100ba00351049104c010a404c0200310700c01d010542200c1c415085103601410070402040170f4009942c00d50a0320002e03280407000703450903010300604502d2041c11114540f5aa42c130031720304420342d032030303001c2220f0f0440c03c80d50040a0015010080c03082810020f14100039a01c82c035500710 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 606802176 1250 606800926 606800933
    0x13020d05010519110c0a030e030a0b040507060305060906131122030b13050a022e030507030c02011a040c2c0103110702011707180e04021e130e011107 66
    0x80e60110f00c1c40250340c0b52001425142200c1000d076180c103607001004041034900c96800351440c18484140e25850b00c81d00310a4030000f4101445644a648100054400ca900e48103000c0c00ba90300103089984500b404408110890310b6080c109020848803500106030f0030006c140001492103a80104041d0b021090301d00e0300c240040c3c0c030b503110032030f84114200c80407a505d8050b860304410074110028025000140342c140503241810b00c4000d4501807224034204001501d0501c5402000005c0000210340c03100c0c00c0002507500b41c0f060407100c05850009000342d6503410100303d20010301890b030600ca5541c98004051132031051007200c1004440490682000010965082e0000c07003070000203000900780300b5580702905051382550304c5181e041e1204051512800700503100c000c0002e040d2001c010720000e81c0c1c41c0c0320304c02100a10080102144c10f448904145c01030010b0001005102406805001d9085199854002215044030112800020600b0703e80740351703c2c0900220490601c0465020404400b403 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 606803426 1250 606802176 606802201
    0x30c1519050903031305130c05040e040314030a090c0b030601090e0a02090307060801181b031d030313020a09060303140c0f010510060e0a080c12100e24060913020d050105 75
    0x341c03101185c0c070000c007060b47d1214401703a504000e40039002074420f0100700034000b01c4440e0743d600f06101e820300f107100e0040e000c034111142d00101c035021101c90300c4200c04014070100d84a42c00143c03003100e00003460740c6040c500181004203580303c1c02d45100c1c001c02c00914064401d0381501c2d0807030001070540e00e0700361340c0700f0004140305030a02909805c0107025051024100840c85501d001003042d014080b2110041c1005030b0007020140c0d200380e0703486014600b9101c1e03030100b40000c51040801d0900d505000100c2c0c018081301400300d030400894246405402d00c01b081d0481000490038101607112965001c0c0442114104040706460302030365030030f1a0500120003622100c89080d0b400300c1d41c690306801d1003a010008000b070140b0032900185c1041404402c2070030030740c00407007080da2540115812189942029001c0380d4804c84213445a40249023096441a51803d00c4820004100c491180e18101302000980c0c50703001806d0f0030401d00e40022607004640750700c40c80e07822a9030408020081c500c0c00d607410225 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 606804676 1250 606803426 606803429
    0x1a1c2418080c06011211010c080714030301061b2315070e01141e031302060c010f0c1e050a0909050f250e12030906030108010209030c15190509030313 66
    0x10b42c001c010010400c80b0034500b0348010590802e00000072401110010f440210301d03010152526907041041c2d401060f045642140b44c0c024500041d5920362500c02c1c01840340c0c500d90040e4503000072840650010034400c418030100b2401c0d100404089034074141000b40307029014056203883c4964001000b20a40d08541c82c2c18070030344217032a6001100c0da030303d403a210580701d54104540c07400c02500000f51005a15400f45a0009601e805d0110380940c0303400141d61500030442d94000703030303440d1001145e003030005008240c5d4400083c20106098003030030b02520301c02c1c00c1101100040003808580c0c11585441403000000414000008110909050700c1c61295210704441440020b804890b18400c00c581d0030a00880810043d650224181ca0580810084018420750400544824410400150f461500440c0203064040005030b03503145280a0500741031400030500d106904106403e0681c030802011141140024183c5540c0c44a00350340c242e030180981c00307000d6050b20001c6183d407a0f4094842c00c030b60 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 606805926 1250 606804676 606804697
    0x130512070603060e1618080307050a0204060905280f05010312300e0a050303012306090a05040c0201090c120201020f070501050a0f02030d1a1c241808 66
    0x1200304c0d00c80d0240c404524042c1d464040e12001150003220041c0714440e01d42081407042c084103038043e03030381000ea403035900b100c1d60944854101c01209411480d261007060000c1004510520051800207440c000e200784090120b054440130807001d075410401c692242c8000b07414039104011b1b41d61a03081c22a80403c0b030344480408200014454030301c004412005082541e6403480411024900380300c410094220310390941003510030314003038000003030051007c0c5001c0c104281000c0c2c19881d00e941020508220091241c0c01030604000c454840e4a500e03215405440d01076502054840594904a006000c204400340c0380340c44816020803400c42001e614a200c3c1c1c000d03400c8030b85040c1903260458031609103215560109208004c040d01d181d006e001040c1005c0410b0042d00e08141d940ca4074042940c0081d4200c1b54000500d406c2c148040c44e180d030308902844210200034031410050b41d0b078002d002c00318180290402c9826403000400700c40070782180780c901855072407030203144000c1c1c5440000742e0001d0075201e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 606807176 1250 606805926 606805931
    0x203160c03050c011103031f03050303010e07020721030e0d0611090316121101121803030c030b01020c09220b060405011203080f0a020f13090606050703080a02130512070603 76
    0x3d010b251302c9025001111440310010b913113180c548a0010b002d00582d0614000b01d609464000070120300140702541c0200b09801e8407003000d00c0c1c003140c000d0402d00301d50441c0075414404002c83c40011070103800d004506616041c03260800d584000040e00300801c20400811003803c0050100d403110f403400107400040015400c40300000f815000206030303914075016071700d41c00c400401c15070045107203c8041c494500043c1841c294600c1c142d054003040da14000c108500c040703484000c410805505110301100d412451130100401041900001d40310368402032400c0c0326000050100300d00501c400b500c0c4210307030742100b00704007048504d04d82540f582a00b01da1141c0f146140000010310b584007401d44c03400032a0b15a0303403006d01d90345444158451850290142000550a0210500300e40000c1c00600d19410b86009880d041480d04110009a03103c54020108011003880f542c0300203900800d129411040c0e041c40545c640e10a0019041c081c1d0140d801741d81d100d0100011004441c1d030104002d41941c9855805 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 606808426 1250 606807176 606807193
    0x60e0f0618010f09080604022b060506010e0603160c0309170106050f0a080a0303090827030f010c02030a1b0215120c0403021315030c090c020609010e07030b070203160c0305 76
    0x5a40c02031321440380b07219680141001a0040c0f0705a51424030001009111180c0c0e04014268061115070100c0304a4019a840c400d00c00c1c1584c20841d4201a071030308480c902d140d45402040300c0d1024820b030f5070140234480c420b08424101405a20038502510300480c1c000442040c008526028103802c0c8522801010340194016107400e1250703035101644c0401c001059001c0b40e40c1d50480041a403240c0036204038000b80101a002e003012044840b0b4100308029106006000030b040505200304905500300f540e25000780300b82030036008000d40301c01e840c03039050030203220120040c0e101c0340c807100c600c1c020b500c01101243c2117003c2c203151000c1c2081402c1808224000e40c1d50442b070507070503c90750001a611070740019100034a00802e030404c81180c4140224140c0f00c039a81e0356891000403840d007004803650748a131081022a6070410400d41d00140c440d00a11024100c2e00a1a171601c26900010307090042d810f0018a9050080080b1402401c84148040180b61281801c551890060000f204c1d0360041448 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 606809676 1250 606808426 606808457
    0x2013605040b06070809361602060103121110020c0d09091e09020301020904110d2703080709120c0509010e1014120105040c050415030c060e0f061801 66
    0x113807811540d020104600c2c2c40080f004105090407407a80c021f0b42c20104840f50300c00b5603103c0500342420003c1e2020781440d414005e01d551032000305d000d0b58208540c40140100041840c44145d2640140c0d581010384841d081c210b2540d0400010810010416000040f25241d40304002801240040251750702540c45860300066815503480d4103c080880351001c0c8158841c40305640824002c5100800043c43e240b041808101510310404000c0c1c0905404100203903418064054003070700220302c217009480c11060450241c981010404058100b082900005000c41c0c00b4084440240014001a8640c09094035200d52903050038080d150295031840000110345100f240c5442c0522480d581883c516410001c00051842c404080182d000c10b1003400b4144000d400e00c2036502480c058207000c410b0741d0410081c0401d0f690689110018628040c501f0800718510343e200f602660074914042240020400c00501010035055145901450000d0400402c4141d40130403074034410203803101e5026400180c2c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 606810926 1250 606809676 606809689
    0x50d02070e09030307080a0b120601030209100303090e0903071406010602010c0801060503190626010c020a02130506150a0c120e010203040902220e0106020c03120702013605040b 78
    0x44070007103158018400301711094081e007544d40c0c0c0520320b00c03800110a198000001c180d6584100300e0081c5421007401407040d0309011100c02d6111000000358840d0501e9030343e0040540f40144034102403004504041110b40c80140212090345400c03d1101450341c40b08400c040d100d180a11910700550710701101803071a05d0250511078100c07005a181c07107045644200829001013a03101480117015510b4402140c401081c025200140c03025480100e60640401000360071603e1100703061056600c22044500140c1d00c50840d007614145408010840c0e45514001c40d000e411138500d01404000c0100b40300c6c003480d40c007642c3c48201c580514551200c2e44131101c400e450080b07910980c140181c00030001808100c445800400d030000102c1080310010605000e1000c5202da590081d9462024200c0108100c560402c8140b007214001c50181002d00003001c10b444a6102c1e00038001d06102c0329652a800d5412103c8041c41c0385c50a0075107416444c3c1403480741e005545854040c0a11441c542008003042c0d04090 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 606812176 1250 606810926 606810931
    0x7030c0801031a040201030f0501090b030f06090a14010f09030c0201082a07080903010612023c01050702040f0501061803080a031e02040f0e01050d211b050d02070e 72
    0x2d00903620180745903d00071841c91000308264145615140f15114800880c410340d03001707000c90140003861801e0241018101400c810348140c240e44420140300031800c010900d0400b84d54801660344a1075a030032095070140242c3c040c50412a480c015034a01450382041145e007443c1e00c03d82c1c07a0142a903ca82040840c0183c1c07036020800802e540408045038120701000700f00d140c3c09400403030704007030f00c420000b03096071500c0c1c0220208480e82c030450421420911425035142405100030110000d80e90100811540340d070701610340340580c03400d241c000d50f400348040302c0060b078018200b4401114116681700c00ba28080c4240d400060119004c020944400740040060382c0d805640c20380342141423442140a02000e80003107640b0103001d0004030003060144018002000710031904400c00d807030401d44020070709059100d04c1c014554428040001440c0f4100c4100d01400b20351240300070200382100b150101c00302c1d40507c00101d9440181ca0038400d00103800340d016400c960841d80c030252140035400801109 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 606813426 1250 606812176 606812183
    0xf0504111203040801060308070c1514090a15031e0b010e0f010e031504050d05070503070201030504080d020c010912320f04150f030b010e010c0f02150307030c080103 73
    0x44842003911480c00030544104030710480d04036414262244000343c00c40b00d6550080b44c200000249000c100b000f02d0b4608401800080c522140c203c1200d4000380002ca5070641004400c507002911803811f40ea0600354001800e00d6119203280c0307208078800034004281e42080c8070141107a421000d80c08810301d000c0c03c40c21703c0c3c0603500c030b0001d00710050500144c075850001c10f45c14444180441c0c1c005031020402c0782181e008841c450511405c083c2015030034049442d0020301040010840140400c4000049807000740e42841c000486d96543d081007082c6000b040c00da284440e000240c1d00c0207c000c150080d200c1e850140c40c0001050308c00043c16607013419030320400300b45c00e03003c0c0c41c040b03c0d03145107a00410000740c2200c80c9035103010000c1e0118915503015410600f08543c020305000d070482e5110041a007043d8241c2020800070b0300c142c002810800411203001d0400005020203410040d000ea0309520040d4050a20340c0c03504011124480c281e00700300c40d5a0700103890f01c2411104e2901c581041812243c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 606814676 1250 606813426 606813443
    0x315050a0b0d0f0203041b0e010605070f05010b06041403120301030317040501060b071202060f040c15021f0902010822020d031803030e030c041109010c031b0c06030f0504 75
    0xa0114600100c2e009031000c125601e603a00c1c010041c0b482d81d4002144664400c201c6810b03034080124a00d01c00d4803050f002048030b02070000c01441010380200403507103a9500180b10102c130951a2420350301402c41d100901d5040380001c9000115881500a10411000114280c030a40c0512807041105400244409000142c0584010903e040380f1003030075401601510002c1001e94490784d071b079825544110022645038100242c0700701629818031040c1c1e0000e41c040d64005090900c0c1e210303814200304601810a43c510201c02031807200340200650804801d9294442e0200c40902405400800c0d484c2003c2c0d010840c6a400140000c950a42c6018500c40106001245152036020701c000d100d9150011001c1c44241e11030f4224080d6001c030781e1001140710307549450b03801c90440241403c140035841150701450505c010100d6060b0701006682100d8001c1c608628203c400313040c21101040c0c0c0600100700514011950414000403400d50810354130680c5083c045016144604002c84000702e0380076180c4207 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 606815926 1250 606814676 606814679
    0x90402010e0126040c080d1d040b030f060109060b0319050a091506050102011a0a0519031b1a0703020606010305180708010f0b100f0c0227070315050a 66
    0x1800340585914840707041c501807180b0001c083d03107640c40c2c0001540c42e0400300c208204200800040314039001c0580303807000140012030701584c40030700348208112a074501c2141401603c035864545600606050340700600f04c48140750310031161511043c080c000e01c2c00160505c040441c4210348081103074098039000d40b01102030b10200700c04e440205406480b4000143c1c607170366114049036450009070303008140f142c4005940d520701800079085440d860b9000240414240640c2c4d05580e480c4d00c00c13404c981c815140d42c5d0000300c41000c88080d00c8400e800c01005400b00702028601000d100e02e0f500700340c0d0442650800f101e00d0301c841003201c6012350480200103900c503d0000350f455100340c1003981c12400881200010780b0460342d82600b010300503002421a69034504c3e101340074810f103014825440701c0c20b9801080d00f40c20840c004000340c454040a4050040c1c1040d180219200c5e801c03108001511100c2a141204110980400381501690b41200203030400305d0707108105e42c0404000080350001421200341a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 606817176 1250 606815926 606815929
    0x10606080a0203040c0e011403060703060b09090a0b030f0312071b14070506160303050a020c2d1605130e100e0a1203020702090108010204080706050d390e090402 71
    0x2540024402c6400c034070055400506c2603920094680030388240000790b5400c01d85c3c2d8081c5460004020010750030142003000c00c0142c1c18a540442e03180090a454421995503051307a207201a10700d00d050942c051041050540d00c04d00080301400b16003010f0b0040b210b003038480307840464440e10101c80c0c09504004040d14040003c00510b1030601e41c00000341990f502a69500c0051641e0308000f41010220001d01c40d4401050f6240c840da6512450300f0784214103210168403c44e50b100070760041301940b03c1c2104280302c00d02462494100001c0340d56800c450a03e10525480c11540c1014490b0501a418102c0c84220702d20003401008014240321000340921812130f14504080e1400c1c080000c00c9020b5100f0344400714009079421a0748545a03100581d90b0f028500c1403010070501640650314591040c0020700810710701140300030440d825460719a4942d082c41c031070760000300b11001e4614004541100c030702500c3d904005c29408a181440b8032044180881802610380d4400303429516401300318080000e005 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 606818426 1250 606817176 606817181
    0x30302120904091b092a0e1305010b070b0117250506040e010f0f140d0201030f1d0615010801030206070f140f0d03060506030f06040f0603080d0608010606080a 70
    0x4102005001140b4800a916482001103504c01c801d6110744a5038014806041580039040300304640584181416101c0744ca1146c2c2c9503d183d8908041020b00e150203000b642d2103c07505468800c03040c80412465969203007c41555002c203100310f501680d68400000d44440d80c24200e4444003a1502820700032207103240510001d0700001000c1d0000c4140035004c00c0030b071203610242015011010b11800175504149008103840000c2c0d1040c80a070381d420030b06200d00a070344400756080080694a81030184681d20050b80601603c1c5003520035039290000d0190a040040e080c1cce035041d080141035540d80e4070f401d00c1080000b40714641250100703801900420041c10810f0040c20858060125414240616990004c00000c2480c21ba103d0f94031500010412003000d200350b410131956810200140b519120108805c0d000003000803442106030720024803a9261071300040201e0003214810003e6540320707d010529500305200f580003041c070380107001c220719005104060540d5015107c044156488146200c007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 606819676 1250 606818426 606818437
    0x213090b030c0109271b0c05060c030c070b0c0904021908070306050a120203011d0d0f0203040f0e09120316030b030c06250218251b0807120917010603030212 69
    0x10b0f01551110b0300c2c0c0103500c036407104d06e420081d5079603440c41925041c20031601d40600a0000c0919600410034400c1c4214542c0448070b210b988642001c1681d6130341c100c1040705001d0f010515406ca4000103441c0d40e607926080401ca00c0d1010b540b103007641a16109402c07021100075000d140d810124144060003030010100100005038030040001c02d5a9401401502c90f040c0842d00ca82002d603c02400c500d85580c0000c03030b03c0d22405982c80211b0405140045450340c2481714414040900280343c0071404241040c088c855408245520042e580e003803d00003458070350041c0801d28000fa25101c01e00f032161a0100300c0081502000709914101b00218002d01403125640d140307800e951810881c0040183c550190080b029041c1c1c103d5044149054416203881000013981b01d18009032a01c000c00302541c10405a0090118420002c01000814503180c0c2c09441858005400203060030a820007045d801880d0034140c0b9061b9410b03046001c1c1800c001c07800d0301c1c418007000700560000f404001e1001c3c0303880701828 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 606820926 1250 606819676 606819749
    0x3061e0902012309150c1b0303031b07020306090d0216030203150c13080709050610270e1303030608070b0a180312180609030f080309010213090b030c0109 68
    0xf40344c2122a00051000018101505100e60b40407072100d481510074010301c8811800c40c20600c410000c10380000ba228840240f03011034180c1e01c145107443c41d1030311605490406602808642003400d00818080e9619440c02801c0014800e090350402d00c003d903c031003d4102c99002e00102001141c0c14551801ea0318024112072000078184520341813420443c1280b001040914041d260300c03403c1009070415220000c1ca800e00076003002c603584a1481d445075542c49190610903a44070741c0744882510505144242d44229910801d01c42406030400394803035914042407098408018490f0350382c6950351664864802ca4000c11418000e11013128040c500500c4091045070510502903241c2d40c070701042880702c0062900151201c0c0c00c01c041c0c038548003100350203444281004403050b0720715901c0024002403040002c10040d40131020074070440003501503800c0c500060583c103000589a00d4104020028408564424032442465491a500a69903030085e00c00c0d141c00000c0c10340c0302410381800da4400c0461034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 606822176 1250 606820926 606820997
    0xf0c06160b060f0d0c090b010503040206030420040606080613060e16090e0a09030e040e0a0204110c010501180c0513030204020c070503010f0b030615010806010c0f020a03061e090201 80
    0x16400e41e03980c130800f140076200308508184130b41000c8100045903100c48903107040c0581003007440056a101c0c000e40c2c1c0c0c000d03848403440800090752941403031100030000e10a0780060400c88046415900000014440c1400351103812206d000b10805105a80d40d03881000d02e0b0303005103400300304906403075820820184044e0034001c1c00596600745c0011160800c072125050b43d40d865540101300340d4000346414048004442c1801a80303d00039805c0d8030380c007012900038459a980d058030b100014480050351180da0300c90000300019170b0f45034080c0ba180c40e0224200d0000d01e02e40f02a212155000c3c10995000340007080207602000d00310f5083c0700080d88130303004590380c038400d0444c009190380d4240a42d28040b000424007051074086042814940a4040c041d01065403200700c0d40c01c01641d00840d5654011340c2481d0600301c3d83c6d814100410001548500690821240f200210a02100b13410240881000090351060311031034800c1802151107040009000070b148808554040141104185800d07402d513005 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 606823426 1250 606822176 606822199
    0x31a0c19140703091403010c08150a0302030a030c1208240103140c090310020301120204090c09090501091e02010c02040c1206291206131d0f0c06160b06 67
    0x300c000741e0b044444100c000603241c140c24041e800d01c1e2504c0f4007421000790001e0042512038040507081e0500180704550f40c048010441a00f80c2d034243c1a20001c40d00542a11000601820020024200d0a00c2990319009903038542e190710f03200b450000e100d501e5050a00300e4584004000381581226506601d04141d107a90a1a45411b80f15040c20300500c1c54210343c1e6a1064841c003403506007621000b10243d42c0b4170600040200300d0341603046c00046030303044800069040e11458081d85850707498001043e11490850550100141540f00b50441170085000500540e0724501400da002e609020003400100c55060910042c02d0981041c00341c140705040c051021550000754100302d6009a01004160302e5810140c41c0c0b10b0f1515040d000f10380b0fa8900b000c0c0c98024170750101d030303652180906014000c090501e114041d00003a5881461007100000e044440b080c0303900520355941d0000740004156020304210800300d450000c041b664115922000d8858403e0161100901450000d082c250400c808000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 606824676 1250 606823426 606823457
    0x1c1106061c0b160e06120114150301121e050c1e100e13110313020409080d0f0c02062e0506030907031502131806051504031a0c19 57
    0x50b41441501035841d540c01074214100d004011000e484107050007840c0410a0480340c0d10390100c02410345032142c40b6201c0c414000f1000ca84100d40527200c1d10f24101004c0004601d502d09240c0981a003405120340104400c0e06804040d040c0005d03190080c040d03400304000904a003050340600000000d03c000c2d00c9400140c2801040b4140d00c440840d00c000380c40a10070361707500e140c80420300c3c02a01c0750010400c90700341918070000c85480050604050482021035242c00c40da52900044000f07940200d059880d142060454805072424940175041c041c101040300c01002d200140a510440c00300080c0c2450813428403100c5403042c01c492030190031554401005c9040c1e10791100441c0201007681c000c00b1014658101403500c1300510071004030807401000645600000c54440e8015940300c0c0940c0401c034000c3d07043d604020400303075000607000140300d07080903c0994003501500840c2c1c0a9074844610701e10b01c541288240c0300440729282010402d01041200c07a008020036036151145041c09401c0c3d110280 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 606825926 1250 606824676 606824693
    0x20a080f030a120c02060c0f0c010f06090b0909070902090a0906150f171602030c16062304090c0918020d0b0f100302030a0209040e1c1106061c 63
    0x21226029074030000320360030990352014454010f400f007404100324128180a001351200030107080e003003c15501040f0f03500203010f488203c0d801101e004008200c517070032811008026101d03070310503540070354a4201e01303c8240c00d040d480300d8400c1c002900a41407050400e150280207400143c1816088459540041030307082e1188200c0c009460709071603000c4c122141c0b050040c40c07008110888010090b00302c004060303402c400303004203800c25000f09104e041d80824010892035801110388040c82e910a0241000c0f0030480302006800303070b9074196180c011601018441324882c1803841800315180b10200804c1010950130b42c0040b00d00500740c507010501e565940145107003a03040712104c09005500054182d85504c5910411030496020b503402050b0400e4030000445410700e20003c407050540001c00100b142100743d04030380c2d1a410003081085144007031841c2e55559040390161825201c000d030340031000c89001d44400c80012001500418840c3d03216818480a1841107290f01102181c0203402d20010781c00e00e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 606827176 1250 606825926 606825943
    0x712030f02041a07060605030a20060702040c0e1203040803190306050603190b09252604050610050d080715110d1a0307030215070b01030b0f06060a05030a09020a08 72
    0x1034504a8036021241041c81c211b0308682d001d584691b00c0a0500e00015406030500342e8210441c0c0e0031600a00210030100b5064070aa000080d031180c03820010707d001300d40081440e1011103055810140840c00d19110303960f64410707070240101e95813080c030120901400101c60100e42c5441d83c540496210790713410101b50641c005446c0e94041601400383e0f0102c1241c40e105040181104075482210390034030500d607041000c2c4103030f0309500911841000010140c0a00c0061000d413998003440c011201d10702103010501803080d0303401c032014041c402c040b4038003610610340c20341640d80003003141070b108803d581c68024542c03200d901103d586100c81c141d0603410019129461100c00b0a4400c1d560701c10141145c0801c41d0200d81e01e44120800050500110b500c1c0061000d0a582d03065880c9000c1c0145c0808850081c010300c503008203403a940d04004400c1207a0a04014000c0804a5840b4035640303a480811a080c0070f11140000000c1f0b06100189201a10750081079032a40050645101c0ca03440b12401410700000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 606828426 1250 606827176 606827219
    0x30c0f031219120207030e060d09020306010603090605091b061b06010609050f0d080f0a0c17040302090c0301031a07120908041511070b0a210c080c0712030f0204 71
    0x40504801882c0c0c0c002003c04a0301d0703026901149061004d40d4007902241501c243d242c0948030202c1e0700c41c03501195501504045800800f110b0382c0e982e480b034004000c0e14070007004942d007508004c0842c1a4040019a072174078011206281c0706a94400c50504c000d07500840c0a03d006590b4040d90bd401c0d0780b500b070041c640a041c05548e000c65590030141444401071107100990b0040307000781c0c581408190701c0410b9031803840c19039081d6036580071210000c450440100c074001d02002917100414402000b03020040c000c481c801d81d40342d0540e540d20b16a64506010901c000341c10b061807130700004000d44010f03200d81c3e484805c40c18001140f50b050304181080b5401c405084401c208001401e11144004198006104609191200720864000300c1d40742c440703515114440450303002007804007104e40500c41c100c400c0132082007103001c0764007600c03810400b9120031001000460ba0442c04141e522120740111200f1582100025400c00000e44084000f01110200c104e2100e600f408042202c442075105000c180f113a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 606829676 1250 606828426 606828457
    0x27150513030312050f0f04020103111309020706060803031605071e0609050609010e1902042007020f0418020f01020f0102040f2301020a0303090809090405032106030c0f0312 76
    0x500c105000c101c1300080c2240141804400030046158040800503500550a1801040c40d21500000b4205070003081020002410920f0011030841c0343d40d170240c680300340604000d100c6250359992240e2603200c140e4406610f542800c3c10383d15454001c00003040d50303620a00c50003141d02c0c61000d420418021540045640c1d54480384010b00340002044681d0b040b02505c0020003000101c20038041d070740c200103080c03151001000c01c40300c1c05550322a0302c85a003020f0300c10203c0302e07180c501140d60303152544400800c0340f1405421100b1080b5081502c074104286002003003000c49143c0b15001c002c0064441d03401c040c114420503c0c280c43c8424280041c1c0002d12030072092980081c10130360b415041210800e40d010030300c3d480f02c040c03d586aa002482145894150030001401c442a00f003801407803156842268000090509010070000000010070031914200c1107008110400101c940c413014064509035410352000706414028034003240511071808000b0704540c0140d21056604442d81c000c0c540d5000a500e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 606830926 1250 606829676 606829697
    0x4170304120309230318030c060702040905010605060f0a03060e010509130c030501020a02030a1106060a2d060f030b041505040e0a020d030e0102100903021b210d271505130303 77
    0x1420011b01058840084015000c1a2051008100680112030000e48910344503880001400000e601030000340c030000e00550b235210120340c0d40341d1031540a030b51280000780c82d02c000001c0c24030200a600c0e043c0c840041400d0900c3d100c1c12210344c0002442c0344c1c291101100741c1e6000000030404d04c02018485071036000303551500c100e24005030018198840d10881c5400010400001d6501c240d00c0e40c01761f44200c41025103d400001c3c3c8007800f002040798044151002c035a01040e4160081c3d00c66180c0d43c52a40c0138820143e1032020b101c20707940781c0c80e1004148880640240303e039241681060020152000841d10168801d4001803d04223a001040e0041010f0007007c60441d68148118150703401444414013120312a91b03002951100940c100040004195402e200030707540300b4041102c06104040018085401c0713200458561040c240c0000c0826000c40b0606103403440c2030444515a000311000b66845880c20342c41200c484d00c05140d1100708402005100280c2c102c101010000d94040c4c0e441d905041c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 606832176 1250 606830926 606830947
    0x2100e090f06031e03030a18080d1b0323061c060c02010501060c0c0e06010e221b39030206010306110412020f04020f0c06041703041203092303 63
    0x328070b030038905201341000318500038044001003140c1c0c00c840001c40c001141240c2d03040440301200c030b05000400c100341c00281281d082007107810007d80d0b101b03607801134402d4460022059088502001807051452000280900843c0580b8080ba0340a8006403540214200581450b0039001c00c19400300d13801540c50841901c2217509100d840d01515140c240283c02c24840d80701e00503140040d01c40c240d8880c18a100040e116441017031064901c20003c1c00c11072021880b0360900c01c00c00d0600c442484190701d41005200c9100000d681002030303420355180c0e06c4003280b041c0099458041102035003503498959801c6e00035100351201c0301c49100340c06031380a0441541107203845415074440400220760380600b80010700107044c41d040342080403541161141c2841d403c007030109001e4014030420400300c0c1d6010840626130300c0003140aa200d180300b07041c600d001115142c40b042d6280015140039010b900505484100d032030103076100b0780c0c05a02400340000c46e0440c41d0054040c5d840090510b4207035410100312402c89 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 606833426 1250 606832176 606832183
    0x70306050c0702090c0d0902092422050a02130b19080103080a050306030c04320919080706290d0308191803080601081b0702100e090f0603 61
    0x70001e4041c05a141c5a0030b90002140200064845140560001203c084403401036004103074480e40500100346510700511031010b01038031810345038070702c50001d5a5204946042d001425466004d080006690181c0380c1c4154010940202802001030b03081200d504141040200503000f821400750b00d507950300907151075800011140c400d1800380400c80d401840096404000d42d000c0c1045468100d46a40d11440041e00d030101450201390032503d440041300f202c1c0f42c2c200307039008001441e401441102400840741c5007144c808440714940e907000300e00700440441c3d00c41c0f2003091003800340201c14102042c0303466843c03c075101d524060031401c07251a030603c8817040000280180b07500441746110701c00c8080d00c000e040420000c00f61900c1b0340f43c3e00081010791400340e0004035210b0281070b02405848207490007410b44042510750f83e004c44c030540001008880b4503500200b0742c2c030405902c0c50414001b6400d0000310300011040c8010710030002c002a04588503c18024440c07800c181078407045041c0319040c1403c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 606834532 1106 606833426 606833431
    0xc1c080108120901032301150e030709050403260a05091504030509063907080a0b040f05060a0b2704080711030a0305090a0e060d0303090606050a0807030605 69
    0x84407400000e1b2a030580c0d6407100031005000000c80187d6018010946242c0d06900080c800d0082d050340360401900544a404c1c03140b202807402025082181c4205070f10603036503440004010800040b0b001741500501b42c480a4103000821003404210b10f04000c0c8003a080c0000010702054030707160141107403141c0040342c446145a40e43c012100040d1440f01603110640b40d10500100ca035207001146880803a80d07110010320760002e00b07944007101040020802c2d640f1010703a189040100304184105449105103000004459400b041041030344400140c5007480c40122403014603d020106107969080741e00180400d403078100c0da01d80400076050301c1c4000d94160240001440800d600100603154514088501001c0c1ba501c070503903002d2980c4102d502c99841919000c402012034040d074852034540f802071030049980c0e5190004141d031151141d02680035a0f10200081040c030010348600341c2c = true := by decide +kernel

theorem cover : BRFrame.Cov 606654676 606834532 := by
  have h0 := BRFrame.cov_init 606654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 606654676 ≤ n) (h2 : n < 606834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
