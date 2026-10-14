-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3198
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:57:11.267989+00:00
-- url     : https://prove2.me/submissions/de0f48a4-8464-4891-a179-a95f5052aad4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 575000000 ≤ n < 575179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 575001250 1250 575000000 575000011
    0x807023c030c010624030e01090b010f0302011e08011802131d13080301090b0a0302030114070f02030c0d0509120a030923090726160905010302070c0b0307020a0209 72
    0x1c0c5444500701d101c514256101900700b10b00c005000c90181d010503491080300c0914113904d140100301d03103103482002ea0042414000c0030701034803074110000c1204ca01030a075240c11640300b07076118580000740103131400f0709003080140440010344103001040000d800540c405c00800740f0510051a1441400608400b041030360320411700341c0c00c0ba003810703884800302e401c1c42a4040444000d140f03c508030f82c0e03600740691205004100c02c41303540e555018103644482030824083c541c060020410b07980d0340b07400c03108100300498400c0300280710070241c0d10b2900c0c4080155441c0039141001000f40040203002a81c958000904413078000c980d811070802001030422500030140d001c0d454034040e0600300040a960142c0340c180e82a0800200c2400e41c40945682074040d034170040d2071500c00c18144e050003c4401400101c03981d26a0003125409200d28011149a0f01c801c2d075540381c880c2c2c01016a544010342c181d0140e10300207403c491a20b40b040168803150b000442d07001d111071040c1d4900038003c0d400a9428801580e4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 575002500 1250 575001250 575001253
    0x1a12012709060b0a060c0b0403050a1101090515091605060f07060218040c030603020d0206071b06030e01180b0720011a040e030301120f15050c03040c05010807023c 72
    0x52108403810b00740c00c03001c09010249003058036401d03991648440c141c0d026100600300100003440c02d0b0554801c5800102003036010000340583c801900b4001e40d41e24300b140ba061003a100010200300e0400300000c0d00c450f01c0f40c5d241c0c203420b403092800e020801c00b9044496450105901000000c00044041c07008203401c52500010606030f0000c1c0e4103000840301102c1007c403d061034400144056543c6002c19012a6412600241d51754014605861000407e841c00501021114804107500d41c1507085010741f03080d03000003000f925180c20300b80c8000580c000d201400441001000c600c0c080d114403008103440c81009a044810418170301d139a400c60350010120401540c00711b03680c001da03142ca4022050354801d03090084d07003194107080c4122032150700b14074018600c400e0340c00c1402c00c004071800b0240790503000c0e40c020800d40c5010712182c01c550780225012200c443d200c0c1404900d640c000c45006000b040654028142d0212101d10104425035102c5082c016807092442600740c0d0f660302011032080500c0341d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 575003750 1250 575002500 575002511
    0x120105091e10050903040504090f0b0604020304030c150b031e07331710080c0405190c11030a0201060e0f01062a1401061a1201270906 59
    0x41424040d0380c41c09400d0700904412001d544403000180d460300081d150344000782d982c40320200d81e0301d1440f03107500480d006401d0180d268207204400c008941d800d405207080b003800340c2d00c5904100480c032049400601160340c80c3c01c000c0c04540c94010108550b0304032500051a0052040001d00c0e140140c2540c5408040612064110080c1801038400620000068500c100010716124280e00040028500007a106100201d201e910582406c0c68a03030302001c031014241480c44851040700400d0103120b20314403442d14420514101440b030030b071145904000910b13640f643c00c0070714400350108425000401099040c0780c2079010b020f00082c00390010a07000051154907040702500030110050841d80104c9030710300100321480d0080405e0500307241442c00301600800500e1440554180d4410242c0181e00e80050300031030301c40541c020010359992003c45543c1c695420b804442c00e208030401c60700c10001010041142030181d035000300108901c007500240c481500c003401d5003209c0707a14100b82e848903200c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 575005000 1250 575003750 575003761
    0xc0105040b0a0c0504050a05010f20060402010e031906050c12130b01210219080d1206050d020d02040b0303070f05060709050906060307080702030f04030303020d0c030b03060a0911120105 82
    0x51040391990b1055041c07140c00d1038588400038102c7c1d091442042e0610030070098107401c5a102d5a16001042a10f01400e10b180c02e5807800740ea030f50071003220304034045021002c0d419400d1400191070381d190319101c00c1c0d20700806402d0380c07050302810010305115103a03030003800b094007900360924410344030307104c949540070324004a400d0500300d840040e0300c591208003940040b50544c0314100f05110440d60140d402a00000d044180c28801c10724540c09082140288070016203042e6010030102151a09943e0510500d1340316000c0086800c50118001c1d8452440040f0b240141883d40002c64403410003002d8a0415031039445010004005690031a029001002007000c0c0300c0e0401e1081d006001d09070b40442140c50800007003481c0f0304c0007818410900444500203480d503482001200d9020480440a0f52515941e00d00603010350415000d01d0301ea507042c00b0070860541e110388074840340064010020080c5864a9000000a0048035416075030720345030b9905c11283d5140d20802942060044000088502c0d00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 575006250 1250 575005000 575005021
    0x30308060f0a0303090b0f041208030603010501060e0d031220120f04030f0e0a050a060c061d120a0203130b0415020d0e270106080709090e03031302060c0105040b 71
    0xc180c181e03445040702a5061000c2540410300741d080c0c884411246603245848240105180a650310202c911001c4401e007104108010000c1c1d805600150005d0007a40d8894400b0f03100350060340d02d840e410038411303880507020034424410f2031040130030700d00d00058498034805110a55100000206039101c0c2c0001e030b050804851407901c551010f40e001a43d4001e050650f002000ea00344c413003210081103d600046200356940420b1700000b460300804d80080700741d81d5807014080354860f20b400e440c00303850000784850000d01c20070005810803042c00030300030440410301c1c8411140c2010521208510080c008141000f015058090240415204d02d0340c07503500c5c00980351801142c00d0090003c41d0005040480c00d142c00c2142220740d60011640134090300008805d0b1070803601e1200201011680c0740c3c000050254100d20024010b07003080e0f40d68022503031240c0d18101568869900b81c10306030300400004005a80e442c40003980c13284001d180601e0135520089203030a4820950b41074481645071010f02040d681c4d07 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 575007500 1250 575006250 575006269
    0x607050d06091d210f0d33090525090801060306140903090f04022b0e1212070e04090204020c010c12150e09011d06100b0f0a200703030806 61
    0x800d044c01c01504640c20303095040c010b10036203c603002d4020401c280151310036040a5078aa5545090071644001c0031140c10a440c4400d6103080001010344004c41c07018a6070060f28840d8041c881171000301030310704c0500581c20210303250500410000c6500416120f4083c000c1900641c0948804075a040005000c40c0020001034110041a8000c01030494103480f1613090f8000203004507401604d43c00a00c10081c011407007140072168804c40480c406030004159071207102d42d060541c0441e075850f00c00898041d00c61250400703442410a0304800610041e10034000001d41440141c000b0958400950100d001c1e60020207001c0300f980d445504000a0701d80c40000d8000302001352078180402c032084496070550451038007852071000c416400080c00100d09400170303049c003610004052101070240e9a800d03250903050b51090207038104250000f9444d10340e402501c0c0f40450700414149065038891003903801500102e0311282d000e8200002840030902442404002c40c065103d1742c1d81441d10000300918044c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 575008750 1250 575007500 575007523
    0x201090608060d02130b19080d03061d0a060e04050f010f020301060c110f06070f0c050303072307030b0108030c010501170312070507050d0302040305010c020601080607050d06091d 79
    0xe260003004003e59580032600021a01901e80c2100b05030b0700300442d00641070062030180c12500c9910f141c1a1340380c004440070115811941070722124000980201d050341c007940f0a004040e40d1511501c81d200c0c00034500103400003005a800a1413903515110212203540848054807242c01804904018160078080c070710440310410000c40c076641c103040015100f914284000707400c95250f01e1a101858546c50900016004010003060300d41d01f9901c0c000b01002c4a902040320b0022110200007001d007000030a89007d240d00416400012264006146071b080d039403100c030030742481000c00010210700700e892210b0203851054055a62640e940380d8903825a00103070b005646401c2440000d80708054040146d40e0b545440880c8005180c0b03d20104403240d018040018000340646002c40302c0881d01540140b080380d00c40c4d4000c5c4903840f40240243d88612003481148116082400011055403280005184481c54000000345060310740c0c80c4203080f40e01005005500d0b001c649800880581e00300a001a01f1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 575010000 1250 575008750 575008757
    0x218100b130f090b100c03122304110102100c1209020f09070e01020111090a06030c02030f0c030a0806041a0906120303133c020409050303040501060e0109060506090906010c020a080a02010906 84
    0x41000c0d0b0703401408d40740d4003080e07294015622000002114008044490b03854201904000d041c241401e004030214080c5204501502c500050244c40d04014040c00e6403042540c0c0300c0c40200809041c043d0701400d08400c080b6072144501d41d80d2000c90750740d00d0489004040b681d88199031103441000185c215101030300c1741918440c041c03003910880d9940e92a00c2040c1c5e0810300e008a61030045400030f80c518000c1c2d91b041d00d0a1341c000701c7c0c0c024520300008080e201045440c0e5800019407100313030a22007100d035425451440c10020482c01d05d1181442040c45400020192113419002007041b003071801e40d0402d94480003980c0300080d040c801c0c484801e03107003588407441c1940d500300180000000102c03010000c0b5541340b00b1140d0007072401507645d140e0208a090342c00c24203590b628503043c80d1841c02080b080c043e1000c2031500c03600101c2c1074183d91098405580c005410b081c0f51500400c01c109049900424150410408029250050b19460840784c02440c05800a000c0d125581c400500328084a40114041 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 575011250 1250 575010000 575010017
    0x30c0206251101050c030d1d07090911040501121205130305010f0507110d0e01170109020d201611030312072601050d050a120c0218100b130f090b10 65
    0x21011701004480c2502800e440000d403181d840e22903400e40400503240c1100c6402811800125489590000d8507214840d034820281c2a0044081000301c840a00441e140e0707001c00c1006c1c0002507840605008040b08038205103003031034041842004900c0c49a0800c5034540d440343d0f004410207059028054100400b41040341d0401c07148031046688400380d4071020304000c0035030320204160740a0302541409070361541410040c1d40e110450701c006940301d03503861880c00385418034035811480701d40802034502d480c9040e214a02541080c03080300740800582c003503401802c0d5601980850323400b0402004040300e4061702c0b001c60328125030047d100c10322038000ca0501ca4402d140b0240000013608880d4191003003201c0103e8603080c05e00f0100d203050f804090080468a00c08181d9a040c3e4100c0c0800340f00385c0c82201da01100340c007401103010301d55505441d0300000c51401501480015684009881d06519100b107100d0031a50b55045103000d00c010382c3c884104d4603a03813141501d81341081c0400390600461401c0c980740 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 575012500 1250 575011250 575011267
    0xc1905010e0904060b0d060e150c0414010e0a0e1605040305071a0c0a0c080c010c0b0c03090313090c030e0c0102060403050a0909110c0601150c030c020625110105 71
    0x8600800c103000344a00c00c140d0000c3c04020295204542a0340c02030000e4407031100e05d1416500501d04d0b007140303080c103100f203c2d10782841da1039a9000c14840d134072404150703003002d04e850312001001c80141c440e1814804004040907103500e03009411402400c00c0002c0c000a41004549100305c100d095011104102c020007080c4086070002234000116040e104122121800710300c007d982078069078220a034903025402108013804a02074064050f21000d105440e49404030b000151079040409100074000e0103d00700080f01c0f820150003550717024840c40305892a00840d914580384100082e0440011580d5a42801036100c3c1d15104041c1c40300d80100040c1850178209001030741e01c002c0108010f0400400182020078548140a04001800000418004505044800350041c2c009800700181c03841081c000084005c522414201370820903103c1100c8035a040c1c9040f07e804403c100f0503a000b003c1040801d0b503100842d80e00c1090180c03035850152800c000f910780002400155001e8a040000030b214641 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 575013750 1250 575012500 575012507
    0xa0509031303080f250201030e0a05060103060e160609060201110a0c320106080f0a0b010b0a05130803090a05040b03030f0313051e0712030f0507150e0c190501 70
    0x382034a801008107901c40342c0151071442240f00700205160705c00651944407050000c41da0030410180d02c00d0f00e00f40301c41816000003940e200400c6401410700c0d440b000042020070ba40e1b40c40740200004481c152240c1d0220881d00070101400340d80b20000041c51004100320180c0d080c8100d00b0106004a001032814211803002010b00d0040036001e421103145003511440d04242c09500741000006168016078020000e501a000300300621507095076002d0032510105603500440c40400c050b9118400c001c03664201110444550003a800c6102403000421204902015060204c00102191002156940d03944010f2154488513a40124011810a203100c1010703903010081e10203290642c40388070340b43c1e540d546460071041014000078115018180b141504144a08010400517441804403105c159848000402c02030300540054005003040c0300c0440d480f8416070003006010300911030041000480e01103c8103c0e0f65a40049400342e014107050221070800144800b401280c01080e0080306d4070f8600007a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 575015000 1250 575013750 575013787
    0xc020603070e04091e26030c0a03020705010219021c050a0c0201090b0309160b0a091401021c05041703041a091507030e090c0304031e0c0b0a050a050903 67
    0x4409001d48200c02e400c09480b02c2d8000740e00b40d6000140090307042c405804880c5410100c80e03050300e2080b50000f000106100a40074082da14411022262a45e6104051041d0760b0700400f5416040503020841c7c5008940240080c0c0364400c1001c542030f4441f8140e9202a05d0a403100e0100b403e103420200e01c811440390040d003594034002030f90500c2880b80c3c120b0b00c0101d407200c2c403541000f00003000c048244803c40c0d500081a0000b021130040000c040354545042900e0750281e02a45c800046ea500f0b414000005502903800040d081070044901048040901c85080b003150b508460008402103810000048212071000030720540c08007452500307082030115040c02d07071b0b0100c000342c01c4d10000a000d003040d2600580d5508520302e07426090388030400351070010b0800d641244e55500c10305403040861000407110b81203074082c41d8140c651082051800c030030410302980d00801c1c0c0003849480b20201022500c02818144511114240020940f51588102d001c03a003002d0001d001316402480195035001064060 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 575016250 1250 575015000 575015011
    0x140d0c0501030b01050706020f09040507140405010f090b0309061f080606190b040f140111030a1215080f0601061e080a060b0c0c090606030c1b010b03060f0405010b010c020603 77
    0x803e0043c0644010384052084500040000380300040c5214014840d60183c1b071030640c1100d041c000b54035411021200e25003150700b951062202000104180d6001d000810783c500013504003100083c0d500d11b1801a10707041200c0300d802541014041051034a002c450201d27003262140411054142003e0141d603603124000c0402c1e004a09004624120700103900743c0304010409842040d40e02c41d2030f0342440c00c603884075200d032a0803085407071010000707907009403008501210480c2c01507041404580044840031401346100740e045640300d4070200c84c0304201340b10a015005042c02803c1c1454080411032800e20305901078000c000d01b400f8040d12910512241480c0c00394185056192130b00c84060f028010041c1e0f030b010508504002408108104020610b6506510119281c00c2c0c540e60346070074071000d880210f500d1300f90350701c0801c12101030300120010080f01d8159240001030040c0701d100881d281030000d41b02a681110280200001c1000c00d02443c0b507241020b184c01c01d1031075030340d9002c500c082c003003c0c1c01c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 575017500 1250 575016250 575016257
    0x1060e130f0503090405180c04090b0a09170c0c011103030903070326040f0210020d09121e03181401080f091606090f080f0307030318140304140d0c0501 67
    0x41c560600c2030800940f02e407020024001c11070781c10010008038040d480d901c003810060284d03a500c54050300d050310854101c40d40164200140e603a402c0c0d880c00084c100541c0840302d0068900111075810b100f1030240c000c1c201000010074480d0030741400504a0343c802d484140a5074010001c22050000210940c0c0885915017401001c0004130041c2c2c0c1c01c00780001c0200081994640104003d21108000a008540c02501c00792100075229400301d0b25495034089620203e008288200030380b041d02d1040241d2640a500d0040b81d032400c071095801c000c180d4000c141d0018070550b44049101500103040c2c40205003008000d0300c41101540080c0c1a01c0000b04010b08149210b40050040c1c0014041c42c440c01c8038200e15049031545034030021b07100c40342c140548030310b500d03586a000c070360f03c4000540b84d40c441d508c5e02c0055041950707a5a0031409891402c103401c015115070040d41001584840d040080180c100340a15212821f02401016446850708401d00c0f80d04501c0c020004070300481c0700c05041d0703142840c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 575018750 1250 575017500 575017523
    0x51f150b0a051b01020d0f0c17010303080702010e030d06030c0b160b13141c030b090a050901060b07060e280209040204060819050717101a0d0807030201060e13 70
    0x1005080ca800b04400400c00c00d5000045111b80c0c00c0c440e07480001500840c941c00c00541108207401c49074050581c002c02d40440ca8100180013007401100c0f0268808450720000c03603485d103c0a85a41143c214604140728a034464005004005142c0e0260000c0e1400d200e8041c1004668402c03211044481907004e81491000004642100484000e21300e601d90071440036048071006040266817203d4600701e59070b080301d40c1d60101848a2080c01760000080000f4200001030711840300e40c00041c440039219282c15940c4080c0000c52035045000750111500610340007521610804685040610b907030b80842e950448446410301d50525050300890301901a240d400a982d81c920220b801000d058220400703510495501c0100b20744191040d1003018820400c0da00643d9960596500c0b090703803c003003c0d5064001351602e0600b0075170340d400488959080d03145036644c0c0c2183c90114104601c00c41c0140c480d41000900c0e2400d140e02400b500004050740e034002c01c1d051034800044684409803c0d401440ba2020a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 575020000 1250 575018750 575018767
    0x190203070207050d1a060405010b0d051503060c030708010602010612140c090112060b03031602060a0912290907051c0c14011d030a0b0c07051f150b0a05 67
    0xc12508001d0079014040000c0d9550500302032041c0c1c001c20a801816410917070001d08241014080c040c102d81086030f206040251140e5001c000d42402051008a8280d440700c07110300e560104405805040050f0215960781080035008110280580142e015a1b0408408021007419021070303221058010342d5a803840d4401812a60030710030300c1e156055014102a0004c10015020300041c0105807042d0070812050321143d003410b40384c3c00b41e0644000401110071001c4050700f010001000440c01e207241034982c00da120944103641014001050320000ea0b804a50902c1d02c0480780d0340c0b440340349901410005841c184d5607007907544c00c0d46d0181e107010b0080d1010451a080d05030702880c0c4415032003040085940c2d142d0410150360910711a81600150f07006004980e800320b02c4840d20480c240160150016100903220080e900c00007600700000410100315020106070305201c01d48402c0b141072095400b02c0c036048505400e5820f40e061010788001e96040030018038882c00c0031030b50300b425181861030312040203 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 575021250 1250 575020000 575020003
    0xc01050318011d070f0806010905091212040b0a0b0f010f0201021308280c150905040903082a03041707020a0801060501090b0903060402040e190b01030c0e1902030702 73
    0x50001c0e10915030a01c074030b610490841c1d41d0041d4900403050100c2d6015540e51440646048007840303400e8860300640014041d1741515040b0a03841aa8901120701142110000075a20380c01045581000e40e0120184030401415080781e541244414a0501800101500040031400c00b0f14026043c0a00b003d26074248500039010746501000740510070f110f09940306205030b01c408001030502e1902451400b2480fa0705a65003000c0d00250b04001c204500f142070024602171031451010040902c40240c1d00055207903190701604540f02d120ba50380e00703424242001c0c480311aa5901480303041215020020250852140c070940360f00c5078000300d40e04075200880d1000843ca105070140a500822988400300d03422405400c450100c91081c0c2e190130300a03694100749451400360108140e4140c20180100300945020703005201c0e503104910695104110960780f075400851025012140712180c08010405c2c8069840010002d0540c0100000c6500c4c000401d004803442000401f10b004d80e012001c075100910 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 575022500 1250 575021250 575021281
    0x70b100515120f1909080301030606090e1e01150b07050c04050705091e10080906010503191103010f1503151103070c0804120c091d060703020d0e0a03050903060c03090c010503 77
    0x50001005804500d0603c003500c1e47c024003085d650103080000000302c0e61010703c20b0116403499040038049400b08203040302000c0d903442c45018000c2d074951001c9214070174000d00b001c0060290710b42c419602c10031032905a042c6131038203c2c19840b6516101c100480280c002080761780012040320a00588c001040c803155040100003642a00054620016616a5004070465008080100c100c4070540e907103d04040c2e03920062400740e04800ba501c42c240f40010f4201075940207010740100003044d0000074104510484651040303e011200404a0410074014210b14000e8100183c8109000c445c0081c0f201203407a2002520000402821003034960600040345c0c1920f020b8031440301e482d0003842c06800c1600b0a0f040f2030103038401951810140320541b034040c03484502c600100300082d08c0c542d91000000c1e00250031500c203502c0c806460384683c0000c041d00380a440480e5110740c48807500c40d0703292424940380403002450100104000c1041c8042c0d0b4000245401601000340703031071592a5520000c1c6a00101c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 575023750 1250 575022500 575022541
    0x50a0512030c030d09230307030503091504061a04050c0304020d02010c06150e010e070c080c1e1b0d0f02060a0c020603160e0d0b010b0f070b100515120f 67
    0x8144100c400c138864002a07000c5000d801640c5080000880c446e61107142c0b0b00301c420346680208219400640a60042d5a001d01d5a409031680c031100689042c0400e2000c4400f2038100d95a4401c034a8200c0f800c5480c2c0c01d0500080c1c4040165140c14092403440d484064000ba00c1200101c92407421a0700ca0440f0854281d4400d030203100c82c1c1100680c0c4010303185980514206542d42a0000c600e254004036998412070b42c03039440b000c21100a840d40da92681c4071000190f00c81c012181c0200d0b0f46c012a21000b100c400c400340040180002180c41585a410421521446445192207200c040340714160b14451058041340d245035a0803a0880c142d4103045d1080e002500900c0120170003440400c540da070700d03402c0c42850305c030900300751207040030800e4030a990340008010074620b03001070088003442c0014084000121086615220341901c0d8501810001c030740500c12000200014069814650001c222010b00c0c01c080c1c034282400c002c444014103800610022149000c1c00c00100d141c00d100f500d556060 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 575025000 1250 575023750 575023753
    0x60304080714070308030a05070e010f0c05010b0d05160b03010302101b020a080604020a08010209010c03180504110d0608070b0a0c2a0515070c03080310210203010c09050a0512030c 79
    0x130342d00d180c18805500200d8034401441d2515001502080c0178425401076010160b403244540443d20b0000d81380305030f03800c4003a6029907030b42c1c0341c6120b5a20350012040070f00e0300400013000e034802400300394040c005183d0040b07030190320240010001070f11385004203000000141002c64a50001300510301444010000c0030b075000c4407160000411a8010810302d015600030b644c419406910741031518241d1042812a5002032a40301c440300c0440c1c0305512611ba1075907040b1112104c981c1c0c4500080a40b6080040100c01400c0011001c5425042d8410040148080c0000d0030a035447c101102d40240184070005050101e600c3c841c00402c25030603c08072400030011124240341049020031440040c0c24004c190050580d81c0c001b0700070841150903142c04943c0203003108031440c25a0355082e5a604082c0840815000320040881c0302c0d8005c070100c02109501c1c0c10080400100b0340105429504004000000d004a01d001070080303495061070041514000d5a620004400c0d016107a4914420801c0c00341c100d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 575026250 1250 575025000 575025013
    0x6010b22031a07090303050306062a161d010b09220204090f05190c1707030c08011706060105090a0801110409060503030a080a0b0a120c06021b060304080714 69
    0x108801e81046210b42091003030300c1180c1c2d640b19031055507980e14178040a00410b5061000640328600080240102000b20071080441d140005600358440103211500b60684c000511080c1092101c01000c5e0040080205130501185500c1d405200c13200103000e00f20000f800040c550810b40c0b10812845042c500d043c000c10740e00c2c0d20609210000b50424050945024180800c982d00100c403801103c1c0107129201c455400c6c0000114194001e00c03000803218181712001705611030310b001c103856042c420902d50705c02151820910b9001080d0300016000581c1d920f1041154403e002c0e80042d40d81d5201c10203082041e0b440b400a0700180d0030840030f42c07207010950f0070000c641140444440180c000c07102544024032100e0b0715041015242c0c028813645000198010740090803040041e00158202d41020b400f040c900764440b040c1501e990041c06080d10a07074034050003088402e40c10020550300070541c84104400e00c0c4c030207000411600c405840901006400b04101040c000103407444801c6165034004c0341d65 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 575027500 1250 575026250 575026253
    0x904110103360b0105011d060a140708040302130905031206010207090606032a080c03041a04050303180c151c1b031b0903020d060e030d0e0c040e06010b2203 69
    0x107110092200031120f040c650800080c0f294007525213810741e0b496502103075040e0301414091001c035401c1860007204100e2400356144d02100000010200b4034020600d031580d9504600621840c80c01c880703410443e00389401d61103400b11300044141d1306501400c1e0b14590481d100c4000403494010590000c1840c01c0c90074800003101609a441004920382035201c0c0341c502d880c103910202004500860090120fa0640700144606904000031a481846030402c0140360601c03803201041014200e508a590380d01c00018031490482d00d0b1408401c01c00c140700140200ca142c07001003400280d10742000c050080300440c00726041f5064640410381d00c40d685a0400c00700310f005003081d5400a4005806002c64235040044104183c0800305030905c00007619002040c501c0d550074030000e000042429992160f650814a03100038080c8014064144031075408501e4246a400c0d4504240d41400a14400c80c5011050035001e980803502504407502c2c0018141c6880580208085001103071000e02c0048104860100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 575028750 1250 575027500 575027591
    0xb1608190b030d17011d0f09030408030406080702060f0103080d0f02190306060f05030708130510240807030b0c1617070c09140c090a05090c04140904110103 69
    0xc0d080505040003151b41c1c0c5201034140781e0b0f42d026070074140c0c078070910000300407200e0114140d40002e8800c04072031509664124041c11a0003a0300900000740c0310f0018805147e604200d11508070382d01e07018040040d4514bda40310f80c0781c8100d0303031170a0145440c0c00d1030515080c1a035040c3c2d050141d521826214070a0101001001891072f80101c5011440e0010300802c10303485042a2441411107440744030483d2140c020100d03040d00c40c190300302c41c0c5118030018110301480c0790140343d00380e01c1c0010405100500803d020031070b015140c0c0000d10700c2d501411003003000c2210b00210350742040c24400e0060350344801c0d01c1402c40c1c4040c442800303003003410f80d1801e00101e1000c42e40203002c021300500500c041c05868022040984984c100700450000b05500400e6042a00500509100d080100340d1802c3c00e59510115031200742c115901c1c2241100410f040000300f042c0b0101e8100c04104903500c64003032030655600600400c80e160303214105561141d981d40491400701d01383d240c170307010710700e10402081c0b0314141764 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 575030000 1250 575028750 575028767
    0xc0507060603050105160519031107050a0c05031b0319080708042c04022107080106060804110312070609080904020c01020a030e160302130f11070b1608190b030d 71
    0x6503201c0c0c1b14020030007038134031030000c0d203c050551840220034501c00250480c007404c0d031401c01c0c4046c100104026000284e0401071032b01c00911800b4071040052074807003050301348082d00002c405140c2250340342d11146e640200e03003145514116a654000301c186800d281e141401039a00042000d400003a0110703a00e00c1d40c0c80426402d5883da100400c5c1e64401d440c000c0c102e82d0381078400035044011180c2446803079841062040d560141c13802203502c3d49948180482c00d6941c144d01c41d6012904060030701080c4013002c0c032156401e41c02500200804044003054a89070b1180344400750159541d0400c0e0b404011031002240d00303808009006544416411072224002d6104811540200789003904603400309002250b80c0d01c02d408200b11811103d880e580911000c0b40802c6016041290307a002080b40250b01e5204021510145c101d40d40e03101c4000b4038101803c42c0002d4512412940d8000c4d80c0c9817000c0d8440d500640c800407400d049a018403115091201500c0c50101c510b078180100c4004c16007866028016 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 575031250 1250 575030000 575030011
    0x60e04050610120b190501091a0303070305040e070909050a0c1106060112020f0c0a0b011d0f040809010e131b0903050a0305130b0705031c0b030a060c0507060603050105 74
    0x90780c540c0e842c0d500000c1070144151244205207110076400a0115400500b02c56000400b2601c4800c1e8900c400407940403140700340c10031200c0076614103606903001074014804001081c154001c62401d0381c95103014202d03000c1d500c5951144e04c1c0282c00520154814440030b0000c0401180500c694244a41d411024000d003032030907000104594070702240004002480c40c080c00c010703120760303541a20390a00310b0007961050143d1840b8900070449000800760030402250a20f006800d0724280394100b1a010840440c0342c091403070040c3c240c609010a40b03081740d12085d00706034407800003560380d011600169030400303088440c00d501406c120144004601140c00c00c007082c40840c1c031810f007181d1900300152258005400080c00755404403200740006802540101f0041035012000000c46942d1107402074684c0c401601250250404903895000d4454000c00055480b172444082c84425504d9010903580c40d40000302520b200c0d200c0c0070191043d4090b1040300c903c542c000c101030121036164244075010b003405551 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 575032500 1250 575031250 575031253
    0x11071716110108070302271210060603110309151801050f060a3606080d0519080415091112030c070e01240306050418020405010e07141309060e0405 65
    0x5284c141c460300c00c480b4000c5461511035150034082d2010700c3c00c640180f81d4650407184100d294940c200341046078448400c2e00d84000704100c2d0030044001c007640c8020103910102c820600034816000300100e09000d4a040800e083d409a65819010340942008241881400d500c0c1600707000d0741d425071015080c89000d05503100307900d070303a41c030368032010900380c0c074000c50184d122038607046140d040009060029420ad00d0001040b07181c0c941e5042401c0c1501d5501440109100003400442d0220084081e00d284480e400c2103061807034681c54500d0348006044003016a03a0361408002c081190000100c8890007001e494070030f0700d01503081c2090b50303070340003400b0f0140300c1c0315107040011414210a0014162040b40c1420310701c0d040c4110070782e05803001110a52040c141c5601003c100d030b0301c842c8a40441c00c80080401c0c00042e045005100c21183c042e00501b0000c4100c20400000582203071854002c0d01f40d02d20303860b07641c10b6042007650302c80e0b5445e040010504e050490020b200e9000c1c44509008500400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 575033750 1250 575032500 575032517
    0x3030f020c0105130b0915030c1c0903050327060c090103050109051510050d0f0518010501050f0f0111070b07050d031506030b01030b180a060603110717161101 70
    0x401591140904501e0340d1420307008813403c1c041104c10201500c3e9150000c1c0c09245ea81c00e141400c40881d810454000a040b9804106190b1924010350348023130074a000f070380402469100d0388006102c1c0c4002480000111014030140300ca902d00e03c01034402c0d242ca0081581c0088c140300c0030301c4c0002e43c0406e6006001a0030f000020407071021520a103406100c0050034064500122000d00016044402c0058240401032003610281ca01c2409014960600c0080000e12480c01d0b030900100c14071507200081e001c1e031501005220b1030f114403200c07680e0748804454001d14003042400480d003d8142800b01017080c0220031000400000700d00c040c00c54144190140d820380740d00305c48118101d592403a000c58100200950401c85940698080c0b03144110601d400b050320b01001c404280521915516041c00c58042001c0005c0d150307541c45014054015032809120080d0441c444000d039001d9007001400302c3d802c10518424500c1118111121485180c1e40c01c483c0c403186007082c1425000d060303c0d0a002c03580340b1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 575035000 1250 575033750 575033773
    0x3120e060f0114060415021e030903210912010b0a0515040b0d061e030b150a051306120f020a050a060c0605070318051c03020918090a060603030f02 65
    0x1245a600c25581d0800c1c8540eaa80303401e48091403144940141c540040d001c100100d120440c125600c2128242900148490841c54101c40301d0281c82506d0104c170754006001c010103940e004141c0b02d054100070615440144030f00201003030a0b02c43c0c1c0f403000d94000e03440d0001c0301207840f064001700410541226002c40e80b955070420311181174101101040315560401003880945429000f9250100f50300000040154684100c110b2094418400442005005a0810402c061500c80316401140340c210001d082c5861004181c54551502030681320720241200508540390681c07003140200800c1445a4901c0c2c2a07080c034900c041da0070041039006010084001c038017401c08801801c101c89880d40c03030f1024046603464203c020400908003c0406031182041c034880901c680d41c6504143c09880035081c80484481035018a2208010304400d150062201c070040355602c8045450202e001141b00b05030340c0e24031030954102800c00304014141e51078200d000c000d02d0780c098181a06841310790212a15514034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 575036250 1250 575035000 575035003
    0x909070506030112030c17090901241211070f050d1b030f020715090810050c0f1309050a0606020d110c010c1704030503090306130f032a03120e 63
    0x503014250308818100010004204920304d084c84450007840e03ca00104599035507a81c0030010444003480855011400e02d002c1c0c40d00c16089401454801d00f645002a142003c0b0f410000da104450024012403100c0c5024140198010500912440c400c4a659900b40e160092841c00b100100703445034490300c2c0f941150b00303025006101c8100c1c0b10700151540ca8180703640440301070406290b400c2c118050346100080a1580c12110980341c400350f00c03031036045424000000d00d0551510203d490300381c141011f000011541408031403000403602c3e007042c4e85009d02c14000c0e440754201e40c440300000b45040d040190713152242c1d0100d0b0076607071300d603003610802001d400040b030700200c16114980c00c1e90418441c2c400690b0280c0300f801c0c2e0f480d1080600750110384030014580003030303040340d802076490350000079101015240070f20010f41d100300149005400301303a564982404910100e640101440410010413004c520500200710030050044060165110203180003490b00800180c1202c81d01c2c20143d610700d40110 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 575037500 1250 575036250 575036263
    0x905010602062d07020d0210090b0109020f0c0a061d010212010b16020301020c0a020f0a0312080a0609090f02041802090c09181e0106030608030a11070b070f020909 72
    0x4140c1c010700c00c80d2120041468040d405901e60541010081010402600001e41d0a8824090b64024060100410001a0810814490300c1e01c02c1403034804681d00081002c0300c001d0540d003001d80b005840790f61030410201c0c1440380c10403640762072041911540c10820203070881c0b04450005820254080b440e102801d090b401004120709030120004010701c010000c0d04003800884001d01c000720340c02ca4080c0c001c01d0890b4071130701100b08590061003008096040640c0700394a1440140c8030760103c18036585444032000c2062101d0000c000d00c0b400070401d800c1d2103420400151101d19800c104640b034621f0000da001c07044200c02c0b40100d0810405024480c6040d980c16103541c0c001d030402c0d80c6503540d046903d08550000e03500d00e901140781408042d100b15080e60040c4940070280940541603a5014030b11541c100580c0442e0070981000d0302804801804401d9500c88491410304004189252311044d0a15800f03801400c0802000b14028082c48001c0010007649070007a50340701015211000c4041e10f650 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 575038750 1250 575037500 575037509
    0xb09150105011b030e0a0902030114032103090a02150a140f040512460c054501050a0303020c01120b03010f021809010305071401091a13090501 63
    0x601c0030f0a50201c4074000e482d6407480520034a012a180600e840002d07906001d59001000c6e41d0381e004c0014482001d0300e010100ca0104220003c10446681d8030f07013540d01041f8002c11420300f06020010403a148400c0094000c0940c3c002c007010103c5603603882d0b000c0f0580080d800200040c0d07012110f85400c008202c21031345032080c01d04009203050b0900c018402c08401c440d0243c1d04134814224098481d24052560307514001c1200c01200c07100220024078400e0f22981218401c600302c08000d44c0d400148908a8442100c1085d51800001c600c0041c0c01c5249271003503102d0016202c805a08001b03414801e0103100703d8108283c0f58104a662108280b100660342d500004015901c201c100030078541c010021042e14050305600494194054004682950080981441166000315641c403245207510714406540600341d80c1d12070b0030b6142da15030a64a20140c071480a1a4444590140e80340c0d1040d4200310180010102415110380f0403000301c0901c1d8492940340070b4141101e0303c04602c0d540c080c00740c035040341c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 575040000 1250 575038750 575038757
    0x40b0f04031e0215070201021309060b0910022505120f03031506071a061c050d0e010314100e06150a051308010e010606110d020a06020903190b0915010501 68
    0x81d06036035080b10180d0400800034294421000714007146164202c01510440041e030001d03865000c41c1001d1851100d058100d0030a45080160a0001c43d20080690391650021140c1d18841010030f03001341c0c2031103800d1a4246020001c0740c02040c03910050038422080750003c0d42e4610070950402d50030f85c0c1321a003201120324550410808503d00462264520050b1580241403520342007481c0d170340840f4105003182d000b42400f041c404100c030514000075440e4142080c00110716008089665480e11545c480c0c145505000d81c4c00398510182c1d10030ba00c00100401588100c811a04101d46e908840d0300315485654564000e22001400c0740c00c0060304903007a0590fa001c0b0908002d500d440a80d1650805460b0031400c083c10400014460f400740660005190707241e0000034141e0a200f0300900c42103001c18524140e60150b4110356003683c0c0001e8510406801900068907035462100007030a0102102d090700580310207582401c248002802202d02600c03105007202d940260b00c5180110040c401d10445021 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 575041250 1250 575040000 575040017
    0xf070c081e0307060f0b090709060305010603110901180f08011a060924090d030e0a090c170a0b030109031d01020109031b06090501050901020d060e04050a031b0503030f040b0f0403 79
    0x42d15a410504d60034591180211b683c20320070010800351041100c0650009100c0780042003c0c682621400d4054a1a03140c180302c1c11045407002102803007500f041724104803031007180c007040020300d20002c0080c02c0c2081581003420703902d0286502030001d03592411003aa00c10309200001e440e01d2402c5030500305010b81070100a04060214451012044842d205003400800c0390403495502c40a440444905c41e86481e100e0030111802e020100600e50042c8220b5441c1030f1420310056008020480401c0703000821034140d5131000c1910004c0c1500f12025501503003000c502208040c0c221603407150081d140c83c00a003040070305e800124207071850404e01a012940e92802120300703042a900d5802c4030707400740c0c5020503103403225036855007150011101031100740d50208070310ba00c51480340a5000100600c010440d081c9c1070685903d40c0707446003d100103040c880e03000303010300c40120682030360f20182e601b110569490340b4080301d00780c00c15041100c0450f50b44140c00002014007a44c00c84444c0a903030582e0300d0b42d92 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 575042500 1250 575041250 575041253
    0x2a170601120b150303030705031e0105130b031c081b18060304080c0a06061404091104020705071802091f081803070b041b0e090c0f01050f070c081e0307 67
    0xc5840007516026903c3c9110840741e041e61001c0004601405d141d07550035940c0e03e0321104444045070900d41d040303070700b08005e001040a42e40710181a42001200310b0700164240584000920341100c5085604104a0006000c4142500445054031405c80900c401d19040c0555204488901c1844103413143c0800c203040c11601400c020020315441031140c1d0b000c030302d840c0c141c82c0b495103480e20380756040341e03881d403906000d02c0040f050203603c0c041c56038155414000424640d44441d404031b081001d6500455020809078103220f020003c0324014400b6801f00c25030054410042d4000e580000901409016540d001c0701c05140510148203603c00140d8880d14292a40d0000c2d60f81d4010170052040399200c01d100840100354200c00c02801140300e20344040c12400d041010000010302941b0507111480880c0821a04810124941c280020708641e4044003120510059900d8040c54001011101c00414980b0411040e05005001e580c21103048a410000e000c540581880440c907000c04560801c4c400c600 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 575043750 1250 575042500 575042513
    0x6010203040821091801080708012703050f070510050117060420040e0705040b04061203080903120a0c0228020114040b16030e030c01090e042a17060112 67
    0x5551241070b4650b50b28000501300040c600d120f82d442d0406006900900401405004002010003008400002c0c421a84075244004064003030401c07092140d03031400d40c6071007050703c02e50486400280c0d10500913115280c60500e20b03a280b1500c812480039601d0f043c00868080d228195004100e0200001414142d94555407141c0503020514144041c00c03401d40d092946d40c0d070314000d051020a000005000d404d09e0041008181c61241c6c1c8014050703403400303500b0300880c2042084881515050b003800c203803603100c40c00450324610401400301441d8140e1003e10050080d00d400115180240e50b003103074070740c0304c07035021080d00400340200203400309000104260044d4010034000b4251900d407a843d905007555042300707144552107460f42c0b0302000d107000408802c040e000100400c0441d070503001000440d500c040081c1c820903a03401100c446580f90300000c2c0420031100a0400000f80d01e074020902000c1210580541501c640600d0042485902e0710201c292000621075040b174801c80c0304121301c203881d0340380d04 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 575045000 1250 575043750 575043793
    0x5250e1602070f080f070b090303030105010804152c160611070b03070507020a0803030702060f0c09030a050309132703170c09040506060307080a0c02011e0c08060102030408 76
    0x80e003580640400020480844a0400b000b0700c03035200607004603d035074405c0c0340c10415160040c00083e5001c0c0031a20050710000b00760381c15184203082207905a01d4600748080c0d2088001c0e540f20340182414404051f40d103101070844000d10010500d05042810304180903140d0022100205401070714080800800e84507003020140201032070181c810b010740780c56000c487d503401100c2c1e5001080d000248003046080c28205d02d03004042c01d001650071814500c0f0020740310500a001c0e01112007219020a0000c7d50407005c54020001c01010ad034074403000740c50100e07242d40110380042c3c800d251452000702844d0840c019026805004042000c0f44c0300907082003000b11036014001d45c100006a0120381031441c0b0500c45c0d17400b442400040035105e10004003000b0540c1c40041060b4000c000520a001d245d94200210a0300464414804950030140c3e81e400c9004100c0803c4981030504121030954041040307038002d2002100550350f00070703550341c0c0c1c4005982d68442d900c241070840e40000e001008208051070039 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 575046250 1250 575045000 575045041
    0xf0604080601140906061206040b1c140c0604050a290a030203010f1203050d09290910050601080a1515050c06090c0a0e0a140405250e 59
    0x405061684a040451812000743c22441ca0581442c1d030800d154035241403070701e503c0f0400700c603c10300d0441c0c52025583c0981c0060101e030b0046071034020343c8aa07a075801071141c201c140c5514080305045141d0030000d41c0750340c404000e0340140c060030741c041d8003d09007081168192000609400d80e224900b81202c180500000c034003c040325a058915080c04485034010210300f02c0568003d0780300c1d414a820000350a81a5010000809015520200113a0003030140d80c850a125100000d001d480c600f4408070400c260100c180b921804120031040303801504003402d0194000070101c0303055980b80041c2d6422181c00313a805501045000000404120039500f2140d40c140420f441e0003160703656814004044031300040d0748400310304003240034001c0320070801c0401d91120381e49000780070b5010804003280a031100d0303000748420682c0240019840d66816004000410f00040d0441442e141ca81001034640d0841000c1e01004110720715405286038800261006179607500399240e8035600ca0110b8111a032201243c07 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 575047500 1250 575046250 575046259
    0x109080318030a0602040e04170301140d060f06080a0c0509091c02010207050607120e0105100b0d2705070b030f07030e0c030d0809010c050c0309060915030408040504110a0e0f 77
    0xb21100004d040c2d0001d00000c010180540c6c1d400d09007883c0508031f04003c0381c50030002c24800d0004000140380c2482e07407458590309841c03000307410b08c503414840041e00e4a9000000158100800024050000500c2104407400703050500b040b41d4603102044481102640d40340c078203a02924034040710340107031100a00718540074000107160100503582c05082c03900803a0b00d103001c0b0f00046249041c0043c280680541b213140b52008003c00e21307040b92003d05920b4940140d800081d0080360802d000d51407580300700e0301e400c3c1466040c1c030241c40785280d2003010040b000d012140360240303550025460502c0401d5074010400c1d0148840c1a998156085000341701404200350b242c440c030a00007030261810b0143c3c4005550541d038804907450014105425507000002807010400104060000a40048250380b0b402804070303086561a01100d000403180c01c800c92504054000010a010400603807100400480790203480034803030300911124448084c0104840040420151141001e440c41d0060081241101c02003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 575048750 1250 575047500 575047513
    0x10090803041418040803070809160303050a090b13030c061b060203040f0b07020c01030621150e120d110304030c0b0c1611120c0315101d0a0b010908031803 68
    0x928010f101ca5040d601550164800401d010b1303140e03402450b1a82c40249400100910140d182c0d280003144e0039480042d042000218224010620904d40d510003080800701d181d403601608022624251194801180d070403108100005a590140c1d981a40100e004522000302c00255161107010394402042150440b45841490f800241e0b8142261300540083d030082412a85003400074088900a030000859007514411804c0045030001943c0011513010101d5000410101b4110001d0003541c0c21405060007040c1c1c5410364540c25801a007201500b074401407207070385489085800c3d0361109a0300500055645400840400d80002403650060081c015081c50800b00740c107010414a0041c0741203580004400d17071041706251400400310f5100d01900034210360602000069030390685011a1030b2110000000504482c082d00b2030304005081d001388161300c600d80c40305540c4282c44101e03050804146043e41801d803a502c40d00840090301c07045001103281800d8440303003000032160504916818461031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 575050000 1250 575048750 575048779
    0x14180c040903180e0115050904020910050c1b1f0e190e22030c05010615050418110d0b0a05040e060105120a05060f1e010e06100908030414 61
    0x2803081c0c1101e1402541c500d641d80c0c04590000f24404055480030701e0010002d001440440200f07240070785440721904060796520440f001241c041d0103140e6a440d80440e5140504241580000c020012104000141c40c5035041510b01c24a601d40c44204e210341245599504400385030707158220180d032031042d0600c2d01c0780624080c001044141901c04545400540060400803030303480342c2d0000c1d005042e402010b40180c0f00d24400f1030030f203a81220b01030b080081c4200d030b82c414001e003944000b000e80b21089000001d883c0d5080040c00301d42c40b6200b40e0304004084090921b075406a0300c05c4035010640354020318038140880d502c0201500300e101d14950301029640b000202a0344901c130310728441c195403000d80010343c9490100040b161140b46054825000f4003444070000c2e50100302180e0001ca4900011a1500c807401854000c030b07034854050841001e40d40020480c4a01c0e0080030b80b08600440ea80030b6030300130750801180c0301c036464490806503a1040c007051103000190f2402c241d4008001d0401303208074109 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 575051250 1250 575050000 575050009
    0x403050d110c0f07080c0f0a091a09070215063001140603060709030b0403030f0504060524210c03030d02130e091b061908100914180c 59
    0x2900204503401c400041c55000400052002804100c4001c0107000018540303c00d1548619004140c0e51141c140c1c0311900307180d0750301d1800c0240274000c03410082040c00c6654208184c003003c0000a00e00c078001340000250018070000d100e81040f410300c8466800c07515491305100301115418440f000e84070f09507030007000055045050604640e4180008100030043c004980c3c0c0006c0c01406140c0241c0003032007040405a080080b080417a6405200d01c00c555403141000c030004c055102d80f181e2401d00f040180401e1140c070341c0142d8080c407040b2220510a60340c510640001503030400301d40e0b42290344e03503101068012100c00c81c80c12501e440b00c1a103084d108600000f0f41154071400b03000111580c0402d81c01040520714a8500150030300744100c000609044204aa89124210308401c20010403450391400e52540400c0e07410310800c1c0400c58000a50b009400b82205030110b503408100c00076001c0000d040042400743c14201c6c030003d1140d4405440350000002c100101d03220351501403181401c2d0718043d40340e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 575052500 1250 575051250 575051261
    0x1b050a0309021f0233071110091a07080610030f0b03151b0304150f110310080f031612020f060705090306070e031b0414090319020d170403050d 63
    0x43d07981c068680c80c4001000103245c0385a00c04c41401e5003030005a1142038204003994643c10008608154441d11321a1000c2403911101112040c800d41c00e055202d0b003044450108a503003800064100da22554486000321020101222040e507c0824540b25880b283d029502604c0618491080405c601c86017a000c2454030408194582c071381c05801c000c102c003a0a4801603085400031003050545541080c0c0c0325a0000c954109400c0d0341305648644c815034218260344016600e405c1c600041b6140d00c0c007a18107a51140c1903100b06040e90080c0781c000803035142c0200031107210a0b401e030781e0135407003030100d032200c0001d002c0031110744042d0f10a00d40c1600150380100107003031040310b040d6180c0e5541d60300c01003414100742020b00424284901e0905044680d5000b061821046043c00404075803580c90304002400303070040308054070403142400188602030740003000424a4454204003054150304200d0101da6410b9550302c0500080c101d10b4000141c00080300c6040d030000d00a280481c02d01c0b150805450840341d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 575053750 1250 575052500 575052559
    0x140118090c1d092409030d0609020a02010b040603150c02030c030325020609060c0307031d060609100317031554060d0b04030c02041b050a030902 64
    0xc0541001d090b001280301070103544107940801601c4d10305141d4040840c00001c007000075004030341000008a00010410907205c1068035050184012a0740c2e2244000a520413030714200194202451010103042500503a400c40e9070011000640d0080410700030b004181090310482180410440800c0112041019600030324108042b130348100030300500748603a81d090040c1c800554000b441004500380020408a5110080c000c08d01c0e034903603441300c0c2100140b09a00d000001d1a8034030800000701078001070020300c2800266040c2d21140c45043c21580d002c07140b844010030082040d514401c00ae040d010145800c0740104035100c5843c01c0303a40000b03906440f01602201c41d031804c41001015106500c96030440d49070448034071003580d048104000848211100c403294041e800c040801c0098441e12119800c0d29005010000181402c0c42c000702200b81c4442c0503841641466540c1811250f001e45c01703002008da5484152500280f1700003500604048078069a01001c40004d00c0d2811480c44040345192 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 575055000 1250 575053750 575053769
    0x4021803070e0619081504291e1b070c0b1206010e04020313060b03070911121e01050103050a06030b07020a020306090303092e0f1a04140118090c 64
    0x185001018484d0b0000c20303d1100b03001ca0090002004a10400704103085410355030038542909944034100f000004402d800e49250101ca802d41490303005160f40314403401840300400c4a1010803182500f032410b20010b43da0000440c001c0400e0044040c03060000309084d0b88030f16841c60380150340350354914040c0c10260002924450034000c0201641c2c1c004140c0c1e45d40d600c00c0300c0450542c204140c00c3c2400d04e030803a0b0010809680c4202e46201030b9410411080100134103c8148030170864003e10840c2d40d0051502c060420828902184140380c0210b6440c155580840800300641e180400440c003030078004d02916141f0b56601001710101d0300daa1100d610480140d0010400c0030424810f0501e4060014000c40c02c0f60000e10030f10140040c00315900a00b0024180e20b0854015006204601c600b02104481c0300c2c9441d151075244194015040a1b8020066840940d408124003040c0700950b150800d9800307420030307100300500410032a4506a00813456800001031460540d9540340c402102507008036541 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 575056250 1250 575055000 575055029
    0x1803040e281d1f0e1015030b0702030c0d030f02280e090112061112100f05220c03150b030124050301231c051e03090402180307 56
    0x308440421040c0035140300300010268482e8104503e1658110140da6009150300c0d0340200c55000401c1141c265101c005034010090b582060040c601c843d42d50f440200d41c00940f03200094522070006c419901e5010b48800640000d070142030044000f0042031071a0f543d4542d003804070006007021400484082c46000a0800a0805510003c0c1200c505084c401e44650134600060000c131030302600b10b41c2c500b40e00440109030100f17418041c41480c01020030b036010110380300081203400140e00b8010003c0740c0c1602c80405849840310244009030f0803400c00301071032101416070041d68189952100d618607259140008148a001030b0080c03001c445035024580300e2801000522900440310b100e03018000703228a17000b0044500d0040644039010500c910600782040c0445214540080c280100c4204d6006101220001d10b480c043c510300b000319041940c0d18850440c0c2d02a241050744a00e59034407085c24029801c000025040101030340c4070751100b81c8858142d03248540e0a40b01046903402419161403601003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 575057500 1250 575056250 575056271
    0x170a05180a06060f0515040306020a0e120a1a0702060f070e040906020c07080c030a0f06110d020a030507181205210a23040311030f030a030b091803040e28 68
    0xa24601174008901c201c0510040a040c5034646c82200c0c01c40754850310240e2990a03c03d4181d40c07501504119681103100d8101c100288003010440030440b6100d81540d04000182c00340f0580d1a010480700c40c000341e8031140220302d440c00d07107900341136204102c1d1505017150b0003143c01003800d035045480104c411076000b0804845c816410300151000d4a03000d00103102171000b5200003540e5000002000c0d00864074400035030309002e810342040705030b0f448002005542c1d410b40f40c0d110000754000d00f00480064030f400c000c200020300c29044010303d40c200784e9440c03490324280300005c4014400140101c03028440c103507a50003281000300d0040c4000110700c0d6240d44403840ca600241800c5607905644a50482c401c401009103442e00c001d84042d641c00404101040407540042031030301c8203455020000c2e120100b102100d03154182c201070070030841900e500341d054032b0700c21a07220100d580003680103554205110a22507403103a041115405208070f20001141d2411408040c200f4800d844121951510340340c0c401d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 575058750 1250 575057500 575057519
    0x1201020d0b0613150309020a0b0306100816050a0201140709030203160312112506030f06030c1a2107140901022802060318070501170a05180a0606 64
    0x407511142a16041d103811500e66140703000680710f001e540603c0c070095003000240c5110780d024034003080d40070340101125a00c0301c1c80068a5082120f5492143d101c440781010f443d8400c0c00d20324050b4803a4a0b0840c005078500782c0035152078000c001c2c038504541d80c0305802c05203c501d1604c814041c6040340c48100c101c0d0f04500506080001041424540780780b00c40d0101300185004000d00403105051a00e10101401d41c0341084c00c1c1410f941c0c04d05120001c1891042c40722504800e06001c03200a901c00300b003c20151001079054401c00d11001c0c0004100c80d104200150040315146001068801c0e50392800440c0741c00000c03030502d4066100a4021220200030702241c120781d084036600c4460508a0600640c400000d56a03480610f040c040200700030303101030303096500341c40440b03402c0e42c02410143c4030f1424540425031055500c42c401d1880c0b051400008055018001c040c0d400c5008031140c3c2225030750158031401078080907003524600b0b43c25045001d0920f40038000400070038403542e00880c03507500c2c000940 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 575060000 1250 575058750 575058761
    0x10509040614100f0912031b0b0a0506011106042a0801060312033c0f0515010c03080103030c021903050109150509030715110c150a20070c03021201020d 67
    0x5828455101382c6034001c5600842d0100807200758640702d00307a8011610302190802e100002455035068465024000c020396202d60510500b000d5004010302e5039401c00444046144a85620710b0340c102c90042008951500f10502c818544454130b035149401c01200c1c417107658401e42c030126440e5034410301402044040f07080c0e001000000c0c0f03020310090054144034002e50320b10210100400202840301b1603144402d085022002d40c820301c0801072030100d02c1e00e800c042c00301103540035042c1031408040d950390743c0128a510015601a80c40c1c0001da030850740d051319840040399042c6da000e1304071b46120040d6004143c828024612803000411440301d545022610500590210064142040700b0420612000010360708030a0708140d6070340c9804503080480c0c004040100d880328003c80b00080c240301c03480c00095041035180c28640d440c401ea550b80c84610702201d88055031007100d40c620642a4240840160241000a01514a00411681e25400a140c464424a041500ba500414500e03c00003d80c07088 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 575061250 1250 575060000 575060029
    0xa030210020f03070f0e0301020a020a02090903030106091208090a090906051308090105070f0506130b0a02031003030e011206030b1803090d03030504140a08040905090a030c0201030b010509040614 86
    0xd5080c09400b0800e14428040104441d08104500991078503840c0310b41030386407034200050000c540e03940c202000252281118101640103641c8400481c0c40c0032000070031070b1b0407550655900300328642402040844410380e0030007500e15060074844807400c3c0d03640b440781d00002c1a900c2d800040c0302004d49882401e45600910101080a5a000b2800491119811108851424078010b0f9690032240340c081c940c000c12a002900e180b01c2c2400304420009007010401d41035014511540e200da451500d81d405030702c0110340301c0d2222140740e401000028001c0316215100300c01418114001202c26030340c0011141b00c0d50058824068010a1007000a00070681401e8400804061480c280c0121301040000f00d8060000f01010f90398400601880311405105c1c0c1031600d07040a071422a822402d000380c444d0842d024400340780745030030082100312400007500d04107107606444001029100da001074004140c060381c0355051110820101c8940d41d61482a1009450050060b0540e09120000c0c0b20281112004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 575062500 1250 575061250 575061283
    0x61812021c020d021f290102150106090b0306040914300405130b03070b0a02010605010908100f020904090c0e06030312040609030e04050c21100314010605030a050a0302 74
    0xa01d810f1640403a000c0e03080c1c1800803050f024070100e880000700804204050004082c50500728040304c1d00e000880b01e0346c14100768215600038810f0840d40c2e10b0ba90081c407c680100b00e00b030300e0420070544220301a55011200a100061180301031311a110ba5006080d608441d64100d2440c842e02003550458011800d40110455100300c6000c43d1000301700d20440c02600c1c0704810114940071340c14083e422101c692a405026141495500d5800d610281c01c0602000090f5003060808151365100744c81900484003140d000301100e400d41c0807054000c2c981c041040d11425000c2002c50800c4d116030042100791881000400243c514040000d018040e02502d403601c44c4d0410032010079042005000b07103402c01d802ca0780000742c0c500c0e145004e0340c101165090b245d4010307013400c0030000303503180c0540640500480d501204490030302c81c01c445c03411402c0403a42c2025a00b032042090010035840d003d003000001e20040009141e40c1c403440043d10b0038035007000480d00d5034054131401040540c14805807991040044 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 575063750 1250 575062500 575062513
    0x2070c170f1c080405010f140403090e1e04030207050a15080a0c09061107093e19020a0812041202010e070905040f0212010e120f0304061812021c02 65
    0x1030300714140e80c9500d001c4410071000f0404541440b00a40c0802d100740b0300300c181000016400520603c103644121b9058011507041c2c0c0c40010b0154070015014440e4022620b02e101c100d00900c10310502007000740c402d40c214030640304e02245545444501c3c0000d481d81030b2090300400340c1001c008040300e90080005402505004803054403a800241c2c01d401d440f04e41c140508003050304006a8076084065110144a9041040c0e40e441060302030480c07000040c2c11002d200c10600b0700c0040e411070482c0e10010310100740c001c02100d51544886480180008003a00c151140d005090b200c00e02541c22915400c07159180e04c13020f2004005252042102c00c04550000b8003101201e22505500d51019204a00e47c1039201c1e00001c0070010105075440c4101d034001c003468880303103401a05c42e0081240c402c000645200d40e920150100403414181d03081050300400841c43d41c4d43d50707034802c0050101d103281e04c00440b990006d0b1000140c4032820100a40c2096401802e0186120315406d0003005101c031101309540000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 575065000 1250 575063750 575063773
    0x2060d090b0901061503140f090f1501050103060530071214012406050d020c061003030207050f0f04020c070315020a0807090302060d050c0d0c030603120e101202070c170f 75
    0x2124140c0e800101003003808401e80e14101420f00b0034200c1c1d420302825014012f180d5030241c00b02d061580c10380303400385d0b01003180030b8691007840132446a5411034000400e498050201007103a03807070106241d10301807081d100230baa524401410308501c00f02003110740403d00080074000328001d108044510512403241c850020081c038840241d60040d00464003001000261016800d00c66011504d10741403920440742c43e803501c403c81454091840c0002c60041c014804001080d143c9140c0d1649004801002099000646c008103c000e520000080c041030141e0000040460816010040c010500c0c1d000580d0304e4241c50f40051000d04014032050521240003400d00158980301c05450308800c007041e0014180d2a190a608d201d4003408065200c03e90400500d900010740c10342082d0100c900c030700508800c105d10408261030b0303140108915500300010140c00106203208a02203602e00a0b070350fa005140035040d442e00ba17411001600034518543c030341540d074441c44c3d07802c20402185003520f0001d8404078046c0b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 575066250 1250 575065000 575065031
    0x180103020904030305060a030b0712050702032a0a05030403030818071409130219060210050601140307090914010e0a05070e010f02030c10050610020d0203040302060d090b0901061503 80
    0xc0e02c00383c02c01d035a4400094003034a401d11280040d64006003108442c3c900a0001481410b0320410382d4070560074800880c4005000000303903008403040b00869000d018040190b42100e080c4594400c007948952024000031032818402403014500a68036a80d1a00d441e0714141da4104191560803030f9a4011a001c00142c5000c40b428040b01c0f400300d400301150b1b02c4002c80306d2004110940040e610030081041c3c803000a01009080b404c80e04039809503003160041c084030074112241115211b0200f42554044036008249400450707104d001410030000707050712400343c00c00f101d40071848103000e4045e190042c440c0ea52800101940441109418480b52900500c0202102034412119046c4000d9001d12003649000344203861a040740d08045403200c85000b104440a42420342e1464011940205603441c503501c0440e400350280d14603001545130901e03550910400c0ea20100d0030951081e81c6200c0c28000481600400c1e000b00c08038800804c16a0a20741040010071107894039074141441c20507000c22103003c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 575067500 1250 575066250 575066269
    0x1d280f02030102070b0702010b0102101505010c0512070c09050a1503290a050a05070c05060103080f0f0703020d031d1c0309052b030618050a0e0d05030618010302 71
    0x1885201029410014030220780640145203004081d07002180c10000744650540c404549140d09078201e454a0640005803812103a10182115003034010b45c50602ca95405800c054450500c182c0c00c9440b0380e6090000b1041d66005407104490422a0a004104250441c0180e907000700c20800104903c00d542d594003988034072944402840d0140803240c40000c5001d1071a81c2000f50a1265000407a1134a000b040c0c004001c200d420400c96440c0030085803026204541e1406c15981c03010080030140d0840d02e032440150402c06c003641c1b140c1030402c001f181c540c22800c081c11042c2d00c0f81d0020072143c4e1040c400a8281c603144683c3d0b419181c80c42100780c03500e0800050003202c0e03d42400b01440c0d81036005000301e01070a51442c02805038407a0039001042e000080140130785150460f50380a00006440c2c4003141516814811490ba032900401110451100b507448a90032040100d800280307849481c180d142030445041189002c00c1001c4100b00d80c50030300301d071043c91840b00c4455090700d6604540c006206441d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 575068750 1250 575067500 575067503
    0xc0b0a26060d051c0309050706030c051c230411060c1b04020904090f030207051503010303110c1017090111270613032a060507060204091d28 62
    0x5810b071502c681402030501c139981c2011100340c3c4641091640d1032015014258100c1700704c80038400c08a0004900d8405c0c420500c0031300d005d070740d4185403143c403d0803207192004441c880c03900d455940140e14402a14481c50140d1000d0501000145141c20b04000c00c51404403143c2130701400007001215031504001c02c22500d82c0e50040301003c0d0780b48000c80442c000f405000001604a850031003034805001d00c00480b100003e1095085035402c07619071042c041c1181310704c4100701c9100710074401800084c3c01000d521015240071001c44010448500000300380e07031401b106880104102600c210800c8011000c4164442c0d40e00c03000780300341012602d403190359118107032a40d0710780100750400701c403440c00002c0d0601c01020000c10898803804000450b281c018100d120840355443d802009110000c2100c01c140104034211400e080000e1400030156280c0c1c0c800c042c11200706908000219011030f8a1080310520090070201811400a101c403861410040c041112101c00709246800a00c000390b404940c50356 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 575070000 1250 575068750 575068759
    0x308041202122205031e06010b04231f030203070912081b1219080a0504050c0411090d050d090602060408160305041502101a06160c030c0b0a2606 64
    0x242d10300c14911035150813600b04030b50502030b039038045025405221900c1e50200303d2005480e42e590f03071403942c0e1045102d00c2c42203100800e4104284001d42e20001503034901008044c0142404c0d011000126056070581042000840e90110600260f1503009801001411703080d4424070f1403113120788030f2040502032550200c9011355103500940d0b0300e1030140086480140c03007546054461038444a588002040040c54400250008000402d005175900500340126040806814090b244609001c06022003500700200707140100107d0b003268541840c400c007110300800141080004d0900011312880003544404110340c0020240004600301c070080765582c10344110107604080c420310781641c950141d640031140c2c0903030120844034a15004107042072502d01c003ca08220f031315001e034420303144910306079603045c0c003d602402101c020074004400e40c41801c1c05001912429039032607840350441c02c142d402034080c0000c08a03a00032541c0d00040018000c007801c01c1d1035001d100034500100010f100040046105 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 575071250 1250 575070000 575070037
    0xe030403051b120601060504030506072606060f13030b090109022809020406050a0305010602031801030207020a0e0c1905120411220218040b060708030c16030804120212 74
    0x80f5a1841e10111040808906407000396940c0d00d0041c0a5410a100540d401d0040c180003505107407149145000d50300001210b1140300072007801c0070100038130040c00c0d80d8110000304020312800b003400000d800054090a0302c0c0030707164114900f0001d052405040d844590b81090900001a0b5404104200c1519565500410100154000300c80c5600e25404030304460301c001404913680f648900204401c04058a0501250341d0f5401c040740e1301d1055694100c143c0c161100b002546610135002860010300080003851507540340d91a00b00c0121080d0740c10440c0007000920103030170030a408554094041a801d000d41000d541880c001c4210100400003090340502411070b1413035566004c51410810713502e015a010141100b15640000e61141c80e0000440e0082c44501c01c41745428013501e070080c80050b00190070803040351385000c681d41018041a048000510101c40d01d100c1c03135103100500500941d40e1901c607040c18100141d1080320300c91a5811500303d060300f100c90340d003100d0864000d000141000041c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 575072500 1250 575071250 575071303
    0xf1203180606060f090b0a032a030e15060303071221050118022d0408100b090906060a0b3f090607020c0f0612070309060e03040305 58
    0x405031100d24102100a00303020005000d5568007032000d0b600261075400004600c0b00c0152183e9070148506050040b04004000351389219400010b6080d00d0030148105c246030500ea400741a0241480144c0040e6548980007201d003001c104004103080c0d43c115424007403c045000c207440e0f00c40d1010262510310000c0d03003100701510450042d003103158440c440d40c030b5401d820f800007806030000788100c0328010740d03521280c0045841e5208070341e00354101c100c403001c0d68130b545441d4860035014905540580386090100007200b900a01034201140385c10a0001200610b00f070420091b80c0024100303808581c02082005112380315030100300305441e0200310481c0c440036060032600000460b0182d52030b103108400c2140e4684c0c0c0640c2c03841c10303070b1950341140c1c6186603413181200d6076a040d04485040069004001c4c0c040d15007040d85145120764806003002d45420071071190b4240c0e601040c0c842d00b000940d03907050031042c0607081c80f4105010a00c080554907192840d200c096aa088a00e80d06101c0c2285514145 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 575073750 1250 575072500 575072507
    0xf0d2006132907240b0307030b0603030c0f0105190606080a0902060f0a09150503060109060e010c0804080f1b03071a0c1f061d1603141302040e0a0f12 66
    0x3800c040c622503250380c4420300d14260707400c1556000a607800e031000000d201c8504c0a113010325100060080c0013446182d1650f221282412006403c070760f0103000c204150a485801400403000035a05503001080c6403c2c203108840c00c01800d58051404645846001d10a0756070080c101c0ea0800f080f02008281c4008a0000400e280309100c48a0344641000a68020b051b03006881d00d42201c040d017044407000403c002c0203550038401150f4150000e425048144802c50092415039030101041c0f400078011501075503498544da000340c021043c0ca40c0131039a40c1411280401200516181e008000c003110000c18011076900c110310b0281d4030329113035010f00840da485018420b440c41e40c2c0480040314041c48204c4001c2070b103001c021441da0100c0b41801d00100c1d9983c214903200041140e11100010140c0d42e41c1c41d03617449000d042c58072000b09031b1610f0340d0701680740c81c060001c0d0055204000e00800620300d8810001100c0541b007942140381c2041c3d00e503002090040711140710700307504072000003892041707108200e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 575075000 1250 575073750 575073809
    0xf12020901020f16031b0803090105070602090316080c0109060f030c050904060b040f0803030705090f130912230301030f050f01091113050402030604060b0f0d200613 73
    0x1a840b0700c003025603805144d0002c90342200d02401c1d0000b400c1c083d54400f021034100c58011909554400c009010702544640f000304980d9010303140040c205864840001e04051403c07a544801111025080c46030010a20440203404001d003010b41e40b291805002803e41d0b00450380540601d0b65441e00030740c02c00d001c0c60884414000003802045059211100f40e85c4540080c0a61800c1d0010301102051074480001200d008881030b07252141018001810044034080640109800002c0c80d0a0270194405d54043c0120300c9200d000400820f003036803d0001c0122041c14a40c9180900003142090100041c400700c81c15a504100450900c41c0c103410098030748800200003d45640c43d0008401c144146c900103503084ca10121410b20703000703200b19203003010303030354255000f81d8180c0144011a0001e01e041d40551288540946031900350311081c400102d40c0b01000e078041e180080c01c2d071001d86c00c01024041401051404844d428144004e07151009041c144600401505144c4000b000003014081040c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 575076250 1250 575075000 575075023
    0xf010203010305031210030308040b070c1401090201030b010201090b130501020f0c06190204150c0203010605030102120a1428060e09010f06050a06050f03100518040c060f1202090102 80
    0x2590380e96568505659a0760000700366041110514010684016400301090102c903015a601900e50312680c842c500e003c1e80103070402d414019820302003c0054014805514103980010002a0701041c2c0d000150580b00603110090469241900740e03c00203941e01c04071a00060030884010f04440b0b5460458028801c1840540054501141070040c3c103900040d060300ca000340741d42c0140d0800003102070405a0040e806804184801a503501d000548034118000c0c80900007030012071155514404a401caa00040c01c00401410050070055250b45600402007070074800b190403203003440d10320300c01d0401c0f5a10a000c1c640d195194040e600030a0801c2e044280130307210110010880d41400384120740200142e804a074038541c00c00d000041c5503d070444000040340d2094407a0391406000c0c105d0b030701050780018a5001d103140d1139003004c101a240c408840c0b002d4851f4108000250400b070400240b0742c1055408030b010440d1903a1702009156000c0c00c500a1015060005a22841c0f640010307410991550710 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 575077500 1250 575076250 575076253
    0x8070b310f021206071112030a0b041103160e19061404050a12021e06030a0c03060909080c19120509030f0607020d0f050915030705070803010b040f1d010e090f 70
    0x3d640a0008011030f41c1d500454060321600c0003200c0001c2c00c60b1b1981c51000201080707400074400259150304581100b68003134002000021000030300c0381004107035081911000d894200c0211103101c015086940407607468011184000195049480a4045c01003801360380708110a2440c60f03180c03040803000781c1d0007615008103450100340d00c1780c04070703500018014030607446100405a410704044142c080980d000c80041d10b01840c40e51081200e0029100345007244040556035000010b8101c064071a900b03641c0c0c843c070100d41c0d83d03200107200d041c581031030311641303100a43c404286003000508019011600c90781e141085034440c410712001074101849900180c915000d4002001a05540031501c42d075010100d841e400e050340f040c10f90440303e82c02000300d520b0b0041180c0758200d482040704e001450b48495180391080c80d00c07003a03680c1c1028607002a0300c80e85004001090a0151886514540c4060a6040d1000350f8a00c80603020541f50700044c8241240f0500a01c00b0a18100c403e000352020082410b0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 575078750 1250 575077500 575077519
    0xb03160504030530121f08150402030f0d020705091b221d04060203270a020a14060706090507080d0206090d0206041a090a0f08070b310f02 61
    0x15161407030082d2589040d04110b1182c040b50710044d5000b9520107000c040d040d6462991081254940c84a00d02010800404c8220303000458020030410084900c05079441e105650507e441854503240614026010036040100600d82242e40040d156040301c4041740d4800160319041500814a0420044402d40c0100081d0240d100918026004100d8450003050241199034641207068012215040c0c55014607040c04079010a8458018581103071046020301101c2d1a070480340c42242c00b1941d000c50030394020b0040c0070294502104c5a2001304043e80150040f20341443c00070710700780f154200080045955450210900004001c0309024103070302e600b12003200107011006035454008446c00d045510442503131409151004c102d040c0160390080f940c0d0901403d90310000040c00f4020005e0141d40b041e4040311003c0b03128a11112444c0303002d03060702035440c84582014100010010442c00c01350b580100016018001448034440e9000750307002c21100704c1d526117461050031040c500060760065070030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 575080000 1250 575078750 575078773
    0x31e070315030b040c0504060515030a0213080709050c1c0c02070801050c0403061505010f0f020c130603030e090103240b040218030f011107060507020a02030d09090b0103060b031605040305 83
    0x8000d030313000b64060210b6440b03d80c0d40385e040006640c101c3c0a49500300d417001e440350041a05150182d90810b0b498200541000ca40382d049480034003003503010a180798007654007044090f03400d10401d500000c100d0980c62401030145034100d040441450f0490b101d80d6601601e001d418401c3c8a158084c04401c1d00901090800324040b500c0d9410a002c1500e0581c5000304140e140035001c0c01b90401c40301c040e100e002c51180c21260540d180c0e40d6a0748000150300821a4110b19a030310b240c841404034407001c20004200b800c40c20003c00340c000c1d00c810340e4029070341d00c001170022414407441903903500f11005825000c1c042c5010030001130300d041c0c0910b41e0410300205441d6501c820440c00444103607400c1d001c6500049179400000e090321080e00703170741c21583c8042100d080481d445801656114030540115411840340d0340c003203031403c1c40d9005580d00003034440700103001910140c050b540c41d6180901c1d061101c179042402e5007800703200c083c044880210040e251500e0b01402035050750015a00b202c00c0ea145081c02 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 575081250 1250 575080000 575080013
    0xc02010509010e0303100501051e0304060510080d090306050c0d02040902040503240c07030327020901290c1c05091305040827030d02150903031e07031503 68
    0x41e00c05201c0395082803000600c0410000650348a070018412110303480c3d2a00d0300540da40da005032549954050101a41c0e011a4140c00c000c1d4080d03881501c000486107007244825040d10125041001103800c8040c00000c00c603880b10240c01600c0e006000040c1c9521030702d0080c4243c0c0328907900c1010081c000f0130300169520883d8080c0046031000c3e42514040441c9501d40026592405062425400842c01088001c048000588002c0d442814002501119031007800400c0d17500c1424010140040382c0120114100520ba175801414004242800303120514001c25480c0c01c5685a0060440046901025114200026180074a10101c44881c044015000620390390000340c015005180d2105100e0400355584a1076118582104280303080c10081513024100c40e40301c601088412807003001c0700d02207580500001000100a800a00c1d912910540e00c2801c0d1800800a49641d0002d000f0031002000030100d04807046910130440c103071036032002000e0b802013240e0411100c5c000078640c00442003146 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 575082500 1250 575081250 575081261
    0x4330305010c0801060f030c0309300f0203160204110f12060a050a030f0c231203070317090a171b0a030906051804020a03020301030b0907060e01051c0c0201 69
    0x31002842280c085180039103940200b8410702c4000b44910f1500711005102ea8418141c10300e09203004034a40031203866100310100c42032144021444003480c246c10030000100940460412400c0c410194403840b20085d489010f29905e40900b41000e1b14103d0866450b58000c11000b5803642d211911078103071514050030354010800f1541035641d160045401490560b041d0030403500b00504428580b4110f41c0e1b4175100c000582e8044030b00704d100100c0807032618120b041c948050191941e09a00c0711012104216100000880840554001b0090346001c203a0000d8600e110010b0641903d2450300c6032682da6142c443d081780302800711f003041d611095660001d00010840880406030b82091150b12a040035110401d1034001000709140003002c0016500800c050809000e1500300c0c98403030054480840c069030b1010744032500090780000184104200c4503c1c0c160840c03501c0f4001c148046c28980e0103000345200398940740c10300c1008241000c210310004100409205072180510800a40c400081d02811 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 575083750 1250 575082500 575082503
    0x61b0f03080712060b1624240b12130b04050309120303091b0a050301060803030a050c070c1404020c0f0105041e03082703030c03010608010e010506030402043303 71
    0x1642c20241006111035402070105907094460211b103000c82c0d04100d04440c010120b001c540d01d4442003440d605200c0d860029031200030820902040100c0c945281054481c1d503410605140c21078003070180003d0500c0c40942e104942000030208043d220b428601004200b0080e009101d0141e050070802081001b00c09000c1c2600255840d800f40da101c4020f0340e440c3c3c0411241c0b40c00c2e85d0320815445040038401008030b07401140c05000401140d40386c074042070958034a07070400442c2d9030000052000710601c83c4202644001d450039141d0400e42d041d074480418000c03520803031284941509004000b40d41d50b9041b0b07070000301040c0481e401d00034180c9006028001c212016070340011040040c1e001c3d11348040301c0004150345540c580b04da03543c0703c218205510403002c52129040f42c03040d806540c408010001140aa541d0082d11900d070345c94010002c1600105803c030011204101004110f2500d840301613a400550445000c42d0a0541d03400d01c00440c007031944140e8800c901e00791820340b03020700c0c0300c0d605003a203 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 575085000 1250 575083750 575083757
    0xd0207030e0303130e160e041a0a0308120606070203100e010209090415051f09110705060708010f08150c070609061e050c0c0604141f0c1d0109061b0f030807 69
    0x141d8030030980d100c005441d80c09400114041c0c5d540d030721f414606a0700110207039040442c0780343d000c9208804202505407980040b220314100148041c4803506c290b1106a2044c800c81d01240b80c503400b640825228011448114006520b8603803a052030708003034069420140f0081c10101491500d401c2100094134450b24800303945180001049202c55500d00700c1d903641e10703004040d5004915002d00e0000501c19058401222042440b0000000d0014003100b8080c0005980d030422031350502c407042e8400320b525441078003035074000400d9440f100f4268920660151700e400d81984c46800b141002c030064107158000601c62464005411140c208810003010b240c40a15004c201a98404e0100c000c48e201c0d5116035440d44d4400030009001070829100c05071045841803d4643d0307502520040850101c02a03a000034858a4510401c401c035800f10581d800301c0c0140c0003030701c2813440721030018154030460f02600341081003006c80301c0120440b00361000f9000d9400615694040094180200154801c0c0c0301c40001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 575086250 1250 575085000 575085029
    0x180509070e0f010327060204090527030a09031203090c060909060504050f0402060a0203070b040f031b171818040201090509330d03020706230d0207030e030313 70
    0x9551081c441d0100303650203605e50070005135880e01101c3c240c810162081350b12903000c22003c5814030050052a0081001d0f08110301c80b500040c0e0a01c201c41e0f00c6202980300366000303204000b00d481e03000c0e60080490703070040001c4c032950300f050b0747c2100034048005020303000c004495800600c40368800300c941c0849140040070401603485404200c1500c20643e00c03600710030025000300303000d858400010490200d260044a1a21019956000160004860503035000041d51030140615401a18050654038505001480180996100704c0100d040c05402e01d0030300d5000c40e40303644201d0907182c00e0484140c010702c090300400304100d00c41d00001c2e00712012400610080b00000d0300e07003010f0300854081c03013044c03160421841c04a00c40092040046c07509a4500c0341410792000300391100000d40075400d0095020f00f03282400c000740501020545820000c0c40302c0c2c3d001d01e000c9090143e0007070764405a1410b07070140c1d0b60740035400d0442c5e120100c0c2c42c1d540d9241c000069a500075055201d9910100c544100e00c0100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 575087500 1250 575086250 575086279
    0x7110f06010f060f0c080313140d021903050723030c06151f05030a0f06060e0306060303190e040905070f060e01020a0b150409050717150c0a180509070e 67
    0x2541a080540c140104aa80c0030f1702e000100d55001071030f0703c40c080d80302e5640301c10302c40d45508081c00b080414048554000907520f08400b40d0500c180e00b0205034450400318a40c4071a84c00034154420004041e00c1d230000141214084558683c40d9000d0700c20310300c12203860340e8401c0350311500d680040c0c80d003026515140c0510161410070700c210803280741000d100d80140e00540301e010349690388003c2569480c680da6429410f0140102c0c0309810182030a9542c0c0141380c0c0c41031050524041001c6e0200d4801d40c81400b0800004903030001c0d520010300640750880c201100480890f001d00b0740b0a10081043c06031820102e009003078011070008542c0c2c03641c0c0d03841d01d80c903142d001645c0b24512400058000380a0100003101c0d1013034441503400810b4050400034400c203003a101c4500344102500402440b2401900b10100c80b01e0801550300714a003590341d10100e60800c7c410f0340d00e03144074500d0307c01e0506c264510307024110703540d1000d120000c00020303141c41c00c2440c5c00f0a00070502900841c075648282100da10110 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 575088750 1250 575087500 575087507
    0x180b1905010207050f01080c0307050904090305030a051015050a02030c100c1b03140306060d0501061d0604050603010e25020a020a0918080c0a1b030204180f02060307110f06010f06 79
    0x41c070217101a100d1104545032002d0b18410f42c0e2009100d103050203810811403200e9101c0d481041c11441c02640c80707a0f141c0c00c00d04140030035910050003541040728544401d105c11450300c1d1601c140c0d4601414916030b0380c0d810820a078113501aa51101c1e419000e02d040e02030b000351042d0819001207031140c1c1c072007041040c80c1100c00400308900c81c1c050002500c1a610002d40740000c3e00440e00010000d1555051100d01301030b000949100341c01c030b20001680049040104803052190700700d0f11400300c0c2c4440c00c142c1080046107840c001485032a0404090101250b004010f6880c0c810700c00d4102b4000d070b610102110001380d50350f00c54050407405061007000000301c0b6042c500c1403201d0740480d0031194204c150a03844420b540e8000c15402c1c4524041c3c9400c034030005034000041d100d0b11820103035070300c09145140100030846d0803501d08050700322042448240000c83c4c038944030045580c102c2d5090303100d844100c1c04072000e12094141003198450750021301ca0750500010f0b41130403a804440d081c08100d4503410202d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 575090000 1250 575088750 575088769
    0x403020c0d1a04030917010b0405090106030f080a03141338040206130806041103010207050607030915110706051f090926040303080718180b190501020705 68
    0xa8011540980c491604824140c0c80d543c00c1402898585001034503102d00e0884003007000041042130303664143da6002030030140039150744800b00c1c90081100c40d2464982110600e50f02c9002841d0250014403941e1a81c0a03911203070200800680e014098030700f0701d410148013504032030141c0b806583d02000814040308014034000000c030010504124040e01110214400c6005c2c008070381c00582400f108031100c1071101c00c01300605a050044c41c240c180307428544000000c011602d4000e900402c80c20022170000185241c10103120318002500b2016410503a403000a64810399400701c1c00d1420111411074000040c0c103819016880c1003006440d43d0b590704a6a0000d0f041c551401100000100312180035035104081c0540036080030034180e11078440c1c509581d4080c114080900300c021809000345540b007806603510140340d04254818061040904502e1095445948041c1c2006000144060401d81028102d07040192000320b4502141c1ca1042c01c000660041a00511402c400001c01d0702d03061040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 575091250 1250 575090000 575090003
    0xa06030819030905011a09010b040f230306070c0303230114040e0d020607020717060105040905210c1618020702031f0c0e1f0f1202120403020c0d 64
    0x54900e03086a074903011022004064566040c03690391450000815030070300130780c1c80032081e14030852000d0307202d60704114080300181c114280d41002400244503485044800c1c209544281d9544220380000c0071417442d04061240000b82c244c0190400d0010594001e16440c4115110341c40612868946124078100c94070305891081103034000e000100a0360a001c001510803400c00f50010900c0b59051030300600d4100c284c04a08016800b05c020807418940c1400188054650241c0b80440c4010303d2240e20381c0d480040c000e00e44540e56034080c21040201c200102d84500b9105c40013194100064038020348680c001d4480002a0b00415085d5418000d040e802d0b981034038201000904400401c0400c6c4000350020340080b80c043c400c09030307400d02c48184503002804001c1d01400206646810342c10082c00c038503840ca44240a01a00302c1e10a90440980101f8003400005250450740e0b120000d404841e003005524408003401d01c0010703115180b0345000d11440c400c174081c0d001c468580c10700d42d080c0700c07040d9010f0a0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 575092500 1250 575091250 575091263
    0xa08070c0c0306022d0406110723060403050115030c090603150902061204060b0f0a051c05071511010b0a050603043807230f0f0f0f040e0a0603 63
    0x40910000f400c0c0da016004d0195940078604038102c01800320700800710385000c030b0b40149002040401c0500d034410300e040000030502d4042c1801d94602b00b1101090544411105404203008420118a44501c400d480003143c0241c024000e4070070700b030804a62541240016900842000b0b0041204034242c0160400c5a901c0886281541540320402c0014042d0f0b1000b00d9122030108902c16141250000f43c1c5c3c010b0703005071000110803007841d003080500030545108500a541c0c00c401009155140e9101092030054801845880f01e45442e02c2400d016580d0400240110f00311034031007005500c5040411008817410080004402c40410002d0000d0f80d84181a40420f04100040008401401c7d4000c01c03200d030904000d1520103c41d1400c0c46020000c80311000c26124801c020206a2040d200c1c030404185412044200f100c9166403603051003101c03040c081c501d50000704a00200100d508440003d040896101d031190080d403003c25aa9000744920545414890041081461203104420440b6800705 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 575093750 1250 575092500 575092523
    0x150c0807081006181a030a050f01031a061f02030703030501090e12071401050103060b0414090d0516050708061008060c120c071a09010e030906090904051c0201020a08070c 75
    0x580c00c44400c1300b00904100c12860911000844207958019000e070000004107090b00d130300d0030440301e42c00c40704000d101b0701c80c010700540108046860b1464a85c480c504003141e914042e503941000c0390407030055910007000111120340911226902001500c6800c2c841d070380608c1140d9076130258606541406540c0c03040390300012450042540702c88000c2003903d1250203070ba18492000c40030582141c00907402556803d440342c40e1040b0742e141512a14070029050f0003d070000f0308140700801d40c0d8941e0b1003c40c0c400e0100004040803000041c08000c0f80e090b86c003004590605031980b00309070b111142541d03105000081c20001240860010840900c59042d0040c440d06140020303001d0100c4810190000401103c100802d50115481d04007425062046007010561400e20050207800c584591744100b14a41003404040341c0b9544440c02c0302c0d80e44600b1210720b071940c3c0340e03400e180b81007520003081d580800d08680810841d6a4064001d040f8038a0760340c8501d01c041e640c00360185d800710450344000f4180300462 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 575095000 1250 575093750 575093759
    0x30f0601050a0e070c0b281506050904061221020a051c1b030e10030605010c02040b0109150206010305070e06061209070803040b181c0b060d150c08070810 68
    0xca03030542c1c40946440c0c082ca00700600d81b140f407000303a0240c03080700c0e40c80f5464280005c3c04001d80c500c100558030101d0208440541ea02080b1101d01c00c60050304100080080d18040039034481c0c10000c0a081d26182010f000051882c10302c100c0542c8110020594900d401c100e80c2090022400e0060642c001005d030141c511112341000141824042c00e0060048005190640800e80e85403407030002c0c46900d40c4c43c4007209036001c200700344903d140b8031410141040c2c028041664070001d00b2001e140c0c180c078041030194002d401a078540f481d07078000c079200d02080d0315011201d41e40022014126409207003942c038040c3d00c400c0760444a4004a50803508610200541040c540600d134049a100e8100000da40c21291140c1c1100d041d94400da2005201706000b091000701107454820204241300101e60041c0c100224551a44041e640c050015100b09c201c41b0004419445000790b0000460348a414094001e000741d0f0101700500300c04403001e000940b00340000716440e0064401034024081c0106c0c215089191 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 575096250 1250 575095000 575095019
    0x30c05100518040f05190e0f0c220203070504031a061f0c1202100f021e0304050a021908060708070818070b04030602041a070b0402100c0c090b030f0601050a 69
    0x88015141e041942c0f140035249184c858822103025003d440003c0000d039000507504030a80702e640c10081e41a8206202601296100182d031588030305059a2541d428444040d5011381811031140b0780010f28000400c00c4841e070780c410018000d8074130a4070b041d1101c5094030111800c904017140e44035040f50a03012280d000c0010302e411030a50082e0340ca001c4010b0b110694904040017008805100545e00200ca000e0410031a40100d030081c01c40c5040441c10800c60325450340c2c800030200c400860941000010406001c001d1013022440781d00681580c0102c9941745090b6440d108910560740940521008121081c1c4500c4095001d1440e99a0381d0702191588900180800c03c0001c09a4013403090300d2002502d41b00d000c024000542c0503070401603c03145007041c0d0401422907850060f802203001c2240400045061030915082501a50000448000c4900940b0b90102815000e0714021a2101c00152a41d5a4012061043e070950540e503d045200d00510b41e40c1c1400c2c0200c5030302074200f68051207498503 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 575097500 1250 575096250 575096287
    0x30503090a020a03110a0e040506060d15060f06030c02010c17060105040302030a120306080f0304060503100305010216150b0307230901030f05120a1b020a091104030c051005 76
    0x318442030700c21100c07069000500301c5103076600480c0d03500100d02281ca100d01d48154010b0051840c001c5100079071400340d40d429141d8a008141c81d1150700145c00b04030920140018040b440c03900350404100f0651141080741c1038003580c2c0302d07100000381020840c603040d6106000e41c49103403100c1d8171076400000d0850302400300000f00030516410010305010000c0588c0d4200165010540100079240303000c84400401004e607951500080c199074003800242000c0c00000088404440c003601e002c1d9100c3d1140190708810202c1c5a00107400b48d070000c90800005d0b00310a40300600e00384210440c11643d000702a003001030f511b0200d42141d15800080c81044015503a140c0740c105040314280014172034035440c1c0014006242030308240c038140c0c164914102080b004000d52100c0c0c108150b4a10305080645000402c0d0528001009840c1002220518215111640d01d1405002626030900140c8200c00040c003507a003240c0b20640e0358181c4128005041e00f0483c1d580d4008202c50756070503240103000d03081c0010012 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 575098750 1250 575097500 575097511
    0x90a0c11030412140705010c0f0c0f030503190806060702041802120d260103110102070f170c040902060906030c0408030d020306130b01200a0501020415020f010c0c030503 75
    0x402410110401800104041c1461105800b4031125600300400e4880134410300035903507070104009202e96030300000c10110480e0300c00400300f618078030342c0382580600200794480440010a0500481003000100c051b118070349803c404d207100307854800d4080307600c0340080e0b9a0941115040140b0000360816801641018882052009028095a02003404005151011070f840e03085010f9107010658040855403088244003000d0304203024041c2010042841880014491400c0203105040c036402401000010090500010600740d41c4840d4401301161b40c04e2100690301801401a00c503190600c15080600d40251080d401d0030b200c0da00340100340d40040c0050706084014480090f502c0006c100600c2825a54070700941c51303040203407d10452000214101500505008065501d40da000c402405500c0340b0703604000f011545c209415080c01a50b00d4068440e5000240200c1c14403c80140c84200b00082d900701d80350002d520500c5402c0b103030b90400c0280011140c103500c4010900c10340c051600f01 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 575100000 1250 575098750 575098757
    0xa0f0302061530030f12010905070509090405011806050105010e06031b2208071404051302040c0e04150305212b0c0206012d0b0c010902210105070905090a0c 69
    0x1515004103a919580050607110a6440d00040c003c41d402d0941b541980102154581880181813194000d0014002c0040950080c90354400240501809410141c211045d04818150040950030840c000d0705090248501044035000c0c840703e141044001c981c41000d00109592005000034044040d590014021004030105152100806000e02d000b1f1402410800001c0c0056403504009203903210248242d544510301e80390810203402c08214414128507412a000540c03402a00403d4403903003006005150860b00d40352040500d03d41d007a0101c07041c0c038001c030101c0f0307100303140c00203c0303c080d041c0188540114071080c020b00400c1c0e41da55103040719011a50740c4040605010301da8060441c0c0ca2500032000591040004120700441d03402d8114084051040403010f0024031110409940780a1096002e1035600280984400c070b030070350001d801241c0c010716101c12480b510742c0301188075600705100d800e15449c01002c5000c5601800481e0200d480c064003592555036401c1c0b42c5001800e5050f40740e02807 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 575101250 1250 575100000 575100079
    0xe0a030206132a060906081302131503052a0109060311040324051006020c09061c150f0203040f1b090501080106030312020310120507080a0f03020615 66
    0x402d40d400d00310005020800c62040f06858600c00801ea010319611500c1404079260910071440c140d280511a8039806445104000c0f0b403994001d030043c0103200b0340212907042420040204240480d51000013400d1110000c200d0601d58400c18001d00b6074000740f80031501c1943c0400080340240c210525010280030711500f003950329141d0012001685d440d001c9403601a023101c01f280c00d2603214064200c20100c1180c4c06031814803c02a45e10101d031300c1454410030440000070444e6a940f00110079101d840315103400142038600c0d09100074001d001407081c456040c5503c0d0450b181e010700c2680c0c1b0079a0812044080010103468210003034090a81509a5001108000c121a852030040300d00801c8003400000350140385080060204c040516810070403401041440742600c0c03080440f0042d540c0103054110082d03d18901189000816031001415000e9080b0000a228882c0f5103a00c680c0c0c0039400307844a40d69504060700f5018400c55195a00440c0c0d880340c1d004240510b8005c0e031600c403800e40007804 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 575102500 1250 575101250 575101283
    0xf0d0c030b0a0c111c120f020d231302102c180405070504020a05040305070e0601091203020d0e0409060911011701230f0915040e0a03020613 62
    0x5204a049600c02c50080c2c0f65204810345583c01510300c09480360710809419043c402100c072010129043c2415810881d0201c031005145031550320903940b0f145130302c0381151380f218441c1c1070801030b0051200107100164800201e0088500c0020901d00c90101c000c182450030065900708040032000031603441c00c02880c0d480744410801d9100001104016111b00d100e006c11461040108440b4010a00202d521181d410700c80041c3c0c000a47c0340581e007017103034096202c01c4610811111130003a40d102800074440d40000040b000804803415008440030703a100f1105a07211070b08500030105d0605e00400503070140da808070b4218401c00c8070b903100840080c40840c0340a16a15000241c484404c02507e425000c042080e08960300102500b00d4403400021034a041c0d0b24054404903001c050000d00d68000e0f04070420300c403041e5168815001d400000400000d0503003011130225100d80b82100c44c140c041c038604051100c02010010782c1ca00b03220751560040489507a45e001d12210520b002c0402c072420214030b4031240 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 575103750 1250 575102500 575102513
    0x40b030a0501031202030708120403180b04090f061415040504060b031602060f1503010f02120420060a030e0705030a0302060403030b010801030305070204050403170a0e01050903090f0d0c03 83
    0x1800380000c45000324055045041030355121003501912010341d441040010001317007840054448031001c1074100031071307a0b41c0c1b42070941e000358044d100340b1450710714420b020a00038480c001910685030400c0007040601408100c0000f154000d01482d02c2c41554078590400500d0880f03400351007108540445402c0ca0342c1e6201007000d0341c82c581c0114003403000100c20030030240c01300c00d840000400c462000380300c641000d20701d403100c001c030183c20b603440e2002080307d0340000c1c0c40c00d411a94500d0b5406034115030f83d0a500c80720500340300d41500e04a41118a8000002e13162800e84014003040c61300030001490705264540540c000c280c4c91600710b49500a0a40005041e601400aa00914003d8015182e6883c0519009040311180c08145062000c448010b00c080383e030110940304825030643c5c000565031201c1c1070640d942181c150b56031868401e06002c011031110309070407a9550380c43c071a00900050722005803a41d224000c05100c680c00c81c0d910f69655029140001c00e0904203401103079145100b035243c1d00e421 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 575105000 1250 575103750 575103757
    0x3010e0703240626060907020a1e110d11010e010c02030a0602120f04080301051e0901080d09090519090c080115050a061b02011112031611030301120602030c040b 71
    0x3040240b281540402c40d240c0c001061291021a802e0008501c80c100c14403101145401707040c40d401103007641c2c0080c240718020015141c520b80c1000900c0095442d034620503841001859003207559007001c140c00ac5240c109a00e00581140d400385840c1200c00c0c68070011581816010341060405c40f0307400f04080540c5041c003c0380041400b8460140e038407409600300e07507103140c4003521500c013a0601d1400c00c80410140010b80341543c204565410071480c00030040098280c201a00b594002414000000c840f400010303003814240107a154046155907520703841c0110be00031120113802c50646000c00c01c1d0140154440e03c5024400c049103010940c95581c1e880c00c440410758503070598110b0003000d105c2d514203911860014202440c1610440501d07a1005032844813400000381072100040d100c6810a02c20f01030900404281c000c0141c407460000f0510165050b0015040c010031500340b0306401c401070100442c0e0580722001c8a08102ca901c980e543e0000707500050040c41c03200414040400c2084625004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 575106250 1250 575105000 575105051
    0x90703170406020c100836070801050c04030b0426040f1d070e010315091103040c0501030b0102030724022101081605270408120106080c03010e0703 65
    0x107611507040400103842d106206070043e01c50303c48410340070348195000c40b503184e120414503101040c0c84070410345048607c1100d1111080c8680503485a4070003640050010122190388000f03000d2601c8114403140c4501c124000500a41c418000140104001030700f600c03140f002007540303045040c1c03e007021015550072513008003141c000040b038200030105404071854800306520301014224200188060081008221500e050545580362440001170141007a00144280c20003807250b02c660040a013060b900465088441014503200803455510034816043c2014068004620342100c40d26021244a4150340d00310090400540034100a03e8600241c070240d144000ca010312020010304107950894160800807032540240402c118138502c211644d0116074055481c030082d00e190b00c101c181c50080d42104410544000c005000800a00b030004009540510800c01411f0b6240c0714100c030f03030036030031344a150b11050184018000d81e6810201c45420000343d05000131041c050504959004005560 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 575107500 1250 575106250 575106293
    0x10501060c050706020d1e0207150909060b1e0d0b21010c030e0d030e0102040503011d1911010509032e0e06160e01050412050304030320060f090703 65
    0x840040060803c0310002405550016216162021500400c00c103180c1a609155100360111840c00c4ca0003404401c02915a0011403c03030380301c0b648405400f00e030385445103422a41c9401c900041108001c4199190404100c04204264101d2040d60041e5044410f2518207680da581c4108980ea1310450f8580240780240485000c064050441d02d0842d14010a54000d040c10840085c081c40c1d00840d51040401450400045035041054460300a000e560000d980541ca46041c0d02144031041910032803154000048924480c1d140844200c001500c2c1d10060103014840d004460641c000c02c00307001d9696011b0111410651000561000c0280206c13810031402d030200048070001e1782c40e01801a182c01464010009030401d9150051a42006044c00e0200100700c0d0103454281c1c400d608076001041c480c4007001c40c0001c3c50412035181d031b02510040300481c00c009012040002c502e55900200010b403400b416403a52040c8141c481c6040081a07801725001c1c0e08004000204000110356000d4042003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 575108750 1250 575107500 575107517
    0x1101090b0f090102070c0b160506010b03041101090b0a050f07020904030c050d020c06090603041109010308131a090d050c060a03060f0815190216030206040506010b04050a230301050106 81
    0xc0c036091814000b505090702c40c1d00402c00740c3c010032807100b003090889550b102c0041d500e0f900542903403140309650400410368003c1780000902041408080c0d4020303070081c940e40d80040450001900c2c1c65034580307c0d8503404101480b804e0360381030080300a841000c0c03103501703030300e207018419400140300310340031101200400c422404950921500b00251140510b090004042ca0140c00000602d9030048a60007841341e1400400501004110800f00c150980060480c0c1d1840d43c407450036942c0d50b0005070410100305445200050000c0d501d0200c184640d18082d181c40c90100514244103140038601c1f016030f03891041411000329602c3d840000c0407070040550b400030b8183d0a20081c084840001d80c400c0c4c84560044020422590190501d00e4101c035146030610154001000c0c00c101074040c0c1e82110303041d841455440c1043c142c0104181e0311442c4603c1c20346002e0381c0c035000d891a45010b10701405400801c0702400b0300801c041621046200030900070700a48261760140041d0a4480903040207001400d0348 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 575110000 1250 575108750 575108761
    0xc09031c0503100e0c2a0706020d020d030626011b050403020a050307030209370903020606040603030905120309040509010209100e0303070201031d0f010608070812040e071101090b 79
    0x243c8241c806400d00c02805005401d00b600701c0802802030700304441c4006800b2400110f5503c0e0102d1084002038040140c0340c1c401d94418019444001107040ba1000d400b44882c030105051107481481c095450251400791030441c0c040782c4c0075802e0b004a02007115507603620450010310894010032040d160b03036551110740e01c0d4298810b00c0040c0e1030ba070f8481400b13035006c0d43d814801070361250a0150f0000100313216104054a49040030130002550420138220035925003e0034000c4500d0300003d2026010360203c901b41d48600c0b0a10040f107505220203000101101004d00c01417405052a20b003880f50350003101d043c00d00b800c0c001800c88905513083c4996031750024032403405003400d60048010007030608181703c082c40c41c0d00110781c40e4450b032100241010350300d200540c01002a401d4004003a140201112064410011418000d00036801100020721486c54001070b200c10005d806031040401d5201c4600341450030b0248158004040c0c200c906000c48a1208020b100e0248120140e15001e55203040450520 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 575111250 1250 575110000 575110021
    0x10080d08010305060106080916060302070b070206061302030901140114030d080708041209180507030e0706090306020f190306050a0b09030a23030a11240c09031c0503 73
    0x1010418024481004010008a4004203103e81103e10b01e080444241d60350040385410002c1d290b603040000c0004080220b00079a255010f44207051045890f01041e88411100703a94a46044841642c0901d440480024440030b40e000b440c4c000c030389000003081c4440740204c900e4181d60b0076080b880117440c40c1e25150040f4582000060020f012a080c05201d9042c40c100044c01144010000f414036071a6000c1c0b02c0405208040c003c00070048441d5003802c1c010300b074210030301800d400e03151200024200625a0010701c00429842c086075040c0d00c507902e00a03d1036031644c1c0a1740200031844640c81c0b05100706400300c034035514000b400f8412540c000a0701402d0004014800896800246160b81d06000c40c4105403400140d0610340f036000003100e04801c50010704680030f0b40c0708103040c0310280008101c1c41c1585800c00280030450390345005641c9003c560000d2800611a01070140d8010440a03011901440b140002490011005415035000110640e0752210340c112801d05a0001907000040181071000d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 575112500 1250 575111250 575111263
    0x4080106060e040f0c0c11010c0804060e03060f06060d05061503090f010606020102180103050901110c030d0b10231612081803030a0209040603020a090203180a0506130305070b1008 79
    0x1482c0c131080141400c00040103106010041e001008640c1c009040714460780610102e041c03180d80500080c1c3c1d202d032605030082c050145007086500920407440401c1c0c1212180000b24070502c005001142040e411020440c050000600f955400c01d40303c2d4520b13142240200c0066100b004544000c0c840e0071491241d650841b820f591003482164814490300550700c501444c102486482413070041000e0700c1300c1d00704a0044c00e1582d4031060151001074a26013614000c40900720800c0703020001c20803200c0407800d0080303404881000700001402c015202054540881c7d040c000d401401c44004e0800380e80d075000c41c6040103541e00a6030700303885107480e4508072584000b005501441a11000219144920075142e990001410380c148461f0085114401d0b629164044002141c0080c14074103a982c1e1500280f000b58000d588280c040c45c8056444018000c0004000c100240e0000c0141903e6071465401c00a626103e14210108101004814041040b182509010303d240102900c401ea00c0c0522480c078001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 575113750 1250 575112500 575112521
    0x905010b1801030c05011103131404240b070c09050405060402041d1b040f020f0d060b0c030703052a070e011d0f060105131206050a0e101104080106060e04 68
    0x8070800041c070005451605403c2180c5013820000307a05c0d071f06818145d0640c00744007108100f01c0c0c0c041100044016601e1850800000c0c10740f41080080900c40a1100009050b542c1406200910408004201142000303000003402050500191130302c0d07455100540e001940d0585407070380500103000c20b51415201d15114214024003000c020401281041e0302c1d06100281c026200ea07801101092036150394101004102041c0380455551480401c0104c6076041a07050281f400d00d080d0011524004401c100c5001c174503994019410141240d0b022121340c1c0c0042410301c90034240c40c248511020070301c0704041040700b10002070700c40c5a0500762081e441b508147c1c002c2c40000102c0d954040300e500d0111100340c10036000d00e400c5400c0d6403440010784440c81406021401d00c0d05010001642c120258009003510b441b4010a21154480308511710a4840901c4201540c2c0c0110410b104480540d60003c0c1000000f54020307400c0c2540c5005590840f50550701110101e180c0801042d900e02e024420340c5040b5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 575115000 1250 575113750 575113789
    0x20303130e04060614210712031e0203040302030a061e0905030712360503032d0a120507091e03050634091509090b0d02010806130209040905010b 64
    0x4032800004103086c0e88501058000700c50942c09049100092051001400f10014980d41d021002d00c0c0081c4404240042c4640103400308010014091012040764202d0750014000c090400050700c2c0d51300140311001c1c010b030042c6440c118403e0150182d0145580c01406603001d140c54201d41d052007804000007900401c10801c0707001c070307007038405210040c1468216007202450841002c40540a081c124903508102e5040c44046032050111600070194490800c2c01a001c62040441d4a551911806000c03041d2010400405c0c0d4846d0800b42c076400b00f0380c81145403805050141e95a1402121084c1460f801035003500d240c101401440350400806401c00c141c41c4421246104811103040034080828558000c80ca00c11105032039039200d005d009024001c40384420300b8030b80f40c541c40505140d410788982181300f420700340362540a04e84100280919501a1241c1d030316961800d041112414480300c102d00803d40c00c1c4100203054440d803154009131071181c000019031100b0001001580764841740c106819 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 575116250 1250 575115000 575115029
    0xb1215090c07080c010f0e07080a5c0a0f0b03072109031115060111010f0203090d030612080a050a030b090f0a0c0201061a07020303130e040606 63
    0x1600c0c0c0e0540d60358000800c41d94192140c0c90b40c070307240b0428810207107607101070340c00c2a0031803101c030045d07521285200752850101c8031070319075480010703407981d1680c000540940d21403450f0b003407518071048107014180c42c01346620410b8140440502c0e001c00c10301c0800c3d007100329180c15403824014000800621000100e5030340400914015015420f80d0b00b03030180301680c0c1804004140468086c0820940188900820381040c05521070030000034030740030300c06034005903420703058800c0d804020031794201446450700d591040d540d440005444502a07110341c0c0d00c03559070b550300030402c0d94003c0c0302640c041c1c0140805400c190040c508010b0076242250060040315405015040c000b800350f5003207a0740c0340c05500380652070741942c160650052804903c215048103103201004030100206912510804801d1000c0010040b4100c00300d0882e00d81e40200f00c21105400b80301e03424680d4040160850728401002c603460840700400c01e4404400380e80c840c10103228040180310030420903000350300144c16202ea0078541c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 575117500 1250 575116250 575116291
    0x2616050307090c02030f040e1504050708040609031202180f03031201061d09012405130e0402060d0e07090b01020c0603060105090d170901020705181605090a0b12 71
    0x32185050b214a8242c181d85840618285009206458118060f2405141c40b80d603207071540e460300403088485911042241031041c8141c83d05101e4903010b030304c1c81c1c4d550034081e07503590740d0b484010041e145054061100c41c1e01c40e04e460010a00013410954042003040740b0001249090124034114480e111788a50000c0c090b00c0030001c4811501c504540d42880c03d0b5100300400c5c00103203641e210113003841d83c011860800116180156441080b140103420b050842c0364010644215118041e540b00700c150801c5012040280c41c034002c0e00d4507049400144218030b8202502040c104583d240c412600443d04130410400c204525445117101415080c00a841648015030004807244001801d80341072004c085122011a15400000400243e0014101d90491206181d40300550800c41841d4014440e00300003050310f0400c0c1044e829020b94105180510ba01c424201c2c03c2840058510002001014081085903036250205c1c00000d140025696139500000303030b82001211b1006000340c0c2c0030880314a0611 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 575118750 1250 575117500 575117503
    0x504020309070519051f12020a031a090103080a0f02030c0a0f021002060c040b0c150901241d0405030c0a0b060907030c120209030a02060d05010f060906020a020906040626160503 78
    0xd00c150700d10260061907403820b80e0640c0c4c105070043c020b894142c40452704040c41505513001800c01e000c00ba0144496113024400c01c80d1596090100512070301040c05801721182c001d44401c10a80014015682842422100c142c07802c80b01440548003454812104801d50a0154440c0c4851420340301030152071800718074a0506101d0341c8a372824050340083c04014580741481104404107000703e009055082409a041c00782c2035000200c1036000d00c880303e20007109103602001080b01c010402c2c00c0e003044516a5610050b110090095072640002c00101c0c0e442501844503d809074403414030402c841c1808010b02008a400070b1608041c10b1070716280000c01c98000340311050340e60f055000540d07180100e501290a006481600941241000c81c04500850042e003019040c0c407078800050080c0c6503101c3d0100c1c0c102070240305500c0036811010b42c20015042c925a091742c40b020161010030310681d02c0d072491b01031001041e405090145c13603200352480d0700410f1281e060500f03c1282e04000700385c10301000a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 575120000 1250 575118750 575118769
    0x6040b010e04110301020d060510030c09051504150504081e06280c0309020f010309020108150a030209070c05070501091a0c010e060903040e090109080919050402030907051905 77
    0xd00c0386600076000103003000302d5000404081c00d0003034003d64a0301340c181c00100241129004544c890344514404240d400d12034030030201002c110740d03a010701040c644024402c5d0015011320343d82c1c007820200404502040e17594071143c0c02d45c0d01075403080d549500d0306d500c1c1d50030b10107541a101040c44031900c2004914000080240c1c118901e51107891200001c01880381c4403403040002c855540d42004144241980c00d5441008014004ea8040e218150f09400440440d200002c0081c040361a850201359040450010000c00c180003070814a402912500001c41140041742c0e480c0014100300c2c0342604005061099000416007800c15400303080c18803090000001c0c0440102e92407082c00b0401c02c010385030075000826883c1c104000d58003141040746a0589030ba01c1030143c42d0100b49000f02003150703088148071b03004035241c000c203040c0e080c130382501e003080b00626800c8182002d44800d0107021900717648a00c0114000c000e994002c19185140c0418002101003000d09000c48144200c0200415240c140c0300 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 575121250 1250 575120000 575120009
    0x403120e04020f0d1a0405090703020102070506030f0f0411030304030b0a1503110f0a0306092102070f1203020a150b0f01030501030213200a02010203040b1f05040b1503040812070206040b01 83
    0x110b0710605c0707078030124102c0207100c042d5a400360811043c010f0320100442d05109480c002c0c0c5c25070300b8250311002400315501c015203150107007010b100c002410200e41c0c01e00c0290010321070380d030071000c00e446040000e1840d0880d410a44800c803418040c0b1602c02c0a510402007015204901009074a10b5030b10340745134000442d058140148909a00e0144503540e03100704101031544007030300300200103040c2001440703a807a0442c843e030b0380b038040422100200d000040e424111851400702d00c0041d0300700034800d50040300c004005c9041d40b103602c2d40040000d60b070340340c0004046080c010000e481381015007000b031002c00040080341458504401071001d0b8071400c01c03401c00b05c8048000483d9090041011480c100041e08001203441404564007600c55410740045000350302800060401da180c4c50540d542c4907040c03004003840c0c07a103518010001c2c0d0900b5041300d122118003d0020982040f6101200c2242c0c0c404c80d0129507010000918110010007826019003120701c903c0200034900c0c2907902d56840381d0042c0107 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 575122500 1250 575121250 575121277
    0x50112030c060f060503121b070e0103021003110a0c0309090e071427040b0a050609190b0d0606090c051c200a030e011d030a051605030403120e04020f 66
    0x1501500010f150005030040c000902121040e6035454081c0410760490f07102c80b04e0160030070171181c19003140040c0203415a500b0310440e0403164650f42c02c00103060904500241410384030070340046918102d20117441450703c20344804210680b589030040c441e041035041000d42c20b28281c0c0e07948042c040002d40c803007030703503003044040c1c420700f108100003041c1100c110221010380c404c40b4030b055800100a0364603801140300c0c514039643d9840d544942c600f951000c4130803980020403900010301250501525401c0c4c40f100b542c0c002203500030440440c00d500c60400c410756503103440304410002c00b0b80c0382c41004a0811246002800d1110850800345402403407000e51050544440600005c8004418201d20510219110b541c0d07603114258060050000c40c6000d404da9440d11005008810b20300001c0311318000510040c42ca420340740300d02520a5000403400c595009074002c807840000e03078100000c0c006103025070100c50107005103200042c0064200304440d4060343c010711400d10004200e00a442000b4103101 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 575123750 1250 575122500 575122511
    0xa050d0f1119080105090c0d0b0409020a0602070e1015140409020a0908010c0f0527120f06150312030604021201180c03020702060301050913060203040312050112030c06 74
    0x96a40001d0034002407800c010000014440d0381100892401d01003409054482e0700050f80d0f03074810421080000c07a11112540c03010804112904407a0b8080d104408004100080680841d00810200c8520341c00c82c0c0c0140c1e0080d081402041c5440002c50b50060710803c803900e40504129000a00d20301d01c120240500400481310400600c03180140c4005e445a000304540719100f04900501c0380c441d40c8036102c059464504030b409010302c902404c0b041c4074030546943c1e19001c082814440e0f00002208140e031035030f494911400c402d079145401c04000b41513050003400c5183c541030280c0c2c28600043d084103481c0000b0881084281c80105080c141c08040b200c0d1907880b40e603802c011034040d10400e0440d00008858200100d000d440d0003603942e035440e01c440c00c1040322600710101a000ca01c40c8460180d800308040c00100018500a0510b503401030f006035095001001c9a518041660020381d021401700304c865040e08086110fa124403170050034662000c0101f01c803242ca0281008076144000fa01164841 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 575125000 1250 575123750 575123771
    0xc141e19120e13020d0902120d0e06030a0e060c0702095415060312040311042301150801150e0303090d0309031a090601060e031c030b010f02030a050d 66
    0x10540f64079000c40d80181590348103400690007004280c1c45108070b01c505d00c400f500e10301d201030010307034540c030300466440e628140c02c7c2440403c009130300018a10b07000d135a03d0302400b150490050001034003802032240d1403500d660281c41005400d44008040881c6503034818000c2241c5002c81c14030903c055942003892500002c801a081c90001607404542d1400b81d607103483e0a030044001440e0300c0422645048400da07502c0351410152202d01c508416018058207000c03d0000c1001e00c01d0010500200520000b840626580c0461098070501c9500383e0124082c8010800141d43c41c001301d4a0b800d076031512240304d40c10441d090003c4000c2074601410054224a060f9550705c0810882e01c2c0494014108a01e51009290007030a10500380012207050010000c00340c0710301826402c2c2402400e170080904480ea00f80001100d06034001807005625200703d0107990041a03039404070340041c106541d004209441070500241c003420740540c0d46030465204000700c464965102c010313940041e90280e400315041a54 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 575126250 1250 575125000 575125009
    0xd0f0b030312250203090414010b0706020c0120070605090309011b0311071715090d0f02030409090609020405070c0519020d0203070b041a1201060c141e19120e 70
    0x6460b0300710040c0003e14108100b503600003015099010382200c0a200c0c0141e1500142c514440a224003500501e080c00343c0b070b000a10603005807440c03801c0303100001025060080e04032542400d44070040084200024400140107540c00703070641c000380090042d460414000002000c00600801c1d042607100176104c038100f05403050800c1c603404000d6108580d045500d542020f440c1403115085101240700301540304249039420918103210724540c10140c05008001d01c0166142c2040c0880e101c01c5010410011036544105d04c070311104103009140014202800d40b05210858401074203035401e0012982111001450001e03c1c2208184c00d4141c41c0440050b510209800003021039000f5810b0040031408200c010200000d40202d03480c0d0707041c0c1c0c2e055400c0c000204945201e0b0700c45984074401c1200c018085940111400107601d4400e40440c40074000c400551400d201d80004207021402e061003c2a00715802040780c6e01da01d944118400f20984010740d62040d0200300e182a0109104c4505160891640da = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 575127500 1250 575126250 575126281
    0x507020402090a15090504060b090411120106090f0603180813030209040609060c05070c031101200c210304180b03030a08070807084302030d0f0b030312 67
    0x2c0900062405038898106002d11201e60b895030f000241348403800a11032525003d49000c85c2c1550312460300e001c076110706003c081c000d01240740800310030800550b803903000c3c64556580200880c3d039560041e90b0403d01d0320741940c3c1d0550b1201003014204410091b0000c920074008950951180060b59035000305000700d204598607500c065131005180e000c0006005103074120b00b0960b880380604204905a5480c180d441d4021000042c000e82c1100c18140005140b0a0789038040440506121031408041e0141035040800603500b20f480340c201c0c0021144a007807140350b007039070b449a003440c9041c5035404140881e81d81c01944190b2500c040700380d6600d0715201d019070001101c401c0c0641641d0340c8110582001d01004429110040041c00303e44c001100184504403860280b0b0b013019015444603600c003580c402c2004194912041c81c24a0030001c1000709800721255044a45500a9510342410740030100031200300c83c003044411401e24202940039500801220100303c600c040001c4141c40d0600152060341 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 575128750 1250 575127500 575127517
    0x160806010e160c03032c060604020c061303031e0c0e01030209130b0f180106020f0a031b020f060c0718060308030103030c06020d1103150307031106210106110d0215010302010507020402 81
    0x1e0300b8014070b00c85d000346c440144040c51343e80d008030b840303503158201804128440c0302d16401c502e0300300001141c140d200706e02e807080003a4002e2502240c0c041300340f4240381e028900792180518407591040381103a029002140d03041c070201e09003803c5042a8080010442d10715907c100c075040180d603031140c04169924a074464030050b4020b411400498110034108524240a000d0000035201d1040c1c684040880010444010755056845c422013601c0242e458004150ba031000300c3c0e01092440700c0e04980d03296080030380b460340208001030640500d4807905c000307415132000c083e4030074504080382031000c5948801103a0440b941841c000d02c0007107550a01e50001c0c05058902e80410782800d81707118402001101441c021000d62640c658506588810582d8604051100900c505058503060840d8500b2401a00a04204403500451403929032a4880c074003400340c0000b0082407000350b00540c140c000300000d45400065000402045420186807040b044c014030000b81040f10002d4450210b4540760141d86444 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 575130000 1250 575128750 575128781
    0xc0513060207050a0909030e12012307410408070308040905010605120a20030907030b09030315040f290427060507050c160806010e160c0303 62
    0x640c85030402511034406109443c883c4442c46008102d1017014822446501c2d41615a1042c0c021444c0510940e90390440b0081015542ca5000d20844000e0040c03807e10040c0c1200080e03d5032410140c098691114503200806a02e840004001c3c0002201030700d10100d83c0c0240728503080b080c0c0504181d4184034513008540103011310400041000300101c064000d84002c16810b01c000c2c3c0e2280401c0300c0b580126078100070480414801321b40c0711459a407110150781c0420411412070b141500c82c1da50564001d41c1c03001c2460f84000400c0060180d40c2c0701d8580c200b803883c030141d483c0d8108418220440310302d0341c46040c400c660701c420410301480a0761160980c1e261646041010003080f03004803091221b080314403130003141409920030f6062165411088800d010700042c82088825403100780080030020102020b02c00204240340c118002044584204113a04203507800441c201100384e400e065040c4d02c04404410082e051018903020480c480118101a00e40565002d136181400c030080e22031b9542c4080d16 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 575131250 1250 575130000 575130037
    0xd02180a03030203072f1917060109050c0f1207021603120206062b0c050613080c0a03030c080a230405010207140303070f05101103070e091005040c05 66
    0x2c0540100142140500030012000520282d10909080005002104103105400039152501c0c0c80c040c41c07040186209400d1800c0e81c4c40d02c072a68072030f0032038030040c850803558420001041051140d024031503010b84660059030802c9145100d400d003602445800a4000d60341c4000240c13030a00c200000358102143c0c50b002844240da80c10440d50411811390024014007030500000da090901c03056454800c109850408a404100894926541416542110b4680344114006030f40e0340d40002030720700444c10321040b83d030245c5400245441d001179000c2d0715000300140300041000c640c2100c0c0c60340798503400450441c1c1d1a03c805a0883e18142e00c4180e880c0304e007001c42c1c10b151302c0c800c014018105440b400e0b000c8178032040c0ca414030300c0301c503100125000e40d05034010400180005c031082c05152003d845502254802000701c1da01100352007400070300410038079020042045041e0b01015280302ea038030940c0d2030103903424184c920f800c12040900074140100d071a450b4060142d48280100c40c418074030850907205 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 575132500 1250 575131250 575131253
    0x10f09180b0f030a02241c09021810090c030e0f0c1e060d02030a02070f061d1204091e0c08060a0b0a020c010f0c17090a080318010c020f10320d02180a03 67
    0x502d2180000c9c0d00402240c0c0715900f821441d00c0da0700e030142800c8480301c07000c1c03840c0c00e102201a000000800c8201602c0c2c065074915000d04000c070300c80c0c002d01c0c903010f03101c40c500b18814055500001c4501002840d442514620356850302130850300012440e21026950fa9241c0c0e120f64041d220740301d4024500350400c0090000e1140342e07030009510030040b00c064142d081c0c01da1840b560302c41c0001c111460b807401c200070800c55080580c9c04038155003042105084c40c400b81c20f04510403070710000118008100c0700c0c0104205460000c011034040c03e400034410b07080c1100d00718002d507140000c20140c0d05000386040100485400303010f8560b0034a82c4041080c2145e007060000134110740005071120f024146910000c100180084165812258412000441d41c2d07100401121820000c403026178015440e0b01650486031140001e9891094090b21206955180c0c240f0045c825081030310490a2040454071080002c4c1299003142c04041980d0340160b10f44c590454004000c0c04951401d50303201d10b00220000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 575133750 1250 575132500 575132557
    0x506070303230709050102030c0c040c0e060301170c0109212d02090c040806130318120215030c07020607020a090c08040b0703060e06010f09180b0f030a0224 69
    0x244100844da84040c646070342c480040e643c0380908981c292058000714401c5100e410958040b003441d0280c0c0c0b42000380313104100d010903250390080c0c00413142e20b1050325641014074020410687d60000a1070989142490300c800c4a42c08209081c680d00da120100c003003203090100220420000080d403200b40100c0d2100e4054440080c00e0300c0b54224001c0030482d0003d440d0f0080c58060702d0880703005001815495a07041c2c000c0340030740c010a4046050200f110302c5240b5583d1488111009860008d400c000000c60600400807545c61000c40001c56003000c01c01c00158080800c00e03603002550580365182c4a070800c3c030008802c0407094208115507440d0800d000400d550141e02c0c1030280c0d01400301c003100c5440f8100200c0c142e8115001c3c4114103240c103c0820940d5100744200a0502c401d40341444400c3c2e1501280258099070700c046288c1c9541f51070440301941741021041080130021001403a1030035056000c14980744940c00e1450110001002c4d00c0300d18103001c0b00f113032343c25215650030744008001c8142c180e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 575135000 1250 575133750 575133821
    0x30b101802130f03120f170109090312060b040b0705070b0a02060f0907050105120a0e01050906010602070609080a0303020a110a0f2915030a0b010b040801240506070303 74
    0x710030042c0c110000d039400c460322205095903003260581103101d641c0d2406640d00c81e1001245010403400086403500c1c66052100039018200040020030301e0041c9040043c5141010a40c03211060300d0035004011031400d1300c0031a001c071a440c8081c5900e42d41030342072650414030a64841c0301080e10003d00d00b45040d50200d0230b54800d5203104c0540446845480983e941c801c0710380221070215004000e2010b03e51103100149500c014000004500c482401a003142515030560f420b010540c06040180310311138050180c130010700454903080b1046864140303500d56078641850040c06244c0e002542c4101ca6104051540442900000b2141c05020510f4076411003142400c040d580c089204150346039600e0380d8803004880740b800c0402c0d031580c0e80b14031280025142c0425102e0b035061080c80190340028081c201c0c90743c002d0001007911034803589000070660070b445e10500d158091000d948206c1b00c07640ba044c420841078070011b840c42600c03000f01780380540040501c0072800b210500c81c52482c400c0307100b425070310 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 575136250 1250 575135000 575135017
    0x9060a09140928020103020d0207060e0d020607180e07030905030a020a0c0e0408270a09050f1012060e1024230f040b040c02030d14010609030b101802 66
    0x211030740a10320304043e40e4014020045000200100000f1a002d988243c02802c0c4a03541070800500d48107d6980309011110001068a000c0c0c010003041e100d0640c040c0003142c0e102040d41080f4158007003161203440c80d910b0f507001300c500000c8580e000c6145984698071204060b688007003140d603103018908000e9540c54003401c003100e03545801d24002c00d071901d0021415004580c0201c4071402c2061017040d0034881c0c481c2000500e0307000d4450280400c1d50b900d450020700148a00c210004141c1400d00e2041c1031840001c00440c03440320481010018001440c0741102d0882d045640000c0c59070f02c181d5420304251340400c04c4440182042100c0442004000404012110210a810392640d9848090310702c0c00e00000940e60481c100540381000e030605905980c080e22000700002602c1520b0700005013210300240d00e102c0140d0000c01c400e11000e140c3c2c49200700f0754220203a03070383c002d62406030014103801d441e0200801121603000400c1a046410707590001a0150008070075400f00d21004100082d0842d004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 575137500 1250 575136250 575136253
    0x1525050111130e1e01121703161103090102030301182301330c0314070803100e010311121504051f020f040b0a20100507020303070e09060a091409 64
    0x21854401c41c0c2c41220a494040c1a114015603181c01c10703903c00c102c82400260340303c3d041c001807d03038210009401581f142044217880c0b0780f012140d000007080102002d480042540c402c0204041581e000070691b030459400c1c6964028980b220b500400c040e114048100d4062041074003940c0c000d22212008034180c030507003a960743c10304061003042c02d039407001a440c098000c00e804001c2c0140c00d200d0042c10100900a003085405482c101c040400b06500100e410740c0e561f80040140142100380c10b450400030184002440120350442d1241d407142010041080d202d000340c88092650030300c0920001d81d0143c1d035201200543e2800382402e40c1c03203030000a00818002081c20141c00c0d081d1480c1f0950724042c0d480b601d418101400c1920200d1107500c140c0c4070505000191000c5044080f03846159880844100060041c00c070001441400342c0e00064001015500f051013041621a4060582200d0700e0040700d01c08819111440400c0c038007103858100403100340c2042e800030408402c019089000d00788000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 575138750 1250 575137500 575137529
    0x1107090506090f28090816120206150d020a080f060411040e060a0906061505070203010609060501121d0109031e0c0b04080f040f080606152505011113 66
    0x1140c28043d040c1c100c59a0740324110007141d01e5000f4811004032155118120700c00a030300900717034550f48001d400030001c000410b9000907090342042204000703119041d105000401160410a000040020b8640030070f502506404112006655546120000620030074007035654202c10102460f4641002701d6061b15544100005540542494850202c540d80170001a02841e01c4081d000009080c00c0001610460303100c513008512031410700455046190a82c650319a40d141c144145429210242d00101c010b918000c401c0060341d0300f001c2012800d8600c07001c00106002c0c136020b00700b42d81055000324142ca40c6409060704c02c064100d00c551990380d05502c2c24070f10340700760840100c0b03902824903002001b0940034400b081c001619a4007410020980705ca503039080c06c0e01e030983c5507220300c0e50758001101c941c46034080c0300d6a41000954078402880600c1d555141c0b500d01d4641c100aa8600000c40350b03401c02c4c000100007400b00a6000b072503200c1020b864183c0c0d42240d4582013002c00002d00800d0043d05001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 575140000 1250 575138750 575138761
    0x30605030316140c0405070c060c090e06040903020f030a03020c06060a301b14040c050a051c0204170d020316020f03030c0a05010204090614030709020a110709050609 73
    0x103030b410204001c0102c1c440c68405076a00508868440410000b0f4810212101c0c901d5845d0301589100d04001e68941280d40c00d00e05141c1e05940f11a4411002d20010481c00c0c044403c001542d103a0000e4103441c08a001c00c4149030482c5006012a601070050202243c0d91504a5054000b810300c0c0e04c41600700c84075911030804010850074523100358803000d51401c9410024000000881a102c40b1802a00c0400f0106407254045240c81045c2099003062210b401e00c1131040741ca0720030004680c181d40030045481c020b0005000ea20411041d081400408036144081d181001c000c070074102521034095490755510244486600d0103c43c02c27030003601440f039484400c584000240c0e480360320036002d200b05400c0d280c2c0901c4414841e190360a90540030070406040034201c10005800840d10450005961360710703103500c1c1c0c03003141e40542104500d640502d01e03444899400049140070303a041c40c60f0050342d4407409002512640f0805900603000d01649000049000066010501c16082901d200c0002e9440 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 575141250 1250 575140000 575140003
    0x6030608010f06050a090b0a0f0905071106060306040201081018090c08240a180b070e01050a05190e0d0f170301150f051c09020f01050c031b0a150c03060503 69
    0x40d0700030a90462900241008091859001f074440c501014000048050322408203407130001c09908904003181e02e59003403290340c2d42c0c48002d1640040b00c0201034141d03800c141d000280c0707030b20001c0d0019041141400108011404150307000d0000c10041c01100b01c007000500381c2c20050b00341c00d01c040d82c40c80b002c90f20025800c1c4000c511208030541002d80300885071002d07216030000c0d020213000d034a510b598070000078500d900850282c4075100e0041c0c40c5034400340340003100100115040b811081c1040014014070307664540210580b00b240c03580a00c0b40501032000501103941c0e501d000c4580c2e500000d000b103402c0030310400000311150070b4040d030120380215205104060892200b80702300e000e088c0706080307100701c203a01c1040f045d8885040ba203000f034649090096060846204464041c058699811100c0d04600d00001001180391003820200e00b08012000401d0301ca0041d000301d014030710002000b403041417605000c100b61042d0b100c100242240f0000b242900241070364003211000c20b14100c00810395190 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 575142500 1250 575141250 575141261
    0x3050f010c0503060102060a110d02040b07060e030f070204020c0f031c05131703062103040602241b07080a0e090a09110f0d0c1203020d0905010c11120706030608010f 73
    0x1a0020109600c2c0c0c9440e4400512107185640489c0c1000d210061040070140000c1c801041d54242c25500c039200c03820044119268080c101c2d0081e4820404280106601819a03061640440b0016194940184c8541c10a43c00720011880b5000004402c8441d28a100f00e0030303141b0307540340c00c01c004c960b83d010f640041c9415405d00c0500f400754130403001c520b030444147c01035502075400761002c0c10300050b0250210204034400f22010803a000803a00344000d581c108004580e00b0f00050034026000700d201a00c10108602421080c1c0e2810824054421803d8200072110704a501a0006503034111002c1c0007001c6032100d0032013a110302400004200489030500403c455503401807a00c040030342e401c03c100b1074100070b0041c009801c000700c0110b042c00b00340c00c525400014074035400c0700301c11040c15290080c20718801444603424003c003901c083c44030b40d034404590407142d9408107640a0360b00707024000030700703414000d945120103100701480460740d280c1c160071600840b80d6200082c003141600c100440241c60 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 575143750 1250 575142500 575142511
    0x614160f020f19210f1b02180907240e090f0703150f120c05090919020103140405011b02032701170127020a0c030f02100603050f010c0503 61
    0x10300903141c102c100980c00c1003403600e8034440c18070000115040003500c01c0c0121012041000301c0c403020b45d410322081d000003120030640356840c820600007125038005076030316034a212140c030104040320000e01c0f805030401a0001a21034a280c080501007040c524001e070344018084440041c2411400a0361801c019005c0c80c0604d14409407000c86503582c0707104500418114800c207071986a241c0c000204c840c80310328440040e2411400d48030740082907003071145c07824007644d0005004e419000c08021103c4000700c0c582c0c0814122030b00c80700a0104600040303000e401e4000b18400b8900d907650600c0304100c415403104000402c55001c01c5950200000245d032240103014180b021a51801c14910490701c04000d130004242050403c002001c0000983d003800c01000d802100b00c05001d01048843c2850f04e042203004024508025071401d5510f040003880710180306402418031a00b040c1c22010076000344021083c22102c90401c11180356a4101640c0e58100c612503005a94079001c00e1a6030705205808492090 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 575145000 1250 575143750 575143753
    0x102060403080411100903050d080610030b03070b0d0213081212040f05060705120603031e090f03010f0b1305010311190915061205071b0614160f020f 66
    0x50359907450a6a0300007008104a5005400050405003030780c4042010400c6a21036491031400c41c01c503e003043c81d202c0a520910b060103c00f40400405075245940503162200914000c910181013002103490103901d500910020f9001164000101140c1c0d400f0b0103c95040f404d84450ba20354400e23500f5200e2441d6542c034120710b030080140d101111500214036800912440d214810f030301c0c490310f4440c18030006840f1100054000900d10140010351042d05030441e03c21000380d454042031100781041075002e00d08a003001c6da0003003140002c6a03990340b4007140005001d030090002c1d08018400380000d01808041c0c40c4110895034900b49108010301c0b07030f203058030b901a032490703c1101004100115074003000085008032a2107030780403c1c00d07030813806180c2e82242b00042c00e64030607003000c0c00505071680b07140c02d94085504d40780c01c2020440d44814184c0d010990f081c2071014896040c00c0c01030150120388003822000d501ca50510501810b030f8214003c0c1503103207503100801440d40e400304071380325100c0c00800c1c5400d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 575146250 1250 575145000 575145013
    0x4030c060b3c090a020309060f090d140c070303020f0714090c0921011b031a010806060c06161709102310030201023919090504050c010305060102 64
    0x141e0000c481c42014500040c2c0000012016003400114100c1c0102c0301e01030010f4011042c08044d5004203c000e80007420301c03144440c549440d0020381d644103d246031020402035040c145401d419590b0045503941410300d01610704050b10781c01e010b540c0da00c03000000c012602ca0400001260f1030703407040840c08203038000d0544105072210080480f8507004a00320b031307a00a00c2600e5066211221000c03004ca42141e0308004226154109007044c0d0b0035150a02d1807090600b050300030343c119a144614003809000900b0402c000f0b881d40d001040985c092454180302a102d8071041c8400080c45140408000310290b6136458004100124844541001e55010105038881040324164899907045407401c0b0440071040c40d542007807407c9540c07158505036860090804038040c180150350b8144029206004c0101c0d200b200102c9a8a5003048000441d2511403610827030321180003503549540b44400c0241c5143d03c5241169100d001c0e400c02840d0a440880311031203002c0030001c1c90350080c020588a41c0058001e880c8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 575147500 1250 575146250 575146309
    0x708060105030f100c14030a150e0411040c02071a030a0e030c19060f2c06010f1802040b280e0a290d2f0f07050705030604030c060b 58
    0xa00000c030704171418800c3d00d0b8188044000000e02852040c0d00011001c2810314140c1004e00000d412900071100f0b203003c000410011880c0251000180303c1c041d5030005c1e1010300228100e0820a064214107001c9400c1e00000360003000c0240510300130300440c3e1040116078996110241c4d244180100c50125802c180c120747d02d15505c0601400540d4021403000c15250700070000d40040b58100c42000428524036213000c03000c41d03510f20074540312030030b082c0091480354100400c2c068088294420081c200d440c9503031544201c602d03901694001e011020110f80c0782c00b080c0100301140d1080646440c201e141c00c00c903040441c1c1c4502c80300004a04c024026840441c10116109100083c042442c0d000300b004240709411030220000030520300e00400c81c0024410310350b410710000e500e103000c92800ea1303030702d007901040c0d410850100310385d14800d100f0416a070340d042601c0e00c075090012036448594103000c0c4000b00418180c001540260380f600c111400c0042150160800c0601c00040001980303026a5900700b29 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 575148750 1250 575147500 575147533
    0x2070c0b090d0308190630080f0c030910230307050d020906090a080618070b12100f060c02100f12240b1b0714090403200708060105030f 60
    0x82c2c00c8083d020701c08200c031209909160584410380c0c401c04954284d0400754106040006540c010750206001c1040c015680b83c40b00c208e41c0c0990308a50111000002e109011184100100d07070760920050f003001c001104a85014000101d100a440400c9541458003001400f000c011030340300d42c48a4449038140381c09031480c407000750041c01c2e956400000403c0070711010f80d260243c0350000d010500c020829031502501b2958150000c0c00032400783d500c4010240861a0740e14203a40c0e034181d040c00c141c411a03490b405c0c40324903c5d03280e030310601c86400040d0010486544c0854084406070080c0ca014a959540d100d00301c640002800702c0300300003660b03550110081301168024450200380740b803107440d0204440e120b10713059004551000301c08082c0003c05641c41000e00300c1d0400c02c02d0307291018246192071310800d1158113400b00641482003400500007402c050260f1400284600c81828650380b5002d812182c560310655806240064400c1d9400003400f89400901c0030a80b40000c4050440c80e2038160303011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 575150000 1250 575148750 575148767
    0x1a0402041d06012105151906060c020907090f08071a0a0806280909050c0a030b0103060e031303050a02010207150507200405040309170c0a0e04020a09020a0302070c0b090d03 76
    0x94124134020521040442d80030031003100c40e60035012000800d03040009951150310254800034100d40e0902c4800c000c465042408141b0041e01501c150459640301d100031510740b4074903000f03490700541d04000403601c1c050000f28001a030b141d00041040900d8840f03400a11130103105280000110284001111802c1111404a00018804803c8425170b2450300341c1c44040640d41000c00001d5482d40e4a0003403000401039a000070100356a851480c0e421911070312410fa205000144c401602c1d4100f03c07854120404c00c40790254075018100142030b0302d134a000c0d5201c030400c04003a801440b41d09408542d4908188401280030a2500e40515208040e521002c04002007804c40e10005a0024901b034aa2150300810b40b040e4401c0c0c0d41c45000340d0070425091200d101c1d5002240d10f541c1b1425940416484d80740341c14003500e00243e50b031840e03039681c0d100040c1001c4507a082111043e0011a840071440e406030041d105491190100100302170f140c505919040c02041d040607800703030f0304c0c1ca104000309020fa50300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 575151250 1250 575150000 575150039
    0x30206090d062c0705120d05030405030f040f03060510052206030c06111608100902041e02030a0b060304020306040f14030c1b01020309031b010201091a0402041d0601 73
    0x2150407202c21140d4603d0407200c070f03d9426803a0440c01d0b05844a5800d0000c1400340000311003c0010520f484103417542c81458481d800144080040450140030b0100251080c030001001c07801c0c1d82c2e54032000d081181c3c1809201c12200c541c101800300b224a40d0040f9520199080680f2010005c40e081021504134002d80c65240f034165503451007c4040364004503404040d0140d605d92250310401100402c0c9400582c9d9101613400105a6050010304c5021a0100502040700c1000c60b1141300d0340000b4009150300c0d000c05540402e128640c52444c10550085c510072080801e0401c440051103007840395500c0203e85c002d50540002c00043d00083c00703044126409401940326201c002e030855200340ca103521840042c282a44001c00c07110b00d00c030010f0b401c0d420540080c8055401c3c40346003030109980700d0344808407902d101d07813807265082e85034400d51004840d0f0381c0110044101c0b44040c216540c1030102510243c1c0170701d081001800706100c3d44400c1440345201c080090102d43c1c6460080c0000c403052800 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 575152500 1250 575151250 575151263
    0xe01020d0f050d09061802030c0d120f12020a1119110909070b0307030b0310090201080403030c050c010204031b060e060301030f0f080705010b19120615090204171006030206090d 78
    0x101ca13804240107204811103281c64480039503200b0040d004043c58018460500ca21030f04006603100002026036601002054107030038084507400d1001e509603072665a103500d50351414404241c0c00d030314651003071481d14040107181c1035a480c141c0c00c10b004015a040003030090f200303401820028a0a00340b618130540d00c115901d050f5031003141c07128a400803d40c4152541c2c80005d49440c8420118941030020b142c2c00000d00351f0401030413480e1350000e4440c2c3d00041015040c15512010042d401e80a05c080312100034010f4000c55a480c0c0701e18001205103034500402070100b031898000314103203006043d4404124001014142142e2035030343c950f008581d40d41021103402c500c80000e480040d1408024001c0a4894070000c42c0104500041c850310051070b08541e505200071311802c01c001881c1c030710528079054022401103511011002850036a02155002d6038072144001000280c22510386948200b4440030b009a0300001110110081502c2035400003944c0a0400c00024186e454585440d1075810312034038 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 575153750 1250 575152500 575152511
    0x5070c1505091506030c060c06100b0901080103020409060e0d050a0801080102031012030513030c170735070308120c0702060a1b0213050a0c0203130e181209010e01020d0f050d 77
    0x447c0c0380f60059000c01221307600078000e02100b2100da4072803c010f00000703c40203091111201c002411420180300282c011076852055505104082d045921400d202034110b07400328036243e00c0140940e00060b00280082c0c154030000c40c0680d810300072a03004440c6220303c01e40f01414500e2980b8104803402c011030030b110040103895106401084118001c50081161402d02450a2203150141400d1500c4070003035048100b05002122800d02d400048030010a0b24400b41040c3d021002e09064602c0c100c1d19051040c4040041004000e41c02003d081b11501802d0001e174865081d1100c0380d01402c000298001c00500c001880588140c03881c49022207440704d11714540a183e00852500380480085a88460312101044803000241c00b41c09100106803005502d0702d0080c555801d081c8515006684150b030a500c0440c022403500014507404414160988000148203040316016500610340f490105a4140d4410102d60010840741d80707803082600c0394948030403115421a01580708202e207008182ea40c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 575155000 1250 575153750 575153773
    0x10f030b1e010b1801020105040218090109140c040c090806040201030519051e0702030703140703020a021003020403050d050a052b0c0201090b130503070b0601021005070c150509150603 81
    0x74008180200780d5807248964030400c80d200b40703540c101c0d030f020110f05580c10041400010785440040800c05206500300e420241c4403d4040d6004d8404414050306c0480c1491501c0848075004c610001c4030300b011101000340ca001e11509540b17020081c030440550343c100388001005940250000c503440703031020f02e004500c4200c1c3c0d4101d4040b102c05481e0302c05034034040c56040318550a82c0c000b03545c101c09a0300040d401c00d8001c0e500200b54503840302114080e080040340300800c143c02000392160304c640c0240800804032000100500942003440180d41c0c0c0d100e070184903402c02e0300400803241c0300392580c4e44030b07442d00c00c10100c031811074249025400094010480c0c11040d0046500ca58160036a440e400410400c100f400c6c21701c1000030181045c40b144060043e1080007640002c1160005544007059405551b1214010317030402490025420544c1d08020821115544c0b0111f000e00d0740380700720601048613019005080031504200c408512540c45020500e414030312402c40e0641c00140101160f040c60b200 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 575156250 1250 575155000 575155051
    0x61709031608070b0c0c0d030207060603020a031401050c0a0807030b150c0a0b0a06080c131e230c04170a0c0b030106200a11180f06040c08010f030b 65
    0x8205446070400810b444040108401e1320070703000f030001c004141c00e00106007a8162501d540030b0303801c010f140d070001d20402081202e40103940115001064070340010fa0724141141c4540c1c030041009081c2d403034a000108a8030440003a101559481d40d180412a03a885009030010010307108819030041c8a51000030100c3c001c00300801070b815103000034020030940c92610240c588006070042001740e0500206010f800c10001707140c80602c00403202102030000311060f8200410032b00b8802d54121a0095450303c143c41190012401d19110402701300d0034403d0381d01ca01580900a650450603071104000c200301e030055081c52000d842c103022094803811000b541e5251504035941d07010100d51000800100181500704078810444026808401e008005910b030b504e0310364a0300200140000c0d042c105440351a2071365140f84080025900540e007183c140840c0c140000d42c1e00301c55070782c49141046100c00e1114030441d2028100d4469040380c0751454250b50b107110070b0040003081401c80c052109035908100ca40d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 575157500 1250 575156250 575156287
    0x50f0d0605041101020106140d06050c130603060617070909020c030903010510090b010f05190e1c060c11060112050a0503070c210317060301060f06030f0b030706170903 74
    0x11510743c0c003000300d16100029003500c0c0c1a9010060300f05d0500700000c0103443e8480c425683d00c0d4004400904d40d9500711540005002e02e40500c00c1ca002d2204000c03800702e8141c0d00060a49001d611200e00700d07100000c95440c44d190488a40c40017407000b0328200b00030003964010b0b01145d1070f003009490401106030046070031514110740e451100c0c9a081c000304a400308611540024a00038a400d000d910082d000280203807040701900c0200c0c030078907040300100501c01d00800b2138040d4000c02410002c0c40d18818400150070f40c000070355602d03290540501049018680c9203921617007090183c4840e80c81c225552103104608c25058900e0302516100d080041c00034001400d05621071050002501d080441c146aa481e406c5030005003240c2501903a808260000000c04501c004903030312990a039190808280035002c070b94403081809803042404079082d9010341000c440d4044070b100c10003800c2c80b04400c1690796203451090780041141c0507407418064092240140d849614203045918107036422350ba02c0410710 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 575158750 1250 575157500 575157503
    0x80a08030901144f2d0803040c0509011203090602030a0905130b0a030b010603060905150d0515240d030e060a03200a021603051b0d050d0503010518040507050f0d060504 74
    0x45041031404000d801c5c14030700140c0c0b540310640c11030403c1c111140c200004c030a044c042c00039180800050100a00c2ca28880c000c1c00340038000c01c0083d41c0d110a0610381e69500301041b80451004240071440900c004141c1d0340600c03450360b0380040207140c0b20074010098050702c0140381c2c0d252101100a159121100d014008500ca03100d4001c9a61404000504944440e0007140b81c990500081c0520036444041d019080802121211030210503860312602e4030190018400b51400032500f0849900d1080019200c0307150030261160030100e04030300f04440591b40c904c0082c04650000b02c00302050800b031002d01000c400c142400101c11700c2c3c60b04100040c030829840b41d0301043c4001184454a0340c1801950342e491413154200da80c1a04640d42c1c42c8c1c980040f0050b41c800005030030920205551000010240c0540280941c0c135480c0218030003d010364000d000b402d0050302013044002448010360b400510135078025004d8204a41000c0c10800e1a0604040345584425809052004180349205090059 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 575160000 1250 575158750 575158891
    0x50406030f05060a0501060c0b07020a14030a110609030417120d1e150303030b041418060709031e020a051002060105091803030c13080a0803090114 65
    0x5400700d01e002c901d001c0000303000b0748080c1d00345001005400e41106051010300e81c451618142940d410400302d00d091b0100d180541f104071408840f0700c80b0b484c0800200100c036440d0340d0308901d40e01d50803800c55640b803055030001c00e0340c0e004006c10806038080c0d2620610706e0620609540383e9510f404103410003500030321552212556034201154140d020650701103059500903400b80070320b03030302d0104c03146c25082030344400340a250700c440c20748116550741c2d80510005031070240000c1240c10f00c025048559100341d08980207510a160110740040d01440e034140c21203a00070400b000d0186d89804039081010220012a00000600c3e8040303820b07a0343c041d64003040d02456008000644c0340c1010009c0f00900a03120070888000d20f06000c00044000c000c8a41c0140c004840c0e03559850100a24120310400d503001030818094102c414080003200030055001b0142c000081c00046410006640000c4050ba480c0540b108041c4a000b0030440841a10380101f4401e60080c0d81208040b071680c140140a4000c0300c1c0b503 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 575161250 1250 575160000 575160023
    0x6030705131e0e0319030b15091e0a03110a050d05060601120c0f030b06042411160e09010e010c1112070b0403120905010207060e0f06060901120c05040603 68
    0x10744882d07800180d458207045028003070070b8000c00d2030070703240c1c81000080d112094044550401d210301a0308205500740010f40681042c0c0f070f60103503000d1642c2158041c28407a00c480507240c071083d00b080325144c0ca080d10080c900714500e45141d44038011085012a8241c02500c40301000070f25640d0301c5110500c40b801070b009810369103002c078001400c489403003440b0b0801c0da1421401040603a848010209030003000d040c005007101040340026403d00940e846110b903020300c52801d400d11407030340184d10082181a1140800c1c0d02c0c101400c00e86842c4004103c031046903c0c460304019042c103000ba03554000c844400002402c0b0724032406070342961300b40784a09000c650103201d00007100302d040103412102c2040c024a9424070342650389035080311401604c040d003000b080b509200400580c65001c4010990700000856403168640740c114081c00140980803002c1c01203160750700d484ca0002c03807481e2040500800280ad141e0904c3c440680014032481c1c21b881d01c00c051400411162103500c546005980180f041040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 575162500 1250 575161250 575161271
    0x717030919060c080708010e070e010207030f050f070b1213150c030b0a05040203010f0605211f0506161e020409080d05180703030e0d0615080d0908060f0603070513 72
    0xc04c0d0241c0b0b41020441003a0040000c1c0600004c00364101d18249801c014034010170b40100d00d80707180303600090120040c190761401003100000f8412501140001a1403140b580e810540c0b01c640100c020b800387c40c02400b0f0008403020100c00c80003000c1e07885480303801000362900410400b00d518402040004c00e07541c0d001c199407890b01030350502c000c120807181907145606100b4041c0040d1154403828082c00408200301548000c002c074a00e030b0105104444054502d814840075146202e681d18400c40b02044079400f045d00c2c22310600701c2c0c111202403602084039500c981d90310940c0300104c11a0f40143c6c2200405580180d542e070140011050203400541d84070f81840c03003805d0407103030098644022801c801d0480e042c49000401c12030100d0b42c050428040320032801d0f0210301c040000c148010001407034521b4520100700f0f00409603056541711b100b202c2001c0480b8405698210460080586642c40b00d0002000c5001e0040d8032513012402900b6039001968800220703901c05d0760f8a685030300035500d0f2011070380c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 575163750 1250 575162500 575162507
    0x90b1e01080a020619022e0c03090b060f010504170714040b01140304060615081812040e06040204120525060c141f140c0717030919060c 60
    0x18054082000036041c180384070f5001401c184107030043e03040c05041c007001d0114420300900c00383c1243c103044926040645510084070149205141c14940c40c0c078544040007c03075070b200e48210041140c2c01005144191520801c0007a8000b88803505810800100301c0031444424030f50703042c40ca1000c02c4004001d102d0820700c0b00ca03c02c1108001c254040da10303100032801e4a0f0f900c10312004441280080b455a2511642803280c00780c09160009070503000802202c0f81440d030310100b0706100d00485512101655680681ca9496041e0000000150714040c80b05000c03000d100c142d06504000000d00041c03805981c4d0407036501d0001281c0f0305585a801ca13440c008801c0950400703507405001008441d4804078180741b800b400b690641c04000d040c0706108002102c00020820a1400b8640081e00e00080301e030a105000001d080b030a070025080320199400300340440c03540001c0d100c19540c080313070141580c00c005c0e240b032540b5000140103d250b4414140224486040d0700f03408070615025007008940c0c0400004083c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 575165000 1250 575163750 575163811
    0x5030c0c0f030f040e0124080a0b04090309050112110f0903071e0f0812030f0a3b01020319091b060519050307020a030815030304170706020a0c030b0703090b 69
    0x1c00c09105840034800c100b60087c0e4241c20b11015041601d95a100d0170f1154004086464109421a241c449910207041d0854071020840d10f091740c60b0380003d2400300e0251b0907a51459030b00000d980c02440390040380010500a852280000f504440c0c045654080d440480b0041080620340081c5001c400e2140702c40f028480c1024007407160040c040c500c0c0388072014003503100c010071007040d40c07080c0760100d03400303544a4000c04a0383c500d0388260501c0c030010151120701850700ca0700700000c0c0510b07034146400c01030040c001c1c0c4e8468400c0d0121100c08403099a54400a010ba200080310310548ac484168416041c0c1001e50014000f41e40d10640c8503050030f91509001c40d082c0310402c00713000050007088903103680024801c0c507880d81441e0420b0b03561501c0d0f031100d4960340c02030282d40e0b040c0000326000c60a184500310001030714004a04891045680e420281d884039a5148098207050040100780b000c283d084440d41e8000c20180b0300001c2c1c818440c0c503404050b10080e2142c203082d18013038817070039880300e8545010f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 575166250 1250 575165000 575165009
    0xa0510170303010b03060d020603040302150703060321020106080d0c060b06030603030d1a03010c02030c071e0b030c0d051503060709060c1e02090c070605010803040605030c0c0f030f040e01 83
    0x10114001140e551941e0b070005110b002c81104c0000001802926a243c02c0d00300554050510341e220309103031802035214800101200c000708908000540070f18400d000302d03003c81e41c118000100e000e541000e5404c04c0501c0386c4c1c010b0159903e07084001003d91081200000c030403201c3d139521840768102d184c81800d5403e8504203138801d40082c41440982d41d0701104441c420440b140e00010814a00708030180c2c0700d40c40400c060b5255190031901c40c02c65802200421814418005540b1650303216001231215030304403000010b054000304030034080f1030b0f0b00300000c1d900803e40786141420b041c4048811020b50303104480303408914202603004c003080d080401146030000307000c3c00c10000290411800501800a944010b0078104005c2245a400c01c0658103c028a0b44c0152140f40c0c030745400c0b440070b5017a501843c4201c80b00c0345440c000059005022050301e0a0740c450396a000e03c1c40d10b4801c05980d507600702c0460284640a2a54002180d001c01c00003451991300c200d00b1039807140d01c1c18503003010300c5030164031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 575167500 1250 575166250 575166269
    0xe07020c0a030b070c02030a02060307050403020109050306040b1b0d0c0c021807050a27090203012111280806090c151210031b0f05120601140f090a0510 67
    0x40030b00000310242c001c0d40e44500d6500e00b246141c109800000d182040c2490b019401000000c103100510303504c64020300589000380c0710b500e0b2240c1d03680c007419507907402190042c02e902e07a10004200900d25001c0640026815610081c0c00d218482403403004407011949400080380e072003076400342107040c00c020101c414090707110990140e00d806000501548900c400440800515180c9034401c030300040403480a0390303812030159101070707191259a0b00a601c0bc0c0036030252056506102e060b000c0c40f01524642040e030048074510070700400320520001840c0c040c08d590500281160541348038008204a0000305224001020300d030a00100c802d0612010044460085010328100c0340403009a400300c0c2c1c41b5910f1600101080d0340c95001e00040c00703030550401005a6038000a10b0150020a030100007565414041410f01030381d900100100c040b841c41c142465a00800010442c8041d940094010410040d04811752240d40a00003032402104481c0fa581c0c5c95514400d0059000e419200032000d81503c00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 575168750 1250 575167500 575167519
    0x504030f030902100e060d020d0e0106050d080406030b060702101206062a0501060b0313020f1020010e0a0507031707050601150c080706090b1b0a080a150e07020c 71
    0x401080c50810b0544d401c00501c0174803c048801615950204d418008620710219241c4086a000c0800781c00c122144590311f41c02c00b00b001c6a1403410421141c521a0300894607032a040c074144064000d440da0803002d0340d02c00c0c410f20000c0050b03104c071059100d500c07149036611250034540c40710042c01c0f00c4698100b5000c10500c0e107040449030a6000940d580b0048102c0681c0444500385030a5000d0611504800b41000005c014403400094601d40015194401c540e1800394180304e03004e102c0c0d180c0c1d1134044000000c2002485016026010390410540c250b8200081000d00c15500510f2a01a2a001c00c817403686c0091810000c0c418000c0d004144820103903111450100943c0350b440d501c8134107025044040c1340b546550854640121840201c1c1980121541d031904840d0400324000c003d010710030b035008400b042c000317150589039003a51000408111842da06140a07000b0848a2400081502d0802d5a0340d0080710744051211180c8001007030300017581c0345d60340341011009060034046815140565070b402c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 575170000 1250 575168750 575168753
    0x2071506080c061303050f160b18061e1308010f05040b04080d14010b030702060a050601091211090907060219020a052b03050309010c0c050a0314120108010504030f0309 74
    0xc01c00c0030b0302c034000300c0380382d5129608914100101000d0f540002e1051003203c8200850b510080340300141d25a5030940750f8042e80c0c1d100c0d04c09981d842442d07034495100c9407400705890300b45400c4001d40031565060040043c0c03c07925030300b1600198820100040c640d02115402c000c24402400b440ce00d03504942c2c1c0600c4a400d02d0341c0c1e00303c0843c201400080c00301001203600d08100543d540449000031111055005c9940d54480c01a0191b0050798940014011040054145002401202c2c0902d1040e5101008245400c00340d15841c200c80c54100c4d940480300c0b071441400c5c0c0d65080720758003401094000e402030503d02200680b901d4016248070100c04a007240e07100250352229000d008481054400d541c0405100d200c0d5441200b0310051440041640800c02061542c010b02451144104c0c40003003000d44841a000d4540b0681840020000c3d4445000e41002038418031014000d003503113044203810011940c4403259041c8d0309030020ba0490b03654004100901d90b102c00000150a42c4c0d080810203203215 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 575171250 1250 575170000 575170003
    0x1f080d080910020708030604061d01051e033406090905061c030305040302010b01181a090a03030302030403080c030910050c220807090204080319170702010207150608 73
    0x51110a81440100000940c085000740050740d00b19400d040304541c0e842d81480d2500181c1c2085d16071700e002c0c07890054003049800542d2886085d00020100700e0080b07078a040100240c07042c0c0500a00390420a8012120f00e549007001003a00740380202001034024a045080802e0540b000e00d02000505010407080007041c4d081140798064502085010801365641004125030a18220b40c0800d004080d03400141403561540c1301d0307070243d80300c3c0e40280701c0154080300449021039102d940304000c038070f941010019100b40f1071000340507044094a0b03600304a126000a40c4031803041d031095012030b03000001c00081540c855170066102c0c2460707034880d0440c01c105060320394a14604104000881c0c0d0340c002705405041100030f0320702c40c1c400e0181000b4031b07000c4100301440811042c4203081c1103120301d580c00b00768262940291025906214011800d2244080b0011031103500160300700d061001c0e05100503103000d40012030782e01c02e0000b5000969240c10714a801005480080c2402c10034070704d400070a0186180 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 575172500 1250 575171250 575171263
    0x210c16051e0102190819050a050f0c010e030c0a1406040c050d020a090e01151a070f1a04081b010b010210090c0e0114101d01050f0d050f1f08 62
    0x85041100005040800c0142d15003621395102c030348400740039107155040104210081c5038225400c0021b030100403506500ba00c1a00030305082502144007440804840084003004e0b120b0159824004901407107107100e42130465200402e8801130ba000200000103000c1c0b11403150200940000007020103242c00c0d00d0710003885403180981c601c10b8a512000030b080d9654148880040d0080305400c009500c54200118003c101d064074075520050001c1d8005079110a90b840f044210b80c100714064500030712581c517403c0801441d241121100c2d024a16080c003070740150304003403280e07100c0c3c0d192507900c058030068500b0a051611030340889a052242c0c080c4582d03404503160f40d00240e80c0d80301080420700d0740b60149042500b9001015280401400000c00c008124081c1001250507514503200da04840740c121060840d03c0350303418101481d141e00c0d02030303940f04034018210001e050f810241401c40e0202c528060701e10690326441103014940a00124100c0000024041c40400455050440c03408550503101c08 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 575173750 1250 575172500 575172529
    0x9020703051926091609020a0f030605130b010203160f0606171e0c1e0a0e1014010e03030c06250e0f1c0c0f0e1504050405210c1605 58
    0x201c100e8081100d1140812017040180c140b41090070445495580000c005d4005025807030004030302040e189803d60203841000c007541d5028018069100000202030064482c90340e1050451004004030350200d244100c40144841c410106180141d4842c10141b041d90720030303003200c0b2488d800c00c02111202100040c010200724111425540c7c22820000080d084c92070b01611103422950b04a5280300d100c02054840208c000c044601d03541c142d03215605c0c3c42c0140001c592180d0161100741081c00010b0301001d090201000c1494020310b0240b60310046411500004098215584648103100501d25200c0c0004031142c4c2518600d8108415500300070001c80c0b0900515000b03c0c08800c615002d0789070700b00004186103c8010025400080d071815040d048420f109240c00f03d45018004034640c005110083e010341d51101b000303908801860200300040001420441c4d840c4a6860b41d000d107940e8102001143d4043c125440d925840e8807903403d800c0ca02e900c2d005100581c00c025081c001139449080420303040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 575175000 1250 575173750 575173817
    0x512030315040b060a120509030304020d060b0f06070b06010806030f0c120a050105070216050607030e06090a181e1b0513091505040f0603020a1a04090207030519 71
    0x98002000b090080900f20040da8000c08009909001540c014a0441c180110200200180c0e51402041a10380c007054500170350003030201c050000403c24641200007a2070009000404130b040f03081c005000d6511100e001c403689020710041120035a0044403040c0c0c001e4040e00603042c1080309010840c3c1340c10014000500c528140d0084043c080c0c0200300082303840390700c54020085400c0c2040003a6403800c80f1003030600c1c0701301e0b20b0001041c5414000e05032007010343c1c161038064a20003900100302036500200d1a00e60000f0704030b00006000100d403190b800c2c4602d000c0300002130304140040d012210400c036078442c1e94010b0515003422154079145900103800411460480d80300c203030f00c5070484074048045d0320112141381031141d0a040540086150411038030103c801b0481c000408040600f03070740640c80065446948034408116881c00c1c074056583c1e80c07100541045c034058484002104a0b004100240e0000b503000c00e05c0d1010100d0b401402c0203503202d504080e01d2402252178805008100d0713100e002c150 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 575176250 1250 575175000 575175031
    0x80c190203091804050f07050102120313021e0103060501170a0e150f07110a0c1a0f0f07060b0a15050d060e16081023010e0a14090105120303 62
    0x414401e0055804050340280f504008001111075483c5207003058506540ba805900d088101d001c0d0002040e01c12514103030050b19600b0101840c5a0140e08001d042e07070f424000000984006994010320f03000340301c0003203101074050003a00000404442d06900b04606003c00141e0224030894000310301d503402006800045151442e58078103508000b007003000003070722000040520403078454000809104d59a150307281c8043c6120501903a42e90741b80e4400207000b20f89841e00c05d000c21882c00628590381c09108945034600041262242c4030ba502c5007641c81300b40d0401082c11020405503024052041d1001c031500c4074950b040c180035506141446203440144000080c400c4c02804054100f140149510f000c0b035001441e0405d400b43d2030b40d400d88903100004503d04002443c010131594400d06035222081c0903010710350381805582c1007030f0740e05184a050004140c24129203903030b068000c10181507906a0395071100c07101e109100006d401a00001c0c8104000c1382c8802d01402d0010075a41d0080d22030b40d40444 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 575177500 1250 575176250 575176297
    0xb0a050a1a070f0804090b041119110a030305090c0d021c020f130b030d03022b02040e0907080f0d0503191103010801021201081501050d0303020c0a03031a01080c 71
    0x80d103218210b001840509188a4002400720742c5000e0b0045030300c4030301c0501c0b07030008500811085070380c49900d000400c0401c0c0540e1184200c80301c62815a00054200101041120421075203018418482100001d07107810400075041001d00c42448100310580b41d140341030103258001201882201d440c50144401d4100c40401e650319006522500c40010b8101c01512141c0c8850710003034569012814001e2007115418030503d0320030b10840c0d5100c0c0b1002031314000304491410303480b10600c0c007079003001c40d80d9024000070a0b0005103440560060220800401c1c1007071411403280c0c1001800100b1700311036000480c51221194200d42100c2d84018043c0c03d2140908040c580c4000170091007442c90b0f4030324401300c0080b501240550040a021300d505440204e01c0c0c2e80d8402d040d50350718203201050380c15200d00e40100011f090000340880268400d050160902c5034a0004616094284000364002500c071541280a03540241014141400070b00e046c2c90503207441c0e05c09406c1c610800f604001a031100008402 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 575178750 1250 575177500 575177549
    0xb03090a110a080d3603050c0d0b01060c020f06040608070f080c090f010201020d0c080a27060c0c050d02150a05061e040207061d0f0601060212160f14010b0a050a 71
    0x21200c048001c05170307180500b00c0d170980002ca140c0c00b04603143e01c1203140f2070116103006401071890960100710b803030301682060b900311181c018101080342c200b070550391003a6080c1d440d04050009011595940e0725a450000740c028510401d40c0074000a0210500038006140103c0c421164004010b807011910b00c030174480101d00a125180c980315125103001e0483e0541e07a8490000c600800016405000010f440c103031620301d241004610640301511001c40e0400500181c10400e02ca009a00349105e00d140b980d00d85909103030040000c48c2c0160000165400552207000d0782c40d40150400004009074648400810718030030002000311901d02d0103a01400e529a1540c040f01d01c6c0b5a40722500b401003180081c2d541c3d88028200707013407500d1750050310245002d81000041d018101d80056004080c81083e101d001c5400da07004954440f14102550110340201d0585040c80403454804d0781d503030350b000c401002c8103400c40307210401c001d1140551035402c0000e40d955600441c281c0305003140003030100c504551000b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 575179856 1106 575178750 575178797
    0x301092309071509051f0c08040e060108150108041b0f0b090f120703060b060d020412050609340915030516030803130201090b03090a110a080d 63
    0x5007aa06c00f03c9041c0800d42802c0d04081007200b0703141c0c5440549510070707080340baa07019522082c4181960701c8188694040c21025121418818042c002808614044e0010704101164080102c0c8042e61081860040888111f484030003a5944d2152061381c11002e051441842c0c26060b03a1100c2c10012104071245031041c000c0c0c42c03e40c0c21a0340e22401041c1983d900c43d0024014004604208507a03c0100043e0082d811080200c9042d407034140c0c0380842c000d2244070700d5000709440c002c861410920000c0c5511026812004154948010800706002e40c0c1c810300441c0d0030901c0d1901c80302c1c49901e1481c152070240040d91903010000844418115a40c40004d1080e103040000070101c07260300c01c500707424030300c14502030b4806039443c0521910745e002600c1019060f0030002004041020107016080e403000b0075035404007078a15015860703480320850f909030000c0c0a8100001071401e010340350721 = true := by decide +kernel

theorem cover : BRFrame.Cov 575000000 575179856 := by
  have h0 := BRFrame.cov_init 575000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 575000000 ≤ n) (h2 : n < 575179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
