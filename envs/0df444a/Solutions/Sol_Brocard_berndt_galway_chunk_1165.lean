-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1165
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:32:54.730804+00:00
-- url     : https://prove2.me/submissions/4201c2f0-cdac-493e-9f59-d34d09d91dec

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 209352517 ≤ n < 209532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 209353767 1250 209352517 209352527
    0xc0c10080615031b0c0d0801060302090f060a020c0303031006090f0620030c0a0807020301050609042d0c080d0206010b0a14180a181103040507030303050702031201080a020907020c01 80
    0x261a000908022002a813000c210002c00119034400000c43e5881c0d5a0454905940301640403010010070074880001c19464030030b10a80300b0540c0010101042c11901406100d03250f40070202550450003889a03100581d10104011802042e00d0841c00402c43d10b0a400140842003030b4005429604005c41d041003c15400100e8510144504074141c5012139440b05261440c0303c1d50f0030300141070007580030b05401d00035804003508071907000343d000307024681d1410100f005004003107a0040011903c0c030102d40d00c084064050101740342c110038800d8801c3d0100c0c2c48804d5030806d168085c51180e4440465482c2d0b031035050000030300529001200908220343c3d010054101d01446e038030301c0031a140108080101400348a00149081c00103014206640c1d165015605501c12500031000c0b09800e000c812406481050210b910446e0031201411b0290305543d000c9014141c050b00500452006010420462000c907800d1802040d2000c01080340714114818405030503001005d02007990007240640701680d801c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 209355017 1250 209353767 209353789
    0xf040b0612130506040b040c050405160503090a0803040506101a0919051906030b030a0201020c0f01050403080f0408010f270228090e0106030507060509040f020c0c100806 75
    0x1c1021101c03141d4485032007442d04202c600703010b011441504144005d0104a11015010b50b000c2e01e41c480308039032294107020903a041620303c0600402d5400801c0a2075100f200550f03001040380d0305944200c0e00a45892050740c0094406a607550801c5050125045083c105070004006810304008050700620b04945070340a0603420602402e101c609001000c15440c922501600c401040392100d0344170180606492100d90040708046840d2507030038102450700040d000700d0990305a006141481920051290705149000403505201c0300b4400480000d5080000e000c080415000d80e80e2a103140c510f180342503070004543c0c6441285007000007103060b0b241c10b200c0d00c1c1c82444018000580d080c0c0384042002c01e420312071400d013950070700c903d114000e000d01c560707500c01c44a07618414010b22005003031f440c4c02c990b0544801066030348144401c004582c0590064040d85900a00002d1490707a000b518074107a0340303c4c210038107403a000202824450f1800500d18000da41c0d65181c04405850400042904d2800c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 209356267 1250 209355017 209355037
    0x308040b030405070302040c0203211915120b0a06050109030b010e071202031005121b15090405010603060302090f040c0b0903010e161a090907050702040b09070e0f040b06 75
    0x8001400c0c80780030042c4e80d00640d4040c000300700b20380305035000a4498001c1000354102000140050b8008803002d941240201c45d03c81c102c0000403610420703400245080480070130f0ba950904030001d104c01c1218148003e80340140c59100c04d82c6010300c41101252203a400260501203031413005d10202d03041c420741c00d0654200041c031400382c1e202c000003544c16003041d200c4030900b1400082001162500c0140441c2102d4042e1440a0055081c0d00c0c2252202c10a44201d2648441c025103407045241c442184000c40700706850706440c1c40d020001142c19034100f45c10030404284c0310b0740208114104203080541c0004c00b604200068100740c0c1c0c4200d00c02c01c3c07502c40c81c00d001202007502d0080d55029880342c20028904004c8500c100100d5041c0c02c0102c40383e2280300c810580d450070051151540d00e040700d80c0b00c4d1008003034490300c0ea074103c0142c6090300120010381c0c0007540c0b00a100526101d040890b1b00400300c64440702c891601d940b003005103803c4001000360140b800d204041c205c6440d90000c1e6004104 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 209357517 1250 209356267 209356289
    0x1205030406210f02130927030903050604240b0907080a0b03060f090c010f142a0115140f0f03010e0604060906060509042f0d14070609030804 62
    0x1002c45030030384802070703081e65904945000c0c010b0141c0011035000304003001405d500340d112590b40e03603484000c40702c041c134040c0b0390400c80400281e41100c0248081250300e2182c1045000e450b2a03495103450700500b20380c121303202150302c411044007202c60400c00e0a0f000020f00b0034085142c080000c60008880904007101780106440810300b50080b58025030200440603007107902501d4100c4800550741c03000d4814900ba8050300c025100194400d000c068160652078548241c3d0342214200300715503078080310880c0010b21110380132085c54130f009482040c04505140001c02c03003000c45501c03131071280000c4d48204101e03001050614003903120000181126030003203901310f409490450119000d09452801c0c8a4240111420001000403581c4141c007124041d14007048500d448800340540c81c1c5080d64050f109544c090f03240122505050443c1804180d6660507a05924007030001c50070500e182c0c1c2c1c040f80c0510782c031180e020241200708400b100820061400c1000240386131100c040e9403146020b00c511010b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 209358767 1250 209357517 209357537
    0x1020114041101200a121b0305090a06030e03040b031f060f090504201b01090c0906050306040b15030a0c0b0403060f060f060c06060b040909050c040c120f0e0d0207030b011205030406 80
    0x40c0181807e0045014820484580f03112900e001002c0c0d9010010300c904c03c052920022844034468412000e44541c80750056281c0f07030510101018542000b050500700710344a140d050032070050210000001c040e56160600f4160b019100506540c8881d0030160141e40b81c01c02081070403158607401d060802000c0240c0d81e5070100000a02408104a41204042e42c02c01e0b0300c10302000300f518608811189008400c10050b40c0b83e004043e103801c8195000b42400400c1004035010107006800c0420440b0014101c41c161a540d9032900c070401c0f003940c000940c860002c501081071107083d00038010351143c0d2400c00c000d15820074062404650300ca0007100f0402200c0010101008041d0340007402520140b68441c2e2504c1da0383c20715002034600702d082100c0324003410b0002c2c200c0341418090320491808039107075084061a03d64a140c01401903007200f00c00a91190035640c0225818000c680018840384d010b03040c11400d50400c1c0341d0f5030b001030388002a207001c210900408610048150707030640e446441c0a048c08 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 209360017 1250 209358767 209358803
    0x429010905060711031614090c07051e0d03150608060a1d06120d0c140102040914100602150105240c1c05090901031101020114041101200a 61
    0x5007908082d0708000c0005542d01803000e45200082142001c030111900c1c1c0948124981500038544038840844103c2c92401e202c1d0324100c540c0d00da109440b01401c509000007910b82518224484403406d20101515050703c5100b4801d0000d400c0c2c1d40fa0314102807040ca40608104100f45005108400800081801254003907407050f10440c024440e828a14840f01040d070b0110751001800d4680d94403a00c02d0100d0010044e01c0400c0d46480892145c907403069003001d6449400080c1c038808140c6080e5582044041490030880c46001c40c124505420b20707030240340c0008601ca40010301e402c80340665100c006100d800340c0c00000310a040d43c2007622516500c034003904580401045540d081c400641c800700d81804101d0000402c00d23154400506020511003c203030f0103440910480030f050740c100455000510100d011910000301d0450180300014000303050300402c0e441010195002c8031090045146803441e0f69000030f402c40c40e0001000d410321100241904940ea880e83d800000f011046050604000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 209361267 1250 209360017 209360027
    0x3010e070507150e0d0309120c021315050f09060307120c030b19051605041a0f0403030914060306100f1103040603020706060b090f4b042901 62
    0x1105a03c5054802d0400303081845001411203010a4441e03071181c0755201e0240c5100c1d0040b003000941010941012400811302102c2144103000e06a0700704200d00b680410000842c468134010403441c2011395403080c104020860030400225003503104070183c0b0144a0166004107510080f40c5510000c8143c00c5040c2c80c102400021540c0050101540c4a08100a00c002c1c50b1174400140580002003140b03a8504038180d034031520500c0704c0030005005110034018a21420100d00c2003150b044600c4d41841c1d9040c07104080c2d41c1c000d0304101d000a4400008024202e446100030f04e091034101c0300345046141480118100340c026556400400c8492100142c4060051401c00407410000090f01d42c1d698071135030301034065441480d04442c1980303070401c00110340c00d5520680e102900c0c0200a1132081c4000030403c04004c540800042c100c100e02101d0055030100302090810b061100d1889404048000390301c521100380503040a03000ba03041107074031004811500740c1c5003c1c015044400c8800c0c25441d400490f5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 209362517 1250 209361267 209361277
    0x915140f0903010c02060f0c0d0608031812030301080307061a030105010b031005040926190f080a0b091b041a04170a0314090409060f050a0507110303010e0705 70
    0x24504000040d0009500040030080c81c009000b50000e220490b0411000c81e5240400c80c0c1c00c450001100c0046500011440010301429200360000f1a2582c0c503940c03d40c1c15940702040c0e00401c0c190030345428000381454145c0004082101020f58150740c035100c089a1030344240c0000502095654200c4508019815420203000e10090020400c0e0340e11100442580c1d401900c4094051411100006003031801d0300400b0750040e402032001d1000c0350a10161544242031f040c80c510f241ca400d020841642400891030000c8410a613290310701c5450810003d4000f82d006040c21200500f403600e80c20300ca40740c0d0145c09030011014102088880510903110040340200d40103040300303824520488414040c80c82c0030780706a0b00d143e80e14241c035000342800240e032840c00750401004210031820704c8048211010140c001d01c0c9002d04041140e680740d0341c968044034900e90080300c0003542c401c01e100007429280b02c1d66a21400d0b85c00c000c43e8950200c1c651580e2404144100420404400009a0301c5441181614 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 209363767 1250 209362517 209362547
    0xf0112170a09051f0c120c0203161a030112030c2402030a051612050a200c0106050604060905120a0f051f0902010c0b1b0c0705030c040204060915 64
    0x16214480560300a00c142d48501c15076200d1040c00155070500300b6289540500814152580c00780400d09540341c14103c01202c00300000d008801c0c0340800546c50500203016120310b829100c25201c0d0500c80b0803c042c0140c0c241c540f00700301c818801030152844404003010340c0da405083c170303501d600c4c50303480d10b0307044a42c1801fa1301c1c07044101900030452010035034000d10700a0408040a100a9555942101d038025022882d18000303000c04840241003205a80240c0c0c00141080001c10500e0800c40c044940001400c10311003040000035075215840300030f10030f050203000221029880c06141600051103603206004140c4603c80c40114148100020000c0010181c0e208801501c00521800c0c155150092040100000c4000803c40541034195202d04070704c1079030507128440018125110241d00c0c500080004003c44154141c0304080545000034003a07030003198004110302410401410300b460604640d0034016801070000f80221a0440059426241c0300c04804c2c00541900717500b22020f4091880700 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 209365017 1250 209363767 209363813
    0x30a05010e010c12020903210405041b020c15091201020c070b0909091216060e0f0c040b010206040b1612020f04090b09190e0c060d150803030f0112 65
    0x455965103064002e40c0f140f40860700d801e10882c3c02c030200401030307111b2a2841c03030303064100c15001c03081911655045981900aa010740b4242910380c000304044440d80d070080e0396405920614480c00981c100014a1030210548244810550344240244240122402c1501c2a440d041c0340c0d010014095068032070781a00d0b0300884024554510b45116182d0194000d58043c80b40700300001c1c0d0b01c0e00c0010b118260315124004030340c940300e0b040c03d805803000c2c40c4c0708048829a4407540d0392640000100020344003615800058820152030744100700c12900c0940f80c1030b055400c030000b0000030032418800340e03900c41001a21161110030701c0e0011180c0c50104940d082460b0f10124150f103140c048000075100381c0d2802c10040000400b006c08011039448200c0d000180c9a10010510000741501e400c900b41540a03c011281880c115000041d9142c2100ea0007900c0c1079528504c2e40241c403130054200c0020448440039501d5400d041c00c04070600348d0140103103400c0541664440c003c0000e08080e0500c1411041d05d4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 209366267 1250 209365017 209365031
    0x50604120507020312071a10090b060f1201090f060e06060d1404050109030e0f06071101030b1c20010f0f12050c0a030b0102010204051c0204020702090c070b09060403140702030a0501 80
    0x1d020261b0704081c9080e40c5410406c01112101d04580b00d000340140165074050780c11038500303151000540864070110344c20000c14082c0e000b40c0130140010381703e55030362200b032090b582d8141100041107841882600040c2400e2900400c551402d000869410110942e80c141e6905100752039140901100f0308010075201d443c904010034044194000200c0b80d1003640d4011060701c42d0810042c91051f02c18480c2d50003c02040320740000713080740d03042480040060402080c42070310b10001175201b01801280d510088001c01000c1c0400909503446110061a240001c0c1181e940c3c20000700400001c40300c40052042400408190501174601d40c1000c02500c4028011807404542c2000103400801041010030f003001a00c80d8158010f00076642619406008803811214501c24184c01e02403c075426a04190708026000c0940c8402c01d20500c50390501c818140c0c0c604051030071250280c8020200d0307038a2b810250074480000d41c4048600040054854915141c0c041400020308000324010020415807030460 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 209367517 1250 209366267 209366293
    0x4050f1918050f010e06240f071407030c0e0702030d09060905161802160203100230010302060c0316030e101d040e070b040603150504090506041205070203 68
    0x544003030790075401060100e925003005500200c0400e0240b8100301c00501e001510350b0604402c400010407120141e03400080141582d108240c1c000002c05190000000d0070f4003d0042e02032070104e52000040040c40c00714a1500c400104207818000c59007140300310408201980d208005581c801041c03407204000e004800c6c60140c004108010049825004a120001c51a88880b8131842140c030500e0080002204100c2103100a6000800f4038034000301c4200d0003405600d08010007508070390341c400700580e03620081200e840303625007044250261001494511028040e00b003540c5044031b03419240301e52168880740b03543d4110b02070741c901c0c03200350020035400b001410350002c844200101e090354001900800040c1c1161588078410f0007086200da203102c400c0460502d40c1c4440340f64411041a45e01c05600d5a260503003e902aa1054000030b0301d07020030280b4556400e00c00401890111420401030b1203690701e158940b1070007000606118100e641d090038090007031049940c801da00605503420914107030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 209368767 1250 209367517 209367539
    0x303021b03030124030c200a0c08061506040819081204050105060418081b030403020603090309030601060e100305070e0d0302070905061801120c03170304020f0303030c04050f19 78
    0x1ca1441681d8078130030300054040e101743c00ba0704c89151b4580058640c1480f120b0010b041c0584818118400d020204011039030495440c400741c462500a01010b0038002c0e1944036104807501407034450541080b0401131071800040806420608ac2c118940c080c60358100940302d07009400d820368101c1c00ca82d003004104801903001c1e921070982154108a0220107a0000c00140129600205070107000c100300320403400ca10780d4450200f46aa411a441c0035102e40c00724019030801d5450480a91003c100c843d400c2c5400c2c041d09004d000c040c90b00d000070030f8100d8000740c07148201c840c0510a055540b0042602c003440303049260080c1a02038102d030350303442507450020f580f01c2c1244903100a0034501000705584d841d0124007000041c200c1340c40700003180d00300908401c40991003442150010071181b400000290942604840441c0352107403030f43c8170315050040c003251001603d20702d40309400800821100c0b00288080e50141e400550b22a0351003900d00000c6684000c07101050806180c101500040e280816 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 209370017 1250 209368767 209368799
    0x50601090c050a030e1509240123120109030c05010c08101401090801060f0602150f01180f06030b09060a09030503150406090911011b030806040c0c0b07050301050102070605160303021b030301 84
    0x119210340200315408c242c0480c042c0c000c0c0038609034621102c0400c003507140045203036845d0f081e00a00c3c400c4961854403802d03003120b07041041200031800024503542842400c4c445c030464040b15041c83d40e15481c00000c21480c0260300e0080e12075680985c1d22149080e403242d43d440025208020081201d15125001095481031038401c00380144070b070113000444040781c09042806031075004181c49080c1d0034803900c000c04841c0000801c0240d40c0da03c0f8051039001c0c6c40e01606000358010412078800e4103003000021304200b4010652480d49003456040030000758401c080720b9112a8a00c900281c0c2d0a440001601610710742c0e0200351250308141d000c005020000c0030049a00c0400d0301c2d0582c202d141e24031480955041d00c0c5002d40400c0300c58000035100d00b0280c0214003000700b40e19154002c0079050f6100014690140c48103000a01c0210051041c3d580401851010704810304006091540e801009500c00350424401030806401051000b2600e81910140c2210b61021013a0790301d0b0760710703501418002014 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 209371267 1250 209370017 209370043
    0x3270c0907111b0a030201050c10051015050c0703020f031905060a2708070c09021317010207050a1b03120e030d0816030b1504090504050601090c050a030e1509 70
    0x1140c0d0b0504843c0c8003200003a1142d40060141e0300d29070315540064606801c1222540d00c1c41c081c680314100345500c0c61088500c103150803800081e0050502161004640c0c0407000307141440000c11a000c088140052040e080300c0d4102c485820011f1044042810300c80c0d25466404083e11310301211003009804601140f15541405003000b0f02031281710796030401d030381c141001c654511503031480a000c01e13401002071105034052024455259540c0340094220381c04002e461049148950040c04440d8050b00100c00500c001d1000390304240194603416114018507030010154801d20b15690030710450b1914078401550020780c40b01c00200061b03c00340c10016030a141d24402c0c090680041c43c00782c0200f1000d8050760490303a04601040c0115130030b4004140071418990301c6900c000d24540c2c100c95640c018130207029905001310b81403d0600d0107a10f011010b80003c40340c2401e00c40300d6003000d40e01c102581e24043c1140b40c08591a1121f9000d94100241c4404400310415001d00b082410b5000056401c18006 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 209372517 1250 209371267 209371273
    0x2131406030415020c030708040b07060b060421021f08041109041203090203010603170a110a0819050403020a06091e06021b190321020303270c090711 66
    0x2004420030405100071600105861807070141240642459809403041c40c894400b00c9280c898144c48401e05c2d070700a94403904034414001160020002036020380c64036000c1c1940d0b041d044c5818100395042c05015451240d18103100c450498040d92781e0380300b010001d6006051704458500c00c03407200030401c0000700c90550703100c1c2c4110401882814038020b070303074480c2d0b4024268034081c46082504401820010406903070540d240d002c04004a00c0100501d00124114002c01ea41c7c1d000005000d0058526485248019044403407071501060f0f03080215040c040e81204648401e000700c0a050b00c0500454001030340000300000003051050300040030000740c4403050070b00204101544000405041c5030700891006800c05030404041005068104051800082100106400032140c1542d0741c9130591003034903d000c02d440800b06c1c203486507540c24440b05846c40918a1450590b2a25020000181e2400c04101ca80406204003c40078030034048404401082601541070041c001480555030101035400c0c0c2c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 209373767 1250 209372517 209372549
    0x2112031104051903051b131107050f010501050307080705060708090604030605010f0e0a0c02070b09040f050c0316090e040f0606030b040303050709050a0303020703061d030a0c030f0801050f1003020903010213 91
    0x900c035031b4000e0003c50740040c032100360444211140800390039000100941804284a00c1002420a1001d01c03200c001c140000509585040c0401d031520b5240d0b48018484c0d00b29080900140d25407008130380140c0c2d00220034a9481402501083c1c0707512660b40041e090a00e002c0012070b040004140e2001100d1001c00503082035280c080e115811036042c004d0840150344034842c100019107400001d400858801400011300c446c94500500070b45008440c000b2980000000300100521000c0110796000118070b49403e1460519402c14944c40025002600180b2105082c00c100001c0350440c001440c1d0010b85640141004e1034040d001c0d002c281d41c11400315140c424046903500700f09410101b01c0782c01d42e00400403507195032582e1009044c01400180c20607214280200882d07400c10040c610544140d0b00c00545101c641001400c28082106603020131100d0001001941d8890487c114524011120b100030807072078500130743c001c0c07248401184c0c049d400403604c404c0d848000000c40040b59046101c802080e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 209375017 1250 209373767 209373793
    0xa120c05090904020d030e0d110307060c030f11070b07110f030606030a060e01020c010903050a09150807120e010c12050105031507050a1b0804211203110405190305 72
    0x30303000346403040b07030012403140000d80545402140008054003e0900b03480100381c4001040b04a9a8408107446400d60182d40c10f04c41c2c101041035030010600d0b40703450200200f1a5070010300c080c0d101200c45c001c1003484820702203001d03002d0104000801060510075034994152400c03d03041c07060000503a100b40009c00031040c0608000c2241403103900010f0152000c0e120701e6480342d008080200c8600181c0d0f40c01e0086c0418587d00740b241c400c10a0180d140c0b01d490302c1c5540801070204407a900602c40c90500d02c02d0540540b6008404c403900180542400844080d60410f82030050410000015240d07003810303400c952642d0401400800014600301c00d00c0700d42c1e250703418146d40c2c01e0b8200c0b00380e00c000f120f040003039201441203016040059503890581300d0281c0003000e180d4440e201c0442510356071400281002040411100703220b140e0036640415441c13640b10b8880f0151f40d03100d04c46031402e1680301c9042c01110748500c0d0484d0064a0000d202c142c040e410900c0190384800180030032155482402461500 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 209376267 1250 209375017 209375027
    0xe040309140102070f06140d0e0f100e0c01080606070b240a0b040b210c030a0b090709091a0409061d070b0403170405060307031505060c030708090607080a120c 70
    0x9407145e600445185919001c1d048944070b207c41019441118103000b600c402800900801c822506068010511120401ca5a0341401c0007808200c1c031552178030310242142540842d10031403035402401e04500c1c507903070803010074294482d40b070008098450300300800031140742c042c43d8040010080403407200c41001b82010b0101a240c0307030040c040340500500c03003085200d403010010a00d000c030420002608400d90380c0c2c05212500180d8469068290100c1007004491681c85100c2d60f2801c112000384a40c205810042c188024134051030800340c0e1101c280c507428540c85071031001d8070980036104110000003400e2601c020510940402003400d8a41f021441182e4006122015a8640094589800d181d540e400d0196520092404510542403000040c181c1e07407400a1403040c55144c0380400c0c0c07144c00c0032104a01d401c0c5034001c11312803403040c4425903d100340001600c044552015020350741d810b400b40081c03d240101c0d103005215100c0092103c120607880024862260000c07030303003484901703002c02c0d081d58 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 209377517 1250 209376267 209376269
    0x180c020601090f11030a02030415020406170720030310080105010b0301180b04050103080721050924130e0f16080a1103131106091c0c0e04030914010207 67
    0x5a21040c0148480e041c1503100d1514076450303403c000340d200203c846110740354104942c900700455002c401c00084c00340c1c092042d501102208011407030103042ca80007400a50385c0c0b0021030b0f048050500080d40403402a0080002c0c43c01c001e00e21a41e000034450b6690b500e40c0110380081c84110b410600080c42d4505016840c10380360400c120368216801e101681042c0042540d204c1c000c00c2d04e45610b003001d41c46600c206030103180a42e512558844040c10101000b80c160004140040b21021803908465404000e131070100c241200d11032902030500c0807001080e00039103040d10745203000146880c401c030b96080ca036104690f0000c0302c501140ea0b440180200d9502d08841045c1080000c1035542e031581e110300c2200f83c0c05a0312600004202410f0080d15100b0303001140c0c04d14000c14104916010f102e106004d041400c03000305c0b40b0b1846c0203001c5002c03510802c00d440d54100d00b030380004000400c01850440a101402088600038031500e803d090080840704a8442d030301301a940445008000e52000c11004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 209378767 1250 209377517 209377541
    0x10306020304060b041a01031515080c22030203251e23090702070609060302031806041506510207030b0105031603080d0204090908040906060c0b070c020f12060118 72
    0x15040b100d901c01d00b51b452040040c00002950004c126681070003102c5840c1c0c501050341c42508030dc5031800c61050500d00303101c518441658100c0c090f003940c01c032152101003000791030b10a80300c040f003240c00d261004c041c40690340045101810065583c0010350a4a82011050303170100c5034408280c0700c55106a0b00c07020301d80180343c0090286001030082c2402034000b10b0b0400805100841212403c8070f00e1420040c042e203007110b107520a2403d056400c62903004801c0a001140d00030305449044554040042c8902c480303080040c5510002c54985481c0040300c07403460030060100c9a80710350002c40007501c62000d40000c4440906080003c5050704001404200c020041066410707001e056448045054010b0ba80805e2903a03020040402d010440c0c2c0a0054082c3c400c41e6510f8496003008600f10030b4401d540c00640c00c000140894001284041442d5a00301d069400c0180b03140d03549001260303aa20720800c0050700402c6c02d00403603914800c00036066040710420008042164500c5002c013059850f80d40f041 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 209380017 1250 209378767 209378789
    0x50a0b030f060a0509100503010e16050d061103040b060a0b0901120e07080a05060a0c020604080d020a090b0f1206010e0109031b0e0c0310080312010306020304060b041a010315 77
    0x194440350449074440d0010801015007001940e903800107030000d03100319034601a051601000708800e041c240a0740480100b0040a8410822a894000041c18191041502c900721180703400c0300313112980e4802c5100c1d641c0032100d55074074541411b21180b207000584020740600c1b000c1c4000507401e01c8102c1524103e810596480307101101c20000d440152030980c1d100c0b017143c0503d0b01e0010791407108105000009201d140500700903d845043c100440703407104425400c3d500084100b000281401044800291000f4401602d810603007030101c071075a0f444d0f0072540a514001403018400c0140b40050150030000801c00f40c01540c80300011503ca0709641c00041c08a203400506000198001d46d240741000542c1e02038404c1303107545401c018200d04056070201410031001040c013501c180d18880ca803001d0640382c002140b0f410581c0c0319007582e0700c07414070016010300c1d400700101c2c0401c51203070011a11030100034000d014044100b180203101d150301543d260702192030030b2800104c80e40c0f240e103401c04403032841da45 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 209381267 1250 209380017 209380021
    0x140105071a0618070c02031c091a0d020d09050607020d050318011b0905120a08030403082502160f03050c0d051c030c0f0201021314180108060f01050a0b03 68
    0x1007290802070141c09254441c0e02d012038603110822420050344102d28541c0c503503140400900606003844450314075441d81105140c100100141c203c90302808075a1003103e003840060020340b201e00980582210044035a00006040c803030b880d103c0e0032200000d8042e1f000c1d2840c40d110980141d90710b003045c20101d0f001c1030060000074000c03110702c016103507211408000490314011610f03241c06113000460800c00412190f10090206080c400c0010007154070038030043c91918142d4503900d42d01c1c00300034001420410f0107000503e40900322240b20a4640441d1101840068802806500c4080c0d2107001c203075290820100107060500b16030110212034200c8054480c03404000c6c1405084280808196001c0c8101c1e052020400000349010140c2407240d94009130340c5022042c014160702407070000c5021a80184081d2000d01d28004141c800c07115062500c04040707455101090410074041d11310010a1a1440001215200030402b0b610031120340d01072040036a20f4008015140300c4034040d0040c44441840 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 209382517 1250 209381267 209381303
    0x608031606020901020a06330e16030b03100c02060a090f08090121060306050c1c0911030124080d080a05220807030201050a06051012020c0102120114010507 69
    0x100800b0564010b00c10364201172251f84503582600c9012440106d08038443d070300200c42c8030201c1c5c0b4404025068511000b801132520f00e20144203000070b403c44e691400c0d040701d10040d180c00790340001d02d18400602a9051009410f041b1001829141c1204015000e503200040c0750b02604e114207500d5550000c042948190540c8480040360808640701c0e0520401c16100413400241400c008098070710010042401822f601d000720948501070041090b206044c0501407881c0161400c030088003c0300500050a01140d040c000c8892007080080c54040d440c00c40d00ca08944034a43c0700c1e40700010220308032680c180d074880f2001d81d6042d034828004001500100450590180c58200c00d800682105030b965140414540d403000880d000320303003141d60340300c00140304d010183c080c000c0300d1b44408491000c01140e4a0403011130340103400c031100001001380550042ca060007035a810744101020315030085440300f1500b61500e500c00028000c4d50f0800d01038011044641d880352080f5841d01c0e034003044651102e40216 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 209383767 1250 209382517 209382521
    0x70204050c280f0c0501060503010204080a0501110a120513141b15031f081903020d0c110103020c011401081e120a0509120d080a06140f010e030f0609030307030608031606 75
    0x7022145552107100002d0b007562700b40003034800f625131100900201861444d10508452004042d0300d08075100344504d5049680000e1104c20b00e072445080031038203030345400c40a01c60102916004007003c000e08004000c02d5000903000d2a0020600944000009020200030f000c00c004032035880140700420014120f40340c3c51142c2a84180d20803040a101a01c0f010742505144070014041c100d020a44074510030b1540c104810011100c1904185811404a890795102c0902a000042c1490b0300050301c6c50303003062700350300204810340c50340c1a201455071aa91116121000d40001000c8550311010440d0900c0000c42c55100d416284810185003105161048d078903904403e58007a0701c05031802601e04808400d0142c0740d5880c030b0796a44c1380c4180c500240078404880203600305540851000c04200c0c8551036035024100109409d0810207072100134840080e1416072500701e48103060080d80280709002000101440c01106151400d0003880d8890b0380b0190349001e0f4002803074040f1a43e5a1010102d420b03070b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 209385017 1250 209383767 209383787
    0xd020d1b0f05280f0b070b060d03020d0e1c05030702010e10050301050f13050702061906050d0204020d020c0304060c020306180a0209091c08040c090902011211070204050c280f 77
    0x1010943d4010303a5500044c003881802503029a40743c0308000b5040041181e84511981e105400b1a01d11542c603545480c000d40e2113280011450a20030303103910f1044241c2e00c141c810b02541d400400d140107032102034580b0b40d84035004550100d010a0821209034113500d0010700040c0c482880740e68441c2584c0c6482d00308259440c148002e1a0040540c00f04203610844074003507030340328802a80043c401401e02031518400041160780c2c0189451414505010703903030341c280403d070201ea01250301503250040d145071480244a150016145403000041c0025074580108199000c0b50003113060710040c0c1e686a000c0c2e800f00300c0a6003c01501c0d0041c40f110001898086000e6030070071240703401c40b003891500400c1c200c8000ca4240303e403008075648404000c204103a24141902904900c0ca05224000c602e50020b082d050541403250403058032144c40106501e502001d071020a60020428410703400d1034a84c260a43d0b00040b040d1a40308050070341c24140281c40084813040c0352042da14540303000300040040b142a181 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 209386267 1250 209385017 209385079
    0xa1704030e0409080307090e1006030b1302040f0306050a05010b031602120406020f1c0203040515070804030602030a05090a02031e0102090d11010f09050102070506090d020d1b0f05 79
    0x99080007240c6894a00c500b1018902c6a010b080d90303410218005003040c3e40e9a480404440e081d0030030000b4541317840d19840200d40d002e041c040b8011080c2800180c4140c00c900c0c419140701d10204000500603080f64801044078040ca078208501c0e00c52000610035180240942d034500001000401c540c8060601c441d104448248140c40700001c01011101e41a40168050001a80b00441e50088100c052115160141030180441100d41480c64042d44074080d9100e03030751142c0304130804110500300301004c5070740403648914420398407512840d00ca8004e40054032410601440c0c240052000400040d402d184140c0060042c9000380c131582c03103a140e20a0aa141d169555001d0029040c180c0b15180c48801103449504d005c0c01c1f19003d4000141030082020944040122482c01003156036004034030725080e00d10640301695654144000b01e519151312040007034201c00a41c03660300c1809544401000008007120100e444540d840d540401d1501c80e5009a660040110300210307010a0044030030800c4000d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 209387517 1250 209386267 209386277
    0x71101050706060305071505070506060d0510140a23010e070c02060403050d1403071b062a0905040b130f150e150a08060a2004060201021c020a170403 66
    0xa042e540700301c1607500c0356108407007503400f25409006041046200c84000322491610509000702a2074181d03a0704c0c07001c1c007440d0242c11440680c3c814801e082c0082c15840d21030302028000b14458002c0c5540f0f10104607400c8101e149824011000c80c0030408640e40241c2245480d03d115909020070201c0c50007005c0d000d0402d1200030f0301a9401a104c00c0007600003140124050117000e400f00d140903042c000107001403000c00e00e00304104240c0380d0308108103441c1210660303201e101080d10740c5003c1000305190700f440320080085024020342c912488080701104035039582d5980705550b4420601060360241300b02141e000382050304020f10540b50783e12000e203880c0c0c211800310310f03410f41c0300d906c00507440b5540003420400c454404129030a03c00c16440400311780103465002150b4504a121070b1126400781800711455100c1c204c01500c0307071090702005000000c81800b82d944a60b2480c001e8001d5001c0514018810010300303440441020382c0c400e545c44840507440d41c04c10801615035401c50610020801ca050103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 209388767 1250 209387517 209387527
    0xc090405100525020106090b06092d0409050109150519090503120705040603180f080306041508030403020a290c0304030c090e0f011b05131517010b090607110105 71
    0x161000e080400780400d400000310103047c01058025a142c0784030960007440101709241054694085d070707007140c0682d64a00d911140300003118441e915042040c0c2d0303510030b0800b0303082024004103611007840e42e84070b401c0918142100350040e200f9658101d4680801402041d06040380a881e0780201d5600d5114900740e80c5800710200480d14900f100761140d100080b008181030003031980601c41c607407414000707801c8030040150554600c040304e10143c8000306010303400b10100b40503840d42c0d0048882051403031012042c00c0c1d150810266203820520069205181e4040001010404004410300c0402403410300e247c0c1c60200e185620303203917001e8501317a04107100810000000c5110450200081c1c034031208080380eaa0304d6907543c6444c01802d5104800141d14000d509c0381549910305c1081b8100e51182406603e80040e50203881141d01180c1c8501100e4001c0b02d52801225440400d50704000e21800070400c003a40c030b071000c41243d8003d1942c7d080d04240100940b0000c601d21b2100048000d10500d8094900 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 209390017 1250 209388767 209388811
    0xb180315011418160801081906110d0c02010c030c08060306151207060315091e0506030c0607060e210405060d020405130b03010b030a0305160c1a070201020c0904051005 74
    0x503070400c41c1c0801100991842c0138141e660300c0310000d03004001c1c507402019010580000103c202c8101c2e04000e0055580d01c1030703111445170384825100a03001420041140f0244940040e010781401514000000d150080001c10a409004030034000c103006002070207180d03201d5910324548401024181d0f07000702e80c0700c1000a0f81d001005004040c2c0115500400c0380310307891000c088461440d0308608140c904000f1040240c1a480251031002c0801060110706510347c940404d04043c00289a503800840c005031791010300a098100c4800d60802104981c0c00c501c1c100c0c00160b0010121480c041a20004c000c10816868000064401001c00e20401860665144002600224440c6800300e01d04e840d50300060803403400b8400d454041000350007610740070110750340003000381c4940c4070300410031205c0c03400c07030000d100306005000040c0208041c00000c000340c8110622158102d0401203006100b03440b1001d00c0b90410907001b9005a41c03080050240b54003519145002e07140040c000c9020000c540d4a00700c0c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 209391267 1250 209390017 209390059
    0x3130c030309031209030b06010e0a08152707120201030f0c120606050f04051504080706090314010c0e0d060b21010b0604080d0c0305040e010b1803150114 68
    0x46229032122400c603483c52610425404207013242c2c0c0c060241d0314104101103440080c4059120740246061000f42c8803810014116017040d400a00342e0744120310000ea10441e0035400c82d4020480c000352024120350ba0b03800f0b01510b2001040d80300613500305410801c50100a1841c41d66000d20504000c03d0300c01982c005541101c54080c680d03400244400440307004154188900c601500c600d18002d442c2819023040782e403480c8141e00c907690140c001e074030046505012078001c5ea0040c3c2401000d58400603074a8100420b0a80240000d580c5142082c5401881d004140b00f070038119052607c9032068038010504111101d002400c0540e40d042d11460244142c2d0b45070b1141e220307980c04462020180d0050070a07001d085a01c022302c0b9a01540d010001406400e40008030100b0600092420401015039850220340798060352380a41403ca009034004205514402d010345041080c51401d041c20a50f6903081540e54009461000780701104100184003580d610382c6819490107018004104825507124a03840d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 209392517 1250 209391267 209391269
    0xf07032621060d020901051216082514040203040212070e09010c03060b0f070c0e01080d0e04180b090102040308030f0114061908070903060f05011404110405040203130c 74
    0x1e8140c40d000c401503a00d01016442d048101540c910343d0540140e80032410036441070154510035201407070801e8000001b040100515020f0b808140102603503500310702c1da501c3c1e206222030881001071507580890190b8030081da0496041d031008251304c00c190400c0c00004d61010348266041035000a0824850004001d55001040220940010342c60310002c1c0768210346241304107408060034264100216445a4160f03288503c000c9505a0380d070f103a62230b0541035940c540d8820b4000c04020700000881840114404504c446292198110607194004000840f260041e000031544505c4081401040e441307a813155008403031000040c17425440340c641c020a500120307502c403001c0f4022070040c454003904042c51890081e090300c04500f40f0b00010360020031500381c002004200100840003c40a03031048021800030b54100c1400c210850300685050080d0000340215000240c0c2c7d41400200c600b414420342440c002014901c60a15003403a080002a50000d4034450f420a8142c10070f40200b48407840c060 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 209393767 1250 209392517 209392537
    0x191703040c030605060f0a0b0a261b0406020a030c03030b030a080d06080708031c1805100c0807050f03060406051804030809061302040504140313170f070326 69
    0x4910140b8500d030034815540010122406000b101c1c4600400e82c40300154842541c6404244035100c2d0410f16040319003090725000b08041001c9000f41014907060760320403902500800203d50007050010542d10788078070a43c41200c0060303010012100200344500d0440b040c541c446d241c040b0320003240030b0000c1e02d0f0001040741510280304c000740f4505103820f10311500005180b0b01d0003401d1190f1034803900c55180d00441160510219440b650043c4050065000050080030306404a41c107040d14244141da400d06a002e55500e140741c11038011102d8041e0f0311840c440c000e140d4880380703002410000204540c10150070507420688480c004070303050359919100b20a8030103240d0710b0f01d028075050030010480f2102400b916460341210b0144000815003440e08840260155008641c0340c80d00d1804031010386000000d0511400082207141c2c039800b042d00e0707600440e00b4030380c1c0c5410400406058079803607850960308064a54000c1d0f108000003294112f4922982d0000c0d01c14040040080c00f0410741640010a44 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 209395017 1250 209393767 209393783
    0x402130e0d05180f0102031606060504050c030a0506090c04050d260c0d0c0c0b090f040e030a0e0102030c060109051f030c053615120c011b0519170304 66
    0x100000c21840f00ca01c20601100301c03800500a4080710010f0b4a038030540701d01c1c1c801402040c00b19001c0c441d65800110090101400400641c9080401c2131550f0b00107860700e2074004d081c0004a5141c0ca05840f1080c054070840c16901d241074039140800c03800c040c1c4002c0480750b40599a540e031000c048811819a544000304030b00c00d58660384619810304042d01c1c40380d108240850a00344401040403d480d02e4140c4110340c0740c03103540c0c440d2400000c1e07446c140409115031141c02c0901c41c020170070000c001740030b4000745034071034407100c1030140016a203c0c016540035460503402180100400706c001d806c8681c00000e40044850b10051032030b6810034030041c68205841e400c4104a013048035080c4841100d22003000c28401c0600b100d41c80038105282c41c2145140480440e00c40b0200b82c5402c1e003203644a660f40b0300113156141200140f42101d46034602d0103941c50200d1003c91045468221001140e92000d40c4034000e000c1100300120140009980c0789000d50705a10240c0c14525403080c504015170080e401840d807 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 209396267 1250 209395017 209395027
    0xc1908090a05061603141501050d020c0607090302030106120f0807060b0d060e070f1401120b0a080a020a0b1303030807050405131b02120403020d110d080d230402130e0d05 75
    0x10103000e81c6c00c074080f000c0414004001704080750142e2103400320790450901c0d10943e11112405001c01a0240c1080101140196000e110b0440d81080e03003401107a10039802409041c1e40d41042e040320740800800036020500d1181c1480025109100070400b140c841c44001442c5041e0b1008200121207500085810030790b105441405000104581070062401c80c3c0d0703080402d414480c007801c41240384140207060040d5609070305500009034018512000000c0c09101001b80d4030ba03200c50fa2000740c902c09a015069001011842294030801c030383c41041605030810000380b0359038040300c07201001401e003001c000c018800845c01d650750b0741182d0388151007000041040c2000025202580d559a4040c00c00e40d440030b00310720b2154150300701f5981142d4048489030b404510504055600a0140c03d00541c4240f410310b9980400c12020050030301c06142d5042004001795801c484010000040032025503640800d002800602e44000003850ba0200311740b000c12107104480c401d618144c6d00079101c40200d400422 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 209397517 1250 209396267 209396311
    0x403050d110105060d0201110c1f080c070201080c0d0b09070c050f0703030801060e0406080a03050a09140303070f020402090405240406150f0c0f0506010501080c1908090a0506 77
    0x260707001c44040680c020001d500b09400002d00402290f800241800315009413112001002d003c01c1401041c081d000f400c0f10080c040740000900f1103000b000000c94040d10200705441c5140003030300c41199041e140d81a80e512841411343c20398214402003100140c40300c800c3d04c0e040d250428114002c0000740c80704418484107240081c14031344040082c600b0360740806030030404240e11022030740c11105c540c00c2a43c0c1108160020801070b018540004400c0c0c40385000500c2015842801000c3e0f20403a035032607072030a03070320740e02211280150805c100e84e0651003440410040340904408200072440100014035181c603480110301941c80855141000056401e00c07a0040300b0005900b0050342e2049400700216800c001800c84030310b00031031200d000c00400c4001c41000602458200204c5a0401e05e01054001c40d0703e405070f5206001d010f4a8005568040851500140030060340d400c810341d0100c1e43c003010071082d0308031225000107222a149100c0d444040700400c1081c400540a82d2950360760032205000c0030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 209398767 1250 209397517 209397527
    0xa03050a0f0207030c020f04060806041407051909111611030706050705060a0c0c0c140103181a19110c010b120601030f08040905010b0304050f0309180408040801020403050d 76
    0x1a000a48040c01044500f0000b94041018410303154112940040900c41a010070028001c68012500754030840b401e002c00c1c01005212400c44251020031a10811b41350814040380000c03501002107020010307041445840c5590f00210031008500c1d11143c1408400d2030426102c4100f90410345030b4401000724089981018010040039245030304200b0700e400318a50f00c1d50f0f40d5030401055480015903483e5031780c401d140305010b220301840e0007445100301c0a444a407136040c8402f0680455001c24034083c401f00000b00b5200140e540150000c0ca912855001420000c4030b2000041c91805c1038010180d03000c410f00c10707030700c91003d80032a03100846440c0e98081015608442c0316000443c4140d10b0444134a00e480000503405054a600c00768400203480305d460955090b0180fa0000320503982842d0000c50b480e03450202540c0f03d58020000c070389803a50b02524164582c030940c10346640000f507040091604c070704070700c000b00d0f00301d446101f0182c64550307941e005c10300326001504105d075030f030308a0921b040181d60b00c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 209400017 1250 209398767 209398781
    0x20105010522050a020d02030f071b0f080307140a1d09131202010902030607030e1005010b090d0201090f261c2f0c0346080a03050a 58
    0x20782e418111201581d9403104040032420b40108034503200c00c00108050b2558058542c1c010429600f5521f0b420040e04000d0f800c85c0440b0000700007400865007020030840f80c922541487d40015402054120544405c03030a85d000030b10358014032680d140340c030300054000001080c041003a1399071007070b00c611000c01c2408400c1803901c039103204070308050500542926802c4243e40080d4801c4a841d1111b00905081c0e02502007880f000e980b6000760030400c4400d40e0180c014030180d0044ca400e450006160450b600e0460f4002e02409038080400d0142000900706000c805244500504100440301c0e81c0c0c40700400e40c82c00c0c5400c144110303028840340b0840c810201281c0001480c644018051007545449041ca00302c004032280c40c1001003000511031080b1340c8004140c425017004003510441e181d80c203034040d503a00404000e64000d106080074014820020400d070035503c014112840c0380d041c0c490380c104080703844102c845094100b0302601d843c00180514010b1002c04d419443c049054a400807103a000c440310 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 209401267 1250 209400017 209400019
    0x106030b01050408070608040c0f08061006050304110906030708010504050c1005073201020c0f10020c19050111031006030c080114012f031b07081207210c030201050105 74
    0x140000d004500c0003085d41c20a4504610707183d4a580d0f904e043ca0300c4921000d03030042d481540000b030041100b003800b060040c410183c810b000245242c0c0d40500719130303601c002c071406008003442d0200322806240c121401500480014100e810725134480440d142151419207040701e41d0360004101d5005424003c10b15509514141061800d100894030b40300d001c204003611040000b07154084007140d07040e019070542041c02d8004001c540b0f85c01205040e5680d036154a61001152180d80191a070104a50084a45a13510301003c0c107084150101c1ca00b82000c52100120707019520703488004201e600581c003035842200c5507828180601d20307000d4050100d40d440a560410044410014410681034551880440c00300b03107850f01c01c049000c111541191a100442c5522001000c4140414003000001d08a02121120040a040141c0c8a45551104184511140c641060006003500c0c04081c003d04010b50289103000c5413103c8202440941107601c0c0e551402141c0b8684d00c10090650900c169409020 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 209402517 1250 209401267 209401277
    0x40c022104260307110d0f050105070e0a120308060d0b040f03170c0a110a0204060801090b0609060109051e030604080406021005071e03060503010f1b020d080c210408030106030b01 79
    0x104091143d01d81c8a21400900b40c001c500344078502c9511102c41d130000c83c6812030280e0f800b50105262403400381600382c0e00240022564260b080d2a071600c201403208a41c90907a0143e01e00806640c1038a232501c009201542c40703100804544081441444030394800c6100b900c0d400024000c5185c084c0c0440303c0c409501d015802a0400c01c012051380c2c4048031000b0410f4203118114600801c012460030700da04030000c0d0804e061010019000340f054105240103481016091143d96840003401001c98088802c2c600081c1c04850810050a2900030301c5600e000b904020180203031107801091409a00b40c90417602c4e41030003d42007105a034144000c40300090150f2081c0310f1828148030080c00c0249140322140d140305107180260301580254088002880c015000b40322100042d60090000e082030340c840010072181103c4220309a1011400303d0345000d464a07440d2450b16160100351450f0000307800000301400c5a243c00c1c201c204e01c0b8940d280302c0c070701c101c40603a6070f5070500c14010151109002e103281840 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 209403767 1250 209402517 209402579
    0x90d0f1208071b02031c110d031a0603060607050a201c080d0f050a02040602010b0603090709021b03071203061a07060e0c130204050306010609060e040c022104 70
    0x5544040400046143c0d2032810722080100e0000a080051000c02c14520701045014856101d070050009100c4401080594110404101058055801d00b03080301d00e011962400c28400c919110740903541100c0090056030509000e90355003440d03d0b400e007000791143c0500c000050080d9030101c0702180c05420a941011100b001c5c400c4040304007042020081c68600007280003040591a0f6104101c000006074040c00755041c0907003120025489406000010350a016017440d560400700d007264081d410307420040a045280118a030000e4202010146070104200805e22440f0400c201070410305000d01d0400c88041c100d80c2015041b6041a406100d40304a45900410702c2000e00040d60012a040340003c5504410390a15904000441c000251300006841068407049100c0d800340003034400c00c3d01280e12903601c030601640e070581d0702d11680300081c0f5911072454103410560050b41a60075640111140351b500c080d03101da2407154043e407040c07640e2400304040024a5404120104586d07400d080042c041e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 209405017 1250 209403767 209403781
    0x7020a1703130c09240e0a050411040603110a060201050108060109090f02060711090114030a020d110306090303011e0b0403120c020303040902130909050c0904050f060708040605090105091908090d0f1208 89
    0x1d83d0060400c403c640d9240e000400748480b4451104605000500402c220de4591614503540c80c03001c14118000e0305da00102107034081c0144070fa0740c1a101c0ca20300400c0b040e0710300b0200002400e0880022207941c07220b0500c003001030301d404000d0200e881c400d80407803004a02030414001c0c51801680a40074024141e1031422480d00c01240050090350107a800e000f24041c1410903070340c960501547c0d550140302e42000c210300f810010000d58143c40046101d66004034004500f10014141070080e680105001c0004000180d400044118500c2460030505101121a00041d0030768010f80d0000c1c00150f00001d00002c10110048600003603d100c0008200c90109516490768820402107228081d441d000c01040038004100f06070072101a0000460700c6c1484d01d248014951142900c04a0741c003414070340030070f01000301070044503c281480802080010101c650314110401c030140c040e584c40b80c2c00c011420840e1100e0450030b103030a000310400565041c1502d0050040c030380c4c090061040110070005c0c4919 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 209406267 1250 209405017 209405039
    0xb040b10090605160b011427010608060d1202011e060b031b040e160905090412120b0306040f020319030507080901030209030f070501020607020a1703130c0924 70
    0x140c401d01d1a0403a04d95141110400c41441e1101c0041c241c6203800d000003e080585104001c0214819695400d0b840c01003c000748c41d803c440e80d04d245d841741410b001070007038a10908041e075200100811102ea81c0c04c035501c0d001646c075008400040141d45525001c0001c901d0b0b0348150700f0044880c0b83c104a82450411002864000500b40000710641031208040315441d007016100035100789464810142040d20143c3c0710603500d40702a10204000040010b03140c40c001d8640f074861074000144d00c2d02603403400700842d07015245201c40c40c4419555504010151020040720b88540c0c0b00b40320801c52101940100342c5411000c0c3e4442c076a0a00c4403281000099020301543d841039800081c1c16180e0042c00010380c043c3c020740b41002d8161181c5e4580496485001415108480007a000d0f6009529818422a254803003c0e0700901b080054002142460004000459002e03401d105030b0780c1c5030100c90341ea03a052048aa070102c905241c440d440805000520f240500c1396054031501d40300500c0c0780c014074070304c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 209407517 1250 209406267 209406269
    0x1209190c050f0102070f0f0e06060301060f03090204150609080601080d0f0f030b090703050406150602030703050c0f0d023d0c170108030c0c04050601080f07110304090b040b1009 78
    0x1029003150488907000c0d134001c00103903001c1c00728a0010402991a4030001045494a100703800c01010349001068840c10600300702c905030740301b9a48030402e0000f4140e01350003600b0118022600a56141c1000042003029400c2c58090146652031202051a01080520386603060708801008e1b004031050004840c0c0050140920110a04040c0c022100702003064006180700c14116410402e404108920b541c1c5c150b01883c480c80c0301d11030400002a0410030001c0754100c03405500056401002800d010a0182010303295901e80441103c498010003000c050425025215103400341e03005102c0d100c56414407000b0030b20340c40740301000081003106000307102c0c10a410340108080444d40c1c80c191074034400c0c8500b000760090fa4030600b035581d00d56901c4003060313603d0f8030030f00e0543c01d14040c100144000c1e14050050b24002c11050350340c078030f0a44910002054507100500311100344080c05c01c0000314110144007034002481003000014803641c49101340020344a015490f00d12400c02140500c14550304800d0900c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 209408767 1250 209407517 209407519
    0x108030a120b030a0b090f010c0c02040f0b0f040906110a031b0f020303310302030d0c020105060f0f0111060f06041b021e1e01021305062b020d021209190c05 69
    0x1000e86c80b801d414504100c0c0f04400c0b4201542031a0682c1d2005070020914040103200755820000408034000030021030325210759140c4c2c031420401480440d40382070340105c1d40460148200080d8a007d603c80c19290354400540131000c60b85544001507801c3e9914003840320404c00d030610442168802e1802522403100134820f244807420340004040c1100e4058007403001c0a4040c094411401d4242000382d42e03500400c049c0144542001015480c1620600400d4006e22000c0c102a04040302c010400c001034261946043c10401040c03540100da0204201060040d096180741806a003400710602064480c8184016001a18120280c000a50000e00c00104521004043c0100b84101031101c1c00c02420712f4880d4610040c1e03180190403d40c040d0f0041400800b4030b10300c00c80c3e40381e507601400400c0c0180c22440c10403a0074904030540c0140d249544035900422540014684103400018100726084810200030281500702041407005040050b41071b1125412641581d03800243c3d118801e03100e05010305 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 209410017 1250 209408767 209408783
    0xf010e0108280f020d0b040b0c04080304050f0102030c120405040f05040302030d0b1507061413030917100203090a02120c1c110a1707060c0807030302090d02090108030a120b030a 78
    0x1007043c41500d41900d44000c2e0300501105005040b030801c00e000b40c5042d501980e00d004c0345004076035031020400840c0c0441e04050301441c28180340000300300074440c01d2881c40307040d80010002824210024401803c0e0060ba0001d8651103904110512003281c0c1c5044003034400c5031600d81880080303038001003900c102001c03080f00807400c6040030021420035075070346040c0c5c04061070100d020f100700411030f046407040c65104e038200f504555440346c20180340c0c0d100b054081c000c951491000d122940100020351000140101185d12071461a48220100d0b40112140212500300d1141582140f80581c4030109200c80c0c04002c0c10300c03410400000712a00100d120251404080c00241301c1085400b000c40480c51a008111a104a40e0782c0c0050100c140030061741f0100c1d005240303000c00e409008507820250345030840840c506000466400303800950080d5003655002089a000b54016600e100c62a4080c082990255071601842c7c40f000e405c50156105074130140303080400f0f540450b14001040000c2540003a04 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 209411267 1250 209410017 209410093
    0x103110d12030c031401031a0c0408030a0e190f09090204060b030a0903080705070503041a0721030f020f0f0306121005060a0b03040c0506210f010e0108 67
    0x103011540c40100080c4078409110074001c2607600340e07200d03403000d22060710144103407000d4482c0289410001d0100505000c1c90300c4404c0045403d1420300ca41c40070070398145c40d15090706c2e0041e85155810400b8400001904401c00040b50b043c20002e030b404201a0001080c0b0030341c2010207070142c1101c980241542c8566848101003995110741102c4000c14107001410f0b038a051009019024102c02030094011600c0180414040e07403080d800c4507909502309019500b89810002c54260031100090240d0b80e0000600019000c5280080e05074010002d004c0c0103a121141080081c051301d0100c0007013840341c5c5c03040c0605d10341c400d15182120320b912002546965665504000031b107844030303006004640e611079a101c0640b11000342e4003113801800d04868030706401c3d0b035604001e8440e120844004040c2e00a03130104128906000c0c014020020703204007408203040201c00c64148800040310f035810b0803040b9000420808180000c594050b0611401030040b06682c0440041d8803039088011611000440340 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 209412517 1250 209411267 209411269
    0xd2409050f0604240f09050c0408060610030915050f0a020408070e0a060308040905010302040b040b0315090c041e0c090b0f09012321011203180f1512020405010503010311 75
    0x24652154800888203002ca680c0340c017a9038070402020702595080310b1524000c101c1b513050b414103407030072100702c0d01c01094555510b000b8402206510807100041c580c4032032001c000030f0a0402410103001090400003414900754110301c01081000e040012114410801484241c1020a069080c0c4424510007074550b22682641c01c0100351660010381031040115020605041c01d81105040b039000716401c0c0700320344104c000c10040b20503d90310305906911044480303038041c2545465130f0380b1446890958200340240d00c04275041d180c5484c410002001e505c40302d403032910032503c41c8000310380940c40c25081090502c1d40d4041c0620403058150201c0c81c004c0f915040d035a214814490100b0212141c0f10710400c207024200051f0781003001e10501c1140c5035500c05512008180456040741c00b90500340300380c407401e80c41c295010740703115914400c28090000c011071230805005400c00207000030001004607140042d4014040d2080b801d04540444c0100010003150380e201040e40e040d00d402442c000c0d03005d20307110 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 209413767 1250 209412517 209412551
    0xb03060105330d0905070602060a05070804060906110a02070302040608030c03030408030c040f030812060d02060306040b370f140114070c030305040f0504060b0d02070203030d2409050f0604 83
    0x1401c0c441244c241103030b03034041100200380781e002c4403083d070202c4c0c0c110f0300d408100c64280c40c8101c42480c0018000000280401d0040e005100c885006490000302d48000400d440300caa80400c81c000096480301108000f10300f0540b003003500034801c00e00514205641e210f400d82c0c0724440980080d21488001c80480e1400d004001114020520005a0501c81d0790303a00e0054481d03048082c0c41c00d441d10410300002c2d031b20f05044880d00d01d000e40c0100031074619135940e410880180081401036030441da0090103400101c00a10040c3c08450030b1a104103001c001a0052003401000713a00811050429608104a00400c0400240c15910300b42810001302c0c980a0100440d401280d402078140624448000141078018000344180c920001900f03149589440c1440151203081c864240400c00070052000e41218560103002c5030381c030003401d90b85443e043d084580141c0310300e40303d40b45031405c5411505408070310800b184401044284000d108610340440b11500300d00004240900444e202c0e040604804004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 209415017 1250 209413767 209413777
    0x80307032307020109121b0209070c0204050f0402040b0d050304030f020d0602070c08060c0903060a05100b04030302010c121a131b0801030507090e030403141905010b0306010533 78
    0x2003080040391900b204000d003c1c2000841c207640901a80448a4100c1d205850803070031110a0a0350b907180321815401d00c290b03440028200800c102c0c4048030600140d49500a00c3c0c0180300c8074155401a0900f40100404c481c42604540d20a008618002c0300046021040d24210381c0c00240c103142e920018000b0807040440303c034004040c5480010f001c020400b9803040201600c4064040720469901c1c910100050f115400c03120f84d040e03214a002912203030403900115800808508c2031078642e59a042c0d110441d4100b50400c60260351a500c1d4004140e90050442054143c407140a220800107010302c061201c408288150181d415020a0101c180203604410342c4541505040e100d01601e64100500c400400e00080b2507601031740d01d0000e110380d11400b4200c40e056600014624081ca1961042c10303072100d0021150841c0148418101106104601d20311006c0c0500004280c8900314001c140c103240058001c10b01c210b07074605840c000b01800d44110ba580c000303450720340c02c4203810f24105440c080c0a5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 209416267 1250 209415017 209415071
    0x5010303081902120702030c010c0e030304140a0b0c0f150402211c03150806071e11030301061d030d050a111015030506070f050f0f12010b032208030703 67
    0x41c0b0f000e2007600346d400002400402c0006c8000c11044810030000c40340003820083c0d2a516074402d02003442400c0c9441c1082c1c03031050b0000d040c24066030313907001390205c13540041021941580200320310100c480410301c2100e056001400c0508814640340e40081c000f44146507400444d80149011020149000c00c80190074005c0482039208203201e07008000c02038010030000403c501411300700000c00b4a0300080c0e80307010350881c1e152981d10440d0164401c5114001114900c20420001131140c81080c0134030085002e0140c0340d41c1c0b264982c07810300c600c4141b5a08002000e00a50012610245450340501620307001f00c520315122015a08076060396150403803403900300500600c0c00800c0f11200403518050002c07a031107081a0f0b01399a0765170000b41d0b0f004d82c0e1200e0b078202003030080001c401d00c0c0035500000c10410350303101110307802c3c00c0d444040f0130380c4010260008003020034000705000032006411146943c2084410000380d19100c3c41e82d0b132021030b01020b4005010701d5103540800d00c89a4141c603031003c5ea010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 209417517 1250 209416267 209416297
    0x30910030504060f060f05030f0a0506041e0605040b010e01080307110105030a0e010612030e03060f01030209040305040e0a0504140705010c020f0303070209070201022a0c101b061a0405010303081902 87
    0xc2c6401034010041514441c0da0700c42e11501400c200d10140222b182c90001c1e41200142800e03540b01c1d220b80d5452050282e60040380d030403564076400007a40174441e1034016401440710704041d40c1020880c2d6110f04044e04102070a510070700505000580e0113180d03c0c1c00b00402e1070029101d0304c441f85044003500754242a582154201f80000c80c2c6082103039403500303c2e54020386e03404516140e00c600f450345030b120503950b0700007071440b9200500140c145100700a420034400e00d44285041c0d41c9190810900340192070511000d902d0790180028171010086a0103840b500300040c0c00c2991030200084c0c10061030040c001e0044424800c0c0e4050781e541481501d040e55000381030240c3c3c0d4038101800038000e501c030340b41140c4036103000154008640210340d0304080c002e01c500006c0008640c10801c1051300d444400d0702104005140d40d8600303085510b9080091a180f060300080f840a00d40201800d2146d8429110760103549041c00410101754404c9816401240b00b05038040d00700e0310469910061706c504184240700341 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 209418767 1250 209417517 209417519
    0x60f0b0402180f06090603071116120c05040203100e041e15110306090403120609061509090b0901120804120b06121b060a031410031202030910030504060f06 69
    0x40c58164064010b514212803103180c031101082001344600800071810b8101d0018000120070a000300e074035501c2808100116801e140c030700030f001e007058141c0340c10804540010070300810420070941000400380ca001c035805d40c1940340c580c244046486840c810341e0006000d01c80840d092006094041c0040d00c0380c075002050142050411102e84140c02c0c4064059038602207841d240548d85800780c90003090002c10030b0802c4c0e25181c6046031400c0040800e01030459075110000b031038076200e1189400616421541b4800a000d914000d49015503079404450b00d06d00f0f10032220b40b9580c5204030070341507034102a9485480b91039030074090303c1e0303020b940c0001c421070354013039400020f00140300d080511855040720301c0f814a013208650075880300107500000402000c3d0001440b03d07441c162010b40345440e02032900182405891b00b00c0b406444082d980c0c0a004450381c3c909000340000391080c0c4c11b0300d00e4580015840c00700d41d50081024944108241000c00d0707a504040341c10007607a60030030303500702402880031302c201 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 209420017 1250 209418767 209418787
    0x6020d0501050a090618020306010315090b0312040f0608180601060e0a08160501112406010f0801061e030b04050a1b020d0504051005211f080604060f0b0402 69
    0x1031400b8001c040c0b00f8250900001040b003d64000c0c00191020f400d81011608092501000690005409141807584508988040c40c04100d030750401070240c0c44022440304861707414107052148090702484c40c407100700014420802c01420307c40031612145040324442d40c8042004010b440240c20005490003404c000060096100b0000d4298403012914490310030f60f146c102981e0b980e0201c4082c080d05d070100001304170030342c0128100e601c0111580c080d10640e50141162105091b248440050054100410322034556400803100d01e8010003410500780a5050032805440000c0640c0140482e80b4a00f41d1000c1591084e0001c214805014009100c00c0c20061401005010100744200d0481405a602c507407040c80010380d107015844036211540703010304040920940c5000c1941074810b100c0100700c4040e007490010541c0020030410110703240d040c203202210b5040e1101400c40e05181808030300007802541d1f40812180e03042580941c000071a000c100c0d0094020344000b8000683c010310106001480f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 209421267 1250 209420017 209420021
    0x50601030b09120703020c01030f0204050d08030a1803120b06121602060f1504020d090f0305120f0f270706020d03050c0c0d140f040f03060b01020c09150d06020d 71
    0xb050314405481803840c00190440c424000c410014005906c410505030880d40280d01070008030300c200340090300d0140c545010a03810084140304840ca4140001001540652031050049401054551180c03541a0f40c40041c85c045000780c40c0d4020980e150121501c40e03581d00b00300c0d40030003c0d00352411418903140703445074810a240e40500015010b01030002ea841c85c8450740103886a05950f5081108a610405001c02500300c4032494032030641d19032010001c80c0004011401d22442652641da89414142c80202c0820001d441e9404208900c010b001c1d8846008480e154841030b080d81040440b1044c001946050644400752407040c041c09102207201a40031428006041152700c0a00c0107454010800110f8403400d12091103681060102c19a00b6105404d081141c002c00e0000504001d100e282c0d480b0180d01036030004203500000348003042000542d010f0b00880c500d00340041e00344001c1d01d001059070341d0300080200c0d250044805000c446030b5035404040b000130350002421902c2c0d0755a0420040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 209422517 1250 209421267 209421271
    0xe0c07210305060102060f13020105040b13050109060206010806070507020d061e0c0207181d0f030d0b0418020f01030e060a060f0803031e0604021b0a0201090b091c050109050601030b 80
    0xe41040b0000d42d03254000586140120440c0f4415115555007031011051056116400c134104802000005414602c460290000c50305442291900528000001d004640326a010105540100c0c004014803400404c0f159071040b06810041c0d50ba802910004002e041d4105000f00f03502c0c6403c2c40000403040201020b88030741900402044000c18601c0d00380e9403000c82c0d01c01c0340038407038003c540418080300981061000c2c9254030440255a49141d241d507040401e220080303003d0790320105840d81c1c168810f0152000b0380b40162402c110341480206402c840026a00000e8002c1c42009c814240907446507020b00060904541a03522500b032902050002e801c1c2d40c820030818403025900800e040001004032070107941001c0700c5c075110f41024108000c0c0420010b2080358010b50038048920039030100102da81c0d900e16020090482c01c0c40c0792002400d008082d030001e802c00030b01840704650584503101c802480d0711000c400244041418548980034040b00d11000b45036001e41d0b0000020000e2400010b8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 209423767 1250 209422517 209422583
    0x91b0634110301060e01051002070f0e09152a09060a0809010b22180b0408120f09030405090a090602190201110906040e04031101020c07051c0201090e0c07 68
    0x2001c1e50898002c041c00c1c0c540600030751020a0110300104400d140003051030002244a0046c1c0e01d40b00e90b503103d9104c4c00e4100303501a422404403101088100d0b001880300d6650300410407030585580c181001304100c601115042c000000c0c22202051103000f980310150313400300c03a0081450b80c2c0c3d108042c078010308040c410389a01260390300740041c1d40c68034506414a00d160407026583c120304843c04040c5c0101400015102034902001da800010206080c0888507200703900422006990b4000c0031015149081c0c020050f11154000100b170000c0490041304803411100201c90741405a165051141d0090039030040042c20184005101030040d8160f1107203034001142d07a0000c005650b0343d0780c50310700740348207035802e441c1d0022080006019010300e07440e156802501030f240000c804003130b0181d850b023203a0285240c9020b0364800340c01040300c6c1c50240070340214400584002c6004030103e500103404641180116080041c0140015000300180d2051701c11880d00910b000c14900141c0c1c2c03e2181c1060742c0f10f42c403 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 209425017 1250 209423767 209423783
    0x20106030b070e0f03060411010c0602070c0e06030d1e03020c010e030301090608070609060801230409060204090608150703020f0f0415031d0604060216050f01060608091b0634 77
    0xe1050705c0d0220f06c01d885941c100030411400c0c28035000450700294204d0084412503401e00c0100c010075030b41c0c001c1c4005000250a005454140a0105841c0140c003500750001c2103048a404610560b050720700940c80c4403d030070056106c000398070009001d04a171541c400d2140c8008000014000030580103241240c04150503150841d40b01e81088030f03e0b009501620300418500c0c0d00400c0040090055050301e2480848031741d400c150311a00241c161000b00006444194001c6018451003a0502c111401030160a0092802d0340d502c000520500360b00410078005c0c141d001c140d620764011204121800146402c004640d1503446880b128200b40e110551480001e2600c41d01a50345140706959010f581401e000a06141e5110359440c13000e075002250700c030b00e084084d81d41d4800241d0200030b1908001141d400208500d401c258004080080080090030b135a0b004c0004c170340c07a8400134a0400d84418080d20226078400401a281d4800358400d0b0003540c980949004094420104030a9414418468000703 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 209426267 1250 209425017 209425039
    0x30306210619090501050f01030c060201090b040f0302190b0106080a0606051b030d02040801020403120c030804030f0e0d030e01080703060f090209040f060f09150f1203020106030b070e 81
    0x40c1000003184480c0c0140240c0c040000300700c1848502d40340501003280c401011601c0000c59131641d0030350740c0541f601c000c0d810b02c40c0014002c0159064644000e452070744000c000c5421552140d000c40e030386c003800140140300c111071744c0c009043c424030803509122508030f401450111785150102c0c62070780074400d0070001208040800c3e15203076070340500411100c06941e01070618030441c51190740802032840e41280791108000b4125085564009800240104400103842d80c2c61030900201c1e43d046502010100075800e0311140000307400c80802500320b0307050f14000c0480080601c00380c0d203020000003000d602060300070542c8101a88040d9143e040042030380d07481c2564031200d50076401d4410f1030242c01c40b408064141403001d1a01903014001c804801040071400d810344d034001d501142ca45800ca80070100602400b4810540385020f00724400c0401c3c2e06d442071607850951200c0c101c618038002c03014000715801135401810b10035004400655003101b4400e2090070000d5001d401c912a0326070550154410303a103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 209427517 1250 209426267 209426299
    0x1107050d020a0c051306050901090603020f100c080f07080d05010303020c0d020102060c0a020c040e0307021008060a030206280201150b0c0d082203050a080f0601020c1507060905030306 81
    0x280140b102c2c1d84040207a80b0fa070700b080e08102c2c002c0c04084040c02c25507550b00d00069541d4451488500034030700c0c2c003070000b2003504500500c031040350085110b60180340b90307145c03125205500c40d03404401250003056841e01d812541082c8482d600ca42007014106680104500000480036130210b0f04172440b0303070201e6048010072002e1060101d01508043d0160300007a00264280280000800500c1003500c1510852009a8001400c40d6000701c000102944089140000c50401d58602d44414659080c00d0b00b85151010020f40031603041e004c0213001d8031004c00c0741c403600060244a10182c0c41e00207240010040c081701c00900901c540b072440c90081d000000000391407941c40d021511409021405440c644a807c9001c0e00d4510002d01601100800c41c482503090b0f024036000c50502c54425501c4566408031a28018807000015204039031000c210f60a00ca066a0005070318a60044c054130104203400703405103d80b4140c040c046002d0550303420b04885000f04400440214030905084610740c11902d5814 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 209428767 1250 209427517 209427523
    0x1a010318060203060a03020d060c02010b0d050307022716090618050409050f0303071d06091c11060d050105130603200d14030304060605040513030518041107050d02 72
    0xe14103800580545000d200880c08980045030700030b00107800302024550380c0d404544c3c0c641b61142c0956020390340300d24440600c1d40c28010486045401c0b2640501211252111600c074414210020300c030314000c440003956100305509402807512048103444151400301002082c0e00c010340a2000001c481201c0030427118020001c50500c50041d04221550900300004d000040034560005da400d4450407001c000b400b90100300441c440c10496031a0300007680d1581420420a40c00760b0030b188a05020300401c80759031a00d04000500b0704901034900c640e8111402d00c0c821035507184d0092500b0860000c3d101441180a1700118121442a19000010008482907004442d018000100b5800c01040143c001420481c08070140c0d00740200f000ca862001561480d80900d1000090341031a0400f100300000c1c4481449901d00600058030203100502d070103a50f0740352492104070006c052100c0410341c00303860716903840d41054158020304200103040031000640d40c60741104030222140d103d4140a00341252002c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 209430017 1250 209428767 209428781
    0x30c0a0f02012310050405190605060403022d0a0602070e0105120a26030f04021003050c040506070507030c08070315090b0106030504020d020d08130f0e06040b010c05030a031a0103 79
    0x1250f4054070035080c4910a540301200030701600d18420040d00c004c2060307a290311405008107210450b85624050b441c80c20015505280d21440c0720385c000344410030241e103511000c82e104020030369000440351030301c0c1c01481c0803600c031000203500a185003601080168000444000345c4817958022006607aa8100304155002c5400511000e9045815403c00140350100c0300340180010701d065504c07070031501c551503416810480301c03803821102030300c10b000a606291364080c40941003440c003406030b480c054041c0c001da44500e100b06c032702607a800074002d01030102c00d2144001130340d40001107030b00050352504042d640300c14a000c01d640042004c22030300f14440c61442003020540d40030300c0382c4039668a01a001d80050000400c1a03810000d25400c0c880140e0f1680507032114240301d510495200c034601c514022064421b40c01040c6a0864004107100c07501d03030141c01a51244007254042041d9045100490b0302c105595402441c40c031000c2800c003d600d4040c1c00c40710744084001c1e40a151740d00c080e8011402c0e0344034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 209431267 1250 209430017 209430041
    0x10e07030c090207021804080415020a1a150405010f0f0f0807150309050d1106061008040807030302040806010602070513090b04170405100210050f042a0902030c0a0f0201 75
    0x4500810030550702c00c1c0d0003a040050000300040f44080450342c1503031001d1401c9904039807921002805025010603403040850b00764841c0b00800c1003074200d980c5d418103122080820002049070200060400a042c0d40400071040098014011035960ba01c10b8020280c1a01a12400e0b812018000c56a080c501e441142241d0030701c4002c0c84560302c0c0c00201c0691301100d0b001c1500700b41c3c17550403010208a0400c0804014072155944403000c4025444090400c003019100512038045141c0300d1800590204003d600590003c031f5061f91100c8628040c4c0086c0f04aa1001090f4040d4000001d0f8407900458103234202d940c10340d089118941c080d010201101c811180041028800e040400c01050344803420140e07039200c200480b460207444078005000502061400c10060340700000c07182075074040f0b00480380c03c08000a074081c2282401d070b0b0f03400f0411190442c48041c007555001000040001d844136100107100e020710466a17421701104201c2e059000c140200085041480d405100c40d105100385400111 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 209432517 1250 209431267 209431283
    0x91e060c160501110a060f020d020a050d141905091c170105010203190f030603021513080604051e0c0406030b0f1819080f16020a090501060509060a0219050708010e0703 74
    0x1d05c07540c450f001402441c3c031010009078203000c0724031440c426100a0481c41c17200c0c0c42e0340382c490b28103807240c200742c0312400c0c12a41d034244101c0038030081e20800056044e148004000124156850035400c0b4a06a00300103011039000380d60161040054011078500044c1250280003000d40e0380728001a80d80b4400c10741070b00030240b4441c5450071100d20503108140114494503000c02d00b03964940000300c4401c04400a04010440001e000c00c003450401c0c41c1c07a0003442c44801828140c0b41c070383c4440340c9400110461054405102c4d0522807488014000f0030703440d8400400422009444c3d0410810003401101c44c998006003010200c0e6146540104040090600d00000d201914540d8084005a002e80d8002c5600c0b03c1e040c84086d10102c16500500b8500c1c0480c011014500580c1c01001350514840d4400c140303861400005200d2954814100ced0301d580c40c01c0c1c482554030040403d00700d1600d40d40300003003e800000005a901000000301e078003002c59401000074407101c100781c0060f5031200b52a120080c640d031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 209433767 1250 209432517 209432533
    0x60d020307090e0403050714150106021006090b0303090f06040e01060201060302150c070b0d02070b13210f0516050a0f0309050a050f2403011d070311091e060c16050111 74
    0xb0f8851240030340b08c18000c01550000903035089401c0c41407800f0380005015820081c3c41d4520058a0b1041d031006080184090100c00c2c02c4201007a220f01c076061307805000f15109200880107450f0b02e8100c90040001d01d10700c107090760b502e0000134020030407404101d10a4401007200c1c4003041107c000e6819402059000e003540034600860981c80d0751208102c02c000c141c092200202113000f1024161080645010084421020b490281c0081c00b24181e440700d096412034032066801d5000e0b0302c084a981c03e0b41407190355001001e141010080d540c69000300707030f031040195540c20009002200701815210751105100350344c450042003145040390003030503008692030f414080c2e246460240079050265020201070481d030f091134044060b1f44260803401400e0f00250600e5281c81000040e1a44580c591404002c0381e05401c04016240c0304860302c0910610f8588030740715030200600c13041c03020090000c0500e607844401c103c00039111291800c02a00b2035980346000a499400380350010140340a5402404002c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 209435017 1250 209433767 209433773
    0x2010b061207110c0a03030206060f09100b03070e0d030e040b0604081207081e1e0a0903020402090111032106030604050c010c031b060504110d05100c020c060d020307090e04030507 79
    0xb5000b1a50140940b10380045030361580c1701c420f80384000d940603070f02a06440c60840c3c10300100101803031030b49000b41c0d064010442000105000042075402070b122140c0e8039240c008084a0a41554901c950300429102c03080042541051480015100c25241880100b0100042000901a0b445030408982216540103079a210399002420880c1c86000d440e41032400c01158039419a40b60981c000c2c0c1200b00103840010220140c0e440803140c0028160b50340707020211400148440d07020f20000780280c2d004030301c40720560b024403c8844420380c2c650849881c0c8002d800b010404a081e564015814046c60303010602900340030801c0d500c500e4003c00100103659280700111602e01708400b0950800100001c001c84c0100380c00809540140198404034250520b8144001038101c040362441c070940c030300c040313403000140e02045500308110045070004071004100c00030b81c1803202c805512035001000040200011a00b54051401101c141c2d503050b18142e1118108400060156405008a4810b000f40400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 209436267 1250 209435017 209435027
    0x14120a21020a05180f0a06120905060a060806130218130b0702011b0329031507020d0e040912050a02011e0e1513061a041d0c01170f06030307020303040b03040302010b061207 76
    0x10f03a0314008c00001c0c408525441c1d5505041d01580d10a0002d9250041001040d00810445400c00c600070041c4a9030304031a80040e0400c1d114002ca5000d008a4100207152800c0051780c1c100200d0b0041c0d5541a01d181c4104000c0c020200880e8030707d41c00780c00310103c0010301d20038410740101ea00c0000f4182c0000760a019401c0804c4032041d1000c2e4144104e42c2840000d1103661111800344049400801c039007201c4000240841d41e400b1038407401980340c40d200310003290107040d84020341d86450504540d502c40d8414102c1c003411014a1800e0f01ea03002c0c210784080424103a110480700182c0c441078070b0a0121122104a0074041542d1600d0720710680c01c2d58102003252036009c0c02580a4150600304609200320200d402d60b8500342d00d01241421206400310a01814081e550b91040240b0b403003181c1c0c0a01e08145070f060032001d040003021003825000a40c3c2c50b20100215111030390010704998440750b0310030001c1c01640c030031a4214019400d200c1015250705094080e03d40c81484540d40420540d1400b9084035 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 209437517 1250 209436267 209436287
    0x7050f030f150d0602031b0a170402120a21020312012c01060810060906050d0905010e07030503040f05010203070812040203010f061214120a21020a05180f0a06 70
    0x803690a4181080070310f5882598014010b0311a090140c0c4070302d07000390034510b0307196144200a181142084820300c03d03030384050b0380016902c1c1c00030391203c01e807118000714040b1807074004805014401c5071465410b204101084981001c00040740c424855071501b0704989a0203401c81a40166a4010040c015860406110801901c3c402c00c6e4009411101c40626400f14080c0d000340d02140707494050011840034080310350041c081c1401c085a0701403030000c006045101c0c2d19006281c156444800404100c0f00303411202c00e080a400484080700d88034200691030f0f600a110740c001a00030310350006815400401514600b0b50010700395420a2a8060fa80490400050080364555a9008001440c4250f8800d10014100240401a0520b824031b042c10f110a01080010000d50040c104d01c10740401341d10403900300401d90710b44641c060250485031032130b01c220364a00c040d04a0010540310880c56010000d010824540d5286503c0d03c01e242c4140314110200450041c1c1020210205000351801480038207 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 209438767 1250 209437517 209437531
    0x109170a080f07020310050115050d090606060503060306220f0311070609060e0102010204030c030f0206070822060e09010311011211030402010e120307030f0e030a140607050f030f 79
    0x40d4004460756611007560b84110500b0078080008100c40c42035040400c507001c50702c860103404010079410704d8140e6200c0000c0d0031192341041000180408440d42c550170030501954013586c18050151200b5014007160030441d0424005e200b81000502d02102c0c02503452501c503950145040038888070b440d0a035280c0301c007030001c1e020700030b40d0001604505000c002100080c82c0301d90f41d100740241000380c02040741d45413118040c11680180028408507154402001c101c0364400d01c00b050000d4540b010440600030014098a80702002c2182c005c2c00901d00301082e5050041d80c1e00c100c06640700c0d00195400591100354a4002e020341700140f00181c41725114804800e014100b190381c8540c0c180704501a03a00c00f06040107a444040140300031540c018030314811000d01200c0d94039103020b803d1040360f80c2e070141c19400340c100b1480d020225421030280383c01c0310f010900902911860110707400c0864980c03800304011240c1e40b02e80c4002482161061094400301030b102c004c030318074540310030280349613141000d0016 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 209440017 1250 209438767 209438773
    0x80f010e060d060e0613121d040f06031e05010612051e01060519150305060d12170103050c030606090613051b04030b0702010621031815020109051b010917 68
    0x44c020520803c02036100351004122070300402da04d8681080e1801031448038030280502c50045107100c01c00541d884000d0350f0140c50000d00918040749550181209600240200c52099894800c2201c94032100500c94001c20084c003410f80d03282034208096803c48006170458016960080b04801d0708030f400076146100d14000720b40c641d2118001a41d1403007000b9030f91108180640d00b044016416400c0034924a075604040042c0d14152000c5032100c8410703400104072500e031120103c41d19000340d6400e142e410211040c18602e40c0c4078509180c0d00c03c1c02e000030b180700c0c0c4034800c0000c10514046070403510800300a0100f004841510f102c41001c6d002c081c28040c80c0e040b006040142d80d21009014000842c081e24a540b103508110401034211103542d0007a089020350f008000e00000e651007010b685e80c41e40340c540038400441107992441c081000b908600c8810502e00381400340d155054010784c100ba802101074403402c507400d80c4005030090603c01c0c903034045a0016020007a141140402c480080519419 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 209441267 1250 209440017 209440031
    0x504020307050604170c0d03021e011404032a0201050f0c0a12031d06010b041a0717181210110d02030403020a1406070e090c070c080a03080f010e060d06 67
    0x101d140d0440c0d08000700b45c401d9140e0401c0d814004100081740ba98090700c00f0310190310329880080d2100c0072b03d00f2505401071112440c55811100750f00100b058002c1c040110300368102803500811109450149200c5041500280c0f0402d0610700d03030203082c0e1a4161903291170708060114109403904184511402070241402c2e000100d511030310006042d01c655a400030700504512500002118070b5801800d03140d000b00b0051280c2e1220701c3c1100e007950107040b0008003240e202078031240c0c6485540001449207007880e201d401010500340240200c0c0c0500001d1101e80311196003488044a52080c00d4280796102d140b01d801d0108099010a8100410403c400c6c0f6181510b89640180c0c1d0042d1800c8006a008141c003000388180b4442d10420300628002415090810f014020308000300716104a1290070504041040c0045c11780450f81d0059000016607482641e03240c1c80c0362110b800b4803042d800305650306d0006507603150302c0c0c0b4a203050301c0a8100f006616200d10b000d011001014403c111859952040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 209442517 1250 209441267 209441269
    0x207090c050f07261608030402151b01051609030f02010c1b0f05100c1b12060e06060a0b0a0c06060509041110020102090d0b0a09140d090f06080a050402030705 70
    0x30052002e070307009900d0040c4807002c045080b42890481d100c1c0003c90813050010140d04115090060078213500011a687c9035102e40c000940032134000d44401e0f1540700e00080422081401450307000c00344a84030020041583c4405402002c400e802c003008000038040c01c6d0074400501003c0440410500615241058a200356180d40910f914800c01246c41a90020108400640b554074030000d04400d45014016022800c000b50298850660080a900d05612103042521100c0c0d00301c8010040954003090380151410000000d10350a5001c8045005000005006040a1a0b15400c440e020720045107030a094100407a10001c2c1d0060440d02c4035181d5400141c2a40c07a4000340d40142c4c0030746990601d0b850300d402000064000b0303840b02000d41e40144801e030b40e01d940d500303815403100e500503401039240d5688010001c000c01541e41d00a00490540308420f407055800030709203c1c0242c680d12a1303a2601e4803101e150074050800e10035200020380e8180007411400045d0825900507201a0841c0c0ca6503071204 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 209443767 1250 209442517 209442547
    0x50d0213030c090b04060f0b1b1e0105090309240403080703030b030d090e0c18060c1e030408030a140721030b09090c011808011e1b0207090c05 63
    0x180c4242e480c050310721424803280410303206141008004032410400c0740c1c941440026032600f144141d104203400410307640c0d00c2c1344000040e407016030700c4642a2408002a05002d202c1c0d03405043c2821519881c2000090740700e84000220340d40080c00078458113a0f00c01e44802911007a004402c103400480e000c1c4800000283c01d0000750003428840c0d00c0215a6803400c405051400d02c42c2112402001020741042041031180c0c0d50441e040890001501c0e5030b4200b203446400f01080104102e80c10420015004405230004900c4c0c0d411810141405420400b048044990768000d901507034403942c001b0491007d41502403140c04d130b0700c81040b4180d03e040034082d03203039540f40306540c40040103024014a0044201641486004109281242d541c03006082c1002c0d0740d0396440c00c01e00020f05214070090300004410941d41042c008ac29560000c4c030401c0150300c01060000881d0070f2400480d4202031a110002a00020340410068254010a0f1240c42c2480c0000500b80300980d560038014104100c3e10075240c10 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 209445017 1250 209443767 209443769
    0x52805060f040317060109090b0a050d05060621031210080a0302010b0103110a05030f04111003021206040209090f07030e031b070905090d0309060f020c06070e010f0c03050d0213 78
    0x10381800100e00c0c00d801c01405a500ea03203260044e030342107201007043c240c0e04140800241e8840140005813200c0540116a84581d6a00f03c254030040c868140c0040040002c0c8180c818001075420380021495542c5110405010002c241202d80040c0301852503101100c0415910881d001c0900d51050707556a4120700b461044142130340181d4403030900080301c0d40c1502074201c15034481c0c0d00325440c5c041a204000c1c103c0c04094031141d4405484000b1400340400c2c014070321001c1c080103101c2480d6041801e4042e000b0b5202070442da100311801070016025203494400c1d2030709024094894010f599500313880d54507200c5c0c000c00c0b4509042d505c007080c0c1d0114404201400c0e01c645034078800c55003002402038113407a15040f0303031080da041406c01c400c1102d6404d01003142c4006a00b541404200380b1028a040c5000c0c2c888404160f0035148086001240c60f0000126203010303501035200c101350f00c56660011212400380c0c1d0840d0300461046130b94240040d00c41c100515004c00521801400c1a142c84040b03041e046e02 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 209446267 1250 209445017 209445031
    0x14030402042a0207060206060a090f02190903060b18070309050a060c02010b0a080a03140d020c0a0807230705100c020a08030304050f010b0d080d090204060e0a0b01050705280506 78
    0x1466500d200c24580422011010317018500040810707281c0103000400300d12050107901e8500307440f035900080000c129010350300f421101c461401e0401d800c600e001031a03038080e032109541d178600703211031014203050046511510f00c031a069813024903610360b4000e4016100c40ba40c101d1b06c034442c510303800c8040f074402c0c4102540c2c3c481c50741c004113148511408000320401c4607081140d650b000340600d940001c0c2c2149564840007a9402c1c0c4944070005000740600034054046090068061540780004002041c8010300f0000d20404800d03440402250920149144031502e410041c1e00c030a40a005c64a000400c9020300419441c140246001e560f0100d200940a64400c05003980044141b0082100c00e015600c107819100c0020805208980001804001c0b1080060801c0100050142d4540c00e0b0790456990241c0160040c80295951a183d49640fa4110b43c1d031041145019030f403041a6100f141200d640a03084002054410b07010b8940481e0302c2034602e582c09841000c05900c4002401c1171140c0c51003905 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 209447517 1250 209446267 209446331
    0xf0105030705010806031b010215092a0102071a0c030d09050c010206102c100611031201030204020c07080f010c0905040507050a0c0602251a04031403040204 69
    0x124290915251a032a5000141404205401c10071075460024400204100c0350020311211019030300141d09010110003c820102c000108202d1400c44c002801030407460400b491200b003840004002c000041c04400e20307401a04403e00030008130040c50489410a045030440b03915000503c5e40f42032866000800005d000c545444040c070600409200c8402181d00030b0014010702c1c6095501007407005000d00134040b2910004561000c58030803104048802d5228008200b000c0c10f00301c074020311185480c4510300004044070802100c480020040d545074001c59010303e0320590950303013088080e400c004881c0c91207215510002907030300820030401440410100001404031640c100003402c2080540000d030041d41808180004942c0c09004c9a1107202c0c5480e044214406914004c00a88941c3c441e034150321380345882d11614040c26964180e007503485214400f2400031801090b00380e0020444000d004280711903688211601400002c0d54414402800055014500c1d02c1c1440b4150202c0d1844030508 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 209448767 1250 209447517 209447519
    0x40906090b10050405030a0b1906090e2512020609040501030c1d01030804090e0c0907091d0115050c010e0d1e090b0315010c020a030501021c050411060a020c090f01 72
    0x1040107540800602c603549482c502e0b0606000109a4a15100200414017001c60f400560b1111652403035800349250b68809100b42641d034424040508008140c8600c10302a9242d6488080b045800d00c0070b0300440d03000700804903072500e03121200c02241800140c0c1c006104020001c0165100c2c41680c0c040c40c41038011000c5241064450440d048100310440d041200500041c00840c4900e01960104c55900a0204011280f15002c50400f068844044d421400f1079042c4204650068160020782d131a54401124583e01c404441c850b10f0401c0c400e0b048042a14880003070581d108100420b83d030803041740041048082820380d54030304041c0726903a0300003135801b4850840c52250382142250b25102850000585070500e40740c41803e10015000c0900301601071200d6100303074000c009481c03a141c1c004060503800c1e662410a039000c0d522045208808403043c814003082c00960703100c0d15000d0358100c01407110582440c000d02509030b100000c120154403030a41b88010903030b24051580c1c071405504030039403125 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 209450017 1250 209448767 209448769
    0x60106030e0f0706110706050c060c090d020411030a0b0d020f060a1709030d060b03060f091503010501030b040501051b030103080714010e010b040506010903110409020d120c050d080c120c040906090b 87
    0x807a0254000c5400c105040000c1c40709e0000000780701c1d0300b01784030b002016901e40600000414000079000300a4200c0e040c582d2100c0700742540d0020310710501c8881d000340201038141342044802c4e021800d00030340c09200a0f10712030503404c03c50040e11904424ac24426001084102003007802c1e4404c80b0804141c1d4400030705020b100031039010311402088074641230307401c42c10700400188042c4500301006020302440c2c800100e91880e14054400d116002900800071540c40e804c0c45243d018044405031b0b6550301b05800303d0004000e96012140810540d1b44940c00c607421541d03420729aa02608094841d00204020300081100a125400301c0301103001c00040c844600c3d000780710a84e980180740030305112008108001254100c4015808060304a4001802460b039100003514601304120241c0780003410b00070b81440039000440030b0300c0c1c5801481202d06240340c1aa00300c0c0c04250481d8100b8440b40140864000e0101680348940c00980030704400b404c02c1d0710341c0070f56000c45e08550712080003e0f171184201c07562 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 209451267 1250 209450017 209450023
    0x2070813060e090f07080703150303081f030203030a030e03071707061512061503060c051e03011206090c030b09160b03060a0b0304051f2903060106030e0f070611 71
    0x6818050783e038400742d45490304010403201401003030306040c001002e0000d48498402e80c090103083c1c01c202804c1c000c0c02d03103034180106001d00440c0c59a030200c4201c20451b200901e6404648200e81e4020011454040450011409424120b5a50340075200a0010314001401d550f510a4681840e440c0790b500d400301800d2a605803480020200c0f5403514a003400d010441600c0b2031002484d070480c90125900341030f004000c2030450181c0c800b400c0d4034900030319160f500c2da01000070070b441e945080c000c3e00000c00030000015184401e206200819101e00000b81c00100d840c1c000c290f00901940c285034000e5540d888880d070b11302d0101c40d02240c5402020f0590031180c44207500f1805402c0480d0110704500c0e110001c01e02d000300350f0043e03000140d40800002d040020410038158043d003141c03221407840ba2022001006085041d032003140c1d60507000300302010b1b6000c0c082140c0310480300030f00a0816920341402a0001c01d41c10104070590702608100e444040010486a00284819610030380c542003c00d0019003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 209452517 1250 209451267 209451287
    0x601062a15140103020a050d080f030705190e06030a0f02070b010608060a0801090507061425120c0215030901090f140105010e0405030307050912010906090b07030e0709050601030207081306 83
    0x2c1c0400b909801400580c13103403001102074075010703903d904007000745040403c072901a560700c4100540000042042c440e9010001c0d01020366420449030707055020b40b8090b02c2c5207090620b181d802600034030004025544681040b0305559481a005252010315180c6041c0c000f400d0300302c0008a20f0940c00d002180c00c142da6140300412101d0700810160701190f860588401c498420002001141c40006a400c90f2950403102242c10301c00e004c9080043c1502c00c1c0030a10784507001520459220704c060001203006850001c00c0650041c00401c01c03e00e80351480c0e4050700003404140481d0358a0b07601c40b00150141104209060082d41101d9000001c0700c0c034542507d2050308212a0030100006120004a002007070340e810041a091017a00c0310890004505540401c904a4950350b00344003101d014050740703500c030a1045003d00044882ca55540b0030550907a014400510b01561010004000042e079640c01260801014500546403500710303100c0903129002440d00c21003c0c600e05508000d100d0308001c0c0340b2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 209453767 1250 209452517 209452541
    0x303060314072714090a030f05030705031306020f1602030706030204030f080d2d050c0901020c010c02060904050f0907090b06090f0a030507080309010e060c0601062a15 74
    0x401518103000d2189482e0441d104143d854000c0c0000c21011414aa00000444029a103900c200d510b01080d03020755172903c1050a402103080c2d18144d220551043d801c59221390000e8490a10716102d02a4034042491034031b0b0260b5240303034280405108a0400c000500021520701110440060b0500400d0f0070510150b00800506104000420006003100b0140d0030392500551059142d040c0c1100007070152000d0300e6080440b007101c1411842c5180d00d08103104142c0410070f010007a41d07440803260f11080c45003100702d42c007680c040c50b00c2066641c801d01d00a2103091000d0155820a41c025000c0b038203680c03040ea64950248400000c100e010407081242c0e030000c00e00c0f00400c1c070144400802181c080d02c240c51541e03004424400346407545868201050f4021903100085400081d036501860391a50040012980002c4041d41030181070f141c00000e40b33072202403a00140015901c1c1907030940d02003140c2500e0180809002c05000c404054074140000070a00a001c1c44500303046071003003003080780c1c400301d400d03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 209455017 1250 209453767 209453773
    0x20a03020f0a020a050d0f0209041202010e010515210a0507081b0105070602160b0f0105010e030303010509180a1a07030f020315090705091903021005040308030c180d0303060314 78
    0x82c009039070741e250090121441650340300084206410001c100c529801c50194111007000c003840100301200d04000c01880640e402003200c00090040c1d1403d840080d1815a003c441200148117549071694018010760314400c01203c40e5074111550a0811100010649440d04689002c20008000340301800b600d03104e0484901c03001d007100c00040d249004e2080e01401807a400b00d150300720444d8041c007257020b40d07400401103c0b69182c030030002903105c0424020940010b0b54803030303040308505000045d00d040e00c03801050203180d0368848030b0031004801d000314802018403850301c035480403400300000003e1b4810f908407140e0715860424405410780c7c00442c041c901c001d104200b00080c05004090003a00118210340b111015181c0300c500325010b0040000303040e400031803051516050041000c4d04170440b4802e503402e114a284086054945016031f00c00501400c00c100000b810000c8058018480040901c5400105610382c00c01701e000c0c07100c03a40f01280444e81e0b035001402071246002d0000c141c040c1034001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 209456267 1250 209455017 209455033
    0x3020a0b040b031303170f0114040605060306040b030a1506030b01060e030c092d0405070608040308040b0709090608060a050c1804020d0603021207060f050702011e1e020a03020f 78
    0x741d54140f100030f04a061a116941d00a81018803a469a04042d003901801c0405410324107580500180d0030f10900c0c60004d40300361300031540d050601410f422298000d00440c10f550301ca60600001e028150403840d8140901c07410600002c00d20802105050128000007654500718504071400c0d000680101c0140601015130202075a4001189906480240c6990156440b5006110b24050260701c0c00030400e030300794881c2c0300803600130030803144110300580449440d9542d0301000d0f035030b0305400e4401030005414000020003041004040642106045c54200300b42c0d030741c03501c0f10310807500715402421142d0042420310035488014029260401d04850000307242c00c204140c0349102c400101c41203070096401003040d80c82c0320603540c003002c000c1d600074000c00e81081008401c2c644a070f41e24020900890f0a211004050f03e11032425a4030b120fa040c2c4403e150180c110034400d140703c00d070700400d0303040000d8002146040b9400f062074404d0b1112603002445400303520b01d4041d0400c103d030360b0500950b502c402c0f0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 209457517 1250 209456267 209456279
    0x705010201051006050a031d0a051b0a0b0705030f030a0c1e0f200a110307061e0509190602060925090b03100e0a1719030f020c01090c03020a0b04 64
    0x1003d40c080b6651810b00340d13600c540035901a0040c14280107044002c1d0304881400e4414200842c0b04c01d003d030320841c10f484161302403000195040d00340b074010780c1d040502e068091040c801c0300c02c01042d0ba103004204076403d01c003403008160a141d004842e00d0b46150389903411510350700e421400d0b45c40c2c2440c080d003581c0c07984802d0407801050203440c0e416140810034130301d4204800c41a00210381e50b014040c0c1c3c084d00d0450b0190b00302486c1018030070f84454004e1007110000240184a01e01100040400f2540d08011608082040301c490300515544c1d41d02c44031206144800e2700d4814000402851a500a030000d4601700e06800d00b003500039801340c10300740c20741401001507246140d4524207603840441e0004100843c000400e1400080e84d85400300741e4545081e4610241c0001078007040355110f001d096103401c1c210005010075005003121800207900034581305d84c0c8103010713800001c5c04031543d44006041c642241140c900359082c130726098400480c240030038010360038a81482d0025003808192646850f01d025 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 209458767 1250 209457517 209457541
    0xe0a0b03060d110f030f03121f09050a0609140106030b0102161205030f12011e030201020a02091801020f0306120a05070b0f0403150f1b0203161e050a0302070501020105 74
    0x7220041140c42144540d002543c4c0302c00c18860398074006002c480d6501d810307440e40c40d40c1e540092144046001c1540003c2c0c41c0310304040b14030050f410307102070301c12147c0d16280d080c0f0301602010740070729072181c0c4455022034601d2051217050180944d00440754861b5240420140403640c122404070b0454012200600da8000e508c2c0301c2c08111003c04104100c0e01d840d9050a034114044c40031803d42e00c00e0000b0301004000e03074403211a8181e07002200901c03445803800c4d142100d180781078400203015820000c10100546092520305510003e0034a038a04044007a09045003240c0c020842d0b501c0f08140401442001c1c00e01001c80a4500009002080408490344603039075110384910641c0c200842c0000c02c000e42800d08020b61f00195030112100301311070381c1550300700083c0010310841d0000c18074200b0ba0381c40e004503040c41e25214881c1134018524181d40c4c45040e041000d040d420031b8a413085041a001c001101120f190a03a007030146002c2d00304880c66140c0203007040e6003035203d581168148410301c0f07030743e424403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 209460017 1250 209458767 209458789
    0x302011812030533060d2c0a0b042a0b0a03050a02030405120c100203040b0916060e15070c030303091a090616020a050a0b0108011508070b071401020a0e0a0b0306 71
    0x1052030040f15183c01d01c002110352241254201c081410300818200042c0004150359500c440d69103501c2c0f840c0a0111f801d030790340140400103010350a5a1001c24041a20121000c5000e0304494503410350801c0202d031420480c2c12079000c01c50201c000a1500c0c052765051041d25080080c0c0c040c15895411300307840e6183c4d911400384405603031a20014502032080f104020030312920b0580f860554592905080109000c1d20444428890b4090f140140d00c0c90540354070501d0645949440c0d10a1601412052020805284400d80e403155010080078000c280c0030f0044100840c03084d900030880c1b000d1894030f81c2d4405240105000b0b40c1030881d050114415000c2489a8000c294100d02083d4450b902800c0340303846d01c0002e001c3c1150203000006400c0c018070b683c2ca207040c0ea201c000288456455900c0180f031076003540c440c0348910303003101d40280a034a07804002041d507140240c0041d1544001001c40b2401c80e88142c8034640403441c0c2803c0c1071518184101441c0c014034074681c1941c110320306240494505d54103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 209461267 1250 209460017 209460091
    0xe04050a0209060d0f0516080309100305070507051b01030c0915050904020906030f01031e0b040b060a0b0406050a020c01050307020318040e01110304020a0e04030903060903020118120305 82
    0x501000500c60344c660700143d90100b81c018200790744807403150420030b80b00c54041c070210714112031183c0046843c880000c00c85da840e142c060013a40107c04034550450083c4405070103142084030230084800031a43c02c00004035000c00100707074aa00c1c40768540014040326144030448041c80341c0c81504110380e4100350b4000d80301003c1420220342e114001e0703002078000d00c56440350b141e0108010080c0f05000b40c00c41c525906032480358407110900001a5010804800d42c1c500080110002e580000c000505000a06030040e00143c100c602c0946c0318030100440c0d03001500107c00046021030103402039581042040b040000a003411480c500304880000e4607446050310800c0c021003510100341403600d50354040040c100e6102c008208006181c2d51001c20750f0310640c0d099108041081008c140c0e4800703d180b5500440e40345c0c0b600c4002c3c0d840d40d912240507085034203064040d03542e145668a4070036076401401c00381034814440110008041003000c0c0840c1c002070b15044144807100c86a070040c10032400c540aa003a2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 209462517 1250 209461267 209461279
    0x150a0806010c08040b09090c0306030a11030c0a081501051008060d020f1c061b0519020a020301050106050301030302061b030a02090a08071d0901020304030806100e0a060906090e04050a02 82
    0x35030308005031048030400300c0003060884001030000e682015500900400c0c0b071704a451000076202d03241190b9a80c04140c519076410b40008040c240001c04140941802d002d014082c2e6070310104100008020811a43c442c4065400013804441c282c1e02c1032251502420085800d44010070203e24014a103240082070311f4014a81e242000c4c0555481105040c1c62580c01041510202111400e038007590701540c00880b041401c00750802c282d1040c4801c0072200207000e03601c3d5820001c80344000001030f008548648207501035030304884050384003070150f24007902c0c041e225681e0325451480d00915001000b49a41c03501d41006818041d1604807600703c075040329013424056140d941e404009801d0703468a0b03101c0740d4103116107480014001d00424441008102605980f103143d5584d50320a801d07480100c400800081d5050f000401500d48103007240343c2105940f0340303040003111207008503005991b150040c40c04203407201c804200582d4420284009842c0c0c1c0e680c50005814241d60b115038075025200c00074401c00b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 209463767 1250 209462517 209462521
    0x9070c0b07110307060510050301061d040b041b03111003090507061817070312020616080c0403060203090109120e060d0507050c03030a020405031b01120b010306051305010f05150a08 80
    0x402c080090318000d0350001400c02c583c0c1010b90510050139002e00c600c81c0a542040400030ba40744003820a0290314204204104050b0f07110780d40d40b000074034020012500c1008a03035107a140320140e00c0e50741018510807030100442d01d0341034003049180c0900100c00401c25080800c1c4100180b00450722200300c4260341010703459414a618100101c40c415000b050440d10131100340200881d00080c40c01c00c40b4092003415072070300c43c028001c9807508021a0b0142164409107107981c40f1070706c00c00c00c480e40306600010300c90520341c40f590b910059a00a0301c1420b201c0c0e440d02d0507481030054011251038541340e50305003c0c6880341c640c0c1c0802c2890003200c1006821aa590000070031280c043c00489401014600c140d0b5501d03c0c0c4010302d04000c1d00103003c3d09010f4403130340c40c00200c074030500b40d40354404013016140c900c2e581810188000142503a03081c0380d410192142c00005040e01c0e00340203120160781c50346002ca615810702001003c1416950300c064400d40980000640300550142294031110340d9242860040d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 209465017 1250 209463767 209463797
    0x40302220e0f160e1e0621010203060906090603070b090a0e0115020d020705011d0301093203030705030c03150a060f0210111b07090609020909070c0b07 67
    0x1451039034400d08031030240d041d103659403102c003082078a100001c0c1e1401e000b019440384650b158482081701c0f8005003006001c0966070840700345009030703031009000b8000000c1d250f03e030001c5d840c09541c00d034034040941c0d00071040c003600d031805000240d480941038584244918043e03000a070340341e0091049039510b000c00600b05019842c0c91201e8809000f088581705401d580d651056190b00c07494154560060050b500040d641e148045450022108141e5910203c001003081148010281c85417055142d0350381d00d00784000410040d00c588902c10884c9804042100c42c40d40c40d402c0e80401c101c4c42106800400811030202d4000040c2c940151301d15100c5502c0b5619101540715000c2001c40c600d80c0301c07260310f01c0015000da11104195103042960b080c3d400c00c410103002502910b0048100c030b1078502043c8000b00141c00304140c410b251001040482d00219a110701c2041140c509410040c2c41640000384c14000c1e00705408915080095407038100014840307038691640c500c201504035410000b1060540c004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 209466267 1250 209465017 209465021
    0xe040b0a0f03030e031002040e040b060102031210180501120308100b070807020a050f0102060c131a0a110312010b070f1e02031b03030f1b03070f030905040204030222 73
    0x107056005200010a620ba09001e80510b0300c0848142c42131007040075140c5054110300a41d411140045181002034481d40c0e14440503e00040400f41144000d00884144000707460001d030081c9100c40000508504143c03003107068114051144400074104001041a090008070320120383d501458848200d40725010003400c00b6500b03500c0b5001580700401e585052098400040c5a002d10071580300140a030b450050142402e00344607442d015070081e03000a44c03040b0141e001006541244900624801d4580c101001c00300071038014100c50f808040340e602ea201e508860030803c8025a0401941000303065055a1100c1130140188a11514041000401c204030302104401c542c0d0f01000c071206480c807035108110880300d1401c007030380320f0f00c10706044410440c40c0043d0b560180c00e02a000c0c6250409102d041240c079407015408944080040c035440101c800e082c00648005440340e5880700032070400d030400500e0b50710706400076413140b403040000b040140e0381d03550400c2c1d080040c030340c10030340e0001e840f282040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 209467517 1250 209466267 209466269
    0x150f030601021f0609060f15030f1823030f07060b060702100c0c15020c010507020d0b010b0c010e0c100c050106170102040603050c07030c1407080307030503090d0f0e040b0a 76
    0x5400852001c0d000d8040030349800807005e5030f0100301d041100c1603458a040381c1c0058107116440040088402c401c0c0e00c18823075045101c00040040f4040790159417030380c6282407900501070a07500140024411040700ca40030b460000790001684c01141007074030011962107203201d801401072103a03130b448460f0265510380100b80c6402540052001c08102402c0002074108008030300100e6400ca104e00c4041035010182d05442d004d00001c0d402800700c80710351001501c0715840740000f603a20641a14202002410000b05140a00018080309031035441e0f24190a00b5102c0d50109104640c00c602204000c0fa251882c04440401c00317450310000866040c20801d00401c86500284640c809142a01c107a2120540080013100c2180d5400c1090740c1c0c0e814a00200c50144600045c0094580711100020403041040b500e400d04808041d61500c65448024500c0c42c0c2c000001100810804020440410820700100d08402c0310740c1041d03880550718003c0101100b070301000350ba1042d07542c0c100d00700c1c2c941c8070204168 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 209468767 1250 209467517 209467543
    0xa120c03120f1a0901140d060b06210106031404171c0c090e1009090c1e0501080105220c0c02060d06030606170a0303020a050d0c1d150f03060102 64
    0x2080454180c036240c05008140d0050320f020101e038031180482c2c02c00c3d40080c0d040385c444c8040e11a007001000c04000200b151414280c0f2400d0700c0d01c21b042210ba032031500070102115114800354000151280300724010300c0591048041c140748c10103000c00720181004a6900070f40c040d800d071001c00303040c64048c2014060184103030312445014401c02c0e40010780f9444190f07500c0480d00d448607810303079813090608590021190f10340c080380608010410359101c0e0700200d40042c4291f480d000000e848107100382007181d152013101c600300c1450741e040240b035801c403e03510b015210580f03840000740101c0210501c5584541c201c60081945c8158410031144940301041c002540241080da8421600c1d03a800084c005901041c1c1d082031420000007111111201c1c0c9800c0c008021000d094103130019113081d00250490403c46080c0802003040c0c60031070459114038081c140c515220103039400203110041c004000121101d9008640f0b646d9020b82602c0000296000501600980c6642c1c1d03864100407030502d07510442c56 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 209470017 1250 209468767 209468771
    0x40e06060a0504031b030c14130c1e05030f0105040606020a030c0c0b0c0610090902010c080a030609060902030403090602030c0c041505150318070b030f0a091e0b06030a120c0312 78
    0x202c20090b09205210704980c061605007500c2515144c400d1096a8038800c2e4035030100400003450000d002e2908411710646840c1462f210070b010390a00e2031700ea00714074214200001d40c00000c00000b0741440c40024050a8103a42c20000c990400e2800b0707640780300c070040140600154034144810080407000280c050031942c0100e940303812309494969540c0805568400800c0700391940842c000134540b1900011680582d2035500031202515441c4044d40002c0d05030f420903803a6000826428214000d400c014100386400598918081c14010100e03001a0030007800c41d00200140c0c10884000642c5c0c0c0101e0408450004140700941c5030241240610b92009030426903100010041400c00700255200752094010f124810840c80c52880e01c1e400b4a002c4c485c40b000302440407880400140580c298007505030400040c0b0520951181c1c1c500502521071070045e0303c601131401e010040300030645a00288190014800c000b607a55684801047c002c51000420038990440b60515104191881c0380680407130007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 209471267 1250 209470017 209470043
    0xc090b0f01210f0b032a0907020f01060b0a031401050108180312130215040f0306051815010807090501080303011505070c120b18150c040504060f06090803040e06060a050403 76
    0x4500e014143d000d131118441e01403d0501039035101d081d561000c164450f028000945901e1600304100d086010304210110301c15010415205417092060070050269a41c2c1662241070264000703040e40e50182c40c045451140500400c1a80d800502194010b980c8003841040c0c031844144040c0b450185138101070807040b540e0f0a02c41002d80080b0180035284c0281d500000d0501d101003140b10742d1185201c1c040c030102101a0800105a05501c2240c10001c0000300b2004000c1c1c0001517403070002c04e480c07941d100118542c0100108c0104002c480014401c0b6a0144035543c90708103a01d41f82d00051255000407100360390035107400340c4900c0c11621f080b1741c06080740c81100e80703401c0d000081207100c1c10202c441c0c82d010b002090808034180a40341c040c00400780100480c00501040740f4202c100036141003004d5a040c00301261555403401100043c0c1003507041b0003091807800c507004001c0354843d4000c2e01c80350020002030119180400d00558481c038161201ca076943c480705400c0b14a44104c6c2d0000d0030448809074 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 209472517 1250 209471267 209471291
    0x1d0306040809030c06030403080402091b0309011b02010c09050d230d0311070b0a0c052703010522030c0c030606140f0102030c1902040608060709030c090b0f0121 71
    0x8080d08803100283d00300e52601014000b480017510081d507028020a01c150002001440c00601683c0d1000c80654a40c2d1600c120074070b24541a001511410b64503512100f600c12000200702ca2264071005c40d200030300c40c03280d0404001e000c2c000b817800b483e0f0007032043c01002400c1c02980b14050342a00500321105161b2030b0140981031b1510f4007540c40d500003030b040104414604074410b040d242c0d10781c1c1002030384109071121107036032000b82440000c2c0f4091103400d01010140380340c0f0000390781e00c5050145110b80309003080c5081508588008111011040e003000c0703084451003030244800b400e55854140100d4040050400c00400c03a600e500007030400c0d0078104080380b60050340c019021001c0c01591188641c00d4124010380c0c03a4054489020116402940045001540e04c400f02450394009080040e2564442c4030107800d0203001c917040b4010a04a1408004010344001e070900107041c110010040c03400041c4c001540304041c07550a034100040221800c2904609604c54040c603d20700ba41040603041d204 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 209473767 1250 209472517 209472533
    0x605040308071a011d371e0b010e0d0f08030a09050a080408060a0b030606041a031c0206010b04030c06050d0b04050411011202040b0f03100e250f020601061d030604 72
    0x1124041176105200120305e48460110340088860305801d800c002507000c40540103841c00c804040c00e05915207a441c0301e80c961140c01700b03201c0d03840715011001c01c1150841001600030035216106500a404140405003c580c0070081459100da1001c043c0c3e94035251130180e20003410f0100070252941c01000d81311401c00c50424010f0003121805006e0712000d540d00c03020700c0203c1d40041a02a0950409000030b03181d45040d51101d00c05100881c0c1d9448412418004649010940703195240d65440d40d0303c141025a40405c240ba0041200b900e00da031815085503201d0015146500c00e01e424001c0100348100c000a840c1c102540a00d00039104120500d06800d018440c242111096808510505203a407020394141c02160207640c0d00700002d51070003800040f404c00551004052000e01048a400480c0400d40541e0890040746034801030944200d900302c0e1501c9103420b90075454103201b2001410078060390007052180c11100c41c2d041c8215000602109030285241c04241340d549802030f041000b0412130700d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 209475017 1250 209473767 209473799
    0x1e07020a0303060608090d11010f05010e061f0504060c170316030c1803020d03050c06040302030301030515010501170603010f060905150102012007020f0409030305090d08010605040308071a01 84
    0x42d603400e001e010f66944054424400c19542d41c0400d800c07070640780390018042c02e01e0b80c100780c91460002510740310341203a40c012120280c00841c0c41a58003c1840b103145482c0b000c8a0050707042e540d441700807000d4810050107501c107600c01c8805125118500e542800641007510103c0702c950041a43d81e40340400c80c65004504503104540030031318010201004134402c44049640b01008031003c0303095815074080000d08600c5041c03c404001c01040f42c200070384e0048c042e850095129400440d22035055203007003420000d400c10704140c0b2911610040140b6a84210885101c1d9500801d2182e00e4450b040840d024042c0d11880b11355050800600081e0b450455006902c11036501d0040f00005006e000124240d428a20303403c8003400d00e8801040310f1481c144010002507100504242c84806d903030010409560300184150b011035a01c104100071240d09000c0350309aa10340e45400d103215810328902520b1170060340000340000708081107060030030800d815001c1100c50701c101d44528669440000054000107 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 209476267 1250 209475017 209475023
    0xc0f0d0506040c0207180e07150903030306090b060306011b140a03110a03020d0f0302222c19020403022e05030c04030204020906070b010303030b0f1210051e07020a 72
    0x40d000c43c0c070001601c0402d0080c00c4c5c03200d0f80c0c0082050f0300010090000740030115400740c6503000e00400000c1c2103811040325800070106888081d051499800d001c0c0c101d44950340b02e0039400342460840d514a65406c41240d50000c1309081911901d01942c10203030018194910003044214042c03061201340c2d000049071640a48203944401c0d50b9112400c2444e01c0c0e0365407030350042c0540c3c8048031005090b4041c2c20301c4800352003d0f00c1c00604100c2c0c070280c00d00c0d5800c3c0034a415a6107150541c8103015403e80072620524545c11030010005044a40c1082403031041c00805504104508000800f0801c0c130a8045500440e0021701200c1c0e20000d003840a41e00c03131500c6c1903d50415100b411030300c803400c0c010b10a40b485008994072680c10540307103400b848041e40c400e160556210300200440c0001030008540e02d4040c500903503002a1140461040c49025030b64418030904c60400e0800212010500042c8400d41641c002004507407611140902c03021080030000c0c0d40034002c0710034100f0007442c0c1d0010300c16801d640 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 209477517 1250 209476267 209476271
    0x31202100614030d0527150304030f0f02030c100203070512150306060a0f0e06011e024e040e0408120f010305060f1807080318010e0d0b0c0f0d050604 66
    0x1019180c1036841d41b00d0071900410705000b400f00e048500903000c0342c0120f12107024112101002003082d8104141d0f1003160202c0106000300c0e104100560f0001520b015000c1c1c40c001541340c805400090b40c0d46d17045814211528640000001e40c01603c243c0c1680ea12b290003820151035401c00900503003440003d900414002c4c41a40d00080c0e40c0d14042c01401e0403502140c0e41c0c880c629041c60051401d140004101c5810300c000688c000500c25030382c081201c0100400c0d400360140781c1c071000202c07106840ca101187d10030011694035031101c503403502c20307820f40821803000c684907001d4074160f103281401194800d0f54048180400c01c0140180c020080c22150101c40c500780e00d41d17880d1081e50a07204e2080c00050000e81c4403400060a000483c0b0b00c3d66040000188650400c03d982040d1524010968000119540001c100030414106801c010714000307109003042c152003c040000b189441504000c0030300302505400200d809580c06104031403550b1103440306540d44000c13080c030440c0509019a4018000c1c3c1c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 209478767 1250 209477517 209477533
    0x10204140405060607062d090201020d080712090c03051f0f021608090109090c09050102011a0f01120906020706050609060a05060a03020a0e12010c090f0f03120210061403 75
    0x12030180300b16845400010b0490303003406442d8903107a0041c1810105000c4c40000d03414441c2c249804038011010101305248042407500691000905054003c04640d0a0000642c140f040158008040a00c070007078642001a84000c1c5041c202440c1105500c09000c0c0d000c3c0141d482e440384c5e070407425401c912074804002d1042da0b0035001e03420220701c6910f0804040c00c861482c0301c1c0000d00300900513304132070149490404252101340460890304840d03000d00120301048020005960280101a0a001d50740b42c151041c24520001c14411305500c49501d0410010410a101462569020a641a800c03130000c44d100c44284c54000010001a9480d9108485580028003540b5216050704140d40010b08014107100000105038040e40104402d0000d02540001200250300e490141d6000d25009000218154001d500040c10105440c0c0020020800b03401c001c1c880c40c60b40401540803240d000850300c18006c03500200700d04007002c080d90b50314000e00b401c5e8005400019100c00442070001101503481c0c41d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 209480017 1250 209478767 209478769
    0x6030607050c070e04110406090501080d0804260f0c03030a0b040e0a020f060c1207110306011a18040c0207140f0a031101030603170315060c0604060b12070801020414 73
    0x6026411601c01c10f58000301d0103010012002e019150041d01c65005581725580030000541074034410f40002e2203043c0d980e8010410400c4c20880c0600818503420a1031060403e6220919909108101c030380703a11082c034102210b00c0301c2010131900341c81442503080751111003000c9040e403079a20a40d4040300e418140351b440300b91072600344544a4856a1000100418140c41d424004c502091082c1340e9444502884400724030502070000016400d45040042d640b84030340d01d072404100b814603030511300a50040006001c800c01d0086c0d941e0080ca40848202c0d201c204480c2040c0758003104c1e440c43d43d0030034200924020b04540000e180c005860202d030140e52201828020311042e0000109207540c0504441010004180340d0f903002d0354182070600d000303c2d04607100c0c2c0702c079010080b00740040350054400004002c1400c0040b00e02541e480b004460700c03481c1440647d171075075503424003504c050601540c0707452000c40e550300d201e88815030046070401d8903a141d40c1d0f03484541c002d4000d44220710450141c0c509184417 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 209481267 1250 209480017 209480027
    0x70e06040806090607050a050a0311041d010314070302100806060d14060a060f0909021c0204261b0118081212180706120f0603081c0c09060c1704030b06030607 70
    0x4401c0140c2d1b0b640b81080c2e9a82000c902400034bd2100c0f82021100f0000030031305007084030381041c0c0d180414400c04420351561500d015a2821404903504a410040b02480140d407005000701040e080d80c078010cc400d4581500162442c07265824103000e1300c0ca400001900f00c030062400a2003103000305c80c49414166540340c183e440780f00190196000405d49101800940d0312a8060003150042c0b1a0700704d24050308250031070480e8090b402902e1005019002020000d10303500c40328200d42d03c01c0303002d05122140d941099690074481c2c0800780c1401509807030460403072100e40d100c0f0300602241080f9000c8140607018818181d0001e40d0074041c2f03807401c80004030b11340c030341c844499401d60602c0c008000c01c40c41c1807400c0301d4842c072103d04403440c7d0340c440c650203020a03e40c1c00b0b0301001e0b60103152070303950310701c00d41c0e1242850200104c0b55600c0350342000f02e20040160056500d6080724800e00381403d540c89589080b00032035480220075007000b80041400f00038017011100070751064005804842c1030781c80311141690b1b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 209482517 1250 209481267 209481277
    0x2091005090705130305010203070504030507090e061302040b030a0b07030c110c04020f0c010f0204050406120201230405030f0a1a010e01030303020d020c030705010e0105060f0a030605070e0604080609060705 91
    0x5003001d079070030101d10300314402d00040a62614601e52401201d80301d0b42c0e89402da0303105440318800204041400d10510405006450040c22003900c10080e6201a81250b52208e10080a4451002d4540901001c1d9110380c2c0110541c140002d052f10040342c01480c004150a40c240c4005002900d000f00c0c04440ca80981c2c0c900c908511010001c182c40301d0740008104c00303540308030041c0c04010000d02040c40300300c1c8240120030204219610141c5c4480c10030040c0f0080701c1039035200e001110b408003d20b2001d03034bc1105801504502681040c3c0400309050341055040c03003640d0010f42c162103040b000140d50200411043c800a100d440d0900a070310500c0c00e24442d0400a001e074010300d018503001000007030b0007540107081e0f181d4100009401c05020034480341c01d540000c0d00584580c0d444106140d488442842507640c815401c0312041032044010021840c1542107000c02881550340300085001c02e4015120f40360881400ac101950701e03a1540582d98495030280c40d12a0703a4407545021403030309409101510 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 209483767 1250 209482517 209482519
    0x29010503040803070201150303080601140a1b11060a0509030c010c080f0d11030412020d020102030c0f071a01030507090b09060d021c08040801151d0f04030905100c02091005 76
    0x40c15a111511090016030000e410342003550750b1820041030202205401100850180d160480c1b145000300024166032110400081c18010810030540c1082e00040e500807202095445660b1404452600b080416030100e8003941c021400b0400803905548003004001c1c42c00294299070485d81480300540d1402d4030300307070000c1280406100c003d00300141c120242c00b10b403070581000709520a01c0c6100c2d003116401034400303450345d00d036040d01070080074ac04008007002340744648001c5165282c5504540300c1400349049000300d4880024000040c4202d00e030900d07200302e01c814015a001c0d41c0d28904075603a1480c520071183c15905000302c0384010f240c40030040e40b0496020380301400300b0f880b07642001818141c0610510304009416812000310b010000608086c125076400000c0c542c0c030302d00149040c02003c0d882000904601c0240700450404550707501d4116094201c0c14003251101d14003a240c0c0c2180b504041d400c520340300340c0e516000d6800219016000e00945040126446d5114140d900291602486e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 209485017 1250 209483767 209483777
    0x614090106122c0606010801031509030905030625020303040213050402060d1a0312041d0c0f0c2a0d02010f021504060b090c070c1404060314012901 65
    0x1040400d00841d1044901411001c00085283c030020b0b0a1a9505000a9104010421a801c83d03a0340c0e1040040303542058003424285015803543d1744402905c1c1d00515603135940d80d01ca00301c1004141c003403c5048054100142916403c0c82c1030348603c0110030b000480242c1c445185036010031440e00100840b8044c68000c0c10008108006c087e031030000d41000b800898103c0c070f04101d0b110b103000c02c030320400801341010001c10100189030002c141c60418081644000c10000304020000c900e10711100c90400418035444610540e0f40b01c500b000e143c003560800c17804050001400c1d070344080010840c40342c9041e001d16084507001626110b0042c511044482540181c10621050301641c0195002c581045141c0b04540706900c2001003142d0f030f29020707141210140e4070f03951801c549140024031a540701100241050038001c507a141da01001c02c0700d218404910818820b44101c44e180c1d0340100c000303160132404404d40d00c0c0a96060740d00800b2070b0040108800d90428203440001030140c228055590305940d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 209486267 1250 209485017 209485019
    0xc08010f120f060c0e030f07050306060904050f0a0309032d030e0a1716151e1701060e01020106060f0f03051e04050a0b0c090a0e0712020301080304050406140901 71
    0xc000c51800420070342d00c44071070355441400034050340910b00410010703559410f20048503005061402c0d551601903031140d0032109082c006600d00149456206804691a141588a40c00c056040081c181d00690650003181d5030a024150000e1100f000c4a22039101000d07001a6005048900d080d400280c1310203000051496012910038150000381460080c03003084140c2c1d0700d0399052034a44803840c074503221fa0001d60480740708111803100280240100c1408081107001c0702c034010042c039001492120a00740d01d80c41112454482c0860600c1400941c003048825615040054040c031200d00b8024010740c01c001000c1402c600c11190b0400c040c1d49519402401079500c1010740180c00020a00d01425400001555032a08040c1459001d540039001030301c2e031460303e800e100700000c0000f40035105485040204c4030b400d4880f00c481711b003101e10110310f0003415102e410088070440b00702041c14000c80d00210002c140101c020006104543d000c032002c21900383d40d0782c40841105407541000b9804003030440 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 209487517 1250 209486267 209486279
    0x60b0a18050406090608010509010902060f030a0e0105070c0203010c09061e0c060c270510050705010207020306010f05270c0703140705030403111806040209030106081e010c08010f 79
    0x540304002224440c5100380068a95002c40d0440301c403030b8013002000740c846008010084003031186580007001e82c002409100050780108000c0c0c41252403c0003541c07c00030018008955640c4810f14080d5098002e000d03030709000b90004c00354030300c0c605c05910951805510303035001401084040100d400c0c503100c07600f00f1404800070341e10340301d400c05e640030502008018040c0001d106204031014100300d929541e0900310f00440e4280d1402003c1e050282d26400350304144450303602c4642e006014549403620740d589441600d40079002e4012200c1c001e406100d44400440d05802e80340c1e903281601c41c2500d4185c2003032680c107151400a450440b5050380308511a006c1002a80c509000341400d9002e81485144056810602801944401400d440c40d0b000458280108401200d0308030001808450504642c2e50000d603905000001500f114450740d40044e030b0306140c1d10207400c190024010b0300b00ba512426050411109a1101c5032540ba400e9480c020340d0801d024010406241a1140c8000c182c0750281090 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 209488767 1250 209487517 209487527
    0x1407080c030a180b010e090304032d0f0c030501050705070b010e090a140102090108060d03050a12060f0303020102030f0601020114150301060f1401090504060b070609020a0b03131203060b0a 83
    0x2034a06a44283c44040c0c000b02c01e4509001050311a03c0740408110399890484e441165800147c4450303440d400030001000400c0102400c60510b003d04502646400a1200c101c41600c610740e03401000074420051074420300130040c0c1c107103080702d00a400922442e0345002e021501071003902002000c049007480184070340f4626071003081e813140410703089800480b4141c03108140d40200400c121501e80d000540c016040d41d0080165400a0086d16207011100c101d5034090900e002d5604007000b0001c01c803c1c1502404d0894100b1801040e000c43c072101000d03281e0900a010354000c8404440d140c02580c08580ca5500c140305071500c840300300c811412580c40e41c3c210000d007121050001680f40d92905c002084c031881c1c01c40c6810080c04541460f59042004034009044405142d020b18801e61a0001c10400840c04c007085940540c5d225a000800540b20700c0055440700d0280c01440741c0765000300c200301e02181e81e981110403444c0102142c0c0224950751000b10103480c0a070103809840070007406111521400380c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 209490017 1250 209488767 209488771
    0x60c1509020301140403020c011817071a0406081e07051b01020d061401233f15011b030e03011a0114040803180303041a09041407080c03 60
    0x690020032001a5500020709403414542240042001d00090104250301005280218242802c2c8000703069004c220801601440c0d00c2a04c10380e0f21400c0104560060074454013000d010494070050b400004007182511941041c00f591012640120100b00450410b0030a19170004c24142c14000d81d50340e502d4203c8081d001401c0120310b05144140e5110752580c203002824a19141d1000000c407607181400e4408159136510249041c4440306040881c40c1d1084000305002501c00d071143d654030642558051620b0440450b41e1000fa035000c071400480a038440790080b000880d40b20301e000d1945400c0c2802c0359040d98a4101808210040c0c0003108030400003002494450207402c0103c040300b070501c0481e00f501c000c0402d04800c3c008461b5200c1480da0082d528400c1080016034142c141410a6105a80e1f4403840b22a003a0219146c2030402e0141c0c0c0030001c603006405071445416941445001c4508990000e0140c00d200381c0c1000120f6202109003a00349110b200c80c6d03650005140c83d944002c09141e0301c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 209491267 1250 209490017 209490053
    0x406020322080f221211061603030c0504030b0a0501090516210905030d0e0d02010204230a08100501080d050a051209070f06120501050904021305070e130f0501080106060c 75
    0xb010111500d01141d0320f0364000170000c1d6101011407100c180f6080e803046000c941d0680c82040d0a0200071000c2d01c0010000680503418140002c0f50b01c83c45c8020b90340c0303010307552008094100c00010400744030040d4016a04980c55140148007645912a4200d00c2000260061001402c6048c0210011745000040d01d24060400c000040c10300b0203403107540c00c5d1740c40f0309800c8010035101c0ca80c01c501860708000c0c006010400b1b00c000c504081c1000a5840c0c0c065030480c80d0304c1c0030580c18040644a6a94030303e03240042114501315225000d002143c040500000d2003001c3c0036000e240c0c5503030b5020380140d0446480b440c1aa854625103469503c04105454010304920f000d0b200d10f00e400300b01c0150301c2d021000944500e4a804000d501d01103004410307210143c201a001d82d0071242070000584981c0145000d900e03a0301c1021500303503500341040f00c4c1004034000c1550f100301607100107828101c00d9400210911424070b000d102c585c1e00c6120b03646c00d030340703403442004002190101c3c2c1c2804201e55440c10b0041c011 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 209492517 1250 209491267 209491297
    0x307031805060c0318190909050f0a03020a0309051905090a1506030906050a110306060a05070c180e0606010806010e03010f0c050405030d09080a02090a140406020322080f 75
    0x40c6075004180140c010141520b0f195100058607030503200c0321098800011011030300e1210650880999401a0740381c0d00c242c1c000c85850b130341c00740b042001c2440700d00e2680c400c000c210fa0700328156090081d03403018400700c00d401050704818082194100403000c00320492080d841c8110042ca008207005041100070403034200c0503510500303070010b00c1031040c90b08010b042e203076004a90780c00c150a008e021564045c09803c034491a081e4110111a0040705407517101408884041c0c481c484803505a0791440384140c001d1209400900c04a100d4010b490000d4112110403810400c2941e40c50b0840d40e076000030380340b00d40464180e00000703450358812001c51145e03048c06400810500c10940c0403800703035441a45c2d10f00200ea400710b01417005003400c00c400c584800701868050300c114904454907441c0d4030b10b210064000c0c141400012844682500000318a0b07003107004081e8249802d0034400000d42095520801c4100d4604014088002d040003420f00203821140840c07804c40451b4a0707800c00d5004083c1005900 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 209493767 1250 209492517 209492519
    0x8070203010e0102180a030f081e04060804060f020a170606120a02091212030103020103050402061b0d0801090b06160c0503071410030c0507111f17010b0301060203070318 75
    0x40c5080c040d050202c40703400c0000d81c58031a40902401c1c00300e05400524011000342208101055680001e05201a00301d81c1980c3d50b001010301c0c20380380740c030241914030840d840000c000541940c000c800354862405500c040001c001029038a0f401d070b119020400c00041c00c01d020b03520003298000e44554008000802a81c5095101c11002000e04800ca0308044103a50110741007090b405d2170889043c40c80e500328094424009002c560101071301040c04064101030b07640c0b00003800c54540e40c081382d100d45020700840c2c405905001e0229030321b220003042240091849000010710181602444881c0c14009101a0414000e0b101036104840c0302e000070b0303031400ba10500000c2d00f5142441920007030300c1c495544244900c0700e43c007800340740b4050000c51000c03d842d2040c41040b05030311034162004954018000340c0c0c04450400011041c0395686461030601203c159204040b58000d03245000c0030104001e0b503a03090780da43d4208440c6020074480c3e000942c1082040b400081d1142000300c81a40d00508072103000c23 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 209495017 1250 209493767 209493769
    0x60b04020d140f0609041703040303060518041709030a110d0b070503071806050405010c051002030c1b0d0c0f0c08070608010617010612020a0c0f0f031e0c0f080702 72
    0x9103880c1c0075607209444030b24007030004201d4500e90b400d500200583d41c81c4c8840c1850b41d0f98084c3c220346812184040c2501001040400d4404d80010b402844001c2ca1103002a0051803001c140760f0040e80d04950421171a21182c03a00b1170110203132212440000d001d001c034441c55485011110540c2e01040790b00c2002000c0c3c1c0000140100f62850007840746554581d141e261003040980000d9180b0709010240300031060400c8a40d41c00403c440584100703103480c01d1203165070f18001c1e240c044024602c440380b030300200030884003005920181c4414109101c62014840030504c2640e01c07160140402c000041d1504200c0001c039408100c22101148508401e6240d60303a9059070700d04115039504400c0000302d00b200100803007a4402070702c2039800d41c2560303021115494194080c0040320740d094507420043e008038200400d50302400c0d040090a421280346240d040c2d062400c03550303107400313003408a000c10101148466140d100e80905400b09145813681c1d0a5003899803140d1200e40f840c19011a0141c2041140d8001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 209496267 1250 209495017 209495021
    0xc080418020c010f2003010510110f070b030907060e090a0e1501060201020306012a020909030d02160209010b040f1406070f030806041a03120f1306020706030522060b04020d 76
    0x4c50614103000151109a0483c2070054145014219424030001c0c00188000d0f41c2d030140c800340e00079150601088098840205506003100141030300a41e0090b00000100c4007484c4004501c0740101005540c1029110002078550034103103240c0d5170b0015001c03400549080e900790b000c0034800d4040c0e411100c840c008000750b5100140240c12000041c0d4000c4148019035070072100500034603841111004881c10100e1f110384058098107030191280c6541008150030b404144201d44a1000c1010250340d6980c12080418682d0007440b8200e0144280c0c10000031042030340002c0e98152640c3d0401c940502d4078140c240050224901000c9503c03010810070320b40069803208016151610079240c400c16482c042c41000f04940d044447c07803440075040001c040c0b6960300442d40d03000c103190002020f500e600f001601c004050003151106540b41c0740502010885540006084040301c105640520981d40c455444c03820503548030800713202d174600c0051402c00040f070507000001d03070f80c2d03003d000142046117100358001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 209497517 1250 209496267 209496281
    0x1509190f0b0a0e0f030307060f0b0a0311121203041217010e1009020913050901060510081501021f050403020a080d0b03100b010f14092205070c080418020c01 69
    0xc00070200180c03000300250402c031203442002086a00e035105480c20300100c0d8030380c443d80b1801450751b0b90745c10041d40070003040c0d4802c0080c0c900203407007050113507141c1c0341800e03520003000d82591140d80500c02c0300c0605c11340090014090314501c0e21103400d50320b807503440c00703100981e4034140424810729000302880c04461842c000c3c02080c03811704004850a1414440500f807055420581055004000d40390b0303140c035030001800c6007440c020800920390303032030300440c9006050541055034010b121301000f0703601d83e501803a424001d003484141031a00d031240b480107981d150790709080130055440c0784050403a8020903520082e401402401680d0350315007640d460700714552002c85200001c1d07540385c410440f681400c00c056500303d0103d080802ca00e605c1d000c0080c000c034014255a904212440c0411001019520140c580394900038108099030300345841100c02d040405500740c9042494400058030151043c2c1986035040d07003128031240380c6410411100c0c2064400944015590b40811030010300003000d1050074 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 209498767 1250 209497517 209497529
    0x13180516030c0501112404030e010e0307140a0306021b070609030c12031209140c06070f06020307051b01020912150f060a0807140a170316021c0c0501020c1509190f 72
    0x1003031b0351800e841c000e8030058007580c0c2d6034104040300303c0030501030718005841c60030748801e030340640482034070700300080c101d412250001408070b400452068001030196401040e207015940a4442c1c254440d0703412100c5100c2c9210140c51000074100c10402c2c1c1030250040b8017800c1c040e252099507243c80301a01c00645080140485c1c6000a00081006426043c00f015544800894005240090710b8842020210b22940041c05850303001021640c0e07907005004a5803444502d4180520001105e98001d00135041101d4542c09400441140c41e1201004900c04000b014400c1e1020140c0d1908020584c80641c010042500186c00007008074069808000380c0004060020002460800c0e034018400301c100f86620000f88c210202d4204100c4003c00f0060702c452000030600c1c20005000c90000035103c2510741780c00d030b1252015032100303014044214005001c0d5042030f021120301c05d81910911040b28545809980c0b040014040249146803900200d081c90360800010744003652104402500c0c010198008 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 209500017 1250 209498767 209498833
    0xa0303020f281d03070515040e0c0c0610031a070201060b0d050103210f0f0c06020c0606091501050901031d161502070303050f0913180516030c050111 66
    0x1a000642e80880380d0f060348411150541d00004000022954a03c110f014151288140c0c5401010b6030007404246ea00916068a1011250030420116851b50b40441e10100481c09407070700280d10822091000000c90340d01814107000f034100c10201c01c0203403030068222405c5549581000424102c0c40004e003004045445001509526524000404108500583c65503c3c0100080d02120760801d107180302030369031804d20340041c00c4030607000c450105000300c0c0104094408520211840800605184506070603212925581c85109036048088070b01051540052010080130545501c0307500200d00c540000720b00088685c22540d41030741001c80c062602e00e0781c42200042004000050741c0ca40c02c400d0064005030641c2c038107503100281984110500e040c1524400107480c0d4060b1100c040328216a460302d401007000042002c5190b40702a101c2030141e8461142c00c200d1074403039003000624005c495000b0340f61765902c1d00c2d000041d52410b0540074101d2080c0180d100b458501c2015082c4010445590070349 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 209501267 1250 209500017 209500087
    0x1060e03010e073b160320030a0c030902130903080112080403080c0a14160e01050901260a030c030f080f0117030912031315020a0303020f 61
    0x1414212140c2e0819108194042c44040040d60100480c012440d80354503202041c200031400306403100300340003424003050b07280c4100300810254140107040041403555130038403403000308000b14660001500d040300400c0e441000410300688a95000800a0750b060402040c8003029800040750808102c0314040c84585400d415400c00d948161618050260544c405a040d41c95494600e200d0281d400000d00700c0c4000102c108900034100448100701750720918108141c0e4040d24080d403078088824400d405401d010002155428107400018180d0700b001e49158800d80ca0a0b6505100d80c2681c0350b00440080324001c1c01440c400e040c410b4081086c080e440c2d4182640092400034000d601010a1030100201c0c00305001c4080d400e0710140c0e0440f142801e120b4001070251482d2800d505c02c1203241c5074010b150384440300d412200840500380a00c8085090b288940da9400841144c1c25030713140ba1001038000c01c0081000a002e58013400440c00302040392402c0c40c102c03000a1000720300c14407409004243d03000c5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 209502517 1250 209501267 209501269
    0xd1b02041d060612030a030921020f0c030109020f0f01031d01021201091b0c141e1e070b0703050702060304080c010e010b0d2301050c031614030a0f0608010501060e 72
    0x10b03240c1080058800d41c00c13032500b600c403260710717405030000d0300c42015221420401445a018400c201d1304241982100c4912070b10302019586a450380a14950350040e1030a002c9180f030180302d608440c070340240003001c415050004120a400b1200c680b241030580d6004018174944040075840004417082c000160b44000c2840c05403200303c1d059101400050504408800c00d80e041d4aa00403084581c0c1455080340c2000c0c0307480040c130315031101c0b212880d2040002c040a82d83c0030402c03054444c401c0000381c80c03241d0b84880e13402d2240f37800780040c4680d40d40200c0081040103a114001c00d0300c40d0003071903c20b0414960394009200303a0700540d420794000202258141e15010300380302c0c480705a682c41c4000c001107110103001c55807291b107100d806004010b6404114462072070581c106100c8102d09c134000c001300d00d4001d080c100760380c10607500b0800004a84c1d000100340e900a102018010000207091815035845080840140004580d09155581c40c0c010000e140c0500340102e0380600140d480700010700032503070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 209503767 1250 209502517 209502523
    0x14030313060b0a0b18010215100509090d08010b0f0903070e010e0a0902031b1503160810030c05040905010207060f0f1a090106110a050d021f020307020d1b02041d 71
    0x40302c0c1c5224200d602c104000d410202c50884240c42d950461600c070300500d440c0140e051407079030a10340151103461020000b5403480034002c801980c0003110328003100d4645c0f400240c0d0b0703405a014884041603068006000f440c41d04e00141c072050401c03000051801c51104041303800d20200c0c2c0d0014034440c070740ca0014400d41c0346c09500290b0280706d0384820040204c003500069035840c0680134401340b00c0801e409402c1c0c6911782e005001100180c0b080b40391380c0c03400c200a58040e000d50f183c030300c880050311003c00705049588040c0074900f1241c0041c0d050b141a400c0104200040c56031810440d0136660800082c40002e0780b03406590825501c1c01c0e00000c00500d0514040e050707a0701d1901c8079569117800a21f941503a510b65107a42d054544601c0c080c0b0810800802451130012400c5010344203108065650602036800501d0030780c80011480407034480c3c0703160030300d0703000b68007043d0760450250b00140e8010f04140c1c4035280e50a8070b840e0416040904102d103030042012617152222050ba05114401e1200c2850010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 209505017 1250 209503767 209503781
    0x50a061b020a110603190608030a020c0105130509070e041407020f03070b0c090a0305030f091807020c131127090115030f0204051503090709150603091403031306 71
    0x680041d0000b05541d07036480201820300100540700e02e601002044100000da01e01510903400c0440800045d500e9440c41c0e0b907079801908500e001885402c0850049520400030303250700704034a00c9410b40140c1000d04100d5002001003c65081141440b2044502e541ea8021105418142c400b003252600b0171140017030401141101e14541d0754000c00c00c0d0760004806903c80c0c0d900040540c9090386a08121000031002d96203680301409501c00454072401e002210401007440460032103c8a211a0007011500c0350f50908030745030805078101c0c015001c40d500301520500d0001c0086d04000511201d40d481174100b82e0400020040162422003401760166031a00481040c82c404071010109585003102607603c12281c0141c51081644480248126660707030b4043c1d0340030b0700c001009409034803540010310318240c10460b00f040341403141050008100c10103205540110190034200107660341080b02c140d01074030903001c003141c580000c000800d12a040601c0690f0141943d611003d194048500309042601c000d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 209506267 1250 209505017 209505071
    0xa050d0b090108070b030606091002030a120519020c01150f0602071e0b0c100906022116050702011106180d0302030f0604180204060e101a07080c0a050a06 68
    0x80758014081e0002c0081c580040f00c00c000c1d69203660360345850100c1e8050040c3c450039600308040381100306c85150080090036a0801d01d0b0303522042101503201600a48205450b51b0800304105007210700440402c0e002080f41814840000c1407003549034144800c048083c1d0700400060003001d0090040c5503041c0140b00040c10313061102003040034416000c141221980c0b081c9034100302c00048426948105004100c280728400000304000c12542c1010780181d8172502d000702110684c003107a24012100c3e024002c0c000c00ea6001030001c50407200b542030b50103601801042e418041c216000b1240c500c1c1c10440d0520525604009140802c2c5c07e1070302c54507283c000203902c0185801441003240d4801c0d81800c00380d000a04440115003412001121255240303000e03000f0390400d05020001c218811400b01283c000c24070440c1c0350012603940c40801c070407107400c00c01d03a20303018804100340c00119042030050600025060300341c91400e440c40c0e94880c640010b60000322903183c3ca5858001103150152040100455 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 209507517 1250 209506267 209506279
    0x608030f090108040212010f020409111303080f0403050a120f0f080f060a03050607030603030f090303020a08090303040806040609030207170c040f0b030a0303020904050a020906180d080a050d0b 85
    0x540d00c01545454010300c10381c0d904000303418001505550b07410b900100b442c1ca90f074000b04502803c104800000c0e600601821a40608002140d20f11003001c40c102c424401c0104c2c2c404001c0c17411640c4040040e8010484108140810b000c0800451f1042c0480c88002d4070500c5a031000c00002c03400a481c03074170409104418000001186150f03140c00500c407ea101072400103180143d6681d10004100a2050b00041c00c00e100d60b03400c120400d605640b014090768000d44078195055816882146c110700c4500004005030040d845101c00035107140d019008500c0014103490905459245581c035000c1c0071601501c0040e115201282495010721204015240314102d6003d0f10035078a41e10307a9100240c000c05801140c0d59400784240f42e04a40c020300104d03000030140c82c010349250034024061b4000780c45030307803180b880c20000c55403c0200f4800c446070044094041402c02c20062242903442e0701e48071485412054150f58480000c04000c010b1904000e152240303510364404170708a20031503150504040c003c00c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 209508767 1250 209507517 209507527
    0xc0f101401050d080c0114010e04020130050a020c0a0c060905090c03011511011b0311090d02011b02090a0f0b030601030203031b0f06160f020106050d020f0130060803 73
    0x3032a164242c0c4150340c0c00c0074504e650355004020950040c80e040e0100600c0c0702400001203034030042c0c200c03100e001d103000760380d8022100d05c40d070381554841428403903070b046140e40070b03101c0c5281504503081740e9444114071500605010307400f1019400d154000c0011220007464040c02d001d01600306003c800600000d55003540e152500514000030741c031045c010441c21100b6180c001c1c0d4550321072114040d5001d4000d00074003c0841d548014150407413403e100401007402c2c5404102c0d10840c0b007042d2882008000c102c103100c1078594006640d60780c441071301e164611120200850158450300c005900601588800041d0461000310742000c0340d0040072458841d800050040016035400001d03200c44940d031b0b9004c00c5403495940540c0749481401c2802247c05d004080800038108030320941c103400c0c810191501e01d01d404041408900b00e07035040c011968444020710244016080550030343d41c5503e810305090b224004441500c44540c540902244a04485548010031003c602c2c0103000013810401d0045041c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 209510017 1250 209508767 209508769
    0x30f090307031202030619030818120604080304020d1a06040e0331090f2703020601090507051209010c1d010c0818060c1606050403030206150102030c0f10140105 71
    0x6100c00d403c0d58000d43d0300440801c030107030f8542d0b04030216070840f01488180143d9901d400c0c0d02030741201c4503501160a001194055a0030411084200904c03c3d070082c00040d0380c0da654484482d0005041641c00c108564a500002040b01a00d0900c10602c404042450714000c0108015151440e1500341e03641c2051040004028444040a5450010020100d407424050308420f10780125a03008900b400e00741301d400c2000b44040c1d4005e900d00482d1202e440ca0408500040d14102c06803268010010383c0813100420204001e075000c0783d040380d694a009882c08031085a090300740720054598074407503591008a004400c0d0081e50b0045460050024503100000d9000081d0008500c41009442e101e0002504100b40c014540718407a580b43c0103084c681c80300c804003c920390f0303000040480290408021800b1845c640140140e030102c0e030f8180c1c000d1020382d1b50140e81b00c02030315001d40402d044d40300500c002c10000740144450090004001c00401269000d08050000c3d41c9038580c0c580c4914289000611136 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 209511267 1250 209510017 209510027
    0x60f0911091021050619030b0406050405070f031a0f1909060e070e1e0c030703090201141c1104060c0228030f0b0601020d2a1502030f09030703 63
    0x42001115000d08101078030400307550001c66948a812003024070f040104450085074015030140409984c0048a0703501000c0d028400760190101030160b1800500080001e080c035000503502500c0342017603400d01355490619101000098100b100c035401c00049201045614505241d03004054001000550400340350b444c00c2408034111009201d80c4840c605410720006410080c01c0045c00700495440079501c018048119500b0342e0b4040132507601e0745c4402c00d180da01003911801340c02c15168051941e20f8005040c0e00070103203801d00324180a40b03940148406400c4002410b12005d8000110644000c420000c408503040c4c1f02d40e0320744580087c07000740304969010110131119941a14130501300d550350034060341d205407074a0300740c2d6100e00b2401001c0100b2425040d4071800501c81ca00409064803102d00690300c880700b501c015000100b0104810406905071240e01d42400500035000ca039000d1a900c502c0259005121600c1020b0740010500032420316444038903500c061141c001d181850150707540103103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 209512517 1250 209511267 209511277
    0x30515090402012f030301080c0a0b031512010902030a0308061009030506040803040309181d0307170d0207061a01080106090605030f10051309060f06080a2306010603060f0911 77
    0x580d0190046070b5100da5044c0320358040e0010703800080326200d6a540c1501f5642c1c0403900d000720b0003610040d01c001240302003001070340d005100e010701c0324a40d414141e0602801c2c141c83c0704a1060356481d5028071025072000d100e1442041e000b56207445451030b001c4140303c921900f0408100c20082e1041042001c02c00109101d07401c2a070014a29a40e40c0b96400c0454182c1c003650407250081d40c14458803268244681c0c81034001800101c0b41c0381c0e000002581d0151280203815024182141c80c8644180c1e55852400400386910040720040c28011503840d1601210381c040782e54400e5909451540b9110b6030842082070051189281c10743e01a8185031001745513000140100000d103c810010070500c0810461800c00707842c0242130000e0107203035050800d01600c50880d042d00c1f10740c40d0070710404003600c03140aa41c09880c0b1200c0241880e00c0180d4821100300b07085a03034411000e40907241703981c1500701441003500034000e0b581c011450f9400e0100c044001800381e40f20610103884d12070000d0301550410240e030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 209513767 1250 209512517 209512547
    0xf060903060504080c07080d031a0f0f01110a150b04090f0803130210080a1a030a02280308030f0106030c0806010305090a060608030a080109061d040f0f0303051509040201 75
    0x8500b40d1501c0ca002402c900440c0300c0031940f030080000c0440c3c45c44002a49008480041e41c0901a00d40b2010740045542404a80a0b402c001c04450f003407a1420001e000503041d48062500140728118011010b044c144410000c4880342c1c86c00d0b1205000182d540203001003180220b8040098054a5a981d0080003c9070002000c0b58070200001c0d0f04150400004500f058001d00f00b0315180e45030303074002081c82c41c045555113500b41c9011860010791201018225802c1c0002d002052a1003040d02046900710021403500c510220400b80f03005901100c00038a0029440780401a031641403540c1d207030044040582020b410035103800562000f0350703071200b05103403c54420b00700062543c440c0c58400c0c0c140061008050210742c100303072000600400000052401d101150380f01d034910f0340c0394107015050300c40d00d10030306070701543c43e500324441e082210b0f0580f07800c140300b508050070b503001559a03c4250b404152003600401d9944c01001040002c1c480c000e140d0b144111881c0300149029030005e444c0b141041c1c521 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 209515017 1250 209513767 209513771
    0x40f0e0303060d050f0d0c03030c0903080a11071203020313140d080304140d050405010314010806070f2606010305060f09010b0a020309040f1a030304080c0103152408010f06090306 79
    0x1e00f0512074280302c10040c4003001403da07a00d040182c0005800c45001d000101c1c0061700d050710103006688524002c80580f58420b210303a14090310700324203d55440401d071201c07107240110b42c0001000040d50b0812034500384641c0285072140c00750403c11030300c4940d035400680004e8148401c003005aa0725000b858a00364405607060302ca40b25800c010100311b00310300f803070310b41485010010300d012608000500121002641c0500445894030035000000c3d00030f105e62001c90b484130003c81d5400780101c000300c0084100c5d01e002125121580c404185028580341c2c45c0746090141000e22000d0b507814000c1503800350b42525000c4031800c00750301060840c0c105206120302081c0204480308014030074000c481102c140200701b48410b52001101e08000d009542403120140c1c0c20084140081c02e001c02690120b5580001402d80d4004007401503001e03000064204501100900f0003191144c0c0e644922551402144007034000e4607101103014200f044180c200420080700b0b050108411a84a8903407401e9175446100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 209516267 1250 209515017 209515039
    0x40212132a2705070905090726040516060f03140c0a080601120e06090705010212160c09020c06090f030c0706120b0d03020303190506280b0c01060302040f0e030306 72
    0x10300081000810340b4080c40c608120601010302e610120034001c1d10001c4841e41d610361034604051310100305014aa030002d001c140b00e01c40d0080103024050394030601039001d50304420b04036164510030244941110010604080008a00300e50500c82c080303504440d0008640c1c0c0d41071800c0560541e000f50303403103c400c2007120000140c059102e0800b10411001c0e8040600c000c03010002440c0e1240b00849440c0c001c0d21880100044c0b540c030003d0003106a100090308107240c80340f101c030321880310107444006a4000500c0c800004060312188004c000c1d406001c0302401070782c1062a885401c200452142d1180e680c024014040550408039092003110218100000002e80101d02e040150030355026090f844280c0701815400c2c10b40100086104010014000b0340300c0306d40c0140c000c2101c2040c0e518070340042d24040c403900c80c01b400150031100d00c0c1003003003004041e50740c86a071610103900020341c0c4030f0303c2d9449440800840c01d02d40602007400c00000c80a0150075010303114150359008c02400030b4070170b141c0c81d81c0d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 209517517 1250 209516267 209516309
    0x90f060c0210061202150a140307050f0310051f05030712060503010905010c08010f0f09050606070204060305010b0f06041401050918040503071403070f060b040212132a 74
    0x104000b042c0440414401c07a6611014101118007485040c2c0c010130000c40d1001007101c0c1081204c0000b101b43e2220000031070200c0e1030b0001c64000422b8101842000c0100035404541c11000e507206d06245503050317070b050381480c09004800501e01d000c1140d03811311001d0726000a8200050341d40c81031251078206000030380309041d0b50242c925588819055440c1c080254280070b019088035040c600360b0380750b080c01c4d42d80c1c0c0d4000d1078a000030b48c42001c10b50031f042c503818001007806070412a009080180304c10308203020750b0002400c540c000c1e4800c0b6002e80d0340d44a55059400d102c0940d80079410700300d0301d0130705152501060328110301c403001c692410013100142c010004e684121009400d01041d01c6008194034003450300d00c0d17032075221800c04d551202100045cad2070030745000001c8074046a403020641c00002038540d601c201510705440f285912503020f1003800340c0c81c94401c000d10f00c6241d040e50801f1481c20340f0304142005200b20166412440030b8128003c0c11111040380201c1242d6500c0e83c00608045081 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 209518767 1250 209517517 209517523
    0x2030a0210020c0a151d19030e0406180e0105180709112704060b07050309220c09090b010306060f080606070c170c03011b0302090604050303120415090f060c02 70
    0x10000c0c002800e05d040404203003c03d43c080c003041010741c1c40d15207007180064096503030b842c8202d9016003140d410501c0c1d400080e10a0181d00818400504007165260704c07184085211600084040c020350b0340c41d03510245c1c20509000e00d82c1c0255624228900e402c2450f00da1580319003090041701c454980b5248240c0340803415200300d580b080200150004104490ec6002e0004403907000350030303c00d03810b1950100d45c40305c000d421600c90a500c58011460b0400340014858000343d40392800007865103240d151840b030b1000f4003a10003c200c50f9902c15842c1428507500b042114140b1800354105840c0c018180142c0d60007100c80c00c41040713142400e1101ea56400000307410703407081c1140140030108010000442c50442010082c2c0f03040804160342100200906040c201c40c1e5a580c0805030840134403c0c840c00e0747c06a40185000d04014054234070b01364448021a141d5401540090403d10302c5030100004d0208800782802c0101140c00e062150640c25200c00c40c007200c10322009450981d8422244003914020 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 209520017 1250 209518767 209518783
    0x2040b040c0c023706020d020610090507020a0624170c0d0f02040204031101110d0f051c02030403170a090807020402090f18061003050c0427050f150102030a0210020c 73
    0xe4249221075003040c00308103005200c45c1c03003a04003501c80c4030310a500c0c9500114526200760154108a00003e28060782c15000e000c02408000c00e501a0120724030101d5254080d125202007140d215000800407041b2a05041680c2d07484040c8189510280802071400030400c5603001070111500b040e80101810318103a551124807000b54401d100103800020815407503039840c82c095003621281000c810035030f1100e4603022613a0300c50000a00c50886602401c0c01580903000c0c14003540c7c201c2c1040d4600309130a508a90013a581500421048900d2079003043c940490154000c004050500c441002c590380c82a45000f210b600a104030b8010a000126444da50002c100e05c10000b0a01c0103040d1000e41e448290710b10a443e514000e02c03440d00c0b5810014020701400c2e0180156220340c034607117850701d414240b962000b80e03408560b66003010680d08035144a0300543d806283e000102035910704140340b500d04080240d2003032030b0554005002020000b07801040d20455443c504201503654800c115202e0f0031301c911 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 209521267 1250 209520017 209520079
    0x3010203090d0807270f09152903040b01050307050a08150403031424060711280602010b03070501030e03030601080921071101210e01021207050702040b040c0c02 71
    0x10461800f0044880407217801c130740480c4042054544c503090b05409442100301c60342d04481181c80200901080e528111928146116441d400c44058000c2ca6056a00c10f40301a2100c4c25004018003161030180551401030808441102078540b0b0000ca03240c59a01d0051a00c54080c0d107000010240350003a040a81c40c0c0c03000407641086450300150418208031001071400c41419a002011009e0400c2c0084a8a0359048001030180c800350908221300d0302880100b5525820070303d02020900707aa40700e22030700580016000419050391007400c1c1803405419030311a604050904443d291818004000ca9170408800c1c81c02415544e12161031318506036900c00515841d59003441c0c52855156003c0c083e00c00107209042020002e140800111180240c5803013491703203c1c0201c030f43c10130440c0d6182d001d8441d1054000c00541408005805015102000c4a80c2002b0030030008142c000c510b018441c241030903038119400c01c81e44c1180c101c000e20508540300005d003d02c102860228034040f58000380b0b501100703 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 209522517 1250 209521267 209521307
    0x1150f02011b120b0603010b0f0706020c010e07140a0f09020705120d0c12051608070903051c111609090c0503030d090b0a0606020d03230a0c0e03010203090d0807 71
    0x3404400a149440c0700308425105444d100902c2810724211003203070b04031801c1ca2485402c1441e0715021117510f0b405105c04840740e640c00c011440c8481002e00070003440707650403c00381c9446840c00004406542c080c02d48107118000b4135209000424007500e18006440ba114401030701c9036014504507180100c0c02403401d030640301c041000303003032401070340c104e2a00101c86a03030b00121001496840720589401707850241e00d403151503e507114418031600640f0b40c480c086141c11004140eaa489140c20b01d01c2040b000340c41c1a40d10710300310101d182c110306801c03c8804800b008020a60103112100d0041031103006108903a5100c0b2001014024000700c0c00000e0040242920303958410010400000d10350352404582584c4e041000404d00140d5104502c00c03640140c01034000c0b2404031038214005d01e41e0140ca800369024441e081c0340c1071840c414040e480f40b0300a100000c0d403001c1c0004080c0580d82c41c0200180705c0c0e801041000201d601c0400e80407070401d482d0600060b1038851120644415000400ba494a10 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 209523767 1250 209522517 209522561
    0x30708060d02152d0307180b0d05180604030f11010905061008070609030c14040e1b011b0807020904030306210618020609130609021605010b0102030301150f0201 71
    0x640c00c40040000c48104449110344403c04803055801d143c4e02c1d81c1d462a103900900c001360805010341050030b08802e4a607040100302d51036a04104941d009001c1c881e48565440040061550424a42c81c488142c0300c801002189015a8001c29601207116803508001054100c09030014003500088001544141900c4980c0740c564980700300e401d881e02c1400c50a10440400140190141c080c8009407604080320302c0101e820014100704001d0420080390300250344418090100320240030b103640c5850841d003103a4050180303000050a040b90b0100344095035420480c01d0340092840c5003100d0200303a0550f00e210450b911030034103800415950b40f200040c400b00600c02541c444180e042da402140c421001080740c03400d800419413841001403c02900320004015400382c910b80768006500305d018240011440c2921b50340850701341e070880140b030f00705c840128440e00d0400c0020b00032112281005e200a60940d80741c241a03458074aa041c0c280720600000c14203200c0c99034800e41100341c908065a4801c5120 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 209525017 1250 209523767 209523799
    0x20c0f01091211102304060b01080105040b060405120309030a08070b070806130b190b0d0b0405160c050109050d0518090103050c0402130e040506160212030708060d02 73
    0x281c50303150710849884002d030b0030008507240261420b0b1921852180140382c43c036800c0d044c1030000d0020017440c44581001000c004151000208401d00c40c1d841150081244000c031400034041070810f070401d0740706508000109081e0780f10702c03003910201e9104642148000c030840c45514214812914829018010381c0240c5050004680c010700600d84540c0d40303418681d5462408446610042d03500940c0000031a12440342d89025030054020341c1d00061055060080e64144006c01040c5680500c514860208502c203001c3d605100b65284030000751028000b519219606403000301121095100784121003a24030140312096114010843e442000c6900d170120480d4003074030325007100e0781210314000c0070b81004001d400c0c400d1103207040325401002803140403041c0d13003080003941042c069034070004a54080040c800c00300c00001030145008a000d086c450814803240c805012001c0c1100096610403ca07144841a08804890780100a80b030725201c1921050001307030602a00580103035005505480c2c40c001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 209526267 1250 209525017 209525021
    0x7060e06040219050102120a26011d132a090b041d070303030c0e060d0603110d0f11010323070f0c05060412050403050a050102091302090d0f020301020c0f01 69
    0x100d0080311181c603218809020044910383c28010240141c2007440f8000180f640c1c1009000a401c050504462001c513450210600000c01da001503100d00314400100410144008200722007581407030850180d241c80f00c107404040c00c2c2800001d013141440700d045001c1c00c80c04a140e03050304a034a021041000e68881d6010080e15038000a18480d03807a000154094003424451006075121120107071100c540345071002c2e0010110304103141e060041641e885a040e654800007480b441c07485150015415003141000042e00651581c140d0241d0102c03064800481c00e82c2d01d002d00000d500c00c80e500c50041f50000103d001d417030071b40d504561048490786800f5411540c040f819104819540c3c440c1061003010b001200c24103848580642036070040300114010400c811040a010020341c18010701e416a070340c0e2203c6c40e1403040003040e501a5404220685149406d10003580210b010322400d50400c00a0400500e00080401e0000c041c0081d500055046407820340554695440200580c0e82070030384d01c848a40 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 209527517 1250 209526267 209526271
    0x9040303050106030518190224130f050d060c021005010905061002121206040b12070e01060509060f0705070e010f0501141201170a0b071101050a0e10020901030207060e06 75
    0x3c046410040003400001800f03017280400c0400c600180389000200b8820941c1020b400700607a0040d400011142c50102404075030011090030344055a80c4558142c0384803449150354001010303a00300601c1c1045256036210803200000e401400000e04a101d4103410381c540745098920142c1c0c035051a0000a02c034840b5844584a0002626041c01600705042c0481e240c13203a038014001d054106114401c0c1120303460450300d6008402501c0014001050000a180503884003c3c60b640c1e580f04000520425000b90022170042c1401d00300340f418190343d400041d02c54001e82d030345000300303480100d031003410700904000c56002811950a014510750b1610822040e0410038018180403400c0d916912046000c42c1c0f0850350490742840b001e00190342040180e41b51410b5420100d0340ca07102e415010f801040138002814090500ca031501d03100600d20715502400d5800042848508618009940860341720104010641d8885900e0041c4d60f5000003005074001d000342d8801400d82f500d024902c0030514000030700f00b8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 209528767 1250 209527517 209527529
    0x121b010f020d0b09010b03011701060e0a05061f0c020d1a0a020a0212031302040e030c1207060506030a020108011a0c0708030c070b07110405070e1c0b060a1d15090403030501 76
    0x440302d10100c10a000c01c5a13001e101d0324583d000b04000420555480c1d4410040314241d04001003082c0c0d0740c52726941400b21094405088480c4d69600b408660700d0301c480e41005442025402c0c900048070000041e180d07040404c8003a00907000e44201c90704100200e221200c0c1c801c040641051181004000400290005e5088201520903031003000c03c208924816a449000070054001481085900303000c080c003444d40504540d0311040c083c54020721000d0144d00c2031003c0d00a06203481d00d42a003095400d544014100a00940040003d01e0150345d100d01007a05494204607003608022440056170800c0c440e02c003060b0014055030344040340c41c800101c010708020a070103084403c95525140b074807009204009000b429044a41001e4610b03040c02c1e005142c2c0f00b03400e0700300113401400a4003c00c3c4002c6065103488410005010746204005454503010740044056402ca050541001c290790030f030b0b40c1c40c00030203014062a88009600e4400d00d907040b40d40100302504000550030146005409403600b0b015103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 209530017 1250 209528767 209528771
    0x2a09240605040819020105090604031b0e07050a03152612250203030f07080316020d09030f11030d090e01090207030503060f0f0301021305090a02070203121b010f020d 73
    0x3940d94403aa094400756031802c0080e14141451034541402480f44042c12414050140040704450740c8500c040d000031400303010307121304840301c0d1100951040219004209403500c4a018007249552200a69060b0169400c00041219580e8034040a001c0d040c0e00c12800c07280134142854400c0b40c0c8080040074440702104643c6c60b0742c0303142c80d039205030b0040b080010b10b200c000c1c041c0c0301e00900e0305200d00034940e40042c0680e4980000c600415500ea40946801d903000c0703d001044c0030405c40c890740b02c43e900c00341c1e510240c00442241c0d10010208025848058134098014441d40f061150380c0e10b241103e088014100d80c0c1c0d0301d810742c2e009000304e07400d8814064000615800041c032880b560003218bc040b50b25507036140c0b844d50780000700003a112170881515000000c11000180c4c0386c034244002c01c1d090900c044000c0c0128039190801c003000000801004a89005200080040c0c80010344004100d103c3c2c2001504d0f4421000f03032016031080c80f40910120f44c200444074074031014a60003400c8234019a481 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 209531267 1250 209530017 209530019
    0x40602030904150b09220c090602061b090609060405100201090b01080c0904060e0109050a0302030301080c04061a0304020d290a05090c040b010302041205282a0924 72
    0xf2021204032030344208808084100244d007101d181a402686032500052000c114804081c9035481c00c891020011902060502805121117501040f2466006a0700c0da00b0103090210408070450600910140350702490300482d4924082d6a000e064802808001d04120b034140e4480d54020702925204000303645001444c4000318180d80c0c041001b15080701c02411041e2a0340303a83e42d40b58011309000402c00030a542e20441480020300501001030041d00940c0115220750421200324209080b0400452085140980412803101d585850124070110f0044481e100e5a450021070740592640380c008000c0e030b1001032481c0201e000106541050320301020b0800703035030381d40c1e070245404c43d00d00380c0305a00140c1c81111280700c3c925217904400c100200616015013040e80c2c540d109041c0321080c44003200c180d0010390300410758025402080741c1041c07405103d1042419152165002e90802c100e048003820781d0074843c100d017120020b000e0402400c00f0101004041780c0c0080c0c458551104c51003520b000544000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 209532374 1107 209531267 209531291
    0x6160203060a060801060f06020717031629040206090405180d0504050907020c0604151e02101a01021b1504080f010e010501030b0106110111040602030904 68
    0x40d000b0580b01d051951117425903d498214180c0ca09842e40704008241c1e00090035012203050b00341c80044070b44d5004034503045204401804404221098250b0108040011b548000540c10a421440c0342c1c0a1460103550a50503200a0361000080c0544e11940c0382c03a500094008205102c14121785142c4000303613003000303840d0400b5030101c0c001250402250412240c40355201305a48043c0c4011102100010074130702450184000000c40c1602600c400c502400c0ca51281c60500303001040c100c44d2004c4020350700c9005800c004442410080380c4050708a80c0b041111f00c00d20142c001c0c010f601448170208064059145500f544500ea90401040c00448040104040c25109015110300820700c1d07400341c255107002254002d141e2420b00108081544000b40505440542c41c0843d0184203002c0702c02d02502d4810f105a500381d2001130000b0f5290307000401464a94802da41c18001450740c16 = true := by decide +kernel

theorem cover : BRFrame.Cov 209352517 209532374 := by
  have h0 := BRFrame.cov_init 209352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 209352517 ≤ n) (h2 : n < 209532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
