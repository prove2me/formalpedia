-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2686
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:26:00.424763+00:00
-- url     : https://prove2.me/submissions/64292cfe-1423-458d-bc13-0a47b21c67b4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 482913669 ≤ n < 483093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 482914919 1250 482913669 482913707
    0x80a1b120c02010605030a0602030906100e04060518060c0307021b03030f1c021314010201020c061803120903040f05150909060a0509040303060509060d050a0b06012706 74
    0x2064a20008045014050115089564454482410314000d602c0a0010040070313094400c508003d0808400a4104031140b480300e00400d03002420b910714038800304094801c440715810301d5803078544405006142c020b0940d614440d00320306069040c2d0040280501c40c8861080f01a96840c1403140282412244100381c542014011690299a40d0202c16549510046115152111008162200c200c2000524243d98601c0020799918100c030400c0541c050360101504081800c5000004900300e00c00d02e1500715403078001001040c2e0940a0841203090b6034500400c8a0512404550001c90404191413065484d440083c081107581b65442c0c201008010880381ca015517078104200219a00c240d076000d61084103a4000568181d549a01a40107070801500842c0e080c0340915016008054074013819224a084a00260312490b00d1700e404150f0395440000303047c006071513940d0300d0040d020103403100d03050105a07503d0003101c0000e8000230f4400e0400601e2108143c3c500500506491501c008848401e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 482916169 1250 482914919 482914961
    0x608030c0105090d0f0e041a0d0c06080705070206070f170d06080601050102070e1b041d060a2c0405010e0d09030b010803040b0f0c070b0408070e060609030a0210110607080a 76
    0x1707143c010030380810340300055402013071084001c1c10900c0d4502c100384200340c1c0840c0384100d45090080b07680020058846079103a0480f1a1074204054030980a2590b0081d803100c810001c031400281683c001c2801d031441541004c203c080c041c01000081e401003807404047c0c550700c06041064030420050f25004000038000751045908040201030700c12401002e404199191401c180c50102040045600800541d0b00c07409041041400c201d03d201d509940c1c42d48038034401100031414001406402c40050f0521316220844001802280140303100144243c569550707a1041c55030052040c400c1c0d9000c14040d9640e10010380c2549000102094183c2200c6100e0b4028801404a80c590008441860018119854a40c000d01007078034548100781d006401a0300012a0004d0311241c002000410303a4810b00b0300c0241503507000d080c0a420700031000c585078036610421511002d42401e1040500d04013151810301c0ea12021480e8552500301d0075509100058240f00801040421300d220700f06a40d008a1014111 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 482917419 1250 482916169 482916197
    0x1401090f061a0f2110060f030e0c2407080a08010603021c18020d05030a11010209030601050108040812010e0a05151e011818110304240608030c0105090d 67
    0x2883c01400740303200010100051003502c01c40781c1a640e0090031166000454503160407400c0554020891050314081485440200d041ca8003e004042c4100c02840080108032001c20401c04003603000030303220720581511201d86160344203a40040140318000c1c2080782c5d541644620013048154160f00510415106003c0d00c0c480ca1144040c3d5404041c040201285102c0320524590b078400718840000c7d840440c41441200b005004000307444440d08540712140007100180c4c609003030348600004c0da40d164000400500c075940c020803a50750083d00070080641803050b10300003080250003e0300b04500d2403000c0d00820001d14414001c5035400751110b26043e84002841000c18845c0c1c0c1c1c20344c5184081d9240c01d141030f500342d12030311110201c046c80c4c0c8212140950b03500b43c5108203800c202800c21040e81054416440440d121045030f0241d0303030010344014100c10001c1340030700c4c0e2110034030203040490300c2d51400103d0705400c2001c1c01c42100b04000005590070311000c16464030914a1014040c04078810304500c0c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 482918669 1250 482917419 482917469
    0x8010c0e062811010203070906020610030b0c031f120203060601030e03090906011101060f03021f050f030a0603060203010303020625050f030c04081e06010e131103011401090f06 78
    0x1d88100e2646440030b4030080c04050782e200d001e04940300c016600c04030400c01d15583c8100c401013262801e400b502c0b40da032604001c1d02003030400b030b0002401c41c810040110b0030400f4150300a607801072040c01e03001c40000007400c404c120403120360b200c403030800b85a10140d415898140b120ba500b11030309003030421605003415140798486c047c0340b07a141d10915540d000a0310990042c0b80d500c9071502140001c101e0103850300d9104464505070b000590046048049103000f01c1c0d07d0f000c0215003035145807a80d5007811076a10360b0001c9544010b001d52101c031b80311980000000c0f400c4c0003840c040c600ca5000b4051520300408016280b07000030780b014240c8048085c40c000261741180440b6990103403c0a02a5240c0e5800003012441c41250b210001034442c440b422402080140845003800460b003090310002d0341d03140d0b1f4800703001c0c1080d5a034005107024003848100140a801d280c62894801a0012402c07410140c4104850b076400da0106180c00c1c0c60b0301e03148555016a204c2da9015000d04240b41d04180c8011081c10 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 482919919 1250 482918669 482918707
    0xa06050f0621120409020c010e0309242a16030b0c07060b0904110310050615070f140c0f030105221505010909030e030604050a03080c09030708010c0e06 67
    0x3000c103420441482c500352005000340e59142a604061990312607441c20010000d45c0b181c05081825460004040c990b114080200c505640c80240f9041c20311420380d111401c00340480d0320782e004510701084000c1d01010060740010301118401c195940064a16401130304059140f440020500720004c018400030b0b010041054208c90b01042003500d81d04545030900080440e2410641c0c8a01032100304010081c50040c030700c500d1801a801c0d00c2d0f240211101e030310b041e10380c2a1821940030812141c14820b03420410060b114890160180c0f4202076240e44504420040084101d04183c006031446111418072040c240032183c8168000c001c145004118200104490703038114610400792041c20013404a4400d0328150f15040d00810000c035650380c01d08000400c000002100400c2659118224a103404942075124903000030151860300055901242d200b400240310302e860110511994100e40c030708115060207042c5070000043c810b600c0c0b10f130250429440e01c40b15807107501c1c2081a070b9940306058440c9 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 482921169 1250 482919919 482919949
    0x30b0f09071401020703050a0b040c0b040f030b0601030f0c0207080f030403051f060e0a1406060f030a11190203040f08010e070b0d0b04111b060721090b0103050a06050f06 75
    0x2081c0c06a0441c2c0103d04204c42988041c00a1240041e46070071b02c446460004c0c0602d105150010b900340d40c4140c0c04500b40a50700c104a0982441c5104001085144c1c0300640c0c072000500d0009010045008540d00b120611201c1000681c0000024026030804008101d025002c8000860400e851655501d64522100704041c482c3d00505500b01d000054507000308002d401000c00560051810801c000000c0403003602c012000c1000c0e4006c40e819090800444074041001c184140c9959210385010700540b04801c6d1404608504100340c1d40d0492a03e0054488680c5a40c099603803039280c0413502030820b9403a00300030002d07450b0265240c15020700103001c0c41100d40c10000d03c0c5e00d0700c0340707240b040d0000c109100c2120780241c10140e41043c030000c400300a0400c607264801c104050002c481c9001e9841c03c04807440f0ac01701d100520b10b8451020000d0300031318225500100451030000c42c0d80c81c0001d4000030b82c4101d40c4c03980700050000411100d8084c45510004503401003d04e485d01c6400610019004000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 482922419 1250 482921169 482921189
    0x315040e030702042304030206070f0c0f08210c0d0b03070f0611030c010c08010513110901030b061b011d0a0b01030201030f0b1009060e0a0e0103080a0c0609050106030b0f0907 77
    0x10030406102171110514001d441121095881d00d0306001e901d0f070000715003070030000e03400c056800e00841c0070300c00c100010b41c1c0102091607021030355581c0c42c40b00d42c4281c800207000040104400c0d030784201e0000b0b251061401c4a001920703030784118064400e4a103c40d48182c801c0e040f00390180038001d030301ca07618003c682507460030b08404011300840d00c1c2035114601d00841d0b65400e000922100310b0700503007194100e50b81982c10130f904681c01c4030a60300721480c0040c8183e04540820203040c40358400e800c011134400c8001d19480c5450040c01c022100c201c3d001211030450b945498902940405029078014001e00300d01c042c14009481c2c1d501c902d803625050100905043d5140310710300d035150300c0742d0000d02e0410b80a0015040c031103c088000e41445080e03c04c020024625002c00012030400301ea0510480300200e425410690031030b61140703000e401c03205455013082804445400460200d000300b09150307008000004401d42903013000d00d003912004181140580b03085040c0140c02000080071400c6841c4a01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 482923669 1250 482922419 482922431
    0x14100302030c12010e0610050a090b0d02090604080607091e0501200d02070302041d030d0b010e030a0f02040506040b180403020c0d03020f010518280209010b0315040e03070204 77
    0xd1030180c1c020301a020800309003040002c80c101724214001d5002c0c41c0c0448414140d00b0151030b04540e02d00c900803001000500400e410081c80800c60060302140e1300e0110054100f4040d080411456005580f04030750541c4030600348200950405a42e1001d08400c2420301141a038010a24145c1d0225200e45410841000c0c2c0340b07103003041111000c9241c0494082518802c0e012014020f5555520b804280d00c198903014005420412040d14090515400000743d42003410300b680300c0e0024540d20f202c0070306008105018a40c01d503014030400c03404512501d000b01e40c1101078014801151001442c2600841c81c0594020407070f5280039038901c0a90080c1c030490034030355491804030705208860240d60b8000314100f03c01010560041039008889580d20b00030402d560320800b42c03900e412242e20b102601504400e4540003a540a0158483c58142d803400560804c1c65a501040c00c80400360700104c40d038034010040c043c0203a480083c0c011f4820080b06e00b4006810241e8882e5240e01c03032688000d1245aa41c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 482924919 1250 482923669 482923681
    0x40e060105040320100e0a05090402030a05070e1b0403020a0e0622021b070f121b061e0806010e1e030111040302010f08010305211b10061410030203 65
    0x454025550101c1030203140380c00007a811036000c02c002005441044e0401742d4500080c880d0100d945148801010f081e000c030300d003030f040c4181079074090000c2e0f815004644601010032808c00030b00004102d00c4a16041030319020b1440720003620109113840004d4410001000903a17660009078007507820020780d10320181c444800180381c0c0425400c00c107200288001d005c00600c030027580a4282402001c05c6601d08800030550280c65051a00510044110450041c0030100130203040c2c10520780706180e010107081c91400d095494032401d80c00743c40001d0105403050b50b4110325110420300680241000201030800d58000780040b04000755980c050a00301c000c51030407202d02440e401c081c2501500821601e200e80e02d04401e0741d4800c1c0000d07400f00742c089604509240c45200424100c941250141c1482401e0708960701e040099500b0700d80000b0004d005484413000003044a0600f00520301c001c01c8402c043c520581d00341d0303030507a0145090031981904808144c0792586e40e020350503854980141d41c2e41d01c41d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 482926169 1250 482924919 482924927
    0xe0603070e0a060503180303010b04090c20070510050901090306021c1811030303010e0f15120a03090603020a020307020603130b0c090418050312040c1d1911040e0601 73
    0x12a04a900c58502c210000c1c0301034001c401107018900041402040045d0a444295030b84000e1040000100c4200020401c00020745d020b00310707038041c51420b0f480a00380000b5000300f042c420076180001c0d80000c2820030440c81d00060b41242e10300b450400d58203044820380042c1c0b00d41c1d02484007030140c41c0c002850b070b0420421080034140183c1808000c2003041d6001c0103408003003004010880300d0b402070050604081c5000002d0b80c0c101d41c200c0e004000290b0f140345040c41089409890300d0100c0c1c4104001300c80a64500207407801e207407442d0340108600901c03414024140f00c0184e0100d030616104018075034203280d010040b41c0076180c050b100660b5907124086160302007650004040c20695840051020100c0d8010040c5000c0da01100c0c01e0240810070640399401034003032100144598420404132420301c140214544d0302c5802a190701c1141c503660080f05a140f0b492a0300444019680010490307a62550040a00030240b01c400070801c0307560204c0c0c000058465402103001052044000422903845 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 482927419 1250 482926169 482926187
    0x1006050117180102040803030103051209060a0c15020309011505092a090a080304090b03060c0316090b0a0c1a0f07110a05030f0405040f291c05060f0901020a0e060307 73
    0x1d240004c41d61983d40c0d103919900e0380c00a01048500c0c0c0a200c034403185d100e01400645070b07002c1000740705600d008c00f080c5041d18052800c0d4000c503603500c0811001d035070f40f905134806144107501d0000081681c2100840811040941390019446105100184801c14950300c41e005601c0c0c0091070400c0b002240656a54194058448250f81c00384080f0004a10303820048007030001c0b2030040a05001a1501c0c00c1010b803221422602c0407000c8109200061b450f082290b1501d524000c2410104100c503242c1055a141d5405503a405003c9800700000c0c03400c0048501d4078a8455501a0b03041480b030810010003e6400b0010380464108022580c1c11168244d0601c007400c0b02e1503120046135a50300800b40001940e40061181d00e01c201d00c1d05030560503200650165046094003415006030000c0c1140904182400201200340c00403200300301c10090342d5140800c80c40d002d000da4028603d80c50720f074407103001e9142c000f8445515039005005141c0c1c0035800150b00011150112401f60b02c035039a00508035000702c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 482928669 1250 482927419 482927461
    0x1060f05130306050c0a0207060e06032206060b090f030703170c070b030916170718061206050105100f0c0f14010f050a0e010b060906090f130e1006050117 68
    0xc44c203030500240918600080007a4040364080d241c0c2c26607120810358001c0d0030301d220300e608104100001039600c800d88150307060b0b212444100708040303281616054121001500809030f214800642d000c02c034a4502e09507040b40001720000d121460039a0380711808100090718802c04004080f490442c003442c00c0c090751003e4043c181c0c0c000d48a2402c92000c598810111072800082c00e5003417808200320140c80c0c2d10412100701003004154140c82e2025048051008912081c0c0c0d150752103070b0124103078403031242d40850b441c0989804038580d41001e0400c9881c0d07104020030400d0003850210342296a401240083d80f86030031000b40043c20b055803d164901030511100021107500e04012644c0304131060340f026000d4003a01000700301082c8203100305800c071820a85c11992048003402818513504e852801444500c00242c000e114401d03484006c18903408020112184942e01e8825600c42240204034180c103401141c00c0c103200f124901000a070400ba0000c0c006181b641c100f07070000d10301414812100070002 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 482929919 1250 482928669 482928671
    0xd02090406081b10110606010807090f0321020c13020d0b100c0302011103060310020c10110d110702130c0c051e12030f0105090709030203070e0109050f01060f05130306 74
    0x2c40c0303c680034400580d2424030703c2258007121200710b443c494001e406114244c8801040b0548904005444070a0001d01e000100444c605010900e44c05901886004501c0b405140c42d1092401008001c00c160b42c40301101194418400f07500941e6810520940f103410700000140d0302c80c0d131004030b0b8000d03004200c00b540c0c00805000c0c0622200d9031100b608040702d8002d900030403250f20b81c6461205144025a030699055115000c7c117400201b95900414288040303108980c0c01c071076807040701000d41d01d2550420056a9000c19045110348884c0500c502019507284401d00e2f00f206607000445411118202017000c91f504c201d00c0e8180c031302a0f035540002c2034016007111402240341c4141c4151b04541040c000301405140326070011410b07a00d0550b4000d09441c0c03000030b41c0da800d00080c0805084020b10709010411a0000000543c80074401900940000c1b80034a03000d605100502080c0e50015103c009646030140c0100a600d5000c000e48000141c1458129a2040141d01f820310140158102420352 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 482931169 1250 482929919 482929933
    0x2120c070602040504061403150601020606101704032a0210031802120601050f091302010f12020a05040e160c02040f1113030203160e040b070504030b0a0902030f03040b0d0209040608 80
    0x4100108000103015104600b100d07427120070a03d1742c0c42c0d901000c0d10987e0240e03001d0808507404c0c0c90200e213084002000c030f141c504006101c8a002d005212019101500401c050b441050100800c81c14125000c4060340700703040b580c1d54181d020072140011075010004055640700321303045c40c2800e1a09010910b80040402c008400851491510341100784103403481400480e120b4441030074542c0c4003511600032108946030500c2180c0044d2203102c6008a80002c01802344c0e08003055481c01d10241140c0b44031a5219501c0710b080c00a40076120303102400c03401500000002c000781281d40160b50181d083e03415580820728070315408030080a881c0056070b00e241c0f140c0c0442e400b41302003104d01107a800c41c3c0c0210101e4a010441c02140300c0c92030300a0041c804a46507460000e00499240c04c1d413960000e201c2c3c500946481c2e503d8580000c40c00707054940a0f40d4503100d070051010342c41d04103c07028403482c250004e14a42480c0a01d407a02510a03035a5001405070082101d01490391190f002c80d00401d144da095800c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 482932419 1250 482931169 482931179
    0x30e030d030c03051005010804080d060518010509060d020618130f0510120b010e13140a120513060e0301020405040903021509030f0f070c1716080102120c07060204050406 75
    0x2514422003020b001900c0d0600081001c58140483d0f4201d5406840b1440a501c59031181d0307000d54469040c2218194071003c000034151070700342080305110b074408180e035503030350411041001c001d80180509124010160701c00700581e8503a1300701c85900040d4140910309004900114901c83c506000b109820b134507103191042c6d4408190020ba102d0394280000c20b0328191640c00d00045070301c00c1040030b0000e00d103403030041c01615403514800381c000301c0b00314148210030020340e01c0100002918540c050302e9040703080d08030100402e070921a001e03910241090340c1041d1402501a00003c000d21800e01049420110345030191403c0d41140c0c00352030054414001c10541c0d0030065501c812403100e0608922104000030141500403003603814200c110140c6928040d05040c0c2500703030f034000b00320076100c0c082d405100190004003011198604100b0b03d001d002c00c0150a90040c21891143e400400785900401c80403040396050114254000c2002035490b0b146c0c503c4d0b042c104000c0c05540c016981207880c00300c0c007180e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 482933669 1250 482932419 482932421
    0x90b030106170108061012080f0412051b090a0c111203010816060f030c12050f0108125412010207030e24040306020a0f02060108030d09030e030d03 65
    0x441618096400c240e90303030303000301994944084a0380d2140c0f81106c18284400414094000306040c0144070a6003410200c0c1d880b05c00d40e03406540500000c844101c11182000018010700408254141000c0d800701d00030301c0400c0315004001c0007200c106039109102010280124074016110302e03418201c500c2c08491655809080d070082c062083c4038881c14403a0303050350f0324222204042c3e80780755031841c11400d44041d0590240000706000030611030011102461400c862080911900118041c2c0290b545030100617810214001711800e000902080130112091952038120411217580f030701c00784518a5500818101c120001e180c100101003e140c840ca00060611480e01400c0b0072145d001101c2640f1040900702c0c03040c00303001000300e500c91001541600d42141c0481320014400854509280800e4050405a0154108481241d0301083c1c010001e940004c0c02c000942c1c142c001002a5410a8402542e0380580d2940444c1c5584800034541018410102000400301c06411680080d840c60070140c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 482934919 1250 482933669 482933687
    0x1110020a051e1612022e0b060424050f0c0604030e04020405240f0a0903030806121b0307090e06010f0806010b0414010504051206040b090705130b18190507030605090703050403090b030106 82
    0x74600b0010b1046082c48c20b1011902100c032400680018504503800e8084904184c4241d8403c1c0030050010341b02900303a040c001c140141d65800035201d5403420b441d010b41b03902005005280264818042405030380c0342c804146441084012803400c00d80b501c007400c1d4000d441954010714501c3c1003c601250031540101d00a4181c0340309482d2aa42a580c0400344024070490702c1610b200d6074014140b1100c0158080510516130740090161071100d51640c02c0380b000d80d0326034030035410207034890320041010040b589800b2000d00303958800351500c0d51400c000110140035030700070f9100004044c6020000d40e800340c801c0360020f0401518080390510300360b51080d1102c00481c0d081c2c03086100c081c0060402d0b10003144460a458001701078200004020b8102c000030b001c080505030304016405000503c1508c400390b010f10602c0e481480101c84014059494262040600040c0c245402c0036020f101c1075036030490342507020805d4130740007415580c0d42c01c080325070318030319400842000400000411041d40c440030031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 482936169 1250 482934919 482935003
    0x91512070e0102010236030f10180203061b0418050703050a0b212803020d03051501050c011d01021305011106071110020a051e161202 59
    0x10341202101d840168240c0c4102c403c513201800300e5940c2e4260143c2d0194415102800d05580014800c2680d8082803902d195100314181c180d210f0ba04808841c500390040404004082c2e04034010981240e000c02d44e5400090007850180c01c0d25500d003038440c914001924020080074640ba0031425125040304001d0000b91000c0700040c1c14080042c100a4490060076050340d0064a440345c01240102a08051103100d5250000e0b40544a100d0400c1d03822007907984004c000d00608501c10f0f00491070f029140c04905210f00040c1814842081800080d001c21724200450a0802ca42c0c4e07801500d4402e8014074820100c41d0a00040c0719440d480b90030154043c0c201c40c0d45103d101d1809680f03400055444d4075200c54451100d80c400300000e400769124070004400d6001101c11255504c4441d280301060ba0454894500022400b18000000080b191f0765078180d6241c5404451800c640708600c100103581403e8080c18000e15100d80c024000e100b0456541c1e00ba201268100801c403045041d1021040580070f1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 482937419 1250 482936169 482936177
    0x14030f0d090c2103051606092a0e0a0c0504030f2006070f02102f06010e06010c06150506040e16090509040605130c1214160303030209151207 62
    0x300e0b07401c030f031201038407444000c0c0d04401c03118600c2c5030b82c121a103912501d5a120140e02602e031000025180d4060f0b01d40e024498440500d00e00c01c1b40103080c64940b444114101d901c980590100622401084500d411001008001c64204032501050f5400e12481c1d00040041440c546120140700c0184400d8061140001c50604c48601000c01c12800740500c0c0f0001d4050842207074510b00510345107124140a040a00b003e03d021080c130060070340604101c1d000e520041c20a80030440c62103070288003040c05000354003080030751401c1c6040009c1800303402d41401810607560f00880400e41c00c240d0045001440010481a919510fa5100b006104c40940e403580c80c0e42c030f4050780d03c0c160b27030300440d81c2c4030540b00050701c0303281d80f03a03901d84614010700000b070901d1000c5400d880c01d040103d502081500c0150000c94030070301c440410b41c43c290b5001e5007039000858481d0040051400000300c06c8004200b00c0c0d81503e0f0268483c1c012070001f840b00c4809040c40005800000380310104280307030311166403003815507440e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 482938669 1250 482937419 482937443
    0xb0d020d0f11090a2004230a080f03030702010f0501060e06030604060902031305070510140d02070c0e0f0f0603101d01050a0c120b0609041d011514010207030f14030f0d09 75
    0xa2114058001c0c0c0c081c40caa00c030101c5025201042041260b1f0300c0d28800284001c040c1541d941c180b82c1007000401d03000030281c10010803c070b002502405810a01c001c880410000d66260150007403101900100ba5072155000001250b082e54a6030808005002101411543c074180200003a94000307402504a909000e01c0800040502c2c00d01154244000141ca410102030001602c0d44443e0780400d109400050f07080c85000e0120701c0e40c0110801900d482c02003001203040009000c0e8054038014407420121502d0410000701e0f031004070703510248401c00c003004500d061400034003400340300368000c180449600c3d02c420451401841d0f00460120801515180c010080f54884032090392182401c040c1c04c29010072003520141001d610007a22401310308026200f00c031080e41c0007425070b2403180c1d0514107000625030901c08103210848402d03002c0000d00041108516540d00d80c2140f50400c0c40160071403003070b9004040c400d1000d000300d4031003600c1950303059910801444060028a00d00381d09940c16104a5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 482939919 1250 482938669 482938721
    0x506090619090c171002120709080d17070e031c08070f0c020607060605040203040308060a0f0503120c0114040501060e1605090904060b130605040b0d020d0f11090a 72
    0xb208905145030014440d100050070040b038120f43c2d0301d0b06205414a0301c80c0400e681d10340380c464800b03401008480c444a58107402e081000604c0c80940f50017142084e0031420459202c280c00442c4070640c2c40c0b07220740707100d481c0d940e840742600d81e2081c10110baa01405001611841003400e5000d183d214030321626290790b25250100e045512152049154000c5901c504801d0003606e8880e01500d0024481c07100840e480b61aa004501a604241c4040b80443c0001c4244030551070080203d20107004c500c44441412450000041e0b980c110f070f914641048440050b50640c10780c000e412061100441c024000501d082c54609603000301168440c0000780d08040e400300743e0403c410b1840100c3c403002991464100038101e0100b103c90803000d0030880e8984c1c4d81d0400040b00b40c8424020300c030152101e40b00040c12031301d00814841511845c2140e6403060190060010050382d0314440044140c2d0003c200740d00d41c2d400c601d4800d00b9050103080b00c690051007441000382d108142d40141040150074542c1402d050882 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 482941169 1250 482939919 482939921
    0xc0801020c030409050f100e060307031e0302070611030708090f030a15050609060d1218060e010207051008041b180902011107050a090b0a0b070c0e0705090f0603130506090619 77
    0x7d0714014401219941c00700015000407442a401060003070942d0601613403552202c41044811000c00905d03a03000c0159400d054041c00003500400d01c604111421099003182c19499102d00c8100400303503040407400302001e1f15480100e1300012000b030100d61444d4503904040c882c0151030300c8250304c3d803820b1400058450030032500ca40e01070140904440d2000703445555070542006d000c15050100901c0c0f20008242c0140907090000816290301c400408511040009007413a045800150050b0a0001c000000d40d9100e0034042c0d0041d000031101c1000c0e81c030050b86010070145544106e5207072641d890001000403140c0e1009403001d2003600c4014200a81865140d106e403a40d1107007950081031090200001e406c603402901200d14002c1040240c1a01c61641488540002c1415943e4950b024018404ea0160410b1150000c034981050f13414610b41100181e801c0074000c10083c001d45010000c101c0900318074400400c0c0b6640602969014a4000e4402c0e030742c2d000c1112001c50302044080381014201032 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 482942419 1250 482941169 482941171
    0xd091b0e15060304060509010209090106050405030f2b11030315120a11040c090308132d05040908040308120f07110c04050403050903070905010504060b180d0c0801020c030409050f 79
    0xa000c2e1411641d4036150f420051000800641655400304801005c0d5a102e81c40f403400703446945c03146070322107041806240c6411040364030448a40d2107118038002e03680c125a51000360b003918000b50301c40040961000c071103800c009101c80380c1c03a00c404401d20405214840400c100c038030702560500c907081c51420845545007500c441c041e0800c0c0884502003800e080c00d4000c01d64400c65800c10070f102d542e980d6904130b03165020854000e400d0102c89010300c0070440361500b01c200e41a40c0d4480030046500c032000d040914030a40700302071046a46120001c10071a4000c203940045800072000c60300c41040100300e07500e06c13070200e405983c2c0d2000500000c028034002c040a26908210390010200d0f881d651080c0402408007800c1582802401e0000174040e0b5001c000c10130152481c8040440d00754500402d100564025421071a009170302802034542001e40c0b0b10060b610b5040403202d842181245041410071141e103500410310325400001c1017003a1060010040086071001d04040010740e40d07032800c522503550 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 482943669 1250 482942419 482942461
    0x20f041202040b2b110d030806030f120d020d0f0e0c09010501081b03090a050d020307060507020d0804112d153c07030c030f03150504020d091b0e 64
    0x507a0304030700a8038510702107085070036034405c000c4607000c0341d000c4c00020300c000d0000c48102d00090402c020894a800e0030b004459400c42210010000c5a0040100041c43d0040400f0590100e130302044400c644c003182d0704491801900c101040100649192180c1d8541c0a010140c1e070082c0c041100014030b03035200e00511840781c0307940d0f105002004540c2c10b81e02c425920250203251103104a0b10303003c01140051109514060702500110383d03400310344c40c00200780c2c0c0b001444902550058803540c41440d8000019a07402640b040c2d42c05802e41c1804001303400350b286949005000c407141c07940080090214a41140c80450840c0d4407801c003552840505403e201d6034100000004241c0210700d1103100d01060078105d2100014240c0d4020201524010260851402076001901d0342d0050b0051581121110480b0318880c82d05114001941000d1800071007144a41d03409950b00040b0502002203c0d4050000b45a10030700b5500729405451401000050074002d44103c0710351000807030350070510200a040191 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 482944919 1250 482943669 482943709
    0x30f07090e0a1806060603020c1b03150402030124090b090405030a080709031b0302011e0f0f11070801060501030e030a09050114070b07032a1b06020f041202040b 71
    0x35071280049005082e01d490202003100410441d0340001e215030242001070020b035607005895452a00c1110b2a02c55110002b0320b071030500140c0c0042d0351324086503003903401e418562450301a131a03d1000c02d005002c0c8420107030881d02491280e02c4500d031180c6501c402c460198400740100c02c0040200640b4003401e40303008210307030300810480b00381c90701130510389501407241e007071040c80d1036a2a2124080080f080c500d6180d142078842e410310440d80c0151400313181d1401500124030007203071018080c15841c50516520180420400195921807080000a8102c0f4041003610350583d554a10207018080d030b03005103400300e8213010343c004c110540003007541c802c5140b940d50742d00e446113444010348044910b1005443c0d54801000107a0100d000e40c031140e40920420340d0006007218252421f0400702c251082c2e101c1840c00e42618500a20f0383c0181c4411480c0a10303000d0280c110801d141c03550081c0709400701c0b0304c41810042030004980b030300c5102c038100e01402954140210034810701040f10001d01d50701c40b52004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 482946169 1250 482944919 482944921
    0xf100621030e0d0501060503061006201e0c0315041a0702100603080316050408030409020306040f4803020d0605121f0e060402010c15050c030f07090e 66
    0x6503514140c0340d441c024145034044024000115219100d89541511269100d0390100701c2d03820208211580b20b01c045d070b00004468284900200006620803a080346d164403680711804441c828003481c1c0c26507240200d464001030000c0c40054171005d058603000e00c00e004802036000103440c1d03401c00b188225448100d40c11001040f580c5c000d11604058003400443c8580410254910086d1080788003850041009a8417031600030080318226000000e1803041020601081002081c00401e490644404800140c1c4965031000400c0c01030200a11b4031410a00704460001003003108982240000203a03001940401c5421081205644a80204a0700c846800c1d03440010a0300c40c1c1d000c3d210072200e89501082c03032a80c030300004244002d0081ca155054106016001100c1408501c04c005101e10f03402c1400f001c8078126000ea110707100100082e050000e040d60460801800000d2580040240c00f001c211600b0b210003818a9904212180c0b501d4440380004a410fa501a4406d04201d80c41d0b03010590f42c0f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 482947419 1250 482946169 482946209
    0x50310230412050a020f072d0302030d032f07030206011a07020906061c0c030605010306080303010e27010605120a11010e21100605120a060b0612090f1006 68
    0x560360001490001714002c004040071100c4080c8617610040461651a44808000c94a07610741c41030104039005503034604a40410068802003078090641c652414009129051b10780700300302089401081ca0180059400d0342517010040e24040e007220b901950031a0040c1e0303200d40d101c09001c10f0111604c1400349082c00100014079000107229401140a0f10103802c04800a1200241a10140c156001142c484a00c1c0404961511900c0024982460144034441c1ba059580d03440344418050703054951034030400192441542003101010441e0015501000850200d00340e0080a45004451140000700c000030f0403036200041148000c2c0e0442d41c44a01c6c00079580c0150ba4014904503d40c5d04280b41001d000241c1c07802240940a00d203000d0043c1007405152100101110443d401c841e104000d80740d52880102c00005903c0000d5a10650000d0404a08000502d0038050000fa20b0a4422140c0130420300d1100840c1c010f0301e088081d0704503020403030400d8601c015680c09005440340d90200c000b001e00303 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 482948669 1250 482947419 482947427
    0x16060e03061306230a0504110105040605070809012304140402031611010b0607051b01110706030209010918020a030e0105070f03020d060807030b1801110a18050310230412 75
    0x441040d407a1001c00034101c00940d6440d0001200d0300e4170342c030707580380300f004180031407000320521001003407900343c1c41e0a081c110081d02502805101803d148408541c10b21f0907400b5108142c03604410100e80060a0040400d11703c443d8040d004040520300d0329a811191400c0c82d0007038070700500e50150038100036000107404644685950100d50b440d0b40d225442244031f601c4807030040079814000d80c003070050380c1c400d001410400c200842086041081d80406111907080c0800d8031400c2c0d80072494096950400e000040301c403c103c603000719143d9200303006001080b00c2a5030080c000f074103454909002c2030350b6201c14242281c008490507070100b804002c080a403280710382d0003801f00010785d42c00050502e0b00c0c0c40b0301502e003480760f40080b50782003060018050221400c011a405100c084002032000141c05030120311035005001441e010b00008a41d540c80c1807144500c40006010f0140072036a95169103d00c10026000c44142007014085040c0810351000e0413442da10b00c9580c1012130304180700c5070080229 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 482949919 1250 482948669 482948681
    0x2090105070209060409150605011e020d081e01061e090503061f1205010c1805030706050306030f010c031505060403050c06160f0807020f010c02010909110c16060e03061306 76
    0x5a803080d946c0c036100780069041c100d580103140001100051540c10000003502c0f1181e90007002003a00011302c0414445503002943e10b001c001140b5040f56541c0b1641043d2956900680903160101c0342c020011650035400109510b50706030003108100c4e10f000104041e6007059260248640542005002855500700820124540c2c1800c19458850320755483d0141d0400400b20400c4070181d44501c04003e00d5548070059581c40461402e9250700d1030701c1d12000076501c1900d44a20801e21801000260740c6035018840b001c1c0c0d01817a9402409480030407400140208004002c000710030300f220001240d142441001d890950b5808001001002c9410003004080d4000048258502d40d00040e05000100600f02088403140f00710b100c0c42c1c9500d22403040040070a64000c1c1541000004442d07500503030303849001e0b08212111020002044820300400f1040e5201d030111005c0300c2c0c418134406008901c60707025010116280d40e621400c0d8251100c00301034440000f900d0016540f0350402d180f5000c98034550084e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 482951169 1250 482949919 482949931
    0x4030926100209010818150a0b030610030b09030703090909050c030a06060608060402070831080609060901050112120e0405040305120601020d051606060e0c070c060302090105070209 80
    0x2800003000c0400c140c0d1900451014815000d50089640202c65803c03849a64010300e070030340840402079001c00305036520000591018242000100424414041503012140001010f8140d44070f80c40c1c1811801c5207003240744411500d40c4c00190008140d42c1c4e0110554040784c0c1d0685e07901d4110f901d072840e89409094509420750b018020005030f800386a90410405009501c0f030b240c0400c42d40e2914101400203d40244501d004500401c81080052407040444440c1c0145103840366580a803001c012820b150004514110050b0344040480c2c03a034000100301d0b103c2d03c4580c0840b42c8607640c080c002c501382c5800b0320540e103148100f2802d03031001031a1400c880f00c5807122031911010715882000003038140c0f002034030141d0101e400043d1914a480050750240e5201d04280001c00f50041c040c44010190300c541c409a182480c00c50141d07004100030740e007061009110842174814036040801c0049001d50043c01c00f11500480f0610014415000e4025100e0941c0140c59070f9081c550260203204030320100400e0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 482952419 1250 482951169 482951219
    0x512032d03041a100315020a3509190f1502030a050403020114270307060207081b011a010c0302010e010614010207082107020a1203180608040309 64
    0x203400c8008003048003a5204034068440c0041c55000a400c1d5060410040c20490f244444200d051011075003803050f044c00442010380060303a41040400071500407080e200045801c5400c04024003800d505a103d10580440000c0168100c1d25809419659038590800e06070f480e24401c140d44010030403441c0b404c859a80260039034500c022005126004071303031040b10a00c895a0b500d000b403009156091041e07059615807144c0c0c251581c06e0004c4002c0f1250360301408610000c0d03101c54400c4d140c01d4144140c03407403554007410664a8070304070310741080700b0f400200101c0341c0d10302800b049200d620014013490751025400d80e45000039407081c00044904010348807041d0155921017410404484091040304001c051b10400340100000c42800242000002d40c46000d041e40308940f0f84603064003a4071000c1a08810b180c40c29500e03802c0d480130400038034066100110b06a948209481495003140000031075108808180d08850b8130317501d040da000740080d20050001040c484051210360542181d8546620308420307 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 482953669 1250 482952419 482952487
    0x10909021c06090309350102070501020c010b0f03060f0c2107020718060501080105061b030f040e01060342032a03020310021309020f07020307051203 66
    0x429510020884021034140380c1d0780060f01c0901d54841100806010742505118080d0b00400303088000e50248041c0050030b40030240d106841070800d604030369245074030100035501d4106400450f8000c20407404980c1c00742d071803084420340340e217030200303038180300302c0c0304001100649d151070340168031a400c59040d0341000c003500c101c0d4030401c810ba40601d601ca0103082e0300a0044604201141d42ca0f02051210f030a643da0030320005004980e04054000d043d80c4094541c1c0d0344038040c450880d40711104109241c0c9440c00005058050b442106008100751102c60070105100c0c0d076603110807022121100c541c00040c002400c550281a05c0410000c03c0c03c0c1c0c036101040d1280d51010b801c49050900036401120150388090f01b5580e4029101d03ea0501d0042c000107590545107580c0100392030348040c03103100c1040b41e0b0028220042034074088144000d0240a07008540703d800c400b4107140c81e580003000580c0700780b007182c0c000035551401c821607401000310207000c3e6041c03010360018a21000090703240b00781c1e01c01c107140c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 482954919 1250 482953669 482953699
    0x304060e0f0a14120c03070b030a09170304050f070b090603180d02030702010815030d05070335130c18021c051b0304080703110f011a010e0105090901090902 69
    0x3821400140c241000d0800855006000f007240c002c11000709103c0d542c1202804515a64010a400f003ca604d4820b108c0e40d40da44803080c41c03004251503200100482080c0e03090380c01c40201007026620032480388003200e0134171040c18801a0781d0b00c190300c25603403035007410803654a06003800005180c2150711003040703000c01031040e0880e508020b580004100160f0011403904103641e40100e003181c11200301d0040710b20084501012a446403c6140118244240052010708241c81074041d840b00b03c4080c9c070a440c3c15211800f41e5040c0500340c0103480003203102280800d13140100c071320050110079801005a9130f02c5240c805440c9808101d0040c600030b641d424000c2c1c501c0082412100c1898615036080080d091410008542ea04c1d683c61184140c3c540f030074030411001800500c01c50310042d406007800307907182c0d0082c0c0e092480c0440d079200c107180715400d00c4040601c052844809011000d000d0326071006011100e001183c1c180140f0301550f0340101c682c0010050f500c01c55100b01c0c98180040d003000112300c140 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 482956169 1250 482954919 482954929
    0x309130209041e1808040528270b030c010e040609050406051f1404020721110d02120d0903020a0209090f06060d050309090916090e010b0f030304060e0f 67
    0x10b01009140d01c0e8079410400407000d82c4c1c450001540103804046065121035162500300340194010107004180d0018002c0440040d83d03880300300c0c240701c0602908408d0b210203107240d040044881903000c0c200411800c1d42d0446003801640034001001c0e0083c1552002c01004690741d1720101000c581103556420045011000c5020b401d00c5a0f01030704010920313007045c0602c00e80d02c0510352203d041a1150f20000d10a02031156108802c040003100c01517102d0300c003420304100707a69003803011000c090030520041071a290030030900761012a0340c000f514030740703540d882c410390311480100380c010880d0908001c0c500c08500598403506989001788129450585582e0208426140949813580554007504284905c0c0304104045940300781c082e1a652601800d030350b0751039901d01403400c03c1889049a4800aa02d03098200480384589101c0044502d16968030103c0000810b002d1000525950a1850b0010242411280b00c1c0503200d02400551400e468070408481200c150310840398840d82c07420917410a0355032 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 482957419 1250 482956169 482956181
    0xe131e0c09060f05180f0703051905070309020102010501050a05010c0206031801020c1f06060507020409021f05120f0f160507050a0309060201180c12170315120f030913020904 77
    0x11509851503c509010411030304091001001500341d140c1c400f08000d020b200110a0340110b058203000c515a01c4524591890035861070f405200f00b13141804000006a045e003205942c28001e80081180d0790300e860a10680c04418050310340880c082c210f8001c0182010070041d940002c200a0041c0403400400806007647c1c04150000150360101e8101411145050341c5981014811402000070314a085d030301034450b00503854080d21a0390344014800540d1181c1c100c502000c0e540d00c9640d803c0b580103450242582c0c0120040c4000d170414030000800b100c1d07046948a02a40c0c4d000300c10315a560311000007800740928208058204001485540000340c01003184148052080c0c0ba88414a400c00c2c40003030860760103441c10070f5a200319400c070b00d000c0340d040b441000a0705d08c0c14604106d07400c40750900e42101c550045003a1150f150000800c144070204550031446400111230b1104e80d00ba0305d017550f5684448400c02d402c2c00f90002c100b44c1d201ca140c500311340c0205402c413002c0581482c140000140c200c40d8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 482958669 1250 482957419 482957429
    0xc090106050903070b04230316170c0d020609040c0c08190f0203180609032a09073b0d030f02101a0d06091502040e131e0c0906 56
    0x190100b0100d26501e000d00006015060044100d82441c0c50000800d5480024002c00c5070003140c1e1628a180c00d48050100c82410030512045803c06130b5203440c00710781401e905d50100f0041c054040d009103146000300030300c02e4160300244014184440c6004000013809030701c80a07014445410001d4000607801409065942005100f48004852102b0043d245000c04800041150810031200810700350341541c00320414002e4881a480d4100d01c00820710f001041c2084080182d0210101890181c610355042100281511003000702d442d8804180c40141a6100404645c0c049204080c4000d0848203000d102030360007040c07101401000b20200768130b40040107042e00000da0801c501c4500640400611046446510041040b072028a03040101404c10240051194185100d48418084550070240d502d40c0c00543c2c040d8038000b04c101000003035120b442005071407a0343d580081c02c41d500c03101e0b00d080940d42207a103201c2501070042500603002d280a0040303904040455000c100f03809244030b814098a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 482959919 1250 482958669 482958677
    0x209063d08070806030613080f0408030c1c0909020a0504170a0b3d051203041a030606070f06090c09061e141003090501021309050a0b210c090106 64
    0x5215620042103200700400600910482c0810300031103440009009901c40808542401d4a006500d07024a0612500032000c00d0350700c0128003c10141000b0004114a10650084507003200e1840f07010309119400030b600402052000c002045130642ca034000b002440d00e40e00e01180340a807a802d81500a402d0034104801583c8214480700400054906680d00030707400c6444a520a402e010482260300c00c074a20b0001002c0d0a24000141c040900721124043d000007401209840030304c001d1256240c01511480c211040c030300d400d205401c1001c804590140c200500014074100c03403a100c499082840b4801181c0180c0d0382e55485d00030900c1d01c51a0006444145070100755903152551910088241840c03070328039200c02e80010040701040303450502038260b094804000f10104c69006400030070300004050001d5000007032140d9510081e039291803d0313511400003000a500d40d01c9030301d8110b581e0a034049801100300c0454002980300201c040080c000084111803003035140b01c000c1107010704282c7c4108041 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 482961169 1250 482959919 482960029
    0xd080601050a110109080913140a020a090f0b03090d050436060e07020c2d06070602030421020f0d030b061b030301032307050d031707210207020906 65
    0x14644820340c44402c200c003820901020003580040300c2c0340e150280ad9440003079400103003402500c2c02a02c40d10010081c07440c1c241d0b42599921480b00007640211f8002c0024000d00c8080c92580380144240c0301690011405c40b20001002c021201e0720f1ba07d9560501c4c1c0c02800b581500300600b405002c4c0002a0207444107144482c03c0101c0044d2420101c80c0f000d83c4079440a0707a1802c40e0900c403003a0a04803480040d12001c20b40304076070110380c1a1260380000b40460707000104200034010b02e002e40310166200c05d14800c4942c00e07150000c030f841c4c4151800943d881d81007078040b1040148213070400342e17020100401e01850512103402494012015481030301e03540d00040010001d000d803d000d9071506070500342c0401380014a900040380c036540c10f80659441407410045400605100b03070410308200c142c44200f0450740c2006500500b00f52000c12150b05000080540302012242c14000d40b809294054078450454440d01c0030000301244141040903407034101c1500340c2c0104800711540e0345000006802c1181d13 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 482962419 1250 482961169 482961187
    0x15100e01030b030114041b050d0507060207050109230114040603050105030c06030c0f0c030906032e270e03030f1b091c020f09090f0f0d080601050a11010908 69
    0x1500c42c108190382c46a450001a503d071044100321081e0700c2030740b100351301445449403a81980741c0a15904a0380d00b0904d150609400c01c400040c0c80400d885036a022100b016964100468a0b0b107060301460480e1888080c1c0a0000c00c9200901401d00c4014104814017a900c0078588509410503400100000e40700e000401036810b003070000752804078042d1a100d10350b10f01000d10144520a031101151080070014100385141c00a1040e9480c030200242042c2e41d9080030b003401d000125034040d0449891404a405e0b08122072001003120444003002c02c0c075840071040c01e6614031011010702d40503001c0d41c0c8500410800d110140015480341c0c90820303220880b81804894180303206280b07418101c080008010b4200e00d6a1204070540c224502e1a9465410010602c0481d4a20b08460742c0280c1003690340c1e041c000700d1400410300080c403001090071074106941000c1e0350b543d13460030321340840042601c04012a030103520400050200200a0030312450003807003400b209085a0000c1c0003910301200201e00a64 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 482963669 1250 482962419 482962421
    0xf050a14010606180803091c0b0f04110405150409020f0603010b0307020d020a1a0406023601092303031b160509040507180b03030408060709171515100e0103 69
    0x80845250504c24041c036041034840340d600c1c0303d0900305c1841a40c18000d5241e1641c4013070014911a03900207242e03501c0b82000400703c0040c410030b0710211220603403600c004c5954249407042c00d1284c0300d40c4d101400301101a009000003404015401c0e60000c1182d80400e14580baa000214000e1034102d03d610340d2460b150000030b04120800c0a038408640006045902090407401c0303000c3c43c400301c0c0b5090300440d210341c94032038020310560400307080b4460400d400078031031030700b50808000800c80301c60b144480c0000080111a26013050185640d803164200b07901311340c00c0c3ca5404403024079501404480c907104070042580081e0380440040e04035035018012211032848611034003c020501030303d2550300c3d800d10365251500c0711510301414190754000c10f50a42454071640110b0045207005d01641c0e5580d03107440c40151140c504030b13950b501191044100048840a040003c00300108a5000c1d042c2500d0b58032100100841c0580300700341c85a0404150f45d520307511084c04c0140c1034110384034201c51600720340000d4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 482964919 1250 482963669 482963687
    0x13080d18080c010b0907140d09050f010f0b180117190b011d010b03070c022403010918050304031725050607080601120b1201090f0c0905070c0f050a14010606 69
    0x5001e00742240c18400b025407c00c1c801144500c0d240081910b851840d15140020302d42403078098440d05c1041da404d441943d0660001e0600801c0000c2400700400d018207208800c00440c001e000e481c9083c00041081c80c2068101c00c52002180060701c411425030b00741240c080280307030820340c0c0c044801c00c0100030705802411040740482e4400201d901540c50615001101d000007450703007041c0001052600c045543d4500c155091400058102e00802c0140b1360049031030b042409000360440c40c15400410700034202100300e509030f40c010b000754503003401c540d41c1c2c0590040c160301c1281200014001105000c0d40989041e8800c010f6800445080c0c15a0030200d2420901504000a020100061100d00d91780310b003c203c60003482506c0442c00c00c00641c00701d0b00c218009c00d48a0b40c070f5460072403201c0030400e428069070409801082d260714025121504002101c10995410006c03480f013804010004401d0340701808520300820036903001c0040c944900c0c8407074940c124204000c0e59030f060b0030710101d40c00801070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 482966169 1250 482964919 482964941
    0xe070c0f020607143007110f03030a02030903071410050a03060e01031202010b1f0e0a1e03140d020c040b03030706060e07030f0612060519090503070c050913080d18080c01 75
    0x5c018000b84181001c1c2c43d4444c445001d0700300c4034a00c01151007602c0d019a0300014140c050102d075503c1c3c0081c2c0e002500d0390003010285102e401044800146d013800a05040d0901100818a9820483c441401d803100d0b84100034030014962980d200040985e411810b00d402980074030341d10300e001c118104009084511500000c2d00c2070078031400340307805080d602050300d25800c1c1a04002d20110130030700c00a136101e001d581c004849034030894210401100f12b4a0044101c80c130820140915000c0150113a4466007a03440040060b44007600304000d502c0c080c4c014800006014064a18000031903c503035040d1001d541011801446000c1400391280c4d243c810380c4030808010000308466400e00074609070080701058041c11007611030700420041881f54484040d150f4901e80101300b141e00307916006480340c10240041d0f90240b0001400038050420f013010790f02c10a554041d10082c3c4081e03035030700126508481400e214265665080040c040c80d84040c1900c81c40c001c100203501e6039508400e40d0b007075071a0010341e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 482967419 1250 482966169 482966233
    0xa060302120106030f0b12011b020a0519150504121d0a050f060c07031b0611030a1101061a09100c0f080306180f07090e070c0f02060714 60
    0x1403102912080c03646410f4a80518000c980c012407030b991800078101451035154800d203000e201c5101c48005501414441201c6203485020070340a182c240e0715584584005085504000406101c02649203046a45c541c4100c412400708003001100c542210301c1120200e901e6001740d0081072415411070354042005889074002c00b040101200484c1c5110450304c6401d000703050b46400c59070265030740d0041c0d4101d2520b0706e04540b0150ba80c3c1c14104100c55101054800200d140381d800301e140c80c0304914034115503e00c480214682880724008480c1070744540701d6030f00305542e10079000c507101007040181c2411003d803a4503144c0f0b9002c250f04200c5055000c901150a10000421080010307030348039090440c00303030000c6400340c903507035102e02260000c041c8220307030300040c061a030411aa4964600700076000e44856913030000d520351a0180100418400e44d521400b140303000c40c0e01c1c0c3c0011000700c000c50258ac0702400860904c8440d03500d803007600540d403000003480d412103442e44030402102c500000060047d044 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 482968669 1250 482967419 482967427
    0x120a06080705180c192303040f0f021f0201020406030b0a060903080c0304180f0e01150b070602090901060906020d030204050a030627050705030c030c090106031512030305060a060302 80
    0x4000c00441c0f080c0034444903807040001c0c0300d00080c4040e0742260740401c00c1d40e2140c40b4421801040401059600e003113281e0020115039560b8030703d078140c0c2e12855007c42000380b0840f503611a0820750041c494100d0340942c01c4840b4044031607407440d0b160302501c9990000343c1c5850601001a080d61074003080b0740d018000d002001c2103d594001b05413003c07039410100055482650000d00d42c03d40c0b040e0b4024018074000100401206416980b00c181c1d40d205003a410400d2150240c070150a03618001e50107022404c5589041c08901015002421402d02c02c2600602c0c211001d00422a190401d030f0000d40800d410180800038950140310034074038012546411441d043c00e0a000508441c51400040c140903624084a4410342d250400040b0405017103003108046030040c9481941c4031510301609009000301400d000c0313076040c000b910203c00a0000d02402040c1e0030840c04400a058540300e51905610300580000c0c0e00c1c0c071485c401e00032039002e0368022a6a18040e4180b00f2800c9556200300304145c4104 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 482969919 1250 482968669 482968679
    0xd020c010e3d150801060609170307020a05090604020405091905073225060c02030a05071103120d0e010515010c0f42050603070e040314120a060807 65
    0x44000d000001c01c0d20b0300096030310303071248400301c2da00c000d42c100040661a103040822030030703008a4141304032000154002d81c0d0701c1082c1c110640768014424002e402101e0004248640e21300300380000d500c01409000103040c1551040010403400080d036208400c0601d9408154200c0c015003c0c0726031009160801100c0c820100741160b80e60304814a80040a280017000841000200302c101c40c500c5002a440111010b1092420007414a07075080480e41245000b061903540d0b0300101c19124524103a840d01741c1070149030785924145511003a469540360141d203030f40c448100581c0010b09a0485003a80c001040000b03441000c0c00c403200505441603010200f11012020703a07101145040195200701c060303185c50200e03c0c1051146404061303198810440e59421728007980755051030601c02e00b0890442d500c60305040340c0304046030401e4502c0398040d00016420710201c00340e010b10302d030405d201349481d88400b6100d07480710965410030b020f1460500341800034000c0901c40ca00682010305154400b03440d80328504 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 482971169 1250 482969919 482970013
    0x30e160e041104020d02040602030d060501031a1309210914060304030f11100c0e060306060f030c040b030c04151e031505060c070e1008030f0d020c010e 67
    0x1c10050201500c420100d1154585405641590240300420742d00c0c1c0e030710360202175202e0300415148940c05141240001341c5600c0390180c1021504c41103900781d9459807890500000400882c144d003400c2e500d8003407180c001210b0010021414240040c0e1101a1441510003013104030300b41d0003400707040ca4603100000617684031001c803a0803da16091610103c808070400783c0d03402040031100c031103c0c0550660940f041d045608140c01d1942960303034042c03034803500004004484c00191241a08603c06000100e070aca800c030740003143c000344019901402c1955075000040b040c1d0080f0755141400c04081410040da4010150700c06502c03e01d4245036000d00004a66101030f40300c2e014112040640700d51a8040180038141824040c141c0035081941d24501440019130311803440c8a48440001c600d03001803401c40d00501e48000352100c08000d103241030011107000209030010110240c1c0d03e42e00b00040700c02c43c0c5091081c4c5075111902c40140004a149041c4061407054540c80203565a1070a01f44080d03107601 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 482972419 1250 482971169 482971171
    0xc04060806120f0618030408102d020d0f0b1f030603051009050f0319030c0504120c0303080a02090901050d0c27050a0204030b0601030c050c010c030e160e 68
    0x1151500045503500c120000d1181e64640b00c0c1140795004401c945070f00d191000c600640303c0c4030072603020010708401003a50380d602d2140b8414400b085c0c001c81e180c219460300e2504205081480c0540c03c00b4007249481092101d0056a402c1d18103884c4d000421203640074040c011078454240130038080212200240105030300c561440000501c00e07410180c510700030341c000c0d80308034043e603001002c81d914081c120402000030204136030306480d10303c10180d081500c008008100c0713040142c103080441101c0980b03042980500307048003001007480b100740004141110001d03841c00036a401103a1484140d0700d1070901500c0700202914424030540108282d21040c3c0301c00e402641120f2064404140b040814181104a81400d030411b00c82c1a0440a800312500007203840c03802c44145182c410005a01e0382d80300c4100328841e138031004103100c8558000070407940c081d6102d4000c0c00aa810081d1501d160702420600311503800c0c51140100782e49040c08181e07480208080845503d0420b8142c00c12400c2c10406a80300ea0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 482973669 1250 482972419 482972429
    0x160e252a081b030c390a0306090305041a0a1404060c230d05070506060d0b04060b1f02070e0114030304230a031217100501030e1204060503011d0c04 65
    0x1c024403510001c100111540f09101070240e5103e140d9890b5100e2003030b011303e0b46038000d00c402401c0c1588008401c01790000765180c020120348056203990b54160103800121000e4051160a020015101001c0c080721001d11031001201d50b981c812030700002d4900300f0100c00050302c06809100c203012994002803040c450381c1e04070455009071440b10003202081083c1654500d824021150f03400ba0054120028200c02c600c24011b0b0751455403650207000f00350b150410040d1048580c400070401145103507104951180c009040c041c40c04140a028010410020409100590200c00100138089140c6000c9001d0401201d80e056005200f1002139034901850082403420030003541d6000c403207070018801c80200000030b4400f8061540da410246000000d545140e4045038001c1d50405100c100401a01d110784074120104102906180046006145d9030003194981d09c5032640c415880c14041014100900d002c1d074815507250704110200e00c402c01000015081c984100c0d0520840159040c01d4070b023522 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 482974919 1250 482973669 482973697
    0xe01030c02150601140d0c0305100e0c031602012d0c0c080a0e060714011b0309052505041e061e03020603040305040302100206041202160e252a08 64
    0x8280e005c50a03a07130f12603031404000c4d0300c1c07600d00c03c480d01c40d805800c941d00c141078291030305403840e07038071100d90092800840b10090846020000186620745042458400322624400040c1e05a010f8400242c081c42429000d1180d0b1045034204c40742690358081c0680c544060700e0b1250080c1e500e5584c0200d00d0290180400030711690804451076a00c4070f8040e50701040c3c0207008803a040241a41041c002c010502000c000f603102081e000c480305000303000d41d4402c1c80d0310100030325a0f404d41c500410302c50714071009402e540c8480b03444001811b60b514000c1d009040e0000d820030303200b5105050410101da816a000649000c04a91044c0e007034000f03142800112501541d4066903640e4510301100d140c420b5400003503000703a00c04041c2800f65800200d03548101d11030707100c07038000004455059030740326100c98416800c11107020b01402a4094502d855400910358417103500d20f96040d100e038040790300b5144c5604000600e40c240780710070f800440900701003195040d915030076066030030344a42c034051007203924040002c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 482976169 1250 482974919 482974937
    0x1812150a15231c02010305060f130902040e0d020709060f0e01030b0c07021c17130b071103011410050901180203090f0616140c07030b0c09100e01030c02150601 70
    0xb01d00c40200720409100002c01d40d5854244001e241040c48000720802d030700081c0790a000400ca0704000e401220300200003484024550050200e42d40130344810341c0c00300d80064840200c00320200e820084c0c1810500b85401404901d0700303000c81d02044810036032140c110140c1c070741d40410468456414050641e80c01544207210381d50f459100c000c2a11820070001c5d00040b8020011041000746d040c4c80354103034400c000700301c86110074408028003402002069850800d00410811044624000811845d48140101e001c55810240000e00b100d0062001d000740103090000c0005e499070054515015010031146402c40b5410a05009040d10181c0305080006070300202003100d01c2420030940a407201c1d072004030b81c0580f8200320346207451403400464a02050240c030001c203400d0849401d0f924060160300050002600d0341d169046207075805414201384135000c01c8110b443d5241c001a10182509a4480e2250884880001000c9903040340c901003c41d00300d011451072070400c4005158000c0c409107043c2541c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 482977419 1250 482976169 482976209
    0x4080c06031e100b040e07030b090c0f0c011e0504020a23011407060e210f0904111603082d070f022505040608030a0c081812150a15 58
    0x40040d900041340984010400083d4180c103501150302c25611039a09000f0180d0800074000c1000c01a0342c8115401380c02d21050700c01080380c0001d0600130f01d1640000c20b04040b04a8108560507098907038090644d1210100400d40c100020b032040145045619035410341c09012045003590740c039010390f40c10803205c21401c0381442c0c0400c1c241c0e25640d40080d810059400c1c10f0364003941d1010303148031450340c41c43e60150b04031010003068269030b100b1070711440480c03801302d81d60204070042c01c1d4001c4136544480709002840d0014031001c200070045100751660390031401c15034450f00c1c02c2d000745c4101c82e03074881030204030303001140514002540180403410810418a02000306a0409402c15407841101e0034000b00c00c680000c5004074141203a00c1a10100042601c50402ca5124071480004001103021040d81c80000345110340100075142011940b506050030400005aa1b012030450140b002c0d80724002ca0341056001020043d00484402c0381009000c961082411600300c00d885802058040e0078060302c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 482978669 1250 482977419 482977441
    0x30307120f0b090a090303060f0e0f18030a020c0a05120a0f0204020d1404020f04090c06050d0603080c10060b030702250302041b020d02010c08010504091403040b04080c06031e 77
    0xd140070040c21203103d0b190000000000341003440050300005c0c18641c0010300003034510f9015054504094150300c469843e01542e0001800291260000b1114100031030f08040342480030b010080a2603000e406910a100b08000c041c2100c0c1c2c200d0780c0304103980c0d00d140c4000362000621580071640034001d00e00c40c05c1c007030000600034064080403941541c244100b07501e0f14041004130501c100e00c220380d80002e40e510041404120340e160000108001c104403424004d1901450103800854a00c1e0300205607079881e50381c3da42c0e0f01e401c10720386840580e20101c0141d81c00e81142c040e0034040d0049207062400c510f0441e1009503104100b41c040c0307440d09091107000d03030200f501c020310001942e0040c20500c106801c0c40f6203500d0700b11200085600600078088041d40b10362040c051105052080d50b01c001490f401c01d0700700001880042402c489811120740311600c449414000ba00050034071011a94460740f45c13000d0f450602c0e0f01e4040c014801e660410401c40b411002a05083d4101c4062150780e40654410744409 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 482979919 1250 482978669 482978681
    0xe1003120903150603050f06040201020a030c05191101030e0c1e040e070e0402011b0b0103030806010507050105150a081906020c0f030d150501080907050103110d0527030307120f 78
    0x10300748043c0d420160040380c0f06074128008482c1319008903861f0428000101d5101d081c2034900a005802c000e5801000c02d00c59000c42503110701400c241c62840c2e00032140d00301c4001e450142150f0700c94030105800c1741c0e580c142c4142124011440d0140c003201901c800091891007403400d64003100407801d20100959100c80c1d00c5619820f41c1c00e41110302e1951256002e600c10b18081703c003280043c8440c558800b50505504103d0f2055a03c544401041c1e400d584d01943c140800408081c100720302030041e6800b05209000e11070241c00280030f0348581c011300b0f10510004001903000307940785501000d200e00c42040c2c00720080076000d410960045c0c40d010700e544c01ca41800c9035807140f49028440410810600c607013603408494441ca0700b85c024410b00e80d0b00d000550b60740c581182e0321a40d40c0c0103000304002550103900300340b4480c0403801e80e0b1460445050403000884200b075030442944546c184000008044001402d00b5808045009509501e800c003401001010f10384a44910303161070755400300318a04150020 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 482981169 1250 482979919 482979923
    0x9090103061d0f0304050a06050705030301060c06090b1003020f101209030201020c070803042102010206070f030e0d08180f0d0309031202210a051b07020a0f150201060e1003120903 79
    0x500e581c030101c1e60760b80d544d80d080350080b607208404052000800b107014004559020f079218003c4d41c2189e01e031080903599014221000d9528548030007004001035104000f0a2043c0078001c1d00c119858118018004098200c50f01280039100e1118000341ca160030012902d00d52103070b08400300d10a021880c00701d019029003400f85e032080c03081c1e0b8008901647c0110245c01600d1500145000301c4044240040050f00c140e440a03015070815008a05c42034420078503500c4201d500d00b00482c160101103102d5140681e110261030001c2c4c610400c0c4003d074a0486001c14115840c24000c2244071003d2402e0368031440b90795109818140e4800e0420201400b484605242d8039446c3c000712740714075100203081e80300490f12100c00c50b0510281c000804401203441918010402c10741c00594079400004240c40550101d18180e92098111500080c40b882c5ca000040c05041c4440c60405c481c8d088603000790a440040e08440b0a03e0140010000f0f801c1055401408a0780c100310004c00c1041400700030b580702c0c0030715000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 482982419 1250 482981169 482981173
    0xc03070f110910090e01140601050d110408010c11010603051e01110a0914030604050d050c0304050306130210080c090105030a1b030e1207080403080901021207060b010905010509090103061d 83
    0x800c0301c1040f00c42020000c035412007205000d030490485200d0700302d610810318011305c80b101c400490034651042c000380001c00040180021201d800c100028490381065002500c0c0fa9110112115a5a4040c094030102c81c8988000d105c1e03281960b03140e6031030b40b2015030340007400f940010085a80c60001d40011035103020b00c2c400320755103041514005040e0000d9000310b0919007007180c0540340500b4005100c03032203030343c124000d8850480c3d1010221995400380940e1003003440148000f0919640c10300c0113600405d020105092281c61034414003280d801c41041d8030051080d407104000d084800041110064082480e010340d6940c1d8018135400240380031511024081c01241c182d60036280c03d60b12002e40000d000c02122a0300701020201c0f42e2920684400130402c2c4d0701804104000303801a405001c0c907036414015a21b450020ba0b58445440d00403210503100d075a10307120440b4a5580024038070000e48400c0c0b0f441c82c942048400480d1400c1c0b0103120003031049607940c080b03a100d8852a24131416083c08041 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 482983669 1250 482982419 482982421
    0x6030f030503041b031a011d0c030604090209091b0d0f030f0302041d060a08120904090501020c0624011d010806010e0a060c0b01090204050d1b0512030706110c03070f1109 75
    0x610003560f4900b204d06c440800a000004650b03241d40c070181c210840151501c1400c1c2d640c90310a080b81e80c1c0c00140c407840d00152100049001a91040c115a100c1c1c842c0c9402001c010070b5041400c20440b034952000c500034160200e40102003280070f01003407112500b40c01c15070249040750170224001e20613079200391a80450380000c100100c0301e40e204ca6008030b5003112030075511a158900c83c0c1e10b4411003900004c3c6100100801e920300e003031540152400705c0c0924001810000c10341c0785103081c10703c1294080102d40b070f5111401e402812040070b079903840800f0311342030303c1005211441c19109000040401e0600c560b000024035183e00c5048140e00454009d04420710030b0350365840141107440d52a00c03c40d428900070002050291091003074a044886c000c042030700c000030700e80760680124080410020305044115000c5a40d8136800b0727060040000400c01582e03200d4241c01c0c18001c0f903c4151414441e01403c1040c64400d00d000403e03076030400d4124040e8109404d00e844d0010011006e0070f03440b508404100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 482984919 1250 482983669 482983673
    0x6050c0901020610140f04061d160201060608070c141902010e090906040807170f1c06230102031209030712020607020601031106070614160306030f030503041b03 71
    0x5006481008020b800700c2d640c81c1c81d9202c2d542135146540c0211524000c030032054810618000d11100c0f540e00000d00002009511144001c10b800498401c4810711140d81042c0000a41c5000c50714600c034405200030802103040c188000c050b4032000d060842081110403650342400000241d02c684200c0701412500311410500c00c0000452902200740e010521400c00742c4242c3c1091320f5414840c90b6480054070903540d455440d94141d4010403419030325074910b1211140f960701a440107020726022042d40b59164070385a41100d07111840582010800e50403c201000b40c52405042c0013000c1001c040040000440900104e01d11301170140e1426001024406001d660350011006080c50f500074101440a13208086003030b03a585000307803009030059110300010400b003440791110840580740100154600820358850b241624041518468807190305001c4c05101d140303114614084100e641024415203107507445047c2d620141d002e015050043c000001030820040c0c0c10105160350700340018040036a00d034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 482986169 1250 482984919 482984941
    0x21603030e1302070c060f1709031902010b222c060702120d05060a24090f050d020603060604260106090203090303060d02030f030c06090105070e0904110d0605 70
    0x2485214003034402c00c01c07150019400e034002c40f14001e411054401c00e49150540840310380e80e030740040301c00300b1840b042080b4071076030145550303401151024000c3d038071180481050004440041207030b5003560302d4404101c00a854180c00e4080c90069240010690300700d039414500030748101107064020718090f540e02c0707100c0341032184151200200e01080b500656180c1800342e80d00e401300c207082d8140395001d120b000c44007035480e000b642d8040005008240d0256843c1c05a0035000c503000c0c1120b94a0000d07000a08010368013211a6005211291081c0b585500d088081148108040c6003e401004000001851038640304215001480c0314400000000050014045103d0b60410400010750a0510010700b007440ba0007502d019840b450040d61039610b46200b00592811940000c0303825014201849188030790038000344c0341944035000540366902d00302100e030b0708459009042d881400054904180f1684402510a500c15801a40d43d4000c0751400d0014500341500d100003000c079400c1804004403101c2c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 482987419 1250 482986169 482986187
    0x403150e1c032705010c0c0b0c130f060f0e030c10080c12090d08090636010507090905130c0b030c041a0c0c09011404020906070b012d0614070302160303 67
    0x204c00801c41d160f41c40a0448040101c074001400003641407000c56104410f0000904c1e540c901d4a41c652403c40d990b05c030000001120350705c00000702c3d408410440700c0b103030040113900500c80120041c00c82102030380c00041c080c0d64101c96510400a42000140040c10004215012102c1c40004a4040c0c500102425a03803e801010200012032400101d0040d800000d5020f02030107940a0305912035107440e504064000c6820310440908a0100107100701c3d88007817141c81d001c0c2030f071aa1188692414074980d0707070545001814002061200b103503400701041311087d00f10240c4041907807440d82c80d06e814401c00c403140548d40213155543d0280903080201030005004041d441241c0701600c900740e068008010300b8140034030036551101c80c0402942c100d8502036000b00320104000f00001c0c203150058070703064204d00e02600802600d203040c07415890141000d6816030b400e00c0714900140401810001d0040c20421801114803030108007260384000c0600030311081414160881c1901a69a941e0400418000c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 482988669 1250 482987419 482987423
    0x10b041d1b030604020d1e110f010804020916140c1b09070f121512050c0603190507120e0115060f0503010b0a0c0203070b0403150e1c0327 61
    0x2282240d000101d245041001000120007030240070a90f55540070703c68000f81801c01114058128208583c1c8072001843d0246802d02039401c10b400e04405c031050289103040b01030028140110700c820040141e89031290f041d48100107524050801401d074070240c42c142d00d4003614400643c408100401c51240004070002d0f0031030980c800d0042c26a400d018040c814009641010006030003500000c089030045103800200f2042c0c001c00204600c1c22003402180807040d0300320741d41d03410038a43c43d1028040200310755014050700321a050b1460409070080000c0d180a03e924448058032440001e5901e40104943c6541d1218100c0c240220018080480d00818400c242c40c088114502004101e10f071003101384012034642c6450310707855070f421b1824140154028031098400c000040000c140162003d02980004002c61450241c0b61801c516001e00004001944080d51030320b0002c3e44a1034030000500c2c07103405031a04441c007441100d03404088024001412041080c0715481105a40d01d00c030400e06451654 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 482989919 1250 482988669 482988673
    0xc09040501050d0f020405071e0c0203060a02120115120e0102070b0702070f030611130e0406060b0f07060c020f030c07030b010509400b061f05031503010b041d 70
    0x40e80b41c20400006141c0f14002500710840100c0d440e0042c03c195001c40c0c0c22070610706092442c40310201c801e580402c004070044001501c014005800c5040400c1320350f421143c907041c01c1d4204400c204084005600500c151040c07010640303401140f40340112090300e4002c4007030074284944803512103614040d520400f0215070000480000400c0c1503c085240801d86d000300d100820820f140d500c030750340a403a80d4080c02189038820800600d42c04081c2d9034480003001f008500910341d1815091040031a10b0a030303c411441c1004109090240a1140c101e51280c1d901260006280c0d01d0403c04921b4010112090f03601c07803100041f16510410300040103001c9038401e615440d4140c2c1c070b580c02d2196030002540c1100c9d000d05054201a0070400310902c1205000700c0452402c0c000c2030300b82e48840c212480801c199206200c80081c03004904100c0100d001543c09032550320320800c44144002e200740300040924403026007107082894203640a40210f08035510080090042c00742c00c940c1007a01008951824050b4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 482991169 1250 482989919 482989921
    0xd08070b0f0f0a0c02100e0c0306130b090c0604051516051e12040306051e16110118020f04060302180105010f090602150a140a06090c17060d0f02090c090405 69
    0x14410301828143c9801607001d0a0315504c280c0368140905090066440180100356230364809807420040d491055621445007264500a42002800003802a00e40515500007260102240e01c0e103500f150201c4209030b40040070a0600070804035580200c003a440e9408000039540001d005d4001085507414019010303400d80c5405001400744e0350b45c920484040c40110a02c02040841c0391684000c1c0c0c4086000c0d030386c001c400380d0a604a00c074540101d401d80d0768000703034071a184901d6501c52088a11250040020082d1180d0f00015000c05800044003d1041640c15020b044a4644d40c011500859000c9c09a20320344031030242d142414142405401d001030032800100709484e106034080d008031582a0050940c01e041210b0600a40c02c0c000d04484030903840354042c0c000400a0294184541d007540c82c00074a4a06002c003079029910b200803584100304240d42841e81c42108030304015080740d8115004075100d1810701c0e11004d12801030201070340c000c42400810001c0040c540040c682450308980800803 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 482992419 1250 482991169 482991181
    0x24050d1e060618150c0f05010507090b04380c01050910151206090c030b041412090415090e0322060e1909110a09080c06090d08070b0f0f 60
    0x40306602c0300f00848804003e400b044000021100b4642c2e6446900d40f01c0f600440f42e40303c0507140303060200202c8017030f0b56450410021950010a9002604403484558a030a00d044040f50003601140922403c591008144904551603d101d0701d124035013590070641c42e041044440d50080c2411280459213000d00041010581160322803a20105010722048000f5401e22141521062180c01d04076400c0d40e81e203080c100070950316501b00d00154454440e0400d5881c003841e0484401540301d090003010392247c42100c1c03210307503030b481034441190054500041030498040340c681e10061590110217482e240c858408054440407005105e982c00121410b4807010948030121422001d83c8a540c2c0040c0801148030703080c0c5490843e1142032281031181b02c14160701c0d0f50306c090403188080c007007010320307000000d1101102ea08a0243c0c401410990003525491510300081007292040004243c850b20030340c810001000300700d0b41074030410f0781c109001d03810500d0180500004c0480039078000c00b00f41900c2c400202 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 482993669 1250 482992419 482992427
    0x4030c060b010207321903140c0a090e15040816050304150302031f080606100e0315071409180903281d1813081215010924050d1e0606 59
    0x32010340300d00c21b43c813050b01e99110f41d4000c0d010b1451480b02401034a050451603034541e02d07140080c00140e0000109070b2050913907245003d944100ca221480081010000455034030025600140d0100e116189924041d02c0e2050940c0b190341c000e20000780700c8400300c404241d410b50140d80708625440004a000d40ba607000703460005154443c00e052544030000050280c20428082c00d50342d0b02504090900c2582c00001900f0600080c602c0c01001c29880d0800100c591f0000194400049140985103011084800701c0c0350000108509a44006051701003064031104004943c0000d00140004441e1110343d0500f100c1c000c48001c070600043e2a40da9020752030316590350b140c6081040189200342802e60107600102d1060010700c19840e104002818001042000000b80401c14008150141e1498108035241c2003501e01d500d90742c1044000c04051000d080c1540d801544182c2131411010002d40d86071007142c080c481d000301c1209050810400008410030030300070101517101c80005103c2c0d584c80d050211 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 482994919 1250 482993669 482993689
    0xd120908060420010302090301020c10181a04032106030b06010908100903020c060d0f0e06010e0708040c170a1a07050703050f07020306040b0a0c030504030c060b01020732 75
    0x2810318009100f0307000052403100b8820290b1501814054141505900060b0881e0010381000d5910340000c0c1c0c1120540f079140c4501c00e030701e00760081140f94400d5a034903500c118448982401200721074039800b0038181401a402c038402c0c911032481d8403801b120a462400b02408040c4401c41e481110700e400f082c82036015540410940d080017008002c0880a50782c514080c2035403180503410350152280490450700c601c8001d10f0a480d90200119010b400c03075000d84125403c0724512130040d0003d1005108803e0401001a0480880e01c0c2c140754a03101d506020812246560001e00d0301100e480ca80d809402010a01010984c000d410b10344070726410051034001ca840490344640012010441e500000e8007030805000d811280568280c149916980030174549001a0340c291001c6801c40c2c01c02455444900400ca01d445c4640f078140301300e0070943d0700600083c004d01d0006080310307121012003800b648204070203801420062145002200e9404440e1211620401d02d1540001307644900c050350f00780102e1035 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 482996169 1250 482994919 482994923
    0x804030c1d04020108130219090b1309050c0907110604110405160e190b040902131205031206040f060905070f141b03270a06020613060b06090d1209080604 68
    0x592203507a40d1044003e01505811001c9a100040120481e02300b010084070001070140c603000003070880f0100c0c1c10061165601c012a109070b9050418000c000383d0b0108200b00750072410b459013011906d442c81306032046032451414034110300c141402c0009000c0440492420b003030044c0c604120365103030703541107059410604600f1004202148034050803801c4c441a015295000c044040300707600c0e02e502e10f1540d185c1c001c1d84440030780d5401150144800244d0710308540182a01c030b4504600030880d070348041c0c6070b001d01504c0b1005000b0100010f01c40d529280c010234003c041a41c0104162902c2d084c0d00720042c00c0981e800400284000004021180690300e04590200110301507810004000200c1c48486122083d46255010a00c542003029040034a40000d50400340c41091945100c03000b8070030060819841281190301403024440c203020803981d9016141e82010000c00c041180c40d01250345d5104405030160880111a007c4c0c0034402c00c1038103c940541d040c2c0d00c01d180d2070b036950049603680405440c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 482997419 1250 482996169 482996177
    0x70305130f020f010210020313020307060f09060c06141003061808090f0a1a0d0f06240203130b040e0603030c1e070e0106030903080105040c14090307030804030c1d040201 75
    0x7203000945403600c03108100782014411901e41d01c405024010698100b03850010b1070b0310174641c698045150034070994001e0310307803031030810301030034ac0704500070904030303140c46502c045c4102100580140041904080500300600500300d01c142428914514030700c0852105407206440e1054008a412444400c05034031030b0230190041c10015081c04100380700301000071041d800510407400007030106007081540c0e2101e07062030035940c0395580e5140050603500443c040c102d41c1e51406d00300b44002c000109a80003903600040300705844041a0b80c0030f83c41c40c8115803007011138101e82040000e201c461071000b04252440f04441010769203030340003410b5607805000f880f0099500500c40301c0c07000200014030a92881410302c21144969034603002c14030008000e8000c00300280c2c440a0700f2080c10782100e0f0107030051005403810010b01c1c1c0e0001008002107018555850702d10000101d03103995540400810000d90342080000f51b58994030b29054003848600c0c0710b03842d00c074480386107842d00c000e00c1004501c0c419501a12 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 482998669 1250 482997419 482997443
    0x30c04061b08030906070f1b29010e040b071e121d1b040501050d201005030603010e340906090902030f0c06250b0a06081b0d060216120807030513 64
    0x2542e152440a94001414603480c009000100c0c80305c027030b1505000b41040a10b940d001d06003800c4c400c0c00702c1002411700003840403501802c40003501d4415840d50840f607070300d4a60003c0304030707804400c00750840d480103000500003805000c2021030041400301c83c951148101d20f104000840c28001524000d20a0903480030701c1c00c003a0008070f114401e02134401c804060498011614003800901e01c1c044d582c461100080020040220604092080e10315400c0e9610007040074040750b880e10079000380b031001e65840c4e1007454440a00400c2440503c40080e0404032018000c4544401500c8010046c04d0f41c1030707111b403140d08103c100d000b2000c00d011000c00c0c0060302d00c619202d030490300201103e0305602c82052847c0103003e8500882c0f19162458090050301d403011600520b09054240b411801041c1c44488101d440c035400896560007100d40303182c962256000d46c590b00c0c07456009056011582001e03040603880054610800c0d408540c407403042d150754904014540300c64042403030501c245c420013400390030214 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 482999919 1250 482998669 482998673
    0x5011412030901030c0903050d03151d01090c23090307060906020304050402091c031710051c03030e0f03030415020c03120406150801060906050303030c04061b08030906070f1b 77
    0x80c02c91082d000b40c6040c40c6c503000785e4036075510303103010050358513070300000c0d13940790302c051000c0f810345000d4000d1035104207401c0c500408803061000340006100b4035030340d5a51103800d6880301d8050122128110420188011481c8010410b4102c2e0340c444040284170340146500456403c0c003d0003034600f0b41d1002c2d0b00850400b8100000e004c0254031444200e580038810000d108506601082d569660902c06d43c1c6115103140c0c6c0c1c480030201920040c08012811411482c10702c6551606124116001c42e0540c0c02005442d40f400e0a074004d0004800840d00c0740541415600170440c000b00840c011031141c0d03180001080741079044422405001d4007407400350010841042038003201c0c0346980d0058041c50300020f903c402d2120342412000c043d0700200460351140d46c1081200c07542c0c8203c10081c881903000c0c501e180b40c4210800901c0c826806920280048140038901e810340c8031440808450740b00001d0317603607400c025480c6d964410044030a500020030342506054003911454030700788140079107440c0c07240b507080342d03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 483001169 1250 482999919 482999921
    0x10c0f020613020103060b16051204050f0105030a0204120b18070303080402060d0b060408100b040501052107050312090f1f1b051b1504030f02060c100e010501141203090103 76
    0x140c00140d0415440350401f09000203c84000d04035007070007024403840111240340a0b07051030504891044030042c18882000030391105112040d4220003445c02541d29030b5195a0640203000b507800228000450701842c0040012004251f8080c4005441410081150500c001e547d00c50078040100001c0c14480801c00500f803841c040c0c184042c903000d01141c100c0007007001c27401d00d40040d8451030059000ca418000700503854407032172442c80d506507000d1042d981014045100005c03809040d10440000700d104d0140c0c900f051210310003078070004058610010013031462050702c3c0c2000d000207100b681208046065442c100032048801d940550410800c00c600035000c0c0c071062010100000f00da00015401e50000e00c0922440b010040150801032440c09001d0901030324807000c040d8125000800c22051011482088078640050307411a406071355207035040704d60703810100e440d8683e5050f2820403801101015064025a0503106191402203c1032203c800700a54500007241c03003c0d00b9081008112340c55482 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 483002419 1250 483001169 483001201
    0xa03020307030f0c0906090603050c190c0609060b041407021c0c020303030c030103121803021e0904050d081e010504050c0906070302010f1a100305061c0302010905010c0f0206 77
    0x9141000144469003160580a1322190342100c80050441c072414004103403c0110100500041e05d820030451501c0c01805000303110724003400c4940c615031403221f00180c1c8aa907504244a501130700600440343d15103005800f420803c3c5403070303101724100800e2500c811901e080d001d20a42c09a4024074800c011506414255580042c1ca442089905480e0303a015860401c0254014070100100c6a030369807450400300828181d00d880c00c010020070031502000ca01d50380071321406507038048500050312401d48107000f91100c60214059000282c210800c800c1c000c0201d0f215105140d2a02d03042001e9640c942d50002898250705407000d5912803100500840c00c140c0e0009506c9820410458984503000000600039041f4072030072030050b9150981104d006009025010315224441c01c04440e012400000600e03024020340000e007007695810000c1c00540d0790141c0c280c03a045003400128004865400c009002e052001700c1990190b003411103100000b81300700001d1000c0903181c2c3c050038854682694005103805 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 483003669 1250 483002419 483002431
    0x30603151306050c041a0c01060816090e010f0905010b0907030b0a030803040501060806040804080c01141b1204080c010327150b130b120604030203032d01030602091309080a030203 79
    0x8050101003032413000002030569031b050b8204a60740315403d0060081c00c1d980c06401054a079040b004142040910740008401941d4031000301203904044611050300610400c0710b8044405c2c2402004001d0003810f602c1a01030003020b031410841c0e5546c2d8003068060310b01842c1d001c0e41060282c1c0b01040403800071000382d904144640000b103441a034526019241820540342035400300c2000034200183c580400003040300d00f0081c200000180b500b900b203442c1034003544004145004034041400c2464800f03202103080026030500d401d8030703640c40d0340c00a0b80d01c1031080150780c08640b8200d00314100200031040c00000d00c3c0204011145814165290f1400840c2118080d80f80c42d1903800d24441c075611203240300e00b0341d40841e00c00508040307103000700501c403402c007010300e1b1064020100340008294080200d82e48243c4443c401d9010301d0041d886454500d89000e4003500d0150124004006c02015030010120480c0c2150745408641c1c0b003007801c00031503200d00c00c010503110003000003416142c001e4000d141e012b9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 483004919 1250 483003669 483003691
    0x30c140a0311070c15020a0503070f030e0a031202010605030c0d11012102070b0c0903071a120c09010206060a120201030f0f020a020a05120a0e150403120503060315130605 75
    0x20000030480395031508250f0302154603200907074050020001c1540c030750024115900c01000742c5549034031001e840740714241003c0c20008240c000d90017403600034944484210805001c03040c4441d41d0342001002e44510000802c01035080c400b002070249030000e0303c01c040190040c4540f1150f00b45598605201c0c101410396070501c00e0340c840b525142c0c83c44401c1c210744101c0710000580e5600b5140350411690400805a00d1815414040002c40e610005552010341e04191201304e15041400c0b41e503400c5000c1d618030300d06005030640402080c0081d240c09014000c40a03000c480064480d070081240c01e100d18000c01500350700e4002a40c01540c0701c2d4000d9080210b100500103101c84608520001380d0b400041140c1c05a4401e810203000c0160800078030702e41e0003803083e0b441d06054812070020004054242c8251103220020031420b0441050030032a00190f0388613030f516081013440c0d080500b50b42c0007140c6040c820b004050419414440c04a00036101d440d01c03840b40f0303000708842c1d9244401088040d000708402c03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 483006169 1250 483004919 483004931
    0x2060307113706110a0509041401062c040c0e030d0f0c0b060f0604091b030204050f0d151506020f070f061b080c010218030c150a3c030c140a03 63
    0xf07882c844c1c0040683c810b45684256840350110305020546511030303000490300f4611001085095440101c50b4020240c00720a45118280400101003a19482844650140c40d01100546040d0003c00c554103c107070030f41c01c0c4c0c0c0d1101118281541c1c01480100040081100160321300005140d0500490380300000400030560050254080341c550b41144e00040c7d4081d603513280c030a00c20003201c02042d098502a140551425042c480415540604071810034025001c42121204200d00c130501c0320900c00350990100200b2440d01c4940001081038403a01c07003d8001c0104078111100c0104100003030355003606100e16402d00c0d00c1e200300c0e0210724815058100561a0b4212000102040014010300301d4a400151300c2d0115880810700c01080e00307039460301c29448003aa00003c0d8a4801c408031240c00c1c441e0036070b44c80f920000800c0d54501401c8181400b00342e100c2c1513002c03043d08d007103201c0804520800420668801c40b66425401c40c0e82c0710020310042103101d0712480300040d1241c0144289445850003080c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 483007419 1250 483006169 483006191
    0xf12071106010e19052e05061201030201080a0c170916080c12071d06062101180905060c1b1e0d1d190302060307113706 53
    0x4001081e04241e48505aa0040c400c40c2d00c010315403281048500d504c00c02c01c0d403d00d81e815440000e0f003600301014101502d840401420603444001000f041c0150445a950842e80c00882c68075009001c102d000c9003583c40030404c0081240b185080145140e1581107580034030015080442c03400400c44004d621038144210320340e42107000000020b0805c400100741d61a03180b005c100c04d49000e1269500107601c9071008115440054400c21198480d09a1500c2540c84110201d5894030500e00c22540403243e03480e000e2200c80c4803401a504031060504030000c104c07400003070801501d0351100040c016a000e403000c101e0500000000300a05d28110103c1c1c0603083c143d0b002c3c01e0401501903100743e481c0328004000740c19000c0c144082c245507005407a241f042c01c2d14210011103d00302241c080c6005209862045404401d4603400c680519001840d06849140a07000181000084103410401e40942810320955540b1024080c0c0b10045024240401c6103c0e070700074080402c0320108c29a101500c40902c010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 483008669 1250 483007419 483007423
    0x50906041d0705100e0a09050903090d0f02010f0c050319121401030203070801090c0b0a02070b04030503090109170a020402070f0f0b010906080303060108192408060a020f120711 78
    0x1981000d204040e0144510304030400a000d9584013000f420301c495400310010300d541d90656407007545c100c2c01d0700041c6a1150035040f480c2d130240f0801c1a03007140c48030003017000748001d40c01d5103a50f0704d1003661401c4417039906450803038004458150041c641c0e4802c0c009541410088440c0400341d4050740707001d01d5041c8102d82514151000d0001a03007a401c401c10040c42581030a02c402c0015000301c90003803219100568403440e58080314030980700c0d41403000c13540005980c400e01c036a0b0000d1880340c40294980c0d03240d08100341c6990210245070301040302e10178005a8a14001940b9580071030600103080c40c003149401b0702001e5400400201c640c204400d40d541d0010381c0d0920ba0f90141c034040d040c40314007981803d150390200d40c040e40000400317a0091081000176039125845c950302000344525031580126418044024180011004907100198100c1400340d05542111030304486000d01245c4c0c550b01c0d00f004610891185100420510318200403012015a41030403598102c24285800114004007292082c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 483009919 1250 483008669 483008711
    0xa05030402030c04180507050d08040e13020307090608010b12030313030311040305240603120f07050609100b040204180209030a05060901050f01061701090c090b0c0a0b0108060f0105090604 83
    0x80032010440c401c5c1000c0c8413041103050068801620304082c42c8402d921418064096480303096074100340030000807801d4a1401c05800c00310b40c00f5003251007141d00c449540780984807034040c0084c10f40c030f800c204d0000c0380340c01d14000c01003030313509070103149561603130b035520144850283c00940900d5100c081d240c1c05640d0755401000118026000303024003006503185034494540800e131000f5040e40b5081841055074021402d005e9580d82c1032200380e80c800f440102e06201e40100340c800707440b501400c400c00c4110300000c900441d00160b00030080201540940400c01280120301600180c62020050003800c40310300e0f0300421410f08014102c40815001d641ca90b440e01e5011611218540d4503031080c000e6038502c48500c0c0d4090041c80c10f0180348800d10202580742c0d0001403255840650301d40000cc03001900808040c0040c001d107640071030ba140070031090160790700c080c039108a510340542d5000059131440420420b000e1034544100043c0d5920b00401c02c40b4210740540b010f030b8460b0380c0d410280000c1c1c1c0d80308400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 483011169 1250 483009919 483009941
    0xf080a0612060209010906170a0504020d120917010c09050909010b090103120e18040b0703061d18010509060a020c0705041e06140d021314040b10090903050a05030402030c04 76
    0x5a44c442a200004089820b5540703c0024003c035402083c100c800300030802d82c2e20602800000030959154000500142c0320144054000460000d910410036407249142c010b03120f10407140400411181400f40c201d4410b00c03008800184100001d0045c1d140c0310085030341281404001142020040c00059100c87d820b9000300d5030300d00030108004000390010761420504908443c0b1110050111042e81c8110b24010002803a080100d03000031012402076200001a00d15000595901e0704030a10a5043c1c84041e9402c0c0185404407000140c401303414001c8520400082d0040c02e000c0c2c0302c40e10000c010750400d40c003229441c02010383c086029245c0c0e00c590412815101090030407806e980c2e80070021a10311703401042c0826001c0700c100225403110064056102e9060f590f83c2d5641110085500040c40c8895105405034402d10501c0144030705c0345602d9014101403c1900140c0e07a072080060304649100400801080c01400001141d074041d1018551180c0058143d0f18105c00c4180006c003140c0451142d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 483012419 1250 483011169 483011171
    0xf030a021908071a030106080718090e06060a060f2019060e010c0930080903160302010e04020307230a09050109030b0c090d060e0327010f080a061206 66
    0x1042156410070043c0600a20f2106010f545450041c80c0b100f800c0c0c80140210024408000d0115880c0d503c58494020f076003040030707403540c11b140d19400c9420141ca210034503c40b03644112400300300c2c82e01e4030102e100100c4040f62181142d10042036010703941030350403002c0790242c04825200c40c0240c00082c01180014411542d044c6041140c1e45040002c030303140115808016894405c034600429000343e10b10301544c5c20209101c409200c044202454041e0520b4016480400750006000b0066010060b0080c2041102a15004100402c100f090700c041440040c0c000f81100c000c0500c80d0403d940155006200361521f07100d04656805000c141c8446056001c2c290100024220000e07030b0b00c22a01d07000741400346002c440e16451030326540e8124a015042c2000c020001400c07420541c2c0e00e5001c100e016600250078802e0780010000b042d1640c211005200d8989568424010ba4110605050311100300503118145190300c260340c2290350b800e00900b42c138030203613a804021402c40080d503540303440c0c2842803174 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 483013669 1250 483012419 483012469
    0x53304030506060112200309070b07080a030e1614040b0306070206101a03160c05060f04020306011a1819031b08060105060d020a020307080f0c010606110a020f030a02 73
    0x60a00c2e92400c2171291171403400e080e0900410f01c2000c454280c1c41c404d5030040c0c89840381c007031031800e140c4503900100c0e0f810000110b400800944038040c10398114070381c40402101059202940e20b500c0c40e07503039000701c4e82c1032494140310100f200a0b01e803c03851406040060312400c9100803900e0100140e81901c00359004208104017000648d48203400303050700017681d000c019807100650b81c003400003900f090280c0520399289218644140c0351105055002007c032400ca040103100c215101c1410f43c0c040c0d00074040d500001c1039004028680c225042c003c40c00491804841c0c10fa6440348140f04c03c0d80b594458403220b96060500c042078800740c051400344014122003403c0c0603001c018013003550300c15010b03908040300401540e51000705481c1204400000541d98181c622012410751084800040021b480400c00080956044010b4059454200020059107440310400da800000c17180000d0001c0d80480402001801c00300c0c00901541c401030200e66600ca00c642c002125504c82003101c40101040e44 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 483014919 1250 483013669 483013681
    0x12020f0a0e041a0a0315020f1909080106030c0b070f122c06030606071a01090e010b03010b150c1c05090102190c03080a120e01050a0b01030501053304030506 69
    0x2100354104180d01c180801c182050620102d489101c0780d100282094031034500c00070b40d042e103e4040f5480e10b1b144800d0303103030b52710010124000b401d2400b800703900c00242100c90106031424148070314429030b40c100700000001c500d84040001180d1001004403462105503680b40000b5081c00300c180b1118200d51250003401040c2843c04424414012940c00002c02c1e11000d02c4068a88804598210707000740c0d6500d40ea40043d0804030300d000381c402110810440c00c04c00019003103400c0d910007440708108600a00c140301d40d080c109402d8914110080754003224202c1205510b4a00c00001c1000d0769906d8140c881120b54655000247c038580fa9541c0d02007080000c49120350344e41880803039440e40f22044580032301c0015440300b281180c1c1ca0300009015036400101816414002c3c409181203440d8414284840382804104038083d05041d51a11045e500b0700000f503034150f020307005090507200301070f08160100116940d9001003591000048051301d244138501003c1d40c1c1c0060081016502410060120781065 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 483016169 1250 483014919 483014921
    0x20a030e0102040f122307050a080c1e0a120804031a28090803130b01090b03030d05040201090f140f010c120c210305090606010c1212020f0a0e04 64
    0x140400c00c0c4991040000780486804612160181c5081410580051202e031403c2410b02140c0742c44454855080176114240400005100064510658107c040c0940d03403002180d03100b00d08a0301139032000f85008034103901d041c003101ca00340211000b48070b2400247d641c407014030410103416040c0c4050b03c000070244244403c52100360140c641c04240d4111525201000130102c0da134082000c4407008000310713158001c01181c1c021806094016500e207543e820b0044102040e8400f1000c1224010311003000000c050301e80744510007043c4006000f851a01200166a0004080082c4100e0520010ba140030400c2070320440c07480050411030030140c494401290400c1a485c000700b05c00b504000702c0301461000620841c03080c0b02c2c020080d0a2100c0d1140b0f19180c6119903d018250f00301c0d0401d00c051400c02c82d81e5058001900414100058440315101c107801121060842c1e40081c02106007003044085540c810380417508003840e038000040c1043d2040c000403100c3c0d80003207aa4000102d00d40400f03031040c501 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 483017419 1250 483016169 483016181
    0x4090e0712030212070c03020622150e0d15050403020a170906070f0c090203090c010e030f1203100f061e1e0c0809030114010e0f040c170c100201020a03 67
    0x601c0312881200342099a0082d81d6490400440c00c0304000401c10408006180c03038a0400f859004054030b40b80d641c040a040c0308661803a190361a61a00800c000660400114020041c01c2c42c5607102d80c0d407010580203000c507903031601c2000c6a144240c880941e588180d28030903240214400d40c06400011902e003441400303c5020000002c001a081281040c01d0356507004403285240e04c846c0c0e82d04000c00700d0400d6107080c0380c141e020100301800003040000c1228041400c0070740407426200d00350340154510902d50b03220721729a800c00191b0f00c03c5842a02000c1040043d66000418130304400c0345903290550504031880d43e5024602141d41003403d4400351140c500038042604076450315280c40c0542c651070f005a01000208042400980ca15441c02e1141e40e030101c030143e1801400074003590700703c0c08180551070b800b4407403440407e8461000c41c0b02e0101701d01c82d541c000c42d08a101d001e040303800c00400310070000158510b00c0c520311540710782c8034607a111340951480d88a6680c00040c0c4490b0f00c103001070160340d8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 483018669 1250 483017419 483017429
    0x70b0106020708060103030c1109010b0408010e06010e070305040203070b0d02040905070f1d010207050901080a02010806030613020108190c120f0b03120a0c0c0807050f0a050f090c0f04090e07 84
    0x20b85818040c00c0d40002c0d009046035054508810b1f417030064209407103109000e04016400800d00c1002003410b0b0642c17402841164074120003081040455800c0e01c0d1030704420b020741c014044081e404110700b544a50403451b001800101030307601e4160b4403180d40002e544036041c580c01c100c0d0007240070880f44100703200340e40c5c3c4081c0348e0a11807a68004004010304004180e1541040c171001c584510225910800c01503015101c00f034525902c95031244030040e65286825003c81c00110840005092405d001c1201e9000307000c540c292004900b101d50041d100540001c2413050b040064440c0c0e00460001406491003c400301e4031070220054070a03241c1025161280d1841001906004d0600115103001805014080711000441d44444403034074101d50740b003225240900b406485040124035081d000c034505088a508540114000444506005007403038944166540b020b020b038141501c6080003641c3d21341c045045e949070b9103840c028500765070399904030b030300101803440c1d89800200c0752200400c00b00020b00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 483019919 1250 483018669 483018673
    0xf031f0905040b04150204080d11071d0f0c07061107030e03070b040603050c0d09140606010e090a09020102010e0613141b13060906060f08100303051806091005070b010602 75
    0x880c0c142c8841c3e81d801c1d00a0802095810003a08041410a09a0554000e480c44006032130401110140050410700c2c401c09050990089010014a090010901c821100003071681919103a170f030445c000c0e4000900405001d44120200452070001d18a0300c0364815160001c0341e46520740c02d103401c2c000c01180c81407c0060184e44814428080030880c041501d0440d80c00d4030b008030326683d41c0c00c020740850003200039141507981000c3e102010003030700d000030020082142d0b0803103070079139240001140c1421300d82065603001a07401d404141401c40541114150074018000864140c0211600c10719100084602008009144111031704001c0004400f0303245001d0300e0300a0550a440031400441344491040c0c0900c644051040800128803a4010308001e01041400304105035580002604000f140c51804001030320000c009100000ca850300b0b0001c1e01d8259641e070f0b04280544107150156000d41c0ca02d507a005805101603816982c0d80e98150f06050110b0b40c4040e1600c1c05850300d4a0610410307089a0159 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 483021169 1250 483019919 483019921
    0x9051005091f1407090e070815040e0312100504060603020c07122102031803190620030411030c011e05070c0902181c0203031602060f031f0905 63
    0x500006a107201e2099007441480507000b601000074024200344804041c0c2d80042010042c2d06a000b400070801c445240c40075001075922000c0468038540200c403040701c5131840e00d100411038103082e030082c0c1c0e1101405044900e0001012040c4041781800c0750700c21603d032032640e4180521b040030b0280d0801000c2d0ba05095003400c92030544103031140902e01540d40707a09040d544000503c803c4801107981d1a100b00306c00c070101211011b0094603503015005008041c0c400181000c032030308000036540305440e070180410300100443d039110006040c00285502207080802541c0700c621a0400080d40540d02c2001c0103c128041d91007030500308003c04a149051012a20080c04210f04030010003405101c20b242941c0d9071a00e9260a904204607504011101c1c0d101060350341c28a200c200c05051801011114440c240003182d02018200000c1c1c04002d4141e0002c3c000c00b0048200d608528180520060285003040d613105494450380c1c204490a9400080f0f0190410303161402c40001005480712040600507 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 483022419 1250 483021169 483021181
    0x711031602120309060906090411121005010c05100507050d021b0606041104060c080706090f0b060306010b09190e040506010306050a0b01050a110c0a06020d18080703080a020f0d0309051005 83
    0x100d40200c140d074034094080025412300c10350352a03004489046c40300410640f221010740c842d4040c0c00c0111400c011a030301116000c18150300401502d0701d901d0340310340140140312103500404050900038242e807041c0700c018820306044a540e800605501501299030140c0100409031540c0b40c0b0f14050a481d01481ca410507000e22006454111401d4400034204805d404140303150505030f903c184c10024044e03628104000b0b041001c112841c0c840607004039454001501c1d8030b0101926210288140451000100400b9540f8100300b44882d4003651300381820103041d59039001d03140c41480100c504440d0b54200c000148104041c512076070783c101307810910421484850800107406031089541c614240f001120220248090401810b001c80301c010f09080031855490f20041d50f01c0e00b6808022010400420311040c490203c2418041150031180003000d1080c07854032250b406a000c0003214046000f40380c6c54800b00c20f81086522098070465400045030380144c103100c0d05102130340d443c1024441c100800d1003c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 483023669 1250 483022419 483022429
    0x7060923060a110a1d060d06140f060d0e0703120f08130308060f041e020a140c0607050723070518090706080c1c05070f02060906040305030711031602120309 69
    0x903d521135418000c1d680c1e0f02841c072000703103035212050030b544c0118001600e502c40c0e030048c4c20031411280b07004451524100c2c1d020401c840b05c9156100541c1020040c0400c02e0010740c180c0025184441040648018a44a03100c60343e03400c60500d0550089004180c034900c4950740310664940c000000c00a107a02c84109960041500c2c401819040c40307070380012401119540c0e0790b030001c00c1e81900c0c810803004611140811030069000050107802181156061800e402441000c440c1300614031805444503030f50750107040c0c541350425074042e581340e0358124032488152441030321503081d09003560090032050b1030b103020403802c46546158141500d0040c03090001041d800038044054032040c1c00c1c1300403d640d40602c181c0681c01066000c0e000041c07030f13504c003508038080344d48007a00818180e50348166145559400360b0f5a0b0500f0364003040c9a174020800a004680304001440c1c000d446840d00c620500640c070790315460758102d6100b1025240456080c402140f403c6050302c0f28803025903000e54102148600014 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 483024919 1250 483023669 483023677
    0x160303052a011407020c04061a03091c0206060907090303021b030c060f03010f08030403230c090c030f090705130209150f040306060b0910030207060923060a11 70
    0x21003051141c442411032640665211030003000c4802006a503800d2070216090f268190b0b180c4d005070141c1c00d0f08000c2d03401c06002d20416a48003001c1c00021002a42e48070340342c0d900c01040072600b402551400d0051310004980e00b038028045900070900c60501404200c50160301502d15000e02c2400102000002d402140d00c1c0704202d115000d400c13004e0700f020007003800d01c10b603494829441107002844100c0710201c100994140d5182d002107100b0a51070b04a82a03407481180005000604109810207443e103406030b100c0340500580c000e903040340038210003241c22070000b980d454a0701d00000c002c00c81030a50340c0b4180c580c409001c5004054291074180401c140900c6104005145900060042419210142100e10000300c208030195034515103800c440c40c64006010898445052140020341c1c1c1c0d0140f030540e82040c4004114640d001e052242c07d40007544089003c9600f00c2e119000302c1d01007401c50065404520441c0c4200461030307a00c02c112410260020103130542e0b24030b4040640d00c8248001d00783c03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 483026169 1250 483024919 483024937
    0xf040506031606050406080901020a350a020c010b010915050c0a1b0303110615010c11031203100501080408030a0207140f010c0f03051506030613050f01050316030305 73
    0x19094840001003402c1031000121003003540d180e09000102180d009009204441140c0c0c1c2c0c00201391903a8824900340d00c1440e0084c070011f40301c41d00e0903401a50381c110391401d44a01e0714901c18094200320100807040021110007a84660109208501110a001d8407200328024640032802c0344c14011110510800a2030000402c10007091200f00c1460400001c4001904a000d82050b20580200f8403550a0305000407800912000001408103000003030f00c90003404034600410017181410011291141480303800d5460210050558025440500000d80740c4c90003071140135600d00d400d40c002c0b00d5009443d4030482c1089100b00030000400d10110569400040e07140c00035175244841e090009040010300c4131020341c3d00403480e00020348501503028141c010100d0301c51490300c44a143c0240c0413201d044400e114013141031381299400e490300b01c4c019079004100070100c00c41800e010740154201c90080340e180c840401c0500050005290401c10720307002c090300f020b0f0181c8503030450394018400c1c015a080 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 483027419 1250 483026169 483026171
    0x3021c0e010e010501080f0c18060105090a03021c0b090304081213030c0f0806150102030306040e01021e0702181915030b04080a11190305070809180103120e0f04 71
    0x61004011020b4100381c8041140b00300a004958440c20003540310b42a222400301c07248944842304a4500701aa50040c60002811704807106070340301001582c0c0c5501c004852648100c10440100040c3e5803503401d2141301d11030240c85032000d40a4a000344070301030060a140b0107944240420010b21308005400c2114040301d40c1000d49600800910300249541e1340c00080181110450114002032002e14810803116200c00300c0e070765a03c0304e40d00b0303401200328a0328640c0142c02c00c00014440341807070307049500b4a007040341c0018500003000031000c5403110404140d0000d4240040c034003065140c40b50600c20b1380c0485c1080c400303540c2000082c080060150320f444090355074031114410300991454040e50700035a0805103c007910301c3c062420a1080e4000e0440b000424240c200c140286040003e403000103015180701030301800c0a50700c09590036000000b045030b19801c100400da0040d00c80800000c1e000341c075515056481c1d410361074030026106103141c002d0108041001845115034941e401140d0300322058034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 483028669 1250 483027419 483027431
    0x50a06081213030c170d0504030209010506091915180f1703070203100509100515060c03130f050102061b03010e07030f050906060a32060403050106080c0f0103021c 72
    0x1800078403200b103551000e016041482c02c0002d03d105c0c1c0c51120401c00c0c2c0300400744c03141d80100389005e440b18041c3c0c0c0030180d00031410600504c41410114002e2002000007002c030b1481d88008030304528201601e801205087c4582c850303001d00290001080700720351303045100301c0400e035090095040c1d44411902c14008011820b05904617101d10900c205d4450030380142c19212140050084500a050140c0d05006a8850070a205c04001a00c2c4603030340c091001ca6255180010645c02040300c2d541041520403014041040300d80003024074001c41c14001c082d004c030780301403091030310001905150005203070300c024a84014100100d213021408507410359005030301103002621001c008a000b4501d81d04448126803078102400403696000880d10701c11071045540300f100701e80311900301c40b03508088002010098818400010b459a243c40751a0307614601420380c50a00b65a52222420b403a035942c0034400c0c0c0d400c10000d01103070f4182000001c00d43c035020309065191108404500940780c0b001181d80844942d605 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 483029919 1250 483028669 483028687
    0x2040e0c0f041820130303030507030b041803020f0d05040b071110080a0b060c06190902030d0309060605090613091e1b120b0f04051c080703050a060812 67
    0x405940250043c60560804206096401801046909640c400b032008020b07001000302c410350110b441c088044485030342030610310703501070340500b001410b42d0302415181c3d0340003c903a80f1148034460b000c58041103911034585060070040d040c8400f4004014182d0007103c3d8007404180c00c01e048508482e0b101402e56075680d02c50409903000c201592025502c10344001e0084843c0d58401405805400b845804129046010b81080b02510481442c09200d8000030006010034403801500c81c4178066050b004204803889600203800d00313042e140c506010039a07604071501440103500c2482e0103032000345d940005c1c81c10440002080001c02c640b450029a803070340302c0c12082044811030ba000004826811403203501c0c941c6441200b40c400c900d824282c00d14180d0700000c0c00c0c032510080d40b190540010200c5016110082100310a4900400540f02403184011510040483d1001d8004046003650f4110f40d5041114005040d2040078016458083c240902400064000301c0c00b00e003072505900303500399180b03001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 483031169 1250 483029919 483029947
    0x81b0a020901270501090b010210150509040606030204020c030a0215040209130303150f03110303030105060301050d0807024f1a13020a08010e0c0d022206020c01020d0302040e0c 78
    0x200c20f00320007190400000044c40542500329280e040c0707090302621503501890300e0103400c80c0c0c064200c012a03050b00b00410080382c2230545540d0703001405201c020031015104e0300801e050f0381c4800c100c8040d03580006602c003030303407030341070220b10f11658890a0a0500d42003a800040c403200001d00702c0c0c9882c03c81c00c0c105108140c0a5846140580c141c4d4141d025003580e100078040c0d6102ca10f100c1aa414500e41c10aa280c610340401201e041e100c2c01403034181180d0034401441030341200c00e1401c03185400100041c42c0942c0e0781c041141c0c031039801c0762480900c03c0c2e00d841c5c1d440c02c01240705080885c104220300d45c1403524a1000030b41803a481c1c0208001507044003421012800940f001130071900080181020040000c140d0010618030b4a2505c9003007a690b039070310514103a41d108480d40d0300c03a007806000e01031504045030000d1002c01c8007040740c0c009030b14040341b000da81041950b01c0034015a0140c3c2c0140740d1541c040c40321140092807030070214105403505042c2c06a40e0401868900310740c000042e100c2c0d80c2608 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 483032419 1250 483031169 483031229
    0xe16020d030203091c08161b08160f0c3002040e16030506011401020a0f03050708040b0c01051009020c030409051b0c0c0a0b070305180a05030a081b0a020901 69
    0x20300290f40c0480c005240c5c01802516066a0791040b0024500460340e5650040d042d0f07860f42c0003450180a42c20410761030b00b00d81038001194445181e550007042d4008108011403044030140582e48407a12580382590115100700313007200000542d00c0c0c9581c0c510f20b0503203a880c03c1d028540c0640c4c3c00303e821a58984050705081c1c5840d404000300038400c0703001c41030050018449058519007214190b100c0101c030016a41c13078102d1000201000f101140010020b40714401405000c0d120f903522604203a00e911842d00d454102c00c6820301160754401c20820340c2040a02110003c20000b00118908241a4840c5441e84030394041c0084c0707140c0701c4010589080c0750300102a913084200b9801e549440c1c0320f152003900c6200821090b4850740f4200300225100a2400484400c2641515210314002500c1040005001a504050341c007200301840020b990310140080f0600034492007500f562a5010344030f0405014407401400700640c4510600c40068a8a141180c1540c030001c4140d11240242035500c480e030a1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 483033669 1250 483032419 483032443
    0x30a03030f020c0f0a051612060207170715060519030602030405030408031201231815060f0a090b0909010e0a02160308010303080604090804140102070302060406090e16020d03020309 80
    0x3c01d5180c04e48104202183c0f6640030351003181940c440400803468210390fa00c40e402407000b0b040c17241000f100040d46a90080c41c0d01071107000780690744811410b00c00300c60f4110100a403001500c601c00c202c01c406540c841e170000b80c1001c982c92040c103030003140f0001c500c10385408010812603000000c07501b07005e0300b0401d43c0c00a1907000c08595440f0000c1c0842241090b080c800c0c0c000e4804003198014016180484014000e60083c10303084001c050382915400e8040b0181050003500500070510902d502c51200400864a0902440ba40c44d00062030080408440340d000c0c0f45202c40c00d0040c2140ba545007d109070440e0fa4000c085616502c900040c0e600901c103401141c034080701c0c940c8165042540001c0054102c0303000351184505030342d61302d051100380c40e40305100410301001008140200c125004180503415010320440c3c0d035841d00c0e80e02162040d0b00c5a007100340410242c803000c02c4101600c07114680d03c0341c3d07080030706039084041490195464561000040c249500800001c10007001040705001d150 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 483034919 1250 483033669 483033673
    0x1b080403030507021002030f03190902030d020615010914090c131401080112020306180f10050a05130803040204020a050904290a03111311120105030706030b030a03030f020c 76
    0x1540ca10380504182d00280e801c80c0201e8400380100540c1c6e00104c05e07500884100a4141d00d555600b140100c040c103045600c02070301c5d0369995032070009a1003c110556541825400030542410700c440004044294058428104180110144108968140b84080220040d6440b1045481e010715150041c090904951643c1c00560400a205882c40b0f5940800b200280c0b2005105d0f601d8094590002e4050076000c0c0d099884003020030210703105016024402219841a43c40303003482c007a02c05050018102c5044078054450050002448151007401d0b0803801d05a100d400fa111550345075411400010006445658080384044460303020760215032003050018400c2201e01842d170800900405078916040c01c202c2e1101300305141d0b0030140811410341340c00450740b07035907004e0340e0301008505c2080604002d4031a4855103440902c03603420f00030b0b10780c641541c2c03417040403581404241850070300180d002c0d000701401c00d1404d45c0907890200c0c54400540c2c2503e8080f42000c4501e040c00041d1040281102c1c0c24 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 483036169 1250 483034919 483034927
    0x160c0f1707060603020118120f111003020405150a0f0503062106040501060b090d0605131b08100c08070e0a0512030702040609061401050a020a06050708061201050907061b08 76
    0x10502c2e0388500d06881c401d0703c522000001481002803c3d400f18018007004801d040d642202254516840d80e00d0301c0d104448981e9a42030800c0400d540c0e039004c002c410007003a000701d014801c501d0300d402c01c4041c0681d20450181401c006040c000e0402d003005a242040c0300c0000046100d5455801c00001e0700e0100750030300b01c5414514802e2944e41c000c12142511070354608100840c0124a400490300070140c0180781c2d25101c8140c0c4c4030740d00100b030050b01d0b120f000651360050b00c0005111400365422400c000c981401c030360385444840780c241520090f04554240c80c003184072021907002110290429981e1801759880d034006800f0031081561a00b010368001c0048480d00b10b020780002c0105005c070320941e0140300c0039640702c5482c4241c641900640352203c59035000c5866952180740a81031526151046503038031280d948a0b1000c507603040d52010006202d5074108013042c01e204140285542d84200204003c0c035255100710344440d098003690f01002480840c40380d100661825007080950000388042d61 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 483037419 1250 483036169 483036173
    0x7030902150408150603031b0709061e0602010b0102060a0e1e072105060c03040f0605010b21040309051909021206040e0f0a0215120a090209160c0f1707 67
    0x8581040c410800706100e464074a441035034488404c140110409802182404405400d80003d040388030542030852144080009000c40e4074021000140700386800080c01d5100c0340403110030090141c1001c800c0d68100720000d03109990000e03815a20128030500000c600810b9003100313040c4607882109511070901840c10f221074000c08a8520129a0104086010421828508100744107120406444c0b5008040029941c0070b44800840d030092040070000d041d503805640c2ca800b1140280c000410040011540594041c2e95125171003840194a501d15054981942c004100c40c2140c010203009501403640141041e802a0724040a40340b800415074031034001161007065402d0489256115608100b0624254070001c40d400609030000ca000e00741e04001340d02401282100040c1b044002c1030f041000500d2200c0c030301d440b00d000d07a201d00d80c040741c0940785004000300340001401120500310202c0c081da1900d500301c24a00d40103540a49940040505800c1824201c030b0700e880010011361000132150b00f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 483038669 1250 483037419 483037459
    0x81818150a17070e10031403030403080f010e04060b210a1104110d020a0203040906060c020f030723030f010608071805060105040306200d0e0609010b01050306010807030902 76
    0x6226001c0d6019110580d4810300e041080105800c030003529008550140b00c61403040d1660fa0b03111041500501c1d581e5581e54616010441c0006a0091904040144810154850751030b40c0c20044126514500e541400c1c80c2c025100300161000305401e64a59400107a600c0d0710942aa1010340c0c0700c03607440761030304003c50243c44040341101180c641c1c1c6548500324985c40c0c0780c4250400c24a143d061503040480150016000307610100d04501075100500001503001c0c0a401810090308060303440c0040551544188a1145200c161070f40c482d4110030014040c0c11040101003070a11098200c1da100b140308a404681442c80d102e40742e2042c0c2d42000c00110b0030100004441080311b010f1a68a01400d8011200400300c90055485500184003040f0410100d134180e00000c142e00d08400840249100400d0991883d500142850341c00c2501c42ca51149d4030304080c494543d200504070020b106895030040000d00c5488002c1180d030500956030041041544240e10141342503901801130079100c4c2c3c10041b060 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 483039919 1250 483038669 483038701
    0x40b090406050603130209070908010f06060206100803090105070c03051c081005150903150f0613200f0403080f0304020907020a03020c150c0a08120c07081818 70
    0x150060741801c0000599082c8802200d02c582001060445400159403c01412200c09048203080050320000800c200c203081c070542441c2c40c41c040c80000e0b01e624100303001e410254020000901802c070841c040040710000300403101e03405d6091a00c1c550301c220a11308a060f0700c0303107504003402902c5a41310603052081110039085004a031519140c04c1a81d4151010b91425003a026250300102002c450b03084401c03580000e00f00c18031000b0152200301c2c2d9000048000c0d01c50440700910340340011814865241009102200c02c0c01089c50280701007038a40e071401d611180041f003142c0966100007007524004241405803000f46601011040d569020040302c0f40c4950002e540c26441044002c001c50108dc1c00001e500001c560700da0042c083d542046020041e002d051403070704d127500580800c07401c02808010710565070310601c5284581d0700c03080c41d036146510202c801804195802c2c010000300021614030400d442000850154400a0b141d10b2008035003c52000350510314403c11040c10f201c42020401161 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 483041169 1250 483039919 483039937
    0x10c050f060103052107020d0f02270601180b0d0204080703030504030201031401240302131e0b120c070501020d02031801050901020405060d02091215070828090512040b 74
    0x143d44c42c2d03020001107048005e804002009814007042824018200085885000390161a0807443d4000390380200300d191034031081400800c050303002449080c0c81c1003580c00740c00100a02e0540280c9545581c2e100800e003590088510084000ca1246172000786601200c028008401c01d50304801e9403403030044d02a40041c00704a0209042542050482640001160480b00700c00940e0312510000807070000c5584070342e18000f0802da002c110800d0100c04c903080351002007025001c070f403c4104581200c4041c11041d6000020581001c104464004000c06042500106075002e029034400075450103030700a00c642c0d46040419800030042201c1000100d0b110745512416000911490307881052039400c030320990081a500020501c981c4050700519030144c606680c0c01340c07005819140010320f9a20301508998000e08044406040000c11540032840c50b07000207003000111040049201d260b0b0081565144001c129542c603240d440521608000b0b0322006c98000000e682d5954a41e0940100390b403005000c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 483042419 1250 483041169 483041173
    0x9061303084305070f120314010f080f070302150a0c0c06030c02190b0114060403050709091406060a0911120103030908010c05030402060f0f0705120714030720010c050f06010305 78
    0x4580180c40c0030324222042c0c00d503c02d14045a2500c1e9550704c07048000301d00744e410101f650359419000c1e45d01081590314060042c07031100d03042092400c02413070704e4141c0389207003007603590040c800400040e01c030880d0410760400a0403120351140000e4008641581c401100540030204002d0006103480c0c05901c00c1800303840e1a800d0f07610380000c4902c6d440701c42170801002410426a107004100d62161038041000e4928001c048601c1c1543c3d0f034542e680b400700e0035008140410b50700c0c52030004100c0e0300c20040704c5d8100800060903503880d00d4000a18170184522450500d691900072180c7d4610f0100c085580d41e1508050600707165840382001000141e5500840d4881d41c41c00c007040300c50b03e0145003560312890b4002c05081c50003140e041c46607a10b800c44600e01d0107400c004e002c4003002a03024001200c2c2c1548540f0007503204c182600307100745900040c0314448181d0704200f121401040020200c5c1182824610580c0c100e10900d2004031005035640c10701518070f000f0b058012000d08030100f003c504a07402081 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 483043669 1250 483042419 483042541
    0x6062c18010f1502030310150210051005091018090c0518040312020412020d0201210504170f09190b13030b07050c0d030c050f0d02120906130308 64
    0x180c1e5039120a90f64046071f640700a004003c003404550719003003010018416607503d0010411a4016100291251036048841a10502581c100351520503800768003c4441590a4a808030a201c3c0d281c0c0c101c03c030445a500c2d0300981d02441b4080304503034014400940440346080b00103103003511182080d20101d00246030f001e040c1e44031031018001e03201900c8610030070502d2284540d003040144210f00c0000c03418000b0b8107c1c00481c00e030320700c000c2d0981054051b0b00481c42d0315007403500150016130009580d40e030707200a000000c0d4004a08068418a48041d5040180511026106241054960721400011400203141d031030340c01042495504880c41010488900d468458055074036000310107460344540e0029070b1286c1e030140300c1d420001010b1001e00b0060300d045034000c00c01c05186c0c0048039004525400090f82d505001c100c509107503110683c84090b10003030405880b070824074000c05d40007030100061036000c5806102450b41500004c2c0581040180c2e541c0e48070000924454080300d018001c600080c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 483044919 1250 483043669 483043709
    0x2040b0d12081503120d060b0307080403020706020a031b0c0b0f0c0115030b07050a050412060219140409020c12070c030b1501120c11150a06062c18010f 67
    0x10103c081800004000e0102e548901841c088140c000b20500e89406072100b0b070019400760100f0003140075105550780c0c14801c0c502400d01031f103070140582c030000c05c40d0b20032100b00000c26800b00b0304e60f0040290510840c038500107401e2100ca8054150421035400400084502029070003070020010764014900a10981c8041039958888911078800903100b510301d2400241120710600c0101441821414260709090b246d5081445940d0200c0b0101d9201354000341804c0f2408810035050440c1c4c0d168580407191141c04c03031034240580502e1050101395600030800d8529a40d0a215074045007420f0b05d0030740c0c6c903981d850070014038202562009442603003d0b00d0218403503101403560b002c2009810f0b100d814080c4c200304024001081100803000c20001c58155142d4400b500384000f01307500001c8506d200150401e05003c1c4129120f65011000348020303d010101d04030360940d007a116444c5a610076144200813200800d403001310340c440c05030b02580010000309007204102c480409507810749100c108000808 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 483046169 1250 483044919 483044941
    0x14070905090405031b03070c0f05210c0f04020c010f050a150b070210200d080709081b0118031203112a07050406230a06080f0402040b0d1208 62
    0x2900c003e011600f08221101e1040d800e150300d80c500106200440385480402d803502c5c8000106604440300c041d4000104000303501d02821001c5401840c80b00841030402c1c500c0c0c405980701d6606007014024140d442503142e0725900d550540b02c41e080c0090090218041c0b110724030000309821034101007594500b0380c2842024401e040c0a8080d111141001898204507400700068054035900140c2007040202155103502d80612216804030701c520002c11054030f0542000e00302c072000416000402242020802a0480000d59001d00600c0311584501e041940001241c11100301d100026100d01121000410003401000c89400c0044644c1c04011000700407803120414403904446c10070030701c0395207186003421102403a43c009006003941160003481d6a08082004d40b512540422200d681c40c812280704200d03035805c00583d2070300483c3c9104005090100180c40e142000c1c000c084000700b024005405c54444d58001044800c00512840c10240c640c985200060300090403d00002d007000c0110f02c8040131 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 483047419 1250 483046169 483046171
    0x1101262403070905061f030b011e1709030d02070c030b010506030f0a0e0705120a03110303070c240f0506040b01030b0f012703060b010f1d120f011407090509 69
    0x3008025240492814480c0c5001e010042c200680c0102001b48441c0700b582d1104075050b440b00c2c0c82e01e001c20006e590000260114004c0300034071541c002482c120400c100e60110148980740702d207888c0f08019455620302289180250100406114030000c0d4410602403000c42c9401143e10035110725003240c1c0c0360001d2064a02080d240003039004405004240d581c0c0746a08241160821031040320606560350700040c0702c1c2020504c2e220183d4001407414014142c1c041010a048881c6c03200461860500c0807005121001a00015061100108400700240c101034011000250400310a2000b0340faaa03003440020001501d6080c8101d2a0042460316540a4056075000700300042580d8014ac400c6401076031f2200c211440030b020041c2c00f042c0b9aa4003516880400c020714010400000c00d171080100141404031442030810900400d0384081500b011401c1f45c40b00700c1303c2c0681c0e5410b640c6003030050042c070305000074802d900e20354201300c5500841040c034015644280303040c0d0f8592030b20560b0380080c0060000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 483048669 1250 483047419 483047491
    0x5101103060f1216090b0913120212131d1e060a0909050a110303070b280207050f01061706040618020603040c062a110126 54
    0x400e10000c0c041d49881e545018031910098071512141050100b580d041070a000c0303c606245160741c01c24840c85000d8401c40b20054419900a0700034181212110b0120000b000e000300740718143c80d04046400c3c401e024030383c85111071160141e1122081e00451800c00d000b40100c001846481d8070b120300d1014080c0d140c501842d20003000500441e41d02c43e0000d2110300061825800c00c05151000440868611841000501410203001d01c00c845241090b000444c038030305103201e42d01c02d00c40800810b5240030781a40000d03a00c08a00b2400800d2402041c240d000407800741d044520124102c0103024000c00c0808480d051140208030550302e4500d101c0c50302500c80d41c030401550005002030002945a404000e0503584100402500907859001400645c02103801b207401c0c08020008020094000c0b02c888036101180c842000d140c4130072101711a0500e180c580c040c10070b40064003c818141d000300c1ca003642c8694040e8100b0171030018010030b900600c80548824099030300c0c001c01072042011040807290700e10 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 483049919 1250 483048669 483048701
    0x420040b090108220b0c130906150e220f0207060906050c1606150504090c081212191b0221040807050910120c03061505060a050a0903050a030c0510 65
    0x42c140d0b00c4170b02c4910f6004284480308501000900794620025020b2001404081808500d490030003245010342d10410001d0824006240700b000342680ea0b0003142c018030502e5105d424585002614540c1c09400b60440404000e880010300405009180d0440c51a281c000d4400f0301041d190181c0140c160f128290b40010000c072183c0f800b8000401c00e802c00602c64985103e032080254840c1e001030201d406031582110b1400865504002d400c0c0207001254030300c040c0c42800c2d030034600b125441000600e00145404003450480780c4200c0d20114a50040030010f0003c009415095214030011f0b50711200548100081c1c4012440c4410100c0ea0300c0464064030400006058241d107060140140303030070007400c0058501140c0c070300412040395074120324078003a00a00d00141c4c21413550500b20120781d00e07071100c0c5101c0c0788454824000c50300c0d080200d0715090f4261402541e01e1030304010440c0ca4450a0b08020010b000300c206680500d507101031683c055900038002e0301c0304d55045c0e05040e021105e44030110550a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 483051169 1250 483049919 483049981
    0x9060108130317010603050106020601060f091202031609020c28030f0c05010c051201050d02011e05070507030b16020a050606211009111206060420040b090108 70
    0x41c440040441c09030a00c00d08026035200308001d561885000300340c00410009958800400505504103c040c1c0142000c0c2010029008407100003050740b20746024942d600c4a10640fa03100315141041480c081003001580004c185031950401e102a40c010489078100b4414035035400c0c10340078804040301810111520304590364003160350588425021669000502000a4680380412000c0c002c1c1042801c6a07038807181e0f107014001000b841200107130441e038002e00c035806136800144d80014403440c1614032402c00c2d60041140e050112080d1046031402003490050a1000041022030050a40034a41d03205e24203c098082800c101d03622001200c0c054281d6100e080481c20a0a1110044195061800b03404040100c81c0720300318a080300c41c011401480d551429004144000403d80d01050a000c5401c0c0050244c0e044129039a040042d00c034500c05c550303c6c078a1038440c1000241300c01d07040c0344015402e40c84641d82c880d401c010b1780049181c00e011a441100003039406103003220311380d05007581c1c042080f14 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 483052419 1250 483051169 483051181
    0xc010c0e0301060f051e1503060108010609030b0426070812010e09031c0f020a0804030f0518090c040e1603060806040b0c0918010807050a14010f0c050705090a0902090609060108 78
    0x1c04005444882d00410102110380361949a1f011961800a041446035a0320309115000401c0110140d200d03408000501100380001242000b1007a045070300070151041101c1d509480c4100c04022698803003400d000050303284201f103500d00241c000c0145503d004482070ba43d84241e03600303d810807203a1a40c00d41040083d0642e072061491800407040202500140b52000e215036442268003219160000c0f5951800704000c00d80e001d000040040030901d4a1401d003518a82440c0003890500f00180c4151044e00c0003541000c03812045c0d400500100701c881342242046c1c03603610000b1041c4204040000c0c00c0034408101450000b071a10701a0358004500b6001e40d40301c094654003500b011500d44ea0010301e002145000004c04070380c440c060070b03034480580026803400081110b00c080782c5d40b010340703101d003005950300311030707804c1864006120304909000c441c0c8900c5240c0b031401c1c40c45c9600300d030703511032840070521070a02240c0d8050b58a407442590041025203c0d07404010710200100e40d42c0e40041c44260003d40 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 483053669 1250 483052419 483052429
    0x1703210a09060911040f0b0901061b0b0f0916030302060609040206090a08010e0d0e0a030b040302100c05190302090306010308211501180303020307060515060c010c0e0301060f05 78
    0x90300c052404000a002800c80d0344203010344402c24002d5481c82c0011510100074542403007913885403421101c003080020f110714040390ba94001445003400f4081010700d10854460070400f003041190b40001035268501d486184072000c0642a2035243c4140f1078050000f800c400404112400d1301c4c0c2540040a59503030b8801003040c02240140b0480c2c00041c28050122241c0f030314140c090140401c0d10000c03e40041046007103240c1188000d4560420075481d150721001d4441c0145a8181c9401c100c64961666840c14164a414000f400581c4030b00d00e000740c210407031540b02c005414010304c2c5100300320a10076070301c070100d09034042c5402076507140c0c11032401000003940c0e610003020350b00d20840c0360082d018200008074400701750031a0791b12040030051487c480c103580c0c40074002c02041d04609001035100c0c15610000d660307008000d00200410742e1280420302905000c0c021f00140301d0010021340d581c4610100d8a8003a1186101020104e01c85a5003074819181c107000e18800d0b10303407c01c40d50110074640b000b000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 483054919 1250 483053669 483053671
    0x5030d090311150d060806061816020325110402030702100f11070c03020414090604030806010c0210020c011205010506180d080406170a0204060f11070e0709170321 72
    0x203907000d8480c3d0007200c14607102e480030b4041841c084000040f19450241c2850030450000c04040c810449522002000c0034416451508208a80c0c003982da09240400b00340e155110b031003440e884905400301d0903000c072040c4900c14402544036490303001200301101c1c140300580c0429982303071001d0703004620030b80d84421544d40044003044003000041a04141084404125404150150782e6990601802c0c015401c16003c2c003003c03164046010b00252416524103501d030766018200404102c80d43d00442c0b2141e00c20102c2840381034004246540c0d2030940320000e991007030380d07000c6030b0f01040c1c20806202030b54880d0712941c3c2c121040039040a05d880c06108003003c5a1482c02c80155001c0310f48911400401d10200250001d8140c50300c800801042691000307076604401800c961003540100800c2c08200c2e4032410780c1c610a002d82c1807420400100c0c0d50402d00b046403540044120704180b60401184940c81400d4100300c49490142402040d41084040d4691095007400d01111202c0d422401c80d00030500c0c0c03a9 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 483056169 1250 483054919 483054953
    0x1b050d0308040f020a052d060a09180204150c14010c1d060409051f080106060c06110c0105090d091205071203021903050714010203060f06030702010b03030f120105030d0903 76
    0x1650107070721440024581346207802506000c9030344141c81c40e0301c030303002c903070f100c21080340c08c039100ca040c008030980092001c0c034180168800b0741040010041040150307015200503008205425403d1004100020140e6a0040054900052a80c01900a80030600c0b824076a803040d5512448651192000b10360941c0034549161f40104082100040e513031014840d450103800c05003880004051120110b01752486250010b55990749003e03000c210880e04140c070401c015034001c40c04240700609040c068981d000b80c820000326035003031204100604201107907400007a15140c03030320061030391500f2410f09041c04101c8020007962280800348a202e400c0e000e801d800d240b00c0d10486042407005a040348802889040440c0814804949001007116500c4e600c3e0107048030800031815458190b002a000442012546000350700001c0031a80d811f100307400c860000c0760098100c0e6600d80620180300140d5100203809402c0a20300381c0049080d1030089002034a5441c642c1d51800a20304680b00c520801c0c1b94040302d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 483057419 1250 483056169 483056179
    0x30427180b0a180f050714060406090603051e04030305010303120b060409020d0e12040807090506030a031812030503011d010806041e020d032303070f051305060301031b050d0308040f02 81
    0x81c603c00030b000c40040f82035441c0f04401504c0d00500d4241351038003054009412900c03c89043c0418003000740d2041da404101c4040b41f80104042d107440d11400a0400c034581042d01724280d201c00c0000381078040e00054101c80c8030307540d003842420004800b44202d803c2003d00030f602c2a01044200024012074010f042e9804100c980040e00301c2041d000f03103107417000001c52800f20300c4021908010300c0c036090240200034900d051090045140c4400001c0d100e042410b002402d00c10b4540c0902001600444600054807650200303441c42034044c18007518540007403244222030b80041c8001110000300d09011030480740f07000000c03c60350f02c56944260041007552410041c0301e5100d0ba0450159a03002d84903240f00d0b000b42c5401d1400f220b000c440c42003800043c074880211880c20424800c400754040a0440c4096152030260740314820f400b05422019450750046500c078001000101c144180300c0416419a00c030445960805c83d614424405207151240c1b010b0007003200b01000030041000051080f05d02c61000708 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 483058669 1250 483057419 483057461
    0x30a030518071203030b090f0f040c080d0c0c1d010506070f080a0809011a1c0302190507050907080114060a1704050303090f0a0c0b0a02030427180b0a 66
    0xd4003070b182440303d50101c1c99503c9095020018143c040c800c0c80301a03901a10510510301d00072001828000b4042d100c2c02203007547c03400003010700900d911200050441d180640d0503e0311040300082c5402c190220540708652046400618141c084c0c080b0685411408414440b6038601402c00949801c99a4113a42c8606150607580004140600820013034003a5200c1c00703490b0a00d15965421200b580c40003403070721003440b516003000e5924000e44150b44902001228144051490200c1c242a1600c550000715010407046004001000ca1158151070b001d603400b07403c41d0388090045030004400e00c14440c05400148003d00a801c11728000d000ca40a40e040802001111b0201e03c183e120040b40c0030341d403503040802480303121441403120003104d9605030b006042050040d1030315240d08645126103480030000040880802e802030081d2402003100c080040c428110000750100e0f00d56200c07003400c440c5850043d4500d082034840d00000761054010700e04800a90700c28001000134201c01584a921005c255 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 483059919 1250 483058669 483058711
    0x6081b120d080f060915040216061a0111030f0a051b250803040302012a0f0602070303062301030e070f0801060e090102070f11130908090a05040b03030a0305 69
    0x8451498803540e0ba40800e18039144403000c10b400409013940d803240c24003c040c40340300e22420340f14560300354080b1001a0f030baa03565000340b880d00703001c080001c00c507c4c1094110350403d182c00400c01c000b43e03000e0300ca0300e00c1042100c0c9201d450388102032401007181000c1c480880b440d88110050481644a01c0881d44e9241d5401c41079441c1c06165860000344517a40c54030103038680d12100c426001004040b00a504050543d400641040207040340c0c403184602c5160b904071202c101042114644e41c000200e030b000b2078180d040110181d440048141d0100703080c02c6000950b0040700315030000c0259840c0072001c241c03407060011805000410b03421240341c82002030210305800d085405000800280e40001042ca1a048d03400b1031920005001c084140d106003c800e001c10350361401154215408040d403070513000d2440006041d02c0040089800117843d00070140e0420180d803008101c442c0044a0f00c1c8407886e034039020001034400302098180c16030414400d403084a8040d800c01034100c0c0c0c0c600c0700f1101d5400d5407 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 483061169 1250 483059919 483059923
    0x31d030a08040902030a0605031903180e04150b0907051b150108070819210c080f1b0d021c020a05100b101404030807110a030506071206081b12 63
    0x64205480869000040c01b50401e518803601b0010300c02170303000d001d8582c1103086410420115503409802d0100d2410041c0030426040e540c81c000c0e01e030030701c1300c3e80243c102070800750306283d040c0041c0d400701450090f000d4a80c0c54440c3c00305200740c201c0e80e5211305c3e01c0c0c14420400c0c98903001c011204031910a2250245200400c1c0100318007030405030f40102000703840d1550452818001e5000605001400b200d07040214034218082c5904215040c00700e064194141421902c1c1d024100d03010b4480d44022448240e00351411008020064003162981c01144031800116124695031191001681c003500aa0f00c5000c6000b0070490201401e0059960314000380e01c401d4204000c0d1070725003182680d52a0340d18603918015041c12820200c624220000d144092001440d603ca14040900800c401140b804100b10784007141380c00501d005090a01e2007030380d915140d81e0780c003415694100820000032451184134803a100d07200803101080018650382041c0c0001201c4801d10300003076508815172103c128100102 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 483062419 1250 483061169 483061177
    0xa05040f1d061e06060304030c03022505040c030507080a0506041128080403050403111302120f0106030903050414010203090603090714011704022b0f05010b090103031d030a08 77
    0x603441c0540b9442c038211660001c070300d44508200c5290381c142d205002e03440d03c0b1039003a26030040c0e0509040f41181103900b0140d280c0f49542a400809000c450450714103000410381500444005903403d0003441034100c4140c040e100111481c400040412000420040d500e0b0009034201078013500002d40e070a8000101d407081d40c1320104010500c0b8420100080080140981c1030740541d01b8907160080e0306156400826900c201c0c0300262010107050000b101d6075a80809080c0c180722080790440da1020741aa0741c66200d10102c0300c00e82d901701600000100103000340247c440c501d506a40c3c10b4034040c106641c0440003600f02003a01e04504c018400310a850720391000841c01030785d0f560b0003403021a1a200c43d5042c1207030380884840c10006001030050810341c18845646c0c1203035040320108988001d60b110000148d81001180c1b0503078000c011803406000401040200c0c0c240100003d204801d101c0b0240001d4200030b11000b00080c80c045045008001c103c440740415248c0102540e415841b251280d240f9030304 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 483063669 1250 483062419 483062471
    0xf03050102120112050307080d1806090210050414041139031c020d0b03030406090303140c0619240501080f010303020706030902120312010e0a0504020a05040f 70
    0xd80001d400c0c010a0b0108074890041010201c3c1c20b480044641d100c64480c00b44840003000d045021a02d5100d08546030020106600755a4000240c0b80311403c0140241c02c40003010390041131807400303a1300c07164421012501552108507100040c0d4406d071081c0b01c001c1c880461029030082d01880b83c0d4206088909e0340d80180300c0722601101c1300103200350314030006145480c03100b903080c1d00801440711042c1f03501c84884100c40300e12800588500c41c40c1139100283c1428051310f5454040014085820b43c0c1104140003030782c0c000e41c1e8044490f812903040c0c0c0c4440c4a4140303802a2507000f840044e40030040d280040155a001500101d01420705104003000d894014809547c00b21440d030f000d01581d40d104103115808841000714503031952441c0c070f019407100224090b000030580c039003101b641503403a5241044a00810b5008503981c07500d49820142043e0401c0c003685410940c2c48003c594144582d0081074010354008000ca5603252034681000001c00c0b0305503c1d01c0c1525181d80e90703401000c500303100e42c0c1c103d00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 483064919 1250 483063669 483063671
    0x40c030e060c090904020f0103092a0b0705030f030c1612080601081017070308041502010c0f02060106030b01120515090a0e07030f03091a07050d0e010f0c08040f030501 74
    0x30840d000c64904280d0000c0080c00180b2041c4814251940c5810a0b140c0107501640c1d0020680280c200407805032045641c0078103045040540a8161407003050000d14409002030300900c141e0b1a852004004d100d02d04005e0050707402840096000c00d02c4200660f0031204801c00249031031203103821007880841002040c3c0d6507060204041c110550000c0707a003603014500340b0303003001140751a0360b440b000c400e1140960b0007030036004196580044400c102030400740d074029460907100d5079a42ca40c3d02010b461041f0301d000650030071040c41c08050003264101582e040d25005091160f0810170102c00819540148504000f11205649008c1c01d151040d10b0044502c5d801c0300480d10860014031082d0140540300e104a203180c540454100480410303100140d99016a014840c4002800c04403451519600661408850004a0071110001c00b000384955407182c3d00f0307203010b00c996440544070442030f0700041e404200804032110555109141c0302c02c65900c00e1409a0800b5251413440d0f803010f00940044400ba = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 483066169 1250 483064919 483064931
    0xf060f0602030a03050610051804060902070b0a061d0c0307030609090503090f060310030308060d08030f040b07031b08040201021005070926070605030c210115080105010e10030b040c03 81
    0x70360305001c1c5d981d001100740e689034520070081000404501c1102d107034a040d50990100040213941e140c0080700100041441507403905000e08098440c0d00065512001851400c03600042c152080c0110301e60b600c4d840c40c1200201c1d0f8900464140070340c8010928401c1541e1580007241d0214103215002d4441c0c042c00086407203407001020320024640c1c1c054010f220701400d0082208000ba0003144a040e40e0b854070389a100c6444000c00308202c9080034600908000c00801009254118070140611840c00b8030800d280a0301c1d010350690488040341c80c1c1040d0900010200320f0303543e00480345290060701c10310468401c410244d00c2c0000b01c94080e0f60301d0340010f01d2650100600c640218951620044019489203428480c00c01c095580015100300c9007402030200006803200114401d480b0501a1403146801c0751000005e050503050003401000a41c02c80742003030306060391081c0d600030306035241030b19002d0318096900304100008144440c9001059154001038156840790300941c0b400e581251000f10368 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 483067419 1250 483066169 483066187
    0xf03040b100f0504090218181902060405090403171810020c030d050c0c031617130e2e050f03030304050d120b09090a0201080a140402040f060f060203 66
    0x64030318003514903a03005003000e90501901c035166400303408540040754005030f401010b20204141400c02105000200036000070410320035007010486044035440707000d4801c8415100301c0301014020010010b50461024031003400705003004820982c006001c2c1c241280d00301e420101c84460b90b075045951949000075065002248082003040c0c08407903807441c0081d400c140c62500e03216a207001c2c56a04070101e40d124404a0301c94078030082110014040350058a03503607074074441d9038840c1c200b5032a030490301e850407441e00d501115207840c2641d41e400c001f40d5004403491701c2c14880c1045c0c0c0c0e101401c0c102e03100c107050f0107520907081007889081d141c006031685034203182e180100b0000c111469001d050702a40080040100042d004100003d8a1405052110745200391591060042440c50a50341d080f00140c010b000b4801000074500740300701c1c401da80d80c2c40c0550321004c550003924030807031318a90a400a1000300b0f00500d0203070420692001c9540c0e001811a940d007076000007805180e07021a0250700700040a02c2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 483068669 1250 483067419 483067433
    0x40f03030510060210020d09083001030f030c0201050903161403031c051306050406021819090f0f060f0314030f04030206130803030106030b1207050603060915060f0304 74
    0xd4880b040600502e405032401e88041d446950703030000001090780c001a600d80840b000c0d404041c0140d04411415103628482d66440745210794101c2c1c0c00140203200c025049841d458981c414141d0354400d100392801281c9607003c0e1440032004030304905001c1b052007003030b480303441c10041030611400c0411031703030710662519400307040032401d40075801e000350020880d43d5082c0c100034001006007410310f000011181d8a512003108a80418900107014904100510081c0b0016402411054801d10000501030308507108000d400d1803020b2000b2020300c8a8507081211b605590b0024022400c00c410118038000c9a241c0403080b030300c06400c4001101d050310414401d02c94648a100100319400b8011440c003045c80d80343d92002c0c01144002480380343d00044d480c481c3d8000200400c000c00c8104100d03a00c958480001401514181c0d0306140035044803030312464119400600c44080387c1010740524a0743d100c00c020b12500c1000201b4132455611450100b08054541c2002000549200e0813000c0e160b0030a460110 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 483069919 1250 483068669 483068671
    0x5070605090c1c023d141c0e010b010207060311040902070f03020f07051522081b0303090607030336111807050c0708120a0306050a030c090504080d05040f030305 71
    0x3c018000000c61140c0295410170b14149507207581e03540e0381001d200b43c02040f10800181101900380d0040480c45001c6600c2d50720b59101c090418440500504008014035401c0700c01162040340140e101300000c001643c00b940c491080000703440916071810b81c94803050000c0ea40400000c0b103e65248170018802d050b4148003c0c59100a81d002610a1030f20342000201c02c01b0300000c0b0701111010004001a0000c0d0140c3d154100700e406504004c0f00603601c0e032030107466100c241c001013452401c24010b51014900030003110700341e4000410003402c04d500d58030110000e1481860488111030448262140307030707000c55190307454840c4d19010f014507410b8900d48020550344280791540640c5921540c0c40000460001c01503000210345840c0b5210004048128500b2035140c1c8440c02d140115000040300c6103d0744024a22881d4a0700e013404220303642c0d4103200107240c10348005818200c1061003413041c80c04030380005401030f02940c04581803002240313040d0201c43c0c0070340f41107889848507601c0008064042c0502 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 483071169 1250 483069919 483069949
    0x2508120714040608061201090302061b0408070e0414070b0a031506050a080702160b030a110a02030d02160b0c030604060504050118020c12040b0301080c0406050105070605090c1c02 79
    0x150032200440207a11180554000d801c01d01100e44009075071500c403c0c410000125414000340600b44113030030046d40714841664100b002d64099002e500510004004550898100710010f000203131a04020400c3d070030004d041100c60320900b00c131289500c01304101d00c80160803800e83c2c03107944070441c800203001c90b1040164046140791700710f0104030254008083e110101980c6c00c241d040d5554040c0304030305040030a03400c40d10b4040c0a40e0081100e5201c1e0015500c1034007003110800c18200e0120300c0144c0c9000350340890340181e20402440c03458840715000381074210700440c0d080350006803a60305e68901110480302554206c60100070081e052806002d0800100700c02e96041115504120200d1040000c013804c00c400580c00084959000ba400c2040b107950400c2e000226440b140c862024200540c8203201e4103010380b05d400b14400385031400d80714a5040b290161146c616102d041e94404000c1c102c01005414a8081c0801d94a040d860b001082d00305000e00c272400c14244000c034030421150900e03907450 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 483072419 1250 483071169 483071177
    0x31b0909121d131e2f16120c0804090f291207080a0605091e0a03140d0608010e100506281a040e01060c1725081207 51
    0x2c0c0d05107920b4803510310b8200c010710180440c05107414080901595071002c1e40c0046075103414070110303019011910301c0c5070004150812004074a117028000c482409507440825840c210801000c0002d0b80c01030980c41d0083c01c83c10702d0b42c134035131464075041c0041e001a840207001c5520b450320350307842c0300d0148189a4003100a03032003140711140690001c00c2d403030748416a0700d006544e003003d1444401c03c10007001c07004001c05030454441c20300504c1d1480c0a040282d468420358403800780c1a200c03500242107060b101c001540001c1c5510383c1075481c100d685149416114012010402203042c01c2d4145014050150041100210b8590f061851162030008000504070209161074244200741c0c2c2c0d04c00c09000002c162006400010103035105c5039084401b69485002400018562803c160280c000540304450213080b8080990b03985007020343d00c2c0f0200313180c0141071002000c0b031009210000e00142840c0b80d0380104881c1a4210760303102c041c0b03100c6c881000f500e100c400818820381d0303006075919055000c3c0e52403030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 483073669 1250 483072419 483072467
    0x908041526060901080607020c01050d020c07082104030f030f12050906090d0905030606040c02031903060302150f12040302010b13090c050109060903060b04090c12060c0315031b090912 81
    0x2100075101c00f041143c49042000c000b87d00c4049071040d4040d900081e40800907102d140b55a0345007681c2da4822101161014804590721199058047441503800b20790300542c00c0141918250790444041ca0900024400c2c000b040c41d0341522019140b0949108011400c020070850414030500c51a1400c54482d510030003114407403d00082d00c01247c81d6070031007800e5a0103c0c100c01200010390a502074454900c01d2804a00710400229a2513040241224025200e040b03a1035031640100989102d412030b40825654100604034500e403058858a500501030300c00040ca280f03a603000501d40c0440400201c0341d1030346540f040c030180030744031b84001c0040c1800d00301407074403d242c040040e041a040f8800500019510850282d05445a030004406558440e04892250351654128203c01c02452800d035082d601d000c0541394014040e10a4902440311b010800440034030315075400304140c0c0356201d0a0810b41c400000010141d0703d501541d43c50912440f055003038040c100da07008000c2402420551401e403039800c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 483074919 1250 483073669 483073681
    0x30b010b07170a020c0f100c0b090109080c030a0e03060103200d020a270b030a14030f030c040602011a0604120201020f0105090c100804021503060f120601150309080415260609010806 80
    0xd07405c0e50309549d2201002c0c4450b0f036a49242070050851010240009074001440c0c805050048014540c50485450b000032003e107003014159184024000209802a5140250135090303404811040a042c014a02405400c0030703030100f012052680e0010b08900443c0300b000b0507038400c10b038451600445584c000c01007518850002581c501c4409800f42c203034140e140000011a05c180200c0c0d5440b50701241c0d881c2e41c1e09102600c84d1056020703104d1000154038000080100b90a040102401000300820707090420341000442e000d07070039070400228150306c00c250580100080c2030140d82c0c440c10703d40003d007154003000c40500c05a4100b51300d0f0035041101800401c40180d0720300341c1e46000021180f80c2148c90747c1e14840804c03115040840403580c850002d039000300402c1c0c1c00080541c161288140020443d0116000c1542561044800144040780610007030240000200c5a511049114074000c2c0ca0085801e241090085c20304025008080e0044c0070040030342884402e5600504c0280b009212600e024 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 483076169 1250 483074919 483074927
    0x727050c0d090309030515010e0f060d03030209032410060c05150a140a0618020405061602010306031b08010b0111060718090f050a0c020304030b010b07170a020c0f10 73
    0xa662040c0c45a40d8901e02d110900d403080d403036200a1036100040300c640341004038601c00034200c24403503d41ca480b11a00000c24440c0e10003003540c052500580f40000c4007003181e030b054010350070144489801d44140340341d00c0480795902c100001100040107100790310b8240f844030919007060542161083c00f07600c440070300014000180c0e680d00c0030040c21180106464007800e08025003607968920039015007050611911004542c0320b0000c44009030a44500c40d070640e40303c841680038a01c94a032303000d0303800d1004681001e104400c1c1c016051051400081e9507441c1d0361411210201a46414040b015445043c80100c1091050410418003402c242c021400301035101582c07010700920200410229086842000140d407034400c0141c181540140582419450310000810341202d80b18001030030b00c0c0c000d142c0c4600101c11101502e801c090003804a0703017403140003c130301c0e80a40001c440c124441340f6180180380241020700001c0e21140d001d41000d120000c20041040614416140f10761074000d22001e00302e0304 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 483077419 1250 483076169 483076177
    0x6090703050903090d2a0b16050102043303180f03020a0215120f060604030b07050f070b0a050f010f050d0230100615030e0f0727050c 59
    0x400d15010840d0360701e40d076189081d03015050100e50068126454a0304003c02c0b001c2030900d02c0d8044600424141c10402c1da029051402d11801c01800d104120684901e03043c00f80c1d4604550150001515181e501d0800f002d14039007810302454220b0907454000c896010716080740c0d004010601c1c09000159a5060044501d40c500070000c100c0c9086191b22000c160003800400c0300d00380c008020010414641307294400315030011528a0361049248002b540481c9035201c1c8030700500015114074182400c640d560f00342c01101420170070600405100e000c3d03142944c1002000c040d80325002034111810a0b10074401a290040d02444c81e8401c08001801100c0541020f071b01110021030b01e00c800401c4900100d04000804044101c00822400c0701e40604441c0052800f40c2d151200229031140103510160340442d240d41c051174000c00c50b001d002c103141e030348282c0010420038083d405079504891140c65052409117264402954241d5011042410040d00c160740340310554a10303001c1c066450850342040c91442 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 483078669 1250 483077419 483077431
    0x1006080703240f090b1f051b070618080c100302090d060203090609060105090c0904110f1210061403040f0303060302130f110a0c15150e060f01080609 66
    0x50b80320404100000003028000b01040b480004118080d140e00380c0c004080c000b8003541d003400341461061040c0c2e040400410080c00340309030211920200300d400031140d0303a004d001c0d54080301c00124043e415100040c00174000420054490f40c0e8140041c0c10746416502c00f0741c1c018010740d088281c03103001c940c031180410310340c100380f41c40d0050b0769011303c0d4000b0302814903040d00682107034804070412080000006040f0f0040020000b100d07c1c1d0703a42d46c000c00450300401c48494040c400c00340152002810705401035400800c0171040c0390b0428108503101601c2d908544c80c44a01906040c003840036104403100c107034024110350b00c0c059000e4001c5c05807910880c400907000034104240401c942c2d052521030b50000010311340c020500d800c0c400d14030054601810f10030825620941c50a0100c000c158500c004030340d01e20400d629101d0500460303485001480400f107200c4250b00391140c0781540c0c4a44542a00805002c150003440480d00704103040c03261140c00b0030540c0341849010002c7c040c0641d1000c0c5440d0b4012 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 483079919 1250 483078669 483078671
    0x703080f06060703140c0a06060305070b0f120402010521040204050903031303110c03150103120512011202040902040c1d04020f030f19020d0203071b0b060402180a1205061006080703 80
    0xf0082105d0070450310914810101a00409000e5401c0000ca5000341044901980c212a100380d100e03401262103104841c032510704040c0401850b250b0a55030074617564054014140503050116a64070420420240c84100c0c1040049000b040b085180078420113030002c54000c000c5095141803158991035901d0b401c0301406020028101c2190108100a41804090060300743c620814810204e402410028041107c8109220b059103507054800c0c401d5404003100c000204403a40d184c1000341d6840070440d6030903600541c88011200141c0c40d5409071201c45039440ea03d4418441d01c5900e03040350901803604032881140100045040509550705480d00300000855640d01a1281c641040c140054000c02121050000c9070300c841c038680c1540590300c00c001503141d1341800b940907a80c040c684124403100030404050344005c25030505007a409446038070162903808c0c50581008000551514141d8002c1d851542e00550000400106001041e0421306a03a04000b0032130601002030503090000f040c10b0109 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 483081169 1250 483079919 483079937
    0xf0f15040209040615050c07060302030603030a050a020109170307020d081e060a0806010f09050601020f2a0a0f080c0612061302070813031119140f03120703080f06060703 75
    0xa66599104c0c2006000c007080f00904403104000240958009802080c014000c043c00015102d00038001c032482010010081c5292620324102034800390415035110007150341c0d4441100000340c4c10010781c0030000c0240e00c01600d80c50a0302e0000c0c640b080c0c800b18242000540000e00201d40042180080d140340010015142d07942c503107020070141e1741903a21001041c8078950002504031590451401522000d60013848a41d80305801641e480403119170505103503010307401d01003001c0340c1040d40ca0840d50403c0c445154038440000040c20100c5140c01a85201d0240d0408005006080088030b821020a440741418040c0500b450a40140700906260203070700c42500b090b0468016a044130001907101c52031603241c0030f80c8001581c00442a0200311400414020710160910b420a084a101050035001ea1540c80c2040c8034500543c402291590f0481c110250040342e40d541031080c0d04040c4203d10a194a90401c0d043c0141810005001080d201007000e0074804c0d0350b195101241c001940504281c210 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 483082419 1250 483081169 483081187
    0xf03070f12082101030b07080103240b04021b07060c0f060c021c080f09120f18030604080d0b04060303050a0503061206074e0b0303120f0f150402 64
    0x2041c07003080c100040c030002d800e1a140003d00302c006040e050704c1c028101010203070380380c05e41560190420f00001e0081e08100c0705c1200500340807814050004040100801c4c20b2400401080580c2c00a220010104140755018004150308100f4880185154908003030311803910707103524503108207069001d03100c0d9440b90141d4520500810414041190103851841c507440c1c0d54200520144058400c451908084000300e03112400001d8403e0314059803d030007501c1c11942e9034044d14154808002122681c03018000a03882d0b650034080c5610842c010b8108030360f90303800243c2d0f040460b00314620941c030031890b201e07051000c00d030300c2000d9802e5041c81703013070465403510303030400103803140c0240c40310708c020b922880b810071007050741c88000410b58450312910003441102241c5111003403046400c0d119090b0800d0101104c001c50214031404806d107180c00001160300300314000c80d0856000300e035044402e420b440c0621049020182189901450300281e0340d81c0d40c140355051000c0c004080044500c959000714022031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 483083669 1250 483082419 483082433
    0x60303071e030c0206030a09050d1103030a0c02070e0a05090708031213140a11040b0307030f02190b041e05090601081b0904021b0f150a0f020c0a03020a020f03070f12 73
    0xd150f580080415499141201c140c901411003008100c40e1801100390b001c00960052440303206540c0340c47c01841c00c660b94070020344014a11040050210301c1610000504040340d00c80c154024080701310f010075103241c1032851a1a201041e4400c590321f40c0208580a100d040f080701c020f07003110309860600368508640c24061b5524901840e01d42c01c90042c01082c104101c0c2002e056070110742e050b1014000c000190b01010380f1100e903480050034084000c0c41c0c020040c582640341084d540c07902806028666100c881401c42c5030001d40003443c00800300125000f06c24000fe120400400e002c41780b8040754035010f000203112140240080c4802c0d440b844002c01c1c4800300c0c0f410740c1c50340c00e40a03000f152102204000c000c0d950303030b40b20311111042c096a5441146907102040c42d02c1451080c10007150207494298034180145000c41810410940c01d001c0c41c408070301c06000a40c442c0d4065801800c0c183c61500401034590780d18a9400c0c03095025400c100003020790480301c901260002c80d040c1400038580e0030310907 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 483084919 1250 483083669 483083687
    0x2506050319020a020a03020d030b0f06030703090507030f050c04050103051903051908100b1213060f1b03060f060212090303070b070c05010f0c0c0f03020715030c08060303071e03 78
    0x24001070021480a4003c2e50006903543d20900a608490540c01c0c50003041e011512100c1650303030010402001c54905e0f0420a00643d00a00386160004007004a9111181428455003080b070780310348480c0314503092200030052200e21400c110750400455246996580d600c1e0004103241c0c00a01d107544552044c503002e441034039850309011056441003038502e94024a550011030790404080040007000c40c0d08401e110688102e007070031000120080c3c550000c101508a0504401c4a03000c0e00c61a0740301080c5410f00a1559400301b680300342c4a103507803105019054407926080110342c4030141d0001c005c00360340000d62403641190041c82a954040c1d442c080b900b54071508101a0501203001c0030301101c1c560282105900c81e009030003c200c0400c04111000640d0001c0c5c0600c1c0c0001c4c040d0007581c020036100050f440c1918881c0c01101c191a54440d075420700102c03240182e0012075620700f08000f41c1600003022550104085015610b4803495607071b844401016426600c80071a001c1f1003c40c1014080d15040c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 483086169 1250 483084919 483084961
    0x18011404020907020705030f07060306080a030203120c210f090604050c06090409061104170106030f060203091009141b0312031e04051605090f04020420030c0c25060503 74
    0x952286001da236082541c442c1e0030b104810000786410b5000070250008030700c040b50241d15074065454405c480c0041080c460000e0040b030316400f0300f0072294070400403c8d41e0741c000f03104140001001c2c40ca014100c1c0c02e400d1400408104031034004c0c0342040700103100410044003001c0112151a103c0086c4408203004100c580d00082c5074503e40f80400605c240a0780150003100d0300c218844242d0700c00790300e44a007038542c03922004080c840441020030006883e0b03000b81da4440d08840459202550700c4000c1003c0d9407c01e1700994401208580b0170f0b00d140410b02c4040400e03a0040010031007041280c020995401d010103c20300141c40105c00700742031460b40d01ca000350002c807251318180c007428141409603c40411001d13000702400c05400c006880d09050b500144500030048865010303603502c1d000e00010780207003401010a19030449501c1c03891401100510b0082803d41905501d91200c0c2d5019890903491246582c20144850a80100281c1c510b5082098410718580700352281c0b20b4a1208144504000742 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 483087419 1250 483086169 483086173
    0x702100f020c06160507050109080c0904062d06050a0506040e06010c0f12021e06041106160804080105090105010b071401140703020310061d33031801140402090702070503 75
    0x103c002e031907444c2c010f000100d0181054030101b50703a41c4010344403400c052117004015001070b841c00781d451400900e001e6003e401454003042d590121160070000c3e1408162410180b4000e0749600342c40d803001e100340c8001d018140c2c0d500813468104400243c0c00e000d50321803400c0d4516050002030160748500203828105600c5481c201d880744162420340f00c040d003480c22800041c41000701d650701c100381840594038009501400b401403500d4a03200d0002c440d9a840d0065003003003042080700b00c4070710b8201c0c1e00c402090252000340c2e1a00d0030200c480b42502c20140242002d0303814031005201340000c0108445410b54001201011800100c40c0180544034094440c0c4484021808102c2c455405800a40c401c401c0a04201c0cad2440e191802030b40c41e0b994400c2c3e00c81080c40882340b140011705200c0c0e123100302440c2d1414003d02e04c20000c2d4081480b000300d04003003d143e0708007000740099000000c51700c1800e42217090090150042d94200e0407904500100040c0c0310304c00c84004540031500901c101c0d0003610010301 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 483088669 1250 483087419 483087427
    0x25050414190608180607080c0d09051c02150601090e10090207080a11121b070e070903020a0e011a0d1e06060f0c0c090c090f0603061a0702100f020c06 66
    0x25000d080c9410031919110134481070701400540c02c50104e1610310521b41519284410b0319082d8408401750844400018401d54a4404c0070100302c08000072042d00c0e00904000d5100c0d84100700080c1485100003000303078220301210a00110782e17001103862040e2044242c03048115942d2034445540003403107a10500b0b020703100040e1041800302110051100a10325115908800407a405046d5102d05616041c005618144907000d02c1e0580369a0244160183c142240c4a075500e840600040b02d10664250020551400c410021410414003040007445403001c00d50141d0725010034000c02180e02c5041601108001a04009083c200c5d400401c115210000c420783c00080d14a036903000700460300030700d00401c0d032690340c62003040c0c03145d003a01c2e1400c0e03400406220f0240c60320380c0754005001c240700d4290502c541e195000c2201d1400c041110001c100594011a4491501000c07038001c50381198074040852003044420b01580f00d40c8880c0f10f80b0030084c60100c01c2d0032142c0c14224100030011003241c2d030000c4001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 483089919 1250 483088669 483088679
    0x1f021c090c060806060711190906080604020a06110a06020f160b01031403070503071b030f060203070806011e0f02160f051e030712050a0605040305032505041419 71
    0x30701c030300941e400740d103425449440d0201041503501891400922440c80070030541120306000c008045d503421400000c005241d00c421880c4266289030308520407940c005410401540750980302040103000c1410510710381d0186d41c40c0c20340c4507000c0e4100601070540005240d884105904100e4032175511040c090b010148242c07a003003080740000c0c40169104407807890410340a80000c0100c0d00c400b940000154030300642c41e56044c0c00c020700c14000074803110f4214030010100d081e81840f030550a2050800695a00d0890000703088ca8201908440c108030312098001c0488440d07000c043c2003104076051510b80702c0c4d608001246081001c42103404000c0902400080e6403c50780e0018090b2042200c1c010311400404001c2d180410011a1742d0703606d5406141d00304022341070340300b070100064010030507903c0d03012458450100b138520a8800f100001c0c1c00204025003a40d03034501d0705e61801104803e1201d21405864001e207035000351301441c22070780c1c185602c01700c041d610500e0540300010003040300801183d031a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 483091169 1250 483089919 483089933
    0x5100b06041a2d07030f030c120902060912030a120902090106120605040612051506010503042009070e010e150406143703050402030a0f0203030909090706020d021f021c09 75
    0x4d444110b010411000383c040b0014060302410594038044d42c0c8071401d4428540e810000741810300810391704550100048031040e21490111031690b0790302c0c802182d8a528040c1c0003010040c1e100d16050382207191000c01d01c0185d6651030441d0466481c1d10341601c5501d1505252f000501c482c2d880303164018506180090120044400b00103101d0007882507561b00c40c0a01501c0c20445021107445002a00400005000402812168803404214005130601580c3c1e000440e0142c4804e90b05100416980c04c40902035680c05401032a800300151014503011035089842d111078040c0d4010001488038516240590070040c1003070f1003640c0802c61189649403201c68018044418040c4031046d02100241074282440c0240551070080d80d000c0c0007000c800c1d08a840380e01469102c1c06080b43d02d80030405c02c000003a907554205038018482100030700211460081d01034904654217828038295001010f2411003920301e048014414100f190f0301580d035913140e1900c044c94581c54095000160b16042c000c000344803913 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 483092419 1250 483091169 483091177
    0x3020903251d0601030914010207060b130c08070809330606030702031611042d0c02030d05041a0106080a060f030f03030b0f0a0305100b06041a2d 64
    0x6108110300c5542e00c0380a0004480e00c00c0d000c640e02c0001c0304001c43c1d042c1d4031a900c20340c0b00d1409240b0100310480080030507400d9a02c01d200541d94592501d410f40740906d002655403503503440007441048020031054001c0c0c68210001d00c02803d0080007030014000c14020b0054140f10b9031002c1c55100e0110b50074405c1ca080c41040b04001942071080030001d44581801012170340079034803c3c1c008604090b124079807100065661803040300d9582e001002c4003501d840e14014a1900a001e41140f900141c142c0020000009190740104e1602c0c184441c03a103210707801008841d070000500c4408103065886052a0006520008810f0101002c0c44000514294071400b2240941d480003000e0001d45d036604029500200c0900024001e201503d9415001902a50101042e820040c0042a00282d290300261280710b03542e00580d2590020801105c2010742071140d8144c0440450341c0074141810104100091140c8040c0303012407150010f08490300c0d44c200c070342050820111011551003142890288041d03908 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 483093525 1106 483092419 483092473
    0x112020a120501030f06050604050618040f0219060e0105030106050a031a030f0102040612021801050d0b191e06020c06090406150206061216030b040303020903 70
    0x1c03500425008501035500074207984118100b6105846000b04610b11851500e0200891550380116a945a01d00c41900e0390f1190740c2c2d458902d0074104803942c040d62202e03070b0195849030b408003940108203682c441d40d07500240081940040d40c25020a0041e0804030b40117002d110711a83c4a6404040c4ca8010248001418038212002c81e0406074010140c10b0140d40016003400602e8004044c0848044000001c51030441c400c2903c2014000b4100c13032030304001c40002c0c9410b00c0c80d46c1e074100e2204040b001f820101c41000d081080c0c12011054070400c1c1a060aa01035000c5035005440004200c610f03d40240c4039500c02ca02c03c1000c0c1c2ea0101620301d9009135201d07008501c9402c0801c4000440303106800070503031400c1600030880b0501990404130031540c8108101003824400c3d0408000b1251700403840d82082d00e0318902039019010701c0540c59013500c9054900c1031200b800c034a1005580c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 482913669 483093525 := by
  have h0 := BRFrame.cov_init 482913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 482913669 ≤ n) (h2 : n < 483093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
