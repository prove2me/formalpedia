-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0106
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:52:22.810092+00:00
-- url     : https://prove2.me/submissions/e2b3830b-7ce3-47cb-ab53-43fe9aab7050

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 18884898 ≤ n < 19064754 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 18886148 1250 18884898 18884927
    0x70c090f020a1101140109051806040b1b0a020d05071a040b01030203010e010e150603161502060105010c0206120702120f0414010f020a030c1704060806031209030c130b0301050106 79
    0x519611030f03c3d200414051102d1142c000005d00005034a803542038409000c0141541031b41940400c41c80d1010b60041015610440c062160380a807810103000031046400c00106581c110102048401017040e000119000300402501e030050fa10f20b03175814100107085c4451400740c1500c403000140800d00c407030324000d681070b04e00841c000c20090243d40303255400c0b601480761895103504113030a0203181102911503560b0028003d410317948a010810380c0c10300001442c0d0444902d0690305185540c80d1541001312070701406007800c04221206079030b00010401c0c024118000c094070418800500858400e2001c0c201c407095030340c4060b0700e501844e03503a074050350001e01074213407484ea001100e400c4640c070030f1980c0b010b1840c154025100c501322503141100d6403515070038291340340034400c210b1400c46122b40f0001c20007080d2903560081103007130110405003001c00030025210448014084122241d9020920b9081c0580c1104d80c007004513010b140010281001c2848070b9455443c1000028100b034121042800548 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 18887398 1250 18886148 18886157
    0x30b0702031b03031302060d020904050106050d06050415032604080717060606070f0501020906070c081c051c150608090d05070c052704030f090b1e070c090f020a 71
    0x39090a040b40d502d000441d43c00006044a03d1000090b0500e600100418a1038403005803400c41070401180c140c400a0780101c002400018090b60001d03130a00c1860301404046070284985910410645103116a5000c0501000e09a41c50100c000c0c0e20750016031400c640c83e0000319200d69a500b01e203034588045201d01c00145840210319440720f28041141c52056400500c1941000b610351986141c100c0c010004903055942045030300c546a4500b0050800c2c144107110041405007010011814407aa022000308203c4090352400040354102043e265481c0094602e81e032588045803000380500b014441e41903211070a554081015548014035a105140d04070803105101a440e03811102e52284000207005458a010309001758500f0600008118100c02c0c0701003038968031801400c01c05081690110040f444010b00e015060340c0007070480d4006c140c4000c00703e00f842d009502502d800d0748d260400c680c1c03503e0000b0b80e4200300804d5904203000f6000145042006010500c1d40d00020361040304c1c80c03800724 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 18888648 1250 18887398 18887437
    0x512030a0e030301050d031b05010f020d0e0105090604060b15030a05040314040609050603100308180102010c020102070302150601021f05010f050a061215050301020f03011503050609130507030b070203 88
    0x4001c000201c038101d9102421804054516407030854107080816203044c14190b0244059010607000d000d4816902010100160380b00f103d14240170440e82c003020b901103181d040c40100004e40c3d4001c50300b00c1c2d0090300303c1004260345c0703a0310000555101c0b41c0c2480707480390b41001c41402254429648030522840c42521b905918034010f0340e2002060041384210b10000e0490340050065083c0800515002000140c180c0311b804e880340e8030351445030080c136144c031070401c5c0f0503000b0344c900e690902800000c107020340002c501d0302e061528029100c0000800c00c88841d44010b01040c1103034800c00c800070403060b40d504111412140000c02c00041d080a20880c1851850250089040d142048444080380c4554031040d205990100040340074060700c940c1e40c0350b1030032100c0000030243c40030300003400d0441e00110103a940c0d60500800250000a00b50440d04041c502010005a070b1220f080e19500081101118803c081d001c3ca030040c0b801441c0d4100524080b0040c1c14070140c103400101801c6448031041100d03840 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 18889898 1250 18888648 18888671
    0x30812010522020d0605150702090f010f090e07031a070f0206070c140106051c0203060c040e010608090a050a11090f07020705120705040e150a060e0103030f020102070512030a 77
    0x1403041aa10714482c140c1203190340030081c40c0c941c028843d0048030000800e226980c1d100040782901e06000402522a00080990031860001070942c2c1c40b613040c0f42819000e50401401039181c05e024059134801c035a452481d00e1300408104100c9009513803104219020511400b50142a85402d41e0030b4804144400344e000505400403030b120303105045556845995400c603031a00070013210150b61845055681d9100031446d9207a40c65030178195010304942042c0d0303454520606140c510018084040c011048c4410300c0a5051001244c0c1114900e251414494442c0c00319a8103050320403000410710722551b04d103001003280d440c5014803028002c4400010b00e42c1d840c0950104500111703003180045c0c10401051200e4036040c26481411004501121581911744011900300c07a0203500c1208142e0003200765080c02e80b014031000342c1c424280001409807a150441844c640c0f981800014144101d1030400100c5a100b50305862010f40c10400b01c4d800720f20050300c5100c142d4019200d0103051401c10048250 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 18891148 1250 18889898 18889909
    0x30b131d19030c0209040201030e0604030f020708030c03040b031f030609020405010603231e040b160f0e01050d0e0114040201020c061303081b0d0509010f0c030c030c060b03070308120105 82
    0x21802e81646428038402d02950800c90440710051049061598400d5602000b0100708003aa1085d072081c1c68811408401d0b40d030184ca45021640210003aa004001c01d0410702000300544003290000c114003901d0791100281e0300041f41042824844030503840790000705018003a040348500c2802070303408025030b980b1044101c0947d00000070400d8000d0b45c2c0101c5401e0940204030156000003400840144103503803c03191a03000d002910b0a480d04000700303041c0304c0001c00050b070f81c14500c01d60f41002450f03140c10311005002c1c00740312241c143c1407250102d030040320b03441e094010140881601000300a4400d02c1003d40300c4030780b03040e00d0a900502c83c1c1c2d168082d0b64103141044070a500c3c240d4908500140c40c0d584d07600e01c158802c0b07183c079080d03101003000c401c1d508500300859005807900303444140e03c03680c00d00001000f511854151000f000034584150000c2a001200d24204617014030302800490041c1c1010006408521415500343c45681400010f009130300000e048180c2500801e4882a6600c504001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 18892398 1250 18891148 18891193
    0x10204090605040501060c0f110301090c080d08010806010b0306040f020a0c1a090a11130204080607140301060f050a03060f0b1c0605101b0204060311040f05010f06030b131d 76
    0x1808180702c0064000410a183c950a000d04d2181741e25480f04009c0d50042800e640d0b919000300d42401c403014052141241c2440358400b004240d25100d080366140c850440c3c1e4401c410300c52007080140c00030103d0800c0d2102d80200703100c1c00d407282c0d055603a083c06100c000c000803c455000d45102485008a000c202c40f48800307980512007440041880305c410b5264800300380d00d00b8400561104648040c3c070504119130000e4001800310601400f0f49151001c00904101c4c104103490401c0c1604200601105030400c15458282c2550300e0100e0703e84405d40400e4000b04055000030840301c40304100010221441801020280d0b4020302c10b04880c200000b5820546526006103940f10010444403000303a4450f18106074813810742c0c09904150b00b5680c001c01e08503036903908107952007080c05140c0001400e0a00401c210b80100c54810402503140c00a1070b4190041409410308050300c81804914a46d41d02107038420080c000c20040002c92054a0340c40d0b0100d089031244104c44c0244507280e41024528002036 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 18893648 1250 18892398 18892409
    0x3060c02070807090e161d01080a03080406110d0f020405030d050c0601050906130e01050a05090a030c0201050f07081314030d020303010b13090903020a050f1209090a1409010204090605040501 84
    0x10112513081c07040e010083c00e0410420107452140035600248a1540802c4500400c520020399000c20442001644c007408160800541d40d4000802900025400701a03194459088840000c1407100c20309668000c2c41440615003045051044101201600d40d0083c800c44500318221105030000b4003090b5064052045010882d4019000400007802c10b00c4085a010000800350029001001520b6040380c00620702481261f40d074070200100f81c95984a803a4010000a008101103c1e0680d4014001c01a00300000d0422201141d4000840b0101040d40d19050348202a01d440b440c1c1d94900c80120300540c411102d400c2c24030f09007403240d0306010541e2075140342c099022754903680c240f85080d94142c1c003d4000304080c840c070381400140a04c01d4490b03009030b64407983c0234092651706403d2031450240e03e529a0b00d461b8004075a0f03500c9119280045640310881920540903507039402070300e94020101643c0c0b011100007003104000c0443c0d01903008ac0705a80c07102c041000b40549400c03e000480c1c000b402035 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 18894898 1250 18893648 18893653
    0x6060c0201021c020307080d020a0305060d080a030b030f0f0105061309150903050403060204060509010e0301050c040905040507050901030c03030215150f13020f1e07050a03080a0605180103060c020708 88
    0x70030110388081400b0380b1010421340100c0b0f1810400340c1d140d4407917500061040c5007042c1d02140702c49000e640741c080d2907000042203900000b09a12038880b0400382c810701c070690003031560320540c5070100d46091080f10301c10400001910f40704801c84805901030641142c00034403800b032888001a66142c94400d01d002c4a4008034840c040341c4002e4010001000d605606a0034020107000010009840d8001080544030302c0d6580c075210281440058200840707084814403d90501d002c014410070400c050f076080b05c040010101c0c0b141c4503820664104840758002c1600484a040044140300009200b50200c80c4a81c1c00ca80a010740403161444418003520000a244402c48490f41c1074035060143e14400f5500070111040510a2692241260311103070320000103250115085480d0002199449100c016000045e0310f84001c03607036481d8543d1501e0b94010140302c2c140c404100c611031181d010401400000d4220300143d0510035aa442d0188240f04c2281d03542d00f00740c5008605403004c58030b0340840d01c04100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 18896148 1250 18894898 18894913
    0x30c03060501140307031409010207031b081b0f0a081c060e190204080304060504050108090a0b0c0705010e01050a05060a1a040915030f08070c050d020a06051c05040807050601060f050d0216021206010906060c020102 94
    0x81100150301035a90041082c0f0400e03844c90041d0c0800d00511100e27901c44c044aa65401c048006946046042451800c009240c050104607600c0d2107415140e010304024281c2c11a0300326020004000e004a80101950f444040b0300885c2c001d030007200800640300244ca0369860f9959000032113540315210b000091031882c0840c0420074401ca801d002e000c0c3c2d948240c2c0040b84443c0c0e130b90051401c44004441d1042959210400d00007117041c40320908021704094101c0d00c294185030f81002d42c4601c140e114031442c0d1540c81c041500c0026021908a02959012400e0b410100103810612050f42004506940316511500d000503145418520002d581d0b5016041c52119454600c3c1601d03a6001454aaa407240e0001c61021001550307224203407050303100d0302e080da8880005042091820300c0580082040c480302d84800e04441e600310050761500c4400e901c0c0075903075003981d61106420114888009420580d421202081b01c0303030204a00b4161080c09008000440e941c000c12103104180b040b000e400741c0c00600 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 18897398 1250 18896148 18896167
    0x30207050a1d1905040303140c07031b0602090a03200906010c020f0604090c2003040e0c0c07181a03060106051602150406050a030c03060501140307031409010207031b08 74
    0xa425405000f900110111181002440042e500112811400650b17a802030007100030030718500c0f41c0c02c07916003441c060500c0300c150307805081c281d4122001c0010f4004111564200605901190a440700c0982072821040d41c915094102802c15060520030b502c00f844545c20342d04041c032446108542c16501c504d12280c2507001d000d081440c9000c0290480360802c17020601c0c2141d0301403100c83d1506a5500c0300c949070001844181a80c42c58404c1c94141c004000400817101400e05603a04000e084212550707171100c0c0f0303079050b00d041d00c0c031b070300015080c9207200080b5401d172500d0b8824503100c0700c0c0842c000305082440d010541c0b00d070024022540410340c184103108040222b8603410300000e01c090204070b240c0c1e000c0c1c0140c400c3c039007055100c0390001e41d00141541c046a4140202c5949550508050040c1410100082d0500100380082100100d0100000e800c1c1c0d0721030f80104c0312444c007040d200c0015003400280c0318080c6d4030001c0c2c140c0225402d03a41c40001e07100100340c682d4030799422502c4a8145039011 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 18898648 1250 18897398 18897449
    0x120601050702040b0913031407030c14010603051005150108010503060a181401020702030706030603020a0501210606020c04060503060606070b0403090b0a0e0405070206040f0b0a0207080f0403030207050a 89
    0x1c40c030582e0059a10001002e154907100c0a00740604460510a03210700503d2070b0003481c2150342500390300012401d208040010f0f80208514044a9000810850091016480c0360040c0708540c00030302a84030301340552641d94034a40c00f2900400344890305203129400000196080c94083c07181ca901a480b01700054800041584079014020345c1940c10624080951980c01d03030050b400100840301d95000032481c0462a04200600040003107080502c8000e155400241004080344200c0d4140410f131480c3c1290200c2c000390403442c0c110007402c10480543c440c4402582c6003d0201043d029500d05000800e00c2e1a0000d21036125100c020169842d10381c666a407802c003074502030004c605000c901d00010a654000d0030181103400999a16070548244031010072082e0740002c0c00041c1550001001e000120340d8807041004002d40001c0280305035261042daa4000307208500c005080103101180c00300703051344ea01e00100110380c069401c40704002c0d210b80c10012902d1080c4225803c6880c00590482a04e201c0c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 18899898 1250 18898648 18898657
    0x1050609011206030b0708010e090c010503040f0203160905100503070b0f04052205010909110d050f0d0305090c010809070e0c070609080903010c0302031e0405070503010e03030f09010212060105 85
    0x600d00441c02c218404005015510903030002c5580481c0701041203202c2c3e0340410054014081445008034a0408280d01038840103205079071410088000001000c0c080043c201448043d80a01141c0844485903400d0655840c01d004820b8050708100c0441d044d56440d4070a001075842c010040c1071203e2408001c810f056101200951800100f4080060540e0f02c03001f412501d0f00e00d0818440d03405c00030345141d0044540503003143c14040e2901c1c4514004c1030307100d824404100d03019104400c2100050a1092900380c0720b007900c25803840394000362149650b054000b54054407503142150340012800c001956020780445406845904c82c5808210360050030300026000414605d0280c500512622000c0584204140a03200c8950000d17452080b41802d20407200300441d40d00d4114294107052058407000c4540724aa00e20340c40100c1c0100b8144241401901c0081c00000c1c000c11200e841c040301c5603160b40003158540780410034000004c0f816503040c000c40b20b1000c0c441000607039079602e401c01034600303401 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 18901148 1250 18899898 18899917
    0xa1d0301091b090f02070807060203060307050a0603090302010e0d0816110613030e030a0c14150c0d0906090b03070503090c040e070812090306040803040510020301031b05040212010506 81
    0x4981c011000400e00921002010400051155901038100100d50050351201818000410300c1004030501240c400025074980070f0b403090f03015949403200d40019150031a140c105076404142100001100390301075000c403104034420f400034040c070b5458501c169110010030b070000020070036190028140e81080c10001865218501300a80b20155803034000d1f15002c000c4030307109505829080520181074228a021542000450007000d441c080c560f162200750740c59114000c05200c90a00008060351030998401190002a141944603100710240a0380c03440302c0e2041c0d20101703010700c00200d1218480d42069081d80c03500b812071440d549407044121255840204980e075a809680c0300002c56a4a83c01035a00d01d0005e1801400c0c410304203c001d600b01104c032601d41c0380d034903810059010380d501d012079841d5000d40c00844458813035031a82441410554000b04c200d0100d480080080b082108141d0242d50001301120880003082c2c07076800780070803441201a60380d0180040001009a440d0242c010514640c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 18902398 1250 18901148 18901151
    0x1030c090203040c0e01062f100f020c10061403060903032a031303030507180e070306030b0408120106081312020f0106080106080d02070e0a0f060b03040b06040507050a1d0301 77
    0x7595a0b0105c1950341080c3c106400042c80c5600445088090001c08907500e94150f980080d1a03032040201581d41d2030315504401401d4a038007459500f0600740d81030b100442c030138805880c0d0030000c43c05c5140003841280900c10380309000350154005c0d4240010894400c0340e00d04c0c000d61954540c954840a82034003180707011203580904681c0950b202010010b1401410a0101044040c40b1031401500340c03500108868104250070040d41904104110003c007100d1001000207503549030700c0012000340105410180810071b0b494180400c1254480007032410a5045018450990300d403c03084601041c190740c5041e0042c41d03558071001040035040c0c0c4024091090048816400e00e4840650948260350300c2840c0313595590508000e080c00c148048038a00301c0c640701a00340541004100703070a20a0107044541c54a658808502459280350310480282c440b010525840385800e24225507034000c1194441c0c092030500c0e011032040e9002e0400d941094415403124007074002070062510640000b04030030b03076056 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 18903648 1250 18902398 18902423
    0x4080906040905060111120a0315080307030f020f0a02060306130f0c020f19050703031407020301091113090c15120504060e0601060504080c0405061210020a030f0501030c09020304 79
    0xa40e6000010710003481d02c01004200c07850700c0400908107030300310008400c00360065050000c0e403a1a8074111011418142400a44004103540500310302c105500180020721000403407005150700941102c0070700d10141e0232149a03101c001d0007a502c4804101c2e000350080428070124000340b6048118600311700d2400c0e0005030740700c203504614003520b45100005001d0b8202d440c40350030b8440c05100c0f104511040c100d0800c0854032540d0b07020f9443d049403001508000f482c000c19011584104c04503010150014000c0c011790354907042c5590744c42c42c040b510302c0c480d650903841117124a9103070282d40d00698010383c41c606494681a1114458040207454504200c220321160684809500c106401503003d4240000e14091a60301035181604c10780003074086c42401e010030082e4080000300c0201100094a0100d02900c0303440104001ca444c005181c5818021012074040c55261b45e400b526091319035a8050010408282000f011245d0a0001402480c60030b03a040c000101d407600110b802038810710120400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 18904898 1250 18903648 18903667
    0x607020a0906050f0607020303030a150e01300521040509010e09010606081012020f030a1515051804080c030a0206010510030204060806191a0309010c020a0203070e0408 74
    0x1440c26003011140c541d6a050600407420705000c41c1107040026505546420340307035000a070356404010030002e030f01a120380e00300d030110203050041e0380288481e0007101c000c1d507120400402415456449140405c0b40b8000781180e560a9629101600350020b01810005900700a440354035064800e040403110001c00002400781c98146074203000385410555a242400c0064a8909503900395110302c00700300c010010b1000400303505440d80103d90841d9050080303865184046000b920110030340d41d07410b005214260081c044541c540304c01d0303050705072010050709a8900045444403001d00600703400100401200365031880303a0924680243c0078042882c02c1501c3d5107200d43c6107510089034000183c1200340100302900341102001d4010403917007029800c06041c1100101950030013050b15102d4550354003810407800c807040036000a840264400040000c12950004140e0f00030b40d0030de840f940c130300050304074590f102040c1c0c0c081440d40180078106840c900800000e40d400d0140c820303902c03c0010090581d8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 18906148 1250 18904898 18904909
    0x402090a0504242003060922141b010813150b03030415080f010e0408070f02130e0c04050702030316020c06131e0b030610020c040507110d03020a0518060702 69
    0x8902054140200320300e0500d210140c8031200d03000e410340030080244244004ca1f40c0725048140d01c04003046c11000a02c2e00390f400c0d00301d25040c050300039000b1000300e00004080400400c1401c551500034500c90005105403004641d034550888510302c000c0032401d0440002031f100220b42d0b981001c4850080b071004503003c0041c1c00c60340550322142146a608001c04a51600821440c2e84034420040c11007066141003440c51407201c0c0104000d044030310009010040106110b1b00036503041c0c01038180ca250003040d003041e0700200b07868603071544e4509c10983d2521a40c5824010340380305466940c0070f141980c0790035114820280444042c4e00560085004000c5070703032603207405080c0d10488401c45882d03042c0742c02c07154914150710400e400d244c500004c400344290b0398a6000c0b81c0c1c101100340c03014050360981e00400c80c20000201405540681000c0500c800c0f2503200d10101424030a4000faa000c1d82400c0100758102e10980d0300e01c6021410a102d0a41681c0740e5a803440c1071040040e215610b0b044243d400038a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 18907398 1250 18906148 18906203
    0xc0e070203030f0a02030103080702010c080d0504080406020c030a11011b0f08031602210307050f070602030906060105131e090c0201151505040308090d0f1a0f0402090a0504 76
    0x40141e10100401002e11030700c10031643c2014075940c0451455040d030711000405d1050f404040d0500183d441d11604200c2030a0449680d500428020441c0d820b1a1a140f03129a11034400d90005118034110f1111500d4041a06803000382d10940d001d506c16000da00660740200d084400f08010354100b1145404240803000000301f10f48244c40c001d58916013604184403494040040100b150301c0107040c41c41c2880036181025141d5006040c40b5200d644540c0229001c0c0318030f2401e045405000b0900608020b1160040c600942c0c9840641d12180c0e11070004440a005101c0c400c2002c400c162010040440c0d0785040300c038402c1d1000c411040e49a00d07450a50161a11409a600144e541c0c4841008601d04262101c01811100e1041a0f8000107007000900038051400054100240000d01124640d24810300d56201c035800b400002c0c000030941092800da0700300103d40382c1e402080a0000e0240721040440d10f00c12940288403d01c1358440850300402800018001c54110018506000c260303c0c0701900403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 18908648 1250 18907398 18907411
    0x40305070f080408011401080d03050615040303030f06050f1c02030c0d03230301140103020c1005040516080307150203040201020109020406151d0108010506070f0206040b18010f1b0c0e 81
    0x590303e900d010051400c440200c0071820301c09072194014044402c02042e41191800585070210310340d1561800100106881c0501d1030703011400040000c00c05415800041c0e0004c2c030381504000c072075620b105011101d44000344956100800c07600a14901044014030240940043c0440b620f60056401241c5000466142030b40071900307152880d406504c0864045401940300081d65095501d800d078107a800240403d5050305140d0081003c0200c0c2c0010800d06d1049000b1140520041c28035007049520788800c00310a583d8080340c05c1c5c01140c00d160000c216140250b1124280d020a10300c401c0f190300940014104904554a540203540035a855005e40d801800c9402e441e42e51381407200360003600002c0300d103043c181c00c00c2d000320b003081c2d60303a0b0000c1d041e80c119036054170150340d03400043ca08941c05018a100081d80404080b50110341710040c4005000d0104004001c0c0024501405c010341c0c10034a0380e0b41c0c0c1c1c4009056000318185102c00006c6504c20507205a010820b00f83d2980c010100010007201d00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 18909898 1250 18908648 18908663
    0x804110603010e18010b03060a090305070807080309160302090105150904050106020c1309050d0c03050d06080c0a05030118110303070803010b030405010b0109080c040c1101050a0608060a020906070605040305070f 93
    0x1d0240d0010040310040c00260044002c001b100f0007040800c0d12a1b10040034280c0301551108003009260040c07040b07400c8264000e01c203d95031030342032420301307010b0b00305980c4403805101c1c09520410040c103503000182541d0f0001e0405c01103a01e00405c010083c10302e28141840c0003014440c84095803a02d000d0680a041c4075000b82281003e40340c24402c90350481e0f0b4403d55801c1c10100c40b600030030800302c2e5407242c46000380350900300c00c031240c102940c1e20f01c50704440309601c51030f00703000103502c2101240726140c0070412a80f040046503908101340c00e03034201c42c100101c074000c0030012800050300440d100c0034460303001d070070380c1c4c1002c080c0c5e140d0800940090b0300c4040c88107000010482004020300ca80800c845003403c044800f01e0810f1261507a81c0740c0b0681d60b9004695446403121024000c000040280c807280c002440b4a103084903064000d00003512074440d441c032440300401d40142c4103000342c4099140107000705040004030f440703c5028040190065050140c00c002d0358011401c60103551400c40d019844 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 18911148 1250 18909898 18909901
    0x140103110a120b041406060307050702030613120302030f06010e0f0402040806060405010801020403080414040f05090312010603060b0904020904020903060c03100e0103020607080d0617100e0601050f010804110603010e 95
    0x1d42c100340c1d034102c40d0380b92055151030213504c80810f20710303400741d0084000d0710311039220b40e039514060f119031141300d601950521802c41082400e2500800110702c2a1040000702c2451900400550581c0801e85030b0341140303051a80002c21551107403480d82c41c580070003040c00d010740c1c600d900481c040f83c0c0b06070801c0744242c0068040245602b4603000c1e460050442a00842c5014a180ca03021002d010358029680b810003841c4400e6956510368102c620a950382c6d100420181c100303000040d0341da0340180351003000c400003c0c0000030300b180241700d030004542044103903071302d0702c1480d0041000a600c2030305a07583c800e900380101e203000c0d102000001d10807040c4404d41c80d540d08000c4800d2944100b00d60082d03510034501c00041c401a181c0300d09070388030b09078004591500c0d442554020030150107140c010724510f0311449000c0c4494600004c0c004110307004001c040000e00d500311645a2908802d0042c180c00007400b103d402a9540f00b6000550f2060142e490003000e0b00e100c41c00500c090b4420380c0500880701400c0c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 18912398 1250 18911148 18911177
    0x50a0605150405030303070c03090504051e1609060c02030106031b0501090e0c040e0604090215031006020703050c060a090810152c180609010203010f0e01030c140103110a 75
    0x5104101000001ca0300c07810585880002541e82c8001450b10003080100d00195041500600c1c810001d88001882484945400030030408042c2c00100d41e070260400b0345c1302282040301140304203500d200c072564518403010300f464816900701d44100c1d401c0b81c0540d40c40000201081c400c11401810700031001c8030035100b51a0200043c40b20318190403010b104168201031040b41000401220119000340f480c4071700702ea55000025009101c41f070f00203508142c29580d580a001151001540b00f90316180c2e40b00711081c3c68840407031390707950a800014440e500c88880c3c80003034504003015240d80101d500d401c4000580700c488840c00c0095106404400a4440c840c1101d02d45100c401c1d007016240310310001420300c1c000803615a802d40b10300780c440c100c3d403007113004500e005411000c00f109003c7c0d41011501c8600381815182e000394424070500150111800c00480d84d41840d1b01d406040300d401a0710b000e241c509000300210900e82c0202407506159881484a4082090001400d0808900c0d11420382207207019 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 18913648 1250 18912398 18912409
    0x60c020d0810050907030603021008071b0b04022806020f10020309250f03030c020909010902150904060315050f06010206010807090b04060b0c0607140a0509010e010c0204050a0605 79
    0x403012642440300c04801c1014106000e10b01c1c10840e01c046814402070b4490b807109070700070015508065004414072164003421a0891a040e01404140d0b4640302071402c240102600540389035001030040140002003409454501a010310011031001d02c003100c504d4030700000c8e503500e07000d03070080d00507800403030180549203024000382d88003d004102c2586035140c50382406d52203500611648915101800301003030010b5076808c11002420343d00d0a600301c250f445e42805429014440e4040348a84942c00004103011810700070b4410313469001e0180d0000c4912104144480e80081800c41e800951768000000810f10056507031855100d0707681300140d181002d04c2d545031403c100909090640d4000c40040102040c00030300d000444075031900c0012580c0e180000100641003652100208050103d0030a44003c0c000c10391501580d51034681100203001d07011150600d0090345460808200300b070007822032950007104420b016040514110000c074126a0004080342e01c10750380c203442a65904001d000ca810203 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 18914898 1250 18913648 18913663
    0xf03020f150103080c01060f09020403021504030c05010507140a06050603010c0801050f131401060e19050d060b0d050607020106140a0b030a0b15070308040b06010309020a091107080403060c02 84
    0x110005007159006100d48440c2014040c48010070f42c2c000020003a4000000b980108094405000700440031030f51018000c0181d00180001e0340300d0f5001c10a40b500c60000d210454003100d902400c407013000d61800d401541ea5810816050700c070010300c0001074503101c02c03d00c00000401e00c07138100015641030800905013120340c0b1401003414408003500600c150755800c21351038228482100e40020f1310401200c1d400140c0001a040c420103030800c4004125a41c0001c0e18000c00d21017a9680c0c000703031358070a00b0f0701036040940c0b065940026000c02106c000ca20307103801c54191114054080c0c4906480c90781d800e850813030f0486203000142d40d9060140b0100821034100c00c0301403070848200c940349041800c000d01c0c03440058880403030709540301c0581e562a1100404c100c40d03100b001682c1c1c0e8444286080280124208440031589241004005130842d030080c8650221203030040d0411088604000d140c10003801d07000d100e2500c0000601c0300700e0014141200800c081c510800c0040342003002c0d1500a86045103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 18916148 1250 18914898 18914923
    0x5010c0909240302121015080609030f030c0a030e031b0c03010b03100902030a0507090e0d03090312090203070b04030606080c040c022505060a03020a0206070e01090b030c160f0302 79
    0x4400c0c01802d98507000c1851001500d40403500d507944d103c1d03094205840c1a00390180c0505030b501703045203035140410031003010003120740a6054461b142d48146c0301d1785d243d00c80c4007030291102105101041ca401c0401d40a4114450142000a01e103401419500d103103411911400a1060300080a0883c0d4441071240303605c044000d1f4000d018042c1d0000010342c807452501800300403165521590300940d0b400704610501316800a0503524001d84400b2003002070000120140400c0c0718504408074124468411811030b150107580700d14080c600b10702d0240260110180c00d0340c3c540309088000c00c2d446414002000114032a20b80040d1701440e03c4d800e18240304007000d00f03a20a514004006030483c2d00410584112800192083c000d40710720031680d854441150040c0d60840b80103d019041c040d023650080c10998000c1e02110f120755101c44086034100200102507001815010080000c019104c01540c0c004080740403042c04d05020811001410b01d401805444401c0034a107400103050f018042030b2000d04 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 18917398 1250 18916148 18916181
    0x20d0203010b190e0112050406090807050f06070206070507020d15050106020c09010b04030201050712050705011e1802060409020a020106050d0503040f06090311060304020102010207050105040c0501090503061501030209030a05010c0909 103
    0x40c13500000c1c020041d01c00c0491151500c400c0040c080281a5000740a0f4551248065132598900d0512a5039485400b0002074184201404550030314000114284908119a500c40c945245030b03080c84200040f885044a90f03400007111091027406501800f4060041076000b042043c0100701000802d50040c0d02000440f4010001840941d034080d0840e0b11030354000186031040000d0f42012100ba105480000d010307035107041c0e040743d81038414080c1c003501d40300340e20b034113001425031410444001c0100040c02913003d0f03020841044500300d2a00500403007045400002016540e481c04500240a903210840e8136401c00203050000307808405810000e8403162401380310650544e5102400f0466040c401032050301e000c0300040442e8401d40450701c4007a40038000b8089414540f42c264001c0720b041c02654007061b0081c01c0425103003000903549204120240340300e040308080e140150003c4d4090303039049406002d030026050200d102400f501c0c3c0c2a505e242d0b40c0e00c4085103000c2c0c50100b00e4444046001645 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 18918648 1250 18917398 18917417
    0x1030503092d010c05030d060b07021503070804141e031b0a11090c0702130b0102010e0c03060a0b15030708070306140607023006040203151b030a020d0203010b19 71
    0x3250070b10218180e03050a00705010034002c58141240b45005a4484c808140c2c20301202007100181040502501e61095415560910404003a40c5841c0800c903403034000644ca110015021520314144800121000c1e400c0e284140c61021601c0440e400f000840d000301e520004904100e02104202581c1d00b050000c058058800307165107207501e000360410441c0c401d42c0081c010a03203101c000f204032014544c1c018644220400c008400034090400307141e00134095444d206003144404400f16551003040c50040c0a4142c0d0f554221006009007440c0c10410707000300442030140d600301140c00081d03000341500d4442100518108500030143e07480d503080f10000d9442518000485e403a404182c0d038100f6411070b80070700145a480d1641695440261000354001c07502c24070340c00c604030702150681c000c0b03001f60240e1b11800072031160f045020320182c5105120301c15a010200c0f84107519809540c1001e0030304c50140c60f00b9902c81401007039800c02e0300840403150002a480007556110780c1c6418400c000341c285610351 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 18919898 1250 18918648 18918709
    0x4020a0510080414010f0219090501030203070c020d14060c030a060506040315180606091a060f0f0c0c0a0e07080a0c050a0507030c050607080402120601050f100201140103050309 78
    0x1540b40240000740303454026004590303200000e4100300340c0c80342002400c54882d0102520050450640310765000860f0301d1501c0441c0d41d5109000326481008981c0324954102560f50910400948401041d9600c4401100441c2c504400b8000940030700201103540742c690511030300800c200c6041d584a54400c2e44200802c00000d84140c40000d50340d090400006818141c808a86190142e4111300800e944d11b81480410205180d40c040e00c820b401402c92541100d1400d01404450320400d0181d520001060108007031400b0990700038000c640a0406440500241801007200b00000d908880c103510402010020019846040141e000884c880c0610004030045005865841125180c00410100040d9a424140101e402c564a16800012618280f0f40143c0080510205940403480350003800341890b000d00c00043c2c124140d8000400059102100c80104020349400045407000d65481e500b200d45049202c0040302d00031400360024641d06d003d1141000402101e1a0b00080c180c1c00c5910300540 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 18921148 1250 18919898 18919907
    0x103030c0206070201020f0d02060108010c030501050a090b0109030804030605060111060717130b0a1a01021501090c090302120717030a140310080d02240403050306090a02160b04020a0510 82
    0x15860701039505540d610074500040781804402040801544201c550206406500260036812190140000c02042500c410220159042031207115441256101c0134091240d665020700380e07001050400f00070f400d0750b950342d200803a0003940c0b050f22402c0d59101040b18558000103540c4240301010050020341c9090b140180162104c80c040c070f00b08011420000e8414540100010030844e002039950300940b034100903035409003000100444161082e00b070309503410350001510a01c03803118400b5001035a828540c000c001840059801e03410400503100010140c0c81380c8402007081090300015021103401c000044084100003c00002c50750b0081011740305140c0d200845015100d001c04046540c0e4030740607a0780c2c2ca01758064000d0f880b18090f0303090488401b80c0001e2565100c07582d0441c0c401c032a9181c0301300305d0840e0303104650140108104000050551900c91315459011b22480740041c1804001031a0030103186500398101c658400310400d020075850722255007001840e003180c01150070451a10002c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 18922398 1250 18921148 18921167
    0x11803030b031903050d0c020705060d06080f03030417030a0b0a060e09010f050a060c060b0604120c05061201050405040c0e15120115060507050a170403061a030d050a09030b0403030905070e010303 86
    0x65486d0f40e00c980280c086071082c00302c9002008010009034481c600c01d03929000a02d0140f1682e0494412603400b14248203012040e03901c03030b582003040200e199005001d5090f1030741c0300070010030748544c3d911900189a82e480f400500030381420364803460f141207410140000840103800c80c03481d188809100300550742e110340d80c0fa41a03c0491401411b001450702c1c1002c0507000012100781d1000e000b040110b44000c41807032108000740100d00c0420999913450901c0050720600c540c03120700344814001071000c0c0c02e058001030303000b41c400c904a8a01c0d0703030344511043e4010020f41e0803402d0b109a140c04200c8500d06800c0c545408011900208103032041e036a51200d07860a10320030303102480004514030b402c0c810140864480e150300001c82903406881c1c0201d0f41c24030b038000d010484030030340340142002030f10551980e000016100600200003401401d14151200d810500000e0308001582801100141040109501840c132075140468659403a04c2c0040c100311554102c100c3c00c00035503004101195000300b114 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 18923648 1250 18922398 18922417
    0x4082e0b01050f040e04030909020a09030611091002010204060207080111030a0b06041203020303042a360b010201060e0c03040305070602040302030307050c0f10080a0509011803030b03190305 84
    0x210180d200300140c52600848404074144900881c0000d92220355207600c41c490351195945100841d29140d00030b040f0701910000b100000c4440106000180e02503204002c64224030a40508001100d40051900b101901220700180d40104080080c0c5030104070702d50180606030000d102c0100c10142c1c52909020007004080d00c19151410354001d42c503014121005800042030950100346d8a050103566580b00361821524824107107180b07100c842c1140a0440c0c4091302c1d0a803044441d01e000040d030441c3d04081ea001014182500c2c4141a010a010882116080d00d840c0414100002800642140c25590141d4803240c06503040084002e00502100e074010f5242c01c00d03070b4403051141054402401903400080d014400082c21000b4082d00140c041c0c5451400c03502d20403840364910130304c180111030300c44140110300c26101090700c000850304065130160036080001803004007418058031181c2910400e90210b6a210240b10752401d0134885042e541032100c00c99100c0e140c8955005029210301c001d00c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 18924898 1250 18923648 18923651
    0x408192c010c15020f1303050d080112030f03020d0f060e0106050c0d050304031205070216140102030f0325050706050f060105090f010309060c110c09040503120901110403030504082e 80
    0x8030403a03000684c10344592031214180d05071903000e241865410540070340800e50341449070040c14114584200c0c4118107231105000c19428038004c5503010b07034500c50744103924414560240f0180e0706452482c03184a40a01054901051203840d1040d5400d62036010f0304110700304202000a20128440041c9441214007d490325940c4c9a0399400d0172140056048102c1042900f00710030301440c00d50015840d40380c004550100030b18540c0e200038180c402c81100e403065026070414400d0000d6550500b002d035130301100c0b01003090708803803c18519001405000e403100002c1070300803601c4424000c0a02c1b40c141e1040e5004084840390800c0750001e03207030b405942d034228880c1c1010307002c0e0382d02c0e6440ba4019505007a40310005005042041e20047c00140e1200b8101e0310520130b014101c031143c6000c49015000d15001000380d880c2c110880132140020b000100512519074a80040c640385e0030584009100940c00303a9102504c0d54103080d00350b4141440c02c1400010001c000c5001c2003196600004070441d089111070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 18926148 1250 18924898 18924923
    0x5150909030903030d0204050108060301151503020d020403030201020304030f0509030a080706090c08070612020412020d050307050f031309050403080f091005010803040504052d0408192c010c 84
    0x100503140d03110b111842a00340c003020401882e40c06030b54000d4420f4074400d072038204c1e05907107000506081319200070100007141d074580b004000503101d6040c00c0101410038a4054500b0a0710903610301a40d010358000c0300103039030000420040c50f03401641c98aa05141e8a4181d01d4010300703100099848107486800740c4001c900090080410403c0da1024034000d80c80640c481480d0380d901d0f8400d461b6078080c81202c02144403401480718002592003143c041d00d61a0031007401c0c4050079001d10048190304c030b100b166540b07c02c11450002c40c00802869981c000030740000c2d9035608040707003600e481100b40c0e0310000b1030307a081506001c0080d4000b000d0591010b07942740310780c0160355280c12049c075007825810b660441c0c07450400040307001318000c401402074070026202400b8548894400c410b60500b50544140000c02d0401140c000b00c0038108140c1d0005d0051b22610f017404c0340750262000c200c000035031850220745500940d003802200c1c190207403007064000c5070483c085d07281d00c40007a05904006000918a500c00340 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 18927398 1250 18926148 18926161
    0x6050709091104140a0b0307030c0e04050717090708030313030203120a0906110306061603030f060605070515010f031403070b0f0a0b0a080309010302030a060806010b0d0b030102032e0506030a06031104051509 91
    0x4004400078540144180240e05003c40041c0c00c850a8fd002900207202e120002406040c000a002c81226004e0000b0b500c1c60f42c582610320f96a103031010b02201140070402820300440204140d85004813120790b0002035172183c519000d81260032055001c00c11040902c201700483e03039220191090b48203840300010300e045151808500a1441002d08090b4070b1900c400802c2e0b00754024058810036103d0002c41c1e030944240c2c02c1e0815403540901c2011550b0800b9041880018403000b41d814046034090708680c100080707990380c0600703d20210b810190b0400c084041085242c2940a171411200c01515003c001600b0b05100c42e480b0b1188a02e0941412740000c0030030358410156100100900d00c40c4191521035861b603407105520750004504d501050b0030810020420301c0c0620889001d210030101c08203d4032064215952000352159084070300c0d003a8240700240179214840218828181e10400044007400c618110005d244004c0e031990059151000b0040b84000340d489800b10100d01b140d00c1103d41d503420 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 18928648 1250 18927398 18927407
    0x103060b0a0b0a050406020c030a0209010501050f07060501140f1f051602040c0305060306010906140d0501020c0703051e030f07020d050a06020a0f0815090406050709091104140a0b0307030c 83
    0x1680080b88078074000840d041001e43c0803020300240e07490760342558204600f51042607550751700c84002035030081d640c500401440d809600100180c249017402182024006e44502040b3f072002da02c590003007c500c1014914518184d1030911804c0300c112a48004509003005024502103c804c42800344440054a85440651300a060400660060040c0b10780c00b900c100c028094441500e0950003449090004255121a40110300564a07840c0c100d50245a03400200540380030380420686155600300004007a4050030302030780380a1030068004000702070b202012880c02c00c0307a000807102981c10a02c240f07100d904d84003049683c0301c0c0c0c0407503850031400c2c428241942880809440140103910000c0c0c240c5603540c0001c410030441c04a40c03292401039448141190b107940c4032654190340000c0c07000004000a03115407000750050303910b00e424415503071150400803c94800d104050401c075030100381008102d80e0005c0015200c0e40c10784000030018540024400340f400040d01c000c1c141620b64041a8400d4443c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 18929898 1250 18928648 18928669
    0xf0601170309060301080a020405090d020a120504030203060f060901140a05040b010509030d030b0f010c02090601111905010204030b06030111070b0a02090409080d05090303070203070b0907080a15050901060b030103060b 96
    0x3e000c1c0c3e980f0f503950b12040355030701900c5070124020b500340340c0050a60500405c0461202d210b540180c824081c1c10342d204030b0901000007900c42405000d00020002d40c030708018862003003075000c80042d01e46c1048810001b420364140d12114502c1140c420320b60040c0c40b008000d404807031040e50081101c0c3c0c41c030310058072540140b15860f6014420701401c16600f541c96004003d41480c140e5642800341000d00c0110388a030b4042c2d5000e9003040d80580428a00e500c40c00061f46c502c9405001d4880b50b404011000b05000080c081c29a0541e402080c1407040c04080c0c0d03241d5400450440c000c01560080d0117170031920f4003c11401078540c5420784002030302840c240e01180c040490040c420404140300c0d1038100500c3d08500800380c115480d10340041c00480000085a000c2d225a40055080208984e919041d420f00103009982e58003950742c00041041e410011046501d10070f941d541444507008101700304881004040c03401c5603050a408202d60034684003200e055941150000c9241d540d0100401c4c0181003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 18931148 1250 18929898 18929917
    0x3120d061505070c0801090206040e15090c0703110604020d080304030203040902030c070b0a0915021305040516080c040302010f030b040b0d050106060219050d030e10060303031407020f06011703 85
    0x410700120a00264490001c000342e501c04e503081c2c5003507600e42207040e08840309881c4c0250001402c01050200c00b001c509155031020101d01e5030035001203018082010b04106640001010324003040303d40825400c216101502c0c0d158100400c00e81c9031640004512180314480944440710010108040c14070900445004d0980400b080d584c80c100041c0c0054217038814132060300d0166107207020410750709a50250504031a040700781c0180080200142c08001e50010760102e18080c000c107000502615a4004c040c45080154510407800e0854071001d092804018103070402c00d002008103000513a0001100c134004030a80c64000785d10f10791070012900402181075420f9120344c0303000113070040190540014059904540c240c0c0c8802d4901d8603815032040781040c0040554000540801035640f00343d02450b13844123a84116005074001c40c112104071461504203400003500c1d010701e6180c0f5501c42c00b034550813008900c0106110002d042465481d604103000d00b4030406510181019a0700b020420364000300c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 18932398 1250 18931148 18931169
    0x4050a0b040803010612020306090601030e0106030213050406050c070b0408090d0506090a050708070501090b07023c010c0b04030c05070504061707210305090a0306020301030b041a010503120d06 85
    0x40c54145a03460741c00c24410b174400600007803111050a01c1c140260783c0600e0002c0c00c1c001d1161140c1c00190060007507e0003101d01e035940c80c0c07030000c00b594034078801c42a50b40d10180002602d0411f41440c00079214014a60901b0134410403000e40001c2159000d16481500300500f41d8503103641c0ba00254910600100c080e10900c01c000501020081c041980454503110307000310b4841559628019440e01c070a0310034240441c0c006582084190769500042807120320041a010350800700c00b41881d00c80c4900225501c81c8000d442e03480229155280080040c0c80003402c18004c2c03031031507684a6400d5580140300600300584001c00c01c3c200042041004081c0400130070621289844102d081c120b040070850850040c0b0400000144101840c855030040c9100300790001a06100350320281c505600141495800c124003c0c00040821001d202841c041c5100350104001d03401c007414428002000800e9413a80c48400000401a55400052458149075004c034669100e4484101c010010700c10795101d440001e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 18933648 1250 18932398 18932401
    0x1805100203090102060601090b0403060203040804050a1502061b090f0a1809020307050a080a080307050c0d05030103060b0f0f01030c0309060207030201090308090105010605030c07050a020a0609090b060c03070204020304050a0b 99
    0x15038011010b090354070002e034200c51880d41d40038011940030320503104810461200f08003d00120301c1e42d07001198058000d041aa290964890201d602000584c1c08000c800006081541c803141d0b05005507a084011908403012208050450038004d1107079070946172190102c4006081039031070b010048002803203404980e03103603e9403a500c1c0c403000c1c02881004034400d01561102290030710b40003072003038169130044005042c4034189980700c141950000d07065a00b4410240204416101e00300150000c0e00003139910030f512949035180c110150303425501420f00c0340034103120184840e200c141043c0c041c02424600800d2990044000b0740003005c0385e0f41c015040c2400000c80340c0c1030680542000150b50321940e0b038184155140c0d03900600300c803c28080c00d0001402000400e5060140394054024a8026002d8440118036580055a440c20030340c480310210303113040c80402a41c042c0c0d00c116001c2d00f60540d074407072030000d030148101e4513807280300c2c0024810340e80800464140501080704940303003584801928100d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 18934898 1250 18933648 18933679
    0xc09010c050a080910090b0304060c0c1b030c060f1e0504030204050f040c060215070f050d090606050906030705061e120c0c010c030c0f20120702040b03030412031805 73
    0x41c4c1c060703020a401501e540e101026050301c11540101200d10201c612030850302c4555a91001d02400207120041210700900380000c00d00a9007000c0320414407085150025107586840f20304c0701041da00010501403900f00704003030b03140c200441500300080c40800d24a0790a004005030b405000700d80010b03400070325040401450070703681c0c002c0c0da0096000d000c01503405652280200c3c4d070354070076030441501711940101062501d802000e1004004982d0708155041c02101c0001c40215255090301750341c210b4417504100900c2c10310461154101c034043d07002d441c0c000d042c040414040c2c4107002c00103030900e02c4100e500300b41080c00d0701030340d26400500c04950501d003003044101d41c0540100840e0003044d403804000700390f110301034400c10000d01c0c59501d80c1d07945580c0e009002c1d580d1018400080094001c0c81040b240401010300003803001c095120200e945650040c0180011188454802c6000360300810091041111584026000560620f0040382444d061100602034050b254003160700810000341c4005d2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 18936148 1250 18934898 18934913
    0x5100f020405090c070c030602030402030a1a04020405060603010807030b100506041d0709030b04080a03110d0c080105091012050c090a0f0b04090206090112061509051201140c09010c050a 82
    0x442c0c0e4121042e101035120207050340c9040c882d060b4000d09030f04a0250801c009078054020710b034000d000809a984210f80382d00e40c041901903608040b0f110190504c10082103181510605811080540b0712604540c10541c66980d80d400a0001502e4200d451000600b213010504850000e0040600800d0b00d417035403a50040c0740110744401102410f0804c4c000940b401c0d2160001404894000d2040f61007511692190242a4400000d910405440300324850040040d94000c1c10700c2c0e244808002400d941c1c200c0d0003410840180c1195210384054000d1055040601d04950b068840315811150000400d25180785410300c02c404054111703040030200660074189901035240c0076082d031018840c9444041c1000101c504942d0020750011091100c0c80c410b51081024061442c0300e03400020368103840300c407d441c60400c60003441000800390142404541800c21004045143c908001e001ca2a500903c0c3c611404009204800078134005c50300403000e070f01c1212000d003507541120036a400400303581003088 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 18937398 1250 18936148 18936157
    0x303070210090f0204090201021005101802030c03042315061c030c2004050406050402010f08010303020703030806011202030702060711032109010b030f01090510060501081305100f02 80
    0x2025000d030301d6020001040d5805404503265100d41c4460000b82d1503403c00006000f0b0ba0401d07070440c460308410800e0700d00203204140c01500c0204110109a1400040c8401d100a41e000c50400740d005100b4010805000c44c01e0f070340c100350b2299491460002c4000f501003901c00c8204a02030b00d2180a107980d0302c13000d514044602424050b1803542c40201d44031007680100e40e140400a0010b1a0560080e010a05008004400d2601c6003c6030141e503605200250981d54107603000d9955640d15428002107603040032884204002c6030402000030743c919103001e515403509200240901141030001103d5a100310103546080094003000c41d206d0170f18840c005d50303035982107a0700008501c0740724240390b907024000192010080741d50503c0304585000c0080402804014008071603642d00c9103080740080c0d40034801207031201040000090044540d080070352900200c0d0740c88420441c0381030014803041c1d0740820030036803003d0b9000c1d5002d1804c0719454a540382000350071004105a182c8040301540808540040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 18938648 1250 18937398 18937411
    0xc030a060b0c060718090c030e0601053c040504110f1203040501030908070501090305120a0501030b06010c14011a01090e150d03020c06030717070201090809130912020303 75
    0x4000060315070031511114450280e00c0d28182e0710000010f21101d02c81c855100300124441c42c403801044d91a19000b00b91502101c4090100c0c1c0c0350300607a201e00d1410400f00e4010001200c000c0d210b05d924001c0d000e0301c40c031a03c0140c40451308410b48030f0b008100304d21203400c8407000500204002d01e803a0501c28040c04107540914030660328140b900c1200c2c50308524408200ca00c03031014514007071030400154000d12641c1c1c01182c03043d80510266012850030310800f41d845009899143d034500708484a001042c00c01010b256403145000c00610106000c025503540c00781e000c3c00c1142da80c1c0d00c0ca00340b14a040c02c1003201d040b05582040741c0d05a484020b1420b5400640007a20f807a00480c3d00c403142041b06070300031105440c00c8605d0250341445881c0000f5960718140c043d005541d0004800d074041129a4822a600404a01c198001c2051410f01300100c5d51b11000781d1000700030110070b56481030001c0c0b0586600c5c511440c5a00d00117241d152442e802907070b00c151320040c0c0845680444401a480e40c00c02c03201ca = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 18939898 1250 18938648 18938651
    0x5070c0308121302010503130302120f0309060106020a03020706030504080c0109151107020915060708040f03030e06120402011101020d0504050a0b090609070308030a020d05040606080601090b0a090f0902090c030a 93
    0x45003403c2040300c1110b01407603050f1145802d6036500c0c600f40d00c0300010070b00b040c4c0c1144a0a01d00302c6009103648000c2440c82c040d007030003c0d5a460015420740c42c000b8181d01507821584100c10031300102c2e6021544605903100d5145c00b080c10b86603414a600304c3c0c00f500c20000303029441c1003008070800250007056070303c44081c81c02c18040d000c0070803032041d418082e040010350000c401c032002861000038090851558600102003034109070082e1108a41c60300f117604203402c81c1c1414182401403503040812501c142504898580c40c0041b4008802500c02010700001c0c140810007403c85001d11081d01912032403201c64804201304e2410b820090b036a1480a1000d4031580911400704025079400b180442c858030b0510014003406180d5580d504113513000900741d0241c44d90030701204248003003d0250500460141c103022030101e040c000150b050281c10703480b902166140c0721001c881c503101e8048030350071150710460000b850216107171028090310031070800039401410a81080648038020001d1070040811700c40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 18941148 1250 18939898 18939901
    0x2010501060e0604031a0402040e0303090115090615030e0118030e040e030408030a05030c090a03050a03030e0c0a0302060c03040f060c050c011409041d0d050a18060f0f05070c030812 80
    0x10b00000c0e1045000c09031221b02c292900c0c0942045c0030130125001840a4800100d0030840140d403400d58006650300d6555944411028200c8140040020050311102034208001843c042016440c27009081007a0709040d1528403135901c8200a42c03200c600008030001c0e524220320549402000d941514034030b148076601e884681034000500005440503100031a00651601c1040306095905070002805141c80f48002c101c00e20454841c1c14400008511840c000c04020700103180c040c040c0d510b05d40c40581182e118840c282c04075625101c00c1030440390151403003542e404413444094250300c0783d50040f142d0400e1a00000610b198003509003407207a4012020344501114590044174240c00343c90005404400c28003c02c0c440d841c1c50752000c4000711540741c1e510000034254008508001c408262080800e41c0072500d00b42c0d141e004404880001c03e401c55100e6001e00f0044058211003d020b004000c10800c04a00b01c0b07601c0c001c1040381c0380143c000f02c280b0103460752454400c2441c0d010740c3c0c2c81c1d280d0f48589030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 18942398 1250 18941148 18941177
    0xb0a090209010509060d09050109060501080615010207050f040603051e07080106080703061806061509050108060603010b25051c021f020a0e12010207030e01090305030328020a0201050106 82
    0x800d9896042050f55140d103880340210420446400c01314028082540c0c0f4880040090300911940c00b66503c070780d2010030158076019085040c103600802c0e1420511405042d251641e90224003101911400c85401c1251200c10012400030402d41d000289244101d00450301d40b104010071034107503000510102d404d0f003515640404e090310524031981c40c49a0110310b0502c00175280d500f02c0a1078901000d070340d40540216442d0002030382c846034060201d04101c50b46070300000764000301e20300c06800c6c2802c0141c014208007022035190b20052040000d2a40301081c80500d801c0c0c00c45800e425400c9200111600300e009091850300c44003c40c4000d800700b5640120482c0740b90001c501002070401c8216545000f90400b040140039520412000081241124000a15036960721348400740c40341c5074000588600f014503018142c0a20412150f06020250350700300005100001200da110300100342c0201402c0d001590305a1a281c129500d1700364070700225000c145036905601060403284070f070703440720803582401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 18943648 1250 18942398 18942401
    0x1227030a030206010509060d0204050f0109061406120903210709090501060f0e0303090409030503011514070602090411040810151409091501030c03030e010e0a05120c0a08010b0a09 79
    0x158005000d42c000d40f00400003440d2042c0440c1c0d000310040d21000544a1aa0000d012aa8100d0b0924103282d0203c0060220445601c2081c014200700b481020718403a010700015458001c684119060700b0525000403c0c05000b801070300d281e204000307030401103001807240010611800701c034118000b03402c0003800641c080083c000e45049810540300d2004041086002315071a651020207141c241c401044007124070784442c410700c12958026a2110f84030b5042024804821340744c0907842c0c040120860309405034110000460780119803041300180d44070040c0300842c02500700a542c0c13518050000c00c000414040c041006480d04018203004c1015100b00b80c800421030659010390b1940307000d640002410b80c03c101600c60f4000c031600d0300321001c0741461400850000e130242c101311030300b503600c0204008260300f0480d001c45d00602403c0410510b107074000411042c00640c40340c24800c01200fa8a00d4201e14103200c205200728000d00086586a09d400c00f460184c42c00d40328460046040c00000102c0b203215 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 18944898 1250 18943648 18943663
    0x804030203011119091505091206101a0301030c0512010603020301050f070206071107060f02010b0303070303020406020f0c060d020a031b030605011b0203070303050903120a08040201030b0409020a030204020309122703 95
    0x104030420148140360884045c0c00c0102c0140c2c000c070604e00c0e20300e82c05104000244c0302e42f0820300003d180604100d50011131a10758842036070411014001072000034074052015080d50015100e00c4101619580d0361409040e40c0d40c03000c0c1d0554a00300034083e40e03000c00400140309400f01e40845545841c7c110040307420464802164041c1c0d0099181480400d00c1040103240c802c4c2680b002258403051600003900b15172000900724042a0b00103820864550140729041c0c25003d02c1010700704840444000c101e041c41102c004030707085c1e0750001d00810b055009502c020b15072011200410045020380314050018a118021030b40802c1003000300407044c03000b0005503151a48d0180140080d1491950151629044071801c0b0f5414000d14004542118100d07010300700c02c0325140c0d1075a001d414180000b40880380341c00c0000c1e000c1e40c2040b2100d000350b211107450b10f0450743d054400694950300c0b5940103051052181d600c08000c0400210001e410b002501b90020400c854400c0c03800d260118001c056440e0341 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 18946148 1250 18944898 18944909
    0xf170c2106030d08060301020c071202031204060503070309081c05060a1a12040c08030d020307030f0203060d1104061d04020f030d0f0309030c081c050604020406020a020607080403020301111909 85
    0xb14000210440b4030038844c2a8014070084e00150910b030100308002d0070700601e130300035046440c000003038101549003c01516441c40c5807408424a4581045402041403100405107410301d0307120180750007001300728401c171034207000e902c0124815011410700c20001780100743c0d0300c98401c0b6042d044c04039185541ea640c4680384423100c0302d41481c04e0389140d1040742006000b80b060320000b8100400003034091080c0003d02c04860344c44001aa6071408942c05000c9402d01201c0a0000384103004104454460a4500c054a5000924144145030003000207000c3c110741d412184860414031081100c0c1800445968081c0340b088800703d210b090244103143d42d545010320711000280d443c035024081107000790301c01d2a545001e8a0200380c0c01c0c07000d0300c8030300c910703840821440d9110011140c04c0d083c03099540305031030b0440c1044800303510b03152911000941d2020340400291040f20300040c40740400018004a0f0000d590150082c0a0310848890364161500712561008160f500d103c5210b482e580b0660f0304105a68 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 18947398 1250 18946148 18946153
    0x10e040c050a051c020a0905310c03030309060e0706090e01050402090d120908010207030507050d020703080406030e0f07080a031209020918011e0c0f030603080405010f170c210603 79
    0x140d01c1c0c1d44c8480208451000d1760880f034500004034804a00d80146403162595050b10f90307821100e6190803d1040b038029000620500081c0c000b000100d40b55111022240c0510703010500300c2c05802c098008006504080d044d03441103280000d020350f000950700d800c644d030078103501e000303030b80c0e0b4a040c08180c1c42040c8141d680004007010102c0001d5280e90400c0201000b40f07484000150ad035419203013240e01c9403e055021500104d1003404010b0100401172401090344050030001d455969280c0e07060144c1e000d620705250f202c0780c0000a8450420003100000d81e05000c49540c20380e200310964540d8180e0f0000d0b400648490150114800240500c00320300703501130801c82c516a0780d064944680d40742840740082554a401c4210396003c103041c0d084030f0f4186090000038140320422000390100441c0d404041c103040c00e100e0300300081180c000a036000c4910a00f07014500000c0c22208465500680d00d030f09084105040c1406528000c42028024541f0440d41e64072941c4080c169041814400711100ca40c540e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 18948648 1250 18947398 18947419
    0x1203060d020103091b030b010e0711100c0c0c0e0702010b0102030c100506010e12010510170601030b060a03120f09060302040b070f02040b0a030302012702090c0702010c0605010e040c050a05 83
    0x42d446507010b440710754000d08030801c00d08850614030049050030350066569442d20300c0107010404000700566040307049410701c4882040c92203000340e200c00254580481d459901c60042403054060841c86403196440207528200503141c2806420f07468003541d50b60010741c43c1000c241075650000085801d0300707444500a1095001050564020b040c00a041c5410040c9080c5600d0b0346840e00301e0180d00c003038095000401c5514201c196400c03000c4c5079034040316510701840c50801039824045407640c15603410a0348003045546040c0840d500d00311030751005203050380c2c0c80315015a140d440310341c03403080045554820024650310306c0100d0680c020307409030203410f0404114090000340100305e2052071a10141c40171403000821400101c1c00c0c480d90b4016009130b510b5800d035594007400b00c004e9601c451000c5142030750400d030313680202e0300044c4000d104903080080042e8120540e802074a10841c15030b80b01909000075a16800d052044e14000d8a04490280b0b04580100d902e281c241046400d849000d0020142c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 18949898 1250 18948648 18948653
    0xe0a0f06020a051624050d0c0c0308070201050105010512090a02031509010b06030412080711030d020a020105010905040503160302100f0b010e03070b030c0702040b0301020309070302150702030304090c02010b03010e06091203060d 100
    0x3e480344000e03080501c8402c211f480560105800f488449485685802102d0105403c0107081850f004001c042164034042c0184260b030303041420703142055941e140310788150b43c039000e0061508030711310806507251151009102800c80c1683c2d9540c4990a02c800a0045642c040e00f07024850200742d42c02000e8a05c0d0050100640e449a0101903020186250101c2820140150030b400c561003441c3c0b07040c1d11900005c16884281d0240929030051800c004104400c4c6081d4540e40e07141c1c02100c81c4844c420401c2d40440003414800c010b4000c0d9680304407810040011840c0d00040204080a08035010a410f800c9114152402060040032505920500c03440d503035440e04910b4560f07001c140120780c456a50503e0307100c69102440650300c244502c1000700303101c5085004001c2000107021441d031414008001e220016240401910103d920610000c111002444001c6e4054410683c0f1150191300c1d100a40c044000300042260085812500350340201450705144a018031046501c0c68101e800b48260030700 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 18951148 1250 18949898 18949949
    0x5011a0a0c0311011e06060207140d03080601180b030708010605030403020604030e061308030904060b0a050a030207020105040504090b150402070b011203090312020102030118050411010e0a0f06020a0516 89
    0x122400c030f45000058a40c50301c0980050303c92400b110341141595514244030f150340400c9450090904481c903a4010540341000034800c21001c04001e080044483c0802c40c5c690242d800c41294000c440c0781c2c0f2200b50380324095865540c008032140e10002e82c85400004c1c0090240b012640120f8140e4007030800d0707596a0700c055030648a401d05407500807030304100020300f400c84014024003422100300590b0b91048010100000e45a6a030000d03810394504000082009400604586003070320300e420003584900c2c1c0c500050f540360181d41d05c0725030001c0c10031022008004d081c4240030312980c20b221a160300d000d40035041c00103d00460f138000b0007219580b001030100c0700c403e011411b1401d01c44c0c9000d04500d0b4803961420b21a207200352907140543c1d0044010720030030309204c01268501d240a803041040c2e00d069100c02e8070841c1a6489241445203400d1510700c95184c440841000d070041d06101840c0503500c0c50029550740e014401036996005520044003401000c40c09007044a070302d141803100321a5046c0c400c01 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 18952398 1250 18951148 18951167
    0xc01050322032601030c06051c0506030c06071208010f08030a03180c1203020f010c120504030c0615090b030304030203060c0d0e120904050a0506060d150f0905011a0a0c03 75
    0x2002d10028103a085495000d12031840e401644080440a03c1d503d03500d041c44480310190030003000d011040c00741c001205688034000d080742210b01c3c804240c545402c4082400d103042202d465811490002d840018080d2003580c1c0d8050080c02d0380e80c000540e036030780d0404840740414000d10806400030490390524078842e030001400006018010071484095a80e4650302d0385903540138030300804d4000041c0040c10b80601c4450441110a0000d2100c0201c1000081800d00d0310000c210301d4a5403440851300385441022a2502030b903016208210b60f0300344842c0c202d51003019104410f005824880304a01c5810044280e40440c0e038081c00814141d12100c0380c207072503130b0045407111005594070b0b02006907a4000300720610440c815595515601c5480790240000d070394008084142c80381c2008103001c40d50320b400080f0340d05590001300c006900580c858103000d250501c3d6100348600c1b443c130240440d4026090380068100c1c3c610001c00204418040c81e0f42c1c50034003a5502d42808101201a401c3c0820b0185c0c0000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 18953648 1250 18952398 18952403
    0x2010e060c01060f090506100201090b040209070507050607031a03070305060c0304080d060b0405090601050a02120309011e050a0e0d14090a0b0a020616020a080412081303060e0c01050322 82
    0xc0365640d104c0c2440c05801800e40e11801c4482d4880741808a18242008022600b07012480203221104180c0c440720b03007848018000078051110a40000c1602e40300b402541c0c025544401074440d1030600c0240240540100b03100310102c103880b9841003803e0f00e030004085088903404405086943e55a030310000964100800659401340100042c1e42d80718400e2241c90050007000780495112030034503082c482840ea00500c5181405401c014040c101c07600080c12003e0b4504c18403510b940ca689650016000d401600c030403011210b040494848603a10700d41081e40f04280403842001445410071140340d9508401400b500412a940e1000e8501e820101c024540d009005c1d241c03140456031020b40e18407135846401031000682050b03041c401d2080c68580903031a010f5241c4014141405691034050301c900c80e0740b08a0340604502c4c0b01d045e0030401014107a500c000711003c031442c02e4540e41c3c10903038013500050200300d44500618846965030760180c401e6900800d144d401070b0107419880700100c5a01d0242800a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 18954898 1250 18953648 18953651
    0xc1f03020405030f07060807031802090c09210c101b0302150702010507030b0a050a050609030a06140103051005070503070e040b04020406111509060402100e1309140a02010e060c01 79
    0x71859880420610302c04520a1009017010303444c00e400180841c4000d030042c070415007850000c83c0452400a904800c040d01114204180e803980045050a4031500302c0c3d113500620800003512030142c501c0c5041030460440420b0394060850582080742090351210f02001040c0050500c41004003c03201240440c6d119004a0b00600c0d58a6031561850104550040060303440d81c04020840da818021002d2900c8160b540e042141d04010008240381440d0065a002e2040442c140210f90303010445204030350340106041281009603040d0440ca020240400d450520074001c03075840312181481000c0c810840d41c0d45540c2180c5902108903180a00e9a00059003d6122280c01800c3d50713440c030040c4001c01c284e032a1440190070b0104401c1c200b0f41606411f508801c0ba040c1082481c070000b240256102d54101c0d030341441c05402c140c041e14a50b4601d1205a00110861904103c008956108001445c00b80c840300100700a02d020310740d07407a80c032064001d0024141404015250604001030404c22014000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 18956148 1250 18954898 18954907
    0xf020a17040f02090c19180b0f070c06080405061e0c0a030f0e03030a1104030b041b090609050406180c0e07050d020705010c11031303120e03031803060106020c1f0302 73
    0x644c001c01c06460b10302c800b5030700140c55810442c06402040484c01c00c6d0a00910482040781000c02400c494480e00d001c0705000200c103030030740380f25208480404c0c0d40321208660507900c03800014842c00007220125454031035180882c08220642c1401c0c600c0a100f40507101007a0303140e96402c0d0190300036110700000e02d0b44076903286c00280c000d805012918074114000b15202e02d0141209010759011007580d403c0c5070000c100034000302d046122503603407094106098030006010b0580a4000350b00990002800c1d600d0143d0201e451483ea8100501640c021142800303d50b0840451004101e0fa00400500c6084044c03002c0000340907809080758040782e103062090400c2d806041c6802640c2c0000790403112650340781c480f992b403e50444001010018081d00841c28010807048001d00c0414074000907201603904101042407600ca00c92010350300502905480e01d80d000695404401800f00001500c00d005020000c80c4a9100244a41d58a50001d00020040d01e0704030940c18284a03041d210410941c0800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 18957398 1250 18956148 18956153
    0xf01050702040f05191a04020c0a0c090605040617030712020f070321020d02030703030e0304030609030c061a0117060406030209010b040905010b03060607031b0b0108030703030f020a17040f 83
    0x400c59002c50283ca10104540c03401d010701c42940940c03440d1403102075281c1a0445480c1d0202c404200b41d04406440041c0d681e480882078524012850b0310041c9070315072850000c200034a55801c00e01c111141558180640b1342c13684881c2c0d00d407802d000900880c540c801d00020300420f440c401141341c102c40302e00540b803010100305051418020660015100c8445684059079004c03504504a081403400b0b10190030758028072400291a4803c450300901056140d05001d41c1440050044a0007564800010040900340703103400780c00344180b80415a036181c03a180d14004200200800d0101009050352601742c08840362685044070301c0c01501260704a65210300200041e02c0b0281a01d01070260001c2454403145000c1800c0291081604818007110341442480480d480d00c0050b00c8505030305041c841c2c1c07641c03402401c2d8511152142800740494500303c0001a40c908080001d129a502076501403040d090b00001003c00d034070400030741c071000400504240b5400c110080e28641c03c94400c41d6041d02000d80e58 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 18958648 1250 18957398 18957401
    0xd020a0905100305060c21070302251109070e04020c010e010203070c151a04091a040804080f0601050d020d03050c030706020901030b03060708010308030c0418050405060601170103020f0105070204 86
    0x1114101c29142e45000d042c028080100405a0310001c1e0505003860070360310040b03440100d08400a40d03849030480a0200304824000c0d01600e000d4aa1a181d1109030f0004000d0200840c001d990261810144c801d08442d13142409031045200d4401da4440c0b40009412005000017984240020380d1503550340d461f40714030500f01780011400b41d207041d40e4a100303480030750401e003d00102844040da481c038a0b018120210216642d0740700c100b058211400503030807625081410720104501106004124000100300402400101410966a5800407102e10342501e01d88150f54090a0182991091401c19070100502e0301000c01d000c07452007460b000b070408580144e814a180c00c40c4400b103d54071780200d40d62245592510425440f0f890440042c8a203083c480405040d44a041c04094600c803000000034a030303c2d80c036001301e4008203c1200c035200362220242d5040c2c0240802d0f94122583e02550010a000e907210b40c651116060f01240602c2c040d07440c544c00c20101c89648880241801400d118400c09603403039 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 18959898 1250 18958648 18958651
    0x316053609060d03090b13080d090807080c1302070305090904200d0f030c05070b040b030a050105030d050f07030905060d09050f01020309030901031d03190f030b0904020d020a0905 79
    0x41442040c00d02500411818010040446010300d0b81e48040d40b0120354071049403022214400c41540d07440e20f40f94040d000451540e003000c612031242080712501c140d4040c200030212070320726090b515155160f41000361039440040e010750740007003018003507844948164024615035103e8100f9a150842482c04100000c074101c60544411020880401403582038042d80c1599510884401c2141001541d62a0410390768200190400c074118105408109081180402030181510030301e84861b680d1403000303181d03403080740c046c110701e810f090000585003400101000701d40e03125100c650810206811308402c50f04088020ba0800114000c0020180c4680d4014488018020804038900042d800c0280c80c01c0c3e140210301405038410020404c1c0e01340040250f40b0100024030b0702044010342c68034020600b5206c54203d110038000010100800784403a1820b003220005074032030480c2070001100582c115007410203c25000842c4900150040c94102d0b0011441032004001c07013069030300c805141c402c0310340 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 18961148 1250 18959898 18959977
    0x30c080601030302070f030c031119080109060e0d0504030b09070b070f062904020c0a060c051207080103020306040314070606090203090705060301141c05010c021c05031605 76
    0x30000040c001c0c1541446004082c1c454031043c1c51070b0070303d559100754121426103c040e00a804680c5411b0040c2c1d1307030213000e200907010003140650700394803582402d0003401c070218225000c62400301c08105120f03010a0100d030408858840324189891034403421651718004040d61902d014000c004101c050001000c0c000c4540100140b03078160200b031a06404881011024680445044e800d40c0311804881411400741c7c0e030705580258680c028080003d01c2c0000c48440105064104540e03d010141d020010780f2280308004042042034a444d281a582200280006900f5400103800900883d02845007400b4210b2032440d07151815440392105812940981c0190590680000c1030000b031030030412880002d00750031901c45285d541340507904035509480b202500c0c01480d90103001a80707480d50075020340d0b6043d0404024130900d04c1c0c0103002521440f01c150000303440b61401842000c200d2040c02501c2c814a01e4001c0c800c61000410801e80d500d03001003441d0a0340c080b084141d540c50742013441d4030b50440707030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 18962398 1250 18961148 18961153
    0x20a0b090d0809010b0901051504080303150f012604020a0503030c10060503120702100212070b0a14060102030d090c050a08010203010f0b090310050c070b0c0909101202010e0a030c08 80
    0x14030000c002e05403000a4103400709030b81444184002a9103010401d030440d4802c4a8140c0e501d0b685a03070252181c0140d5122881300e0101104001801c40180100b03c80141e0480d405008581303003070019280e0a100c4458600521000b9030f42600c1c0e1055a20f0310390700f0500050080b0200c03a503030390000e840d50b4041c00344010340c5d400841440d604003500b4011040640012406040c0304000a5940d010070301408001038420001d08882c80072f414000e200d45554000060403083e0b903415a820001c00c41c11084d0303101c0c80307201e1030048030030f2450342501d2055004180503800b840ca0868440f1507078000d0101c80c0400d6824009441000076030382e441102400041c0008000543c0300c0d80b40001c1800d4441c0c1e02d5100543e000f004110003074441e503012480500e4201b0010300014607031180f4062603468010400c004040c8401081805000c6a00c0c0340540140141118500980d1340c4046400303c41103068450503c50203c8a43c0800056002d121002403d2502520781042503a4988030001d004446038405e0340d064 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 18963648 1250 18962398 18962413
    0x50402062703010606030c0c0318090221060406061202070c091802040b0a0503030f0a03020903030406050306040506010e0306060409060e0a062007030509010c020103090605011e05040e100c020a0b09 87
    0x70709084c0514401440c0d070781405c00c1150800c2c10082e22158544070b00800700820600046044c458040c04003001d0503071803008540750b07400300d120f00c00035261244200140704612400a0b034289003500a5906032141076584482c030710391b000f112074003a411040013220212005640481d030501c1501c41d902a8101c2104e544071800312138018802103840c000308450065540c4441070296031800402c90700002a0340080710740e200c2900c90b0440082c0281e00c8140da01d800002000651158000080e5000310011201000a522040019620390f5002c1798540d07090382190001403105c0c81c055101030328044c0281c00103da10182c0000c100d01b80310405508807205695400e54417a00400c404625854115908000746400745603100542180680803406041100002d42c401c1164460f8000c00c003940d41c050410700140d6101c4046100c8064041081610311440760400140c920b480e028a11000480c9000f60008111509968005d007406000301000d512980d00c82e14005058006603503c00c200510180035007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 18964898 1250 18963648 18963727
    0x2090a1a030712030e210105010603050c03090a030f09050409080a0201050601110c0f0a09020a0807030b030318130e060702060402010e010f020c0108060112020414040c090803030a05040206 83
    0x240e800300358a000b540031500500028140c80010a0459014200a910382c488000001c942010761000400c490309003c80c42c1c1d0510005420283c141c4006460070303c900d0f52030941d084003c0c04101e5070480641d00103100b100110380604080310040e20603107480e0240c50349a0000c01c4c25100c002c0c0084509250019030f203013100e54207103d84d0350811300900e080300e15180b00030003003991002003407000c40c403402040300d01401d40d81e520074845000303000e1003100b0742d158582030601802c072810440324200400d00b08500c2c040b40d45404401c41c2d00765003040c3d05040301d6031880410301041796500c4100d842002e544014010151900708062803055507550b00030000384c605440010089a1310002083c1030100e1001856003142d008501c2400741c4100386420744096680340300480b0b40303101c260b81080c144d070301c002800700b05240301070b079114940c0005850174006500d00810132140c00750f00d032041c0b0466070014408a82607403041e400060300a400140882d0070503400018040000c3c21292a0552459040410400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 18966148 1250 18964898 18964931
    0x1020a05041d0423030904090302010b030c0a05060414060c0106030507030309061404030602030a0b10021608150714090402030705031e0c0f090102100504050a03021203010f0510050702090a 83
    0x1015600c118098002d05061391941c11110888a5106181d1212441104003207402c00c196201c4400003441881662614100a402000d800882c0c41c001d01441a0308034140c1420b41c042000c4031b0000d0a001c4c41e0a1910fa4a1f0020889404503036502c9030341040f0140d00f86500f401400065800f4001a0045c24510702d400b070078480b95070780b110342840400d0303004103014074103c03042d45c0440f03400c5200565207607070b48012040186141500d4607031280d10300e070114009950002d40e080300041000c0b0f88406103600c7d0001c035640c441440c00f021450142a00004507164458200c1d0718400c5d1020386580d080054640001d0140d8204503284400108080100424031490005c034039001440441d80082030f0401c0500d1502902c980701c2210b9000c080021401d01d03d910070072110420b1039040c60100114185481c01c1030701c0d071082040c16401403051002e240040201801100d0480c2d5003880a0880c4078540390a111090400c11050000d0003c240301542c0503890310200d251140c4141c680000743d0b140860022030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 18967398 1250 18966148 18966179
    0x40b0d05060703050f0a15090e10110a02010e030f0405010e1f02030a0905040902090f0c070213020a02120a020706200f06010303031505090f0603010b0a09050a050a1b030905010b0301020a0504 84
    0x1030025042c0400d15440da001f4000341c0b0213403405244041211800c0c1040a03160065803a1911440c529100f07003a00b0640000000d460020038650083c401c004a1040d09a033b01d0080c1d030b442c05440282048100328660050a10406140d0041d00d007404040402446066240c40d200345040507030400501c80d081681c1c4a2160740142c00304542c10805004241c0218031204d100501000305450458049951100030905a540d500c0e1b0041c246208005401180c0c0040c0d04401c000740054880c51045590b00700d50001038402c000380642c010491189890011949000c210041050a00b0201c181d0800420300b070091003460307040035000b000709503d103150080440c0c80316500c90441840d103d000f07121076541c0c101c079150040c404900f604159204e0000081c0108100800c059100c40c021b100010b501000380c010510440c070080d001c118980d10b07100d40c4000d44950381c901402c1c296800042c06450741c002c1d80f02040c8240a48000500c000c00c0c40f011a007240c0c054042c902c00300340c000c42e0400100c403141c502003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 18968648 1250 18967398 18967411
    0x18040605070f0f030b0103180c090b0a0302130f09082b0501060504050d1515090f0b0607030809150c0c100216080a1b0803060f01020714040b0d05060703050f 69
    0x880801100c40b00402064000c00b001003090784a8405100d268801c1d04807840138520b01018280040721890300f01c9070340b22140309501c8424140403105480c4d00c2c01180000442c0c1d00901024500e0480c207005000400c0107113842140d80c0d689541c5100883d400c0c902400c030303070b240100d000f5210415401260382d80482c2e01c4080d9245500785070050140b90f40c00405c0e90101c0d0340036104101e108180d840c0941d40d4080d0032000075905458104100c8504001e0480d08045030256007003000094004d0f43e820307003a100301c5448a40c008074104400c0d000680300d44215903021029a05035121340030070f01c4076040c20030402da07047d2354410000f00382a010b00009005148201c064114210315081c10f14146440c404010080035052940100b4182544c6025000d1000881c1000d0424a010704483c9043e408640080e0f810318040d0020750030030100b0b035000041950a40f070644804003c150850000c00016112044a0941101e020307040000018010882940981850b842c045424901805402d446a1004058 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 18969898 1250 18968648 18968657
    0x90207060605010809060c041a0705030307210b0d032006040506010602010c03020403050a030806030a05060112030905010e01020a061a09090114070f14031008030d060e0a090c0b03060a051804060507 87
    0x1d02684189076400c440403240d68109c41d082d800c44500084995000d80c44020300940000020044075907440030190006076502401810010301d035816140456020691a40c2c014400d80c0c200d0021a020b00c40d8030b08031640c941901000da01c0032503442e41c103011040c0d8080342c0c1644504014060260280a0a200301025140841c1011301d5034894940e2030580300c40c05000c0c02400c8000c218162400d2011070911900702085954550356841d0a900a1f0303c0c000c02030f000a01403100c007145540c820503038518403c0050307000782081c00c0e040c2c03070b004000c0481842c1d0000000300c0080c0074025840b080c80303044c4a035079900000100c4040d030080021072054010245000c00c08211500342c01590441c000e05281024800b00c184c880d075500300c140c070618545400c10007182c4000720fa04104a0480d410110503200a00b206944944403136042c2c100350f0b01c480341c0003803138403509207418440d025548000d5903100e100100040542c80d90f0300d003c60b8001d0010201c8684010601d000c01040c08040d000b15600034407a03190 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 18971148 1250 18969898 18969901
    0x705040b03060604020901020c030f07031203050403020303070807050d0f02090901080304030803012709110a06030b01020c0f0d0b19150b091207030b01080304060801090b01140304080409020706060501080906 91
    0x20b500c071180244194861940420100001c0c0d03c200606000d0000140407034a481ca80420303615070fa00c0c003d00c02201d14581ca00c100604403442030040501495141e0001c60564407a10401c0d00c02000c0241000304020b8248036400c0c80d56103601818502c080008401a5200c8654050104502058101c1d000d594402c2008000007001c4008907411551801601e45c07014070000c3c9010300e444c504450015010342050051414000c41c401e4440700e854003182c080442599884040d425220302200d41400741c2c2000d408901c5500b00f400c1400740c0117400070164507803442a5542e40d01004002e48480501e1052142d002c00e140b020782c41401d501051007100c2254085c9405e2000c0344511070548414011a82e80742e0161500b10204400409141d0107070f458000c0b0340e111259070703659400510444c1c0004024800002e10070313426200d40c4800d1078069480d404034007401c01965925905c0580215074850041100040540c010b00c09000c0f058425100850280d19001c0010110b00c0c004e044804286c10040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 18972398 1250 18971148 18971171
    0x9110621010f030f030507140d0801140f03060105101101020307030c090e0411060c0307050a0305030702010b04060f15120c050d050603030901170c120c1b0a080f1b030a0e03070504 79
    0x2c030084103945c9807400d541c0d100c1c04c2c0e01c0c260710300d0b030076901c00e07801c252040340e00c0000c4581d008401d090580e11004080b400d099481002c0040c4140c0b1a90300a2305504000d005100c41d00b0800c14030030800d1400d043c44dc0c81d264410501070b007280c1c422500c00780001e40d45d1007070b0307000d00d503000e5001d40c020098041c1496003403c180c0c9942d45040c941c5081181701c2c1c400054000c00806080c425646120340180075640004142d04029065900440b42c000040d480d10340b681d54a46003600c204401d440148420050a50400442c2140321388152500401d005621210001802d5076005d070901640c03c03a942e40d6240c1031310f819034009588000d448035100750014010365131aa40e0040d1801c158412101039240240c4449110305420b01ca140c1c45240608a00790030801d1134041c120040080d80f00040586070b495440051840e100c4403d000001d0420b038003009284945862040540300d50724020224188000e1444021455903228030305400c00700f07000c0404003c041c5001e00100009200c107413000d126058004c1d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 18973648 1250 18972398 18972413
    0xb0601091a0d15080a0b07090801060e0103060b0d020a0b0a0815060304030e01030b041d06010501091a0307021204030f0606060201050601050a2321090307080d09110621010f03 77
    0x542040342040c3d50b4000419090704a8030715100a00c0c1060541c1c03085a02070403c440441c40458611002c98440d42001807003c105105000c1100c040c00c01d0800306074255514200070300005561680d005903580c202d030015941e1420340b01c00900901503125038400c60f04a02030024180148030b468082ca090a0814850329510100c1e54091713810f02c0c02d44100810100184c000745554016a0f802905d400e0000c414400c10700140ca00c5010382c00111010f581c8d0320001122a500240100c5200146040f0000402019980911b402c05140d0068031a104003a0401e4041500302e0340c03003034174400c074007442d400240a102e10865001d0602480240304510b81140080c0440c46604052010454507020001d040d81c203030f04d01407240f0707080d10b91503076900c2070015070f03014105c42180c41803112500c000000c203449080000c111290a54030500d414103122980b00030300300824000300261744103c0781d4060411141d48900c000d1440a030303004c1060b60004400301d0f0140051005803c403d40750441d4180038000704454 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 18974898 1250 18973648 18973657
    0x10207020f0918030a05070212010506010c0f060204050310050a05060a06080118020c07080d09150804020603040201200d0905030601030b01031106040f0f061202210c1201030b0601091a 81
    0x80e00d40c1002d80e1103407441d000046041d1120224180404180d0781030b519441001406201e008075040090b003003a840d106401c942003601c40b103011603c04200c00000821112450491501440c3c0050800c1d42d500c02003410031a401c6c09030f0a0040d62041004080e02440c0f182d00d82201060742e02145003824908090001e040c18010721084a004010321070812503141c04071209400c1806c19214426a141e98580e902d820004444010460302280070400200380c4407681d4030000107580e5500c02c3d03103071a0288900c5a0020700240d0401013141034000c41d40003003080d010300d4800c40d04010036010f42681e0004007440a60b8003c64800c1c4c002c03000400c00b1520000c82181035941090315002a9004000003400328030465018410600764041d0008082e0b000c12125001c440741c0392919280324500040c880700300e10800200350451010b0050b010f0030f034811000050342c01010386d04014540b078840c0d809085c90440c00d0f4402c90302440c008042000c0e95911a0f4604014400890558028400544021554001c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 18976148 1250 18974898 18974929
    0x1e010804020105250b010503120309032b051305010507050901120c020c0d062301060c0b06030c0604030c26030d05060307050d03020309120f0706030b150a020d020f01020702 76
    0x5010900070b203500c0c0075103144e452498000d07070001400030a40c5068000d04009104092080c000c414401c000b41200b041100d00c9520b4200c040c624003175070b071614000030581d03152031150007088101c10741483c00e24900c02c0c0d50203000506100c480c0500c45151079401d48500912190070000c0501003591566000441c108542a9214000c9180d16100f00c0072840c20350407002281e446103c040c1c840080c41115846010000c0d00388001c8240d00120051a00c00490300b03200301c00004445005100100e0030301c05c551500508010103450480750454001a403507049a081a1051480280308000c50001c1400a40e881240103510140620151030410746030300a036181644400d448900090144c0ea050000d08081d11008040c0c9882e140c0c0c604000790740f81c10060400340141e4a52842c10001c3e0320000314641d003818040c00030444d5500384001217001e0000801d001e90424181c0314488003e58081002e018081c2c0c45034001e00c4040c4003080001c3c5804e1300062414020f9104005060240c4c4450024a16802 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 18977398 1250 18976148 18976157
    0x3040506071103010212040302070504060e0604020d0605040e10180305030613020702090a0207050c0306160f020106030203240c0306030d0e01110d020d1419080709080601030c051e0108040201 84
    0x201c0754100205490140051aa4954030000d80300b039003aa001039140e4003c41c0254200c512590f203075400e20044558078015400c1540d040b100045091a05400421414003e070001040003941c03800410251940e10301e152503250001ea15010001791188070325080c580700c40a45800708072180d00d014000c1d10020b0050b6004081c03130b510920500107181c04071100c00e6405001888540350400842000703420075201120300c0c0c0504000c00040340340009095000d81038034540c0c0f8601c50711011007502c201041512520940d5240d81002015070781c2444843d5016130991074001604000601d04c101ca517000800003011844284244003198500140903440c43d0f840381001111144c0f86001600d0201080320698600c0c464a4038903181540c0c007060b00d1403c003141d602c5540c0e8910000b034041c8041d000d00d01280d21030300c1499868045d40e51060410607044001810403498a940b6026141e09184090700b060380e06416000c0d0030081828075940200607007100145200c0102c1302c01000901d0000081c2002c0e0400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 18978648 1250 18977398 18977407
    0x904080702061201030b01050f01050a0206060402090a082508060c0a03050703020d0e011505060903030702040b1c0c0e01090603050a0f140a030206042a12080417060612010e03040506 80
    0x1500c80750216443c11050101000303480d0382d40d180040704a502401081d004001b00e016940c4d403075000c0c40a4580b240d54a07000341000f9a01d107400c0c40000d40011400e80c2d800b518102c80045c2105090200f540140e0200300d14189a21610031004030305403155201804547c800350411403128464019682c07500c0f42890049031076103941c403080b8068003810070409101071801790848101c0784c05508c4050302105000701e05a04551369020403c1350701a05102c01e405402c10860000140f40544c8200243e142c0102685a08081945100320702442e00204881c1c03811010700c24084500c800010750700400c4071820600440f820766441989640449400400050034481c5100821040700c0c40010042c05100c101e62004445050080d5a404c040c0c0d0b040da01d0815500000c400300625110840c2d1450342e0ba840e40030140d103449a5441e00444442c8141e4401c00b0a00000c108400700607034884105403100000d24030b03070800c2c404000c0034524041e07020402d81c0c50080c40c2c54036000040261412207004941c0c0c240c58 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 18979898 1250 18978648 18978653
    0x1206150307030f2a080702060705040302040906020c0d0503070206010509070c060c11010f0f150807030f0305091017090a03080c0703020f01020705070f1508040b0717040507050102010e06010509040807 88
    0x40c020040e0541d022100b401c08003001505480104e43d40c2c2c0046580364149511011000d90b01c40005030307a00c0d000914100002c0c009400c16401080049101c2c903c014075240c00107082c18200003a502c801c00c00994000140803003143c3c1080400d01405d0110f03034403200c50600341e001900d4203600300c5000381010307154040c08030168002c0306d6442c07102c01100d0090012040c6104910003e02400c1c101c0007020745481c0c8201400740d1221098002c0d0340600000708a03103401e42e143c0c885a505280710031010803000b04005211174559500c0c85240080c1d40d1980c05140081410103220001c004040c60750661080c1922004a42c4c40b6580c0c03500304291001041e03988105050032814034010401d00c51096000040c00c60400000160031811102c0100c0d0040006458079907002803500055211400030300c0c01d0300480c02042d0000c0b2081e80001c80350a00c40d242c01c400c000351002c8000200c6007901d5507013240000700f025580a000c2d460160005c50b000e000e02d5818140002c0c802840070704054900c100219070b5808 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 18981148 1250 18979898 18979901
    0xc0409020414040309060f0903110111031b03090f0d030c020f030712050c0f060703090306020a1106091005130201021509010608030c0303070320030a0e070b0c031206150307030f 78
    0x124105071180d0401841c3c00d0802501d158064850040022000e859854185210b203481c202541c1d4002e001d05640303040180112030103100c0e5030410b48140002c0080c030081c060f05035504041481840701840e1a40caa802c20000460505164540903128110400000070f43c08100042440c3d41200c10860504000c0f000c82d2901209402c242c00290782e0300340c07103001d0250002e000f50824008507544045081c4007014081c4900485400901042e46045e0502c0011215000750003041e9103442c140e814840c02d075003a1803819209540d442d20640082c0c5034208030104c0b6006d041c1d4820300c0b240e148840d41c0c0a82e40002e603180c0710904003828559502e004110244000e40000700207042d00000c580c1c031f030002c03d81c00d50b17200d0b807082d501c1c100420325148040ca421030051161801041081c20135500703568034020b20a018022085400c02a4042c800000c901e80c01407402030001604008011915100c4041c0e000344d1407071000d807229226005402c14205041d010a003120b510814900e40800e90545043c1010f0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 18982398 1250 18981148 18981161
    0x30305030f0405030d1a041107020604030b0c09040204060305071202160b0a0212010303090e010603050c030a180b0a02070b0c03061011030702180915060303190908070b27030c04090204 81
    0x15608124091b203102208441d10780f00d4080c00c0300c00300107510707400b0030804052003000e2000350840b00c02d01042010803907401d141903020494503240c03460104a03100041c22030307002d41c000d400031a0766002031041c060390000e41580346014503802141f40030502040424a9000544028820903d003c00201c4002140d01600d860202c000034402e40c6586902d40078001811a00a80d0702511003030000240c1c0c18400e014580c052400301326a1441c41e00d5000c0c0806c060044503e40025043c095a0712500142c00112524030507103920a0060312034a8510b0040d80303041c80030f000c6001444050052201560303400113442d03000700450916030f44182d820340303115081d4010380b030b0007075030200b141450036a5120307840c51488e20407541c003000d0781e800c04034071044540e10302015600c6580651080c86080e420b11440811400c0c0c83c0385c58100030441a0351b40401e98500f14203504181755504000c1842c1c584290441440360039001c00d11648520a02001e011075910080b0400c03251180d038490104c1800d64989500c0700 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 18983648 1250 18982398 18982417
    0xb04090207020f0a081507051204030f02031603080105010e0409080a0c020d05010501030606090522110a09050109020405010207060206040f060207061407030b190f0504020703051b0a0318030305030f040503 90
    0x41342155a480009440d8800399103008010788040001540e00362140049642a200250286400e80c03115141207d455070780e00c54110640c4000c0051000304012102d0742c0d003080d40b00b6034690041d5810900010036001d048415540240c0c01c2c6003c0c140010341c8802030300c00c46582860140b21084103030000809507844581c0207009075107400c0004c01030105542003241680c1903490284016112050184140381400c1030300003010f01041d800d00009461401480504500108034041c110b03100c0768088202d81c82a0f01101c15654009000c1040356014080940241042c0c00641214a0540c5a40c00d0035640c040c1d00402550b40081e02a0410204d58407401c200030100c501074402c0d02e4010006401000b003003101c00c6c071800400c040302600341c0802c1c09440507518030400c3c9005080ca040d0520020b5000010210305201d014008010f221a0264600340030030460001403060903003d003005006003c804c0810440c110180b002800420741090803070b07800c40351342c2c014440c1c1941d0780e0600c581503000382c0109 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 18984898 1250 18983648 18983659
    0x20111040902030402030606060c0c0906040b0301020a0305090f0105040503030f0405011506020604030e0303030610050309010f18170f04050f040603051608010501050904030e010f030e0303070f03050a05010b04090207020f 97
    0x8941c00d002940a184a41e100354111145611003204010708c602400519140c0c607400341101854900341070a0041e0400c00240000c40c0e800d04050000382a0382000c0c4446001075618420402c4254041141911100070180200040d040c203803112626440300620200040401c080450104102544501650319032000d29041240c1c840c10002d440b29004d51301540003501c4044118214035003c400c40380107480c020550700d0440c034000c0f011713a4144c000a240e810345568980c01100c40341100c0c0250034510031080c0341d90840c0d40d103a00d842c0500c0381e170036141441d080f40f050101d4181041035600321015074000700c6002a200d40901c2c00100600b5494100520701d002e14156075140d0b000742085901510100f0000f44070583e202d8051094134030088401500040b681c00414031954000c1000000d669500e2070007141c401c03090081145141d0050b9031040000781944019580743e640b61046541040b91504140515407401883c405580990300030316a4143d4001081400c40d50346440203400c080d070143c071 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 18986148 1250 18984898 18984907
    0x1060f020a06090b0106020c030d05090f060909040302030910020304050306130501020712030203010f0605070c090e03040305030301081f05060a06050a0e0307090207020901050a0b0f0703200606150703020604080901020111 97
    0x11304c408660002e1040d03002504c6800d004142c0c40c82d0120b90101d54507141e550385402c00603144200101010307099081c9411050401050309607440303101c402c5104501940042d580d40780a2002d01015060b201c203818110740042c0b205000c140c1e008130328075400c0190011003007071030b5946060035030081c40346c808010200800440a01034468058000d14120b1340d048018410035643c4440642d07c0344900b9400910409480005100d41d00d0b9a0344091502c80610003124142522036940529603442a040060341e60b116035850002075480044945580015400500403420840e022644180381405240d0500c000480d41c010403c2c422041c02c5c2300280000c086500c188d0b41c440ba014000d42c8400760503401032800000108082c284041c1e040102c5030700050345464540c034038a401400340c21842c011002c018440c402d6034640d01c01d1a2805e01c000e19110080c00090900c041000003104100f04403503103800c0180005008a9008145294069040104140d42c3d00c01000101d005007054542d61282210204 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 18987398 1250 18986148 18986153
    0x50c21070801060302070506011208040302130b040b040e190201030b0a0608010302032107030509011202030a02220513050a0e06010314191203091511131a0301060f020a0609 76
    0x10011401032400307489640e01039803251011000d03031190b40d4000d06a03921802c01002007040f12104203c810380901000b504103510fa0f400034001c0402c2d80011040c036070300c1b4408030700a071070148114003851404880c100144800d5403002c41c2c441b82a00c00c4080761900100c02c03141964001d40049015002c0145039081071512000c015054903c2070100307900130b1041c000c500c0700780e4410b42502d43c40000c1405444d41004095a01240c1e16400841c810b810410031540b11a1441c02c41d0004c1d502a41500320050b0312030b00d03007000c191010194001d240c400c0354450201040315860314109004100c0e44418081000ea81d500500005041d0740d00c0c22039070341d11070b00780000309100020007121303688486038045d0768500700c3c3e00d4008104070040c000050090380304582d000342d14900039401100003074411080d1501c0d00e4001c00c10502200c10100f814009508000b640c82561000140b420380504440d04580e00892641c4003903040d107000500491040c0180540713400e180e41e0017007240d07261a41d40003d0030b014122292 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 18988648 1250 18987398 18987457
    0x40e0d020d08090102070201022d06190e0d0503060409140307030503060109080619020307031b0f020d0302040b0f0906070519060b0303091f090504020c01020a020705090f060103050c 80
    0x1040c40c0c500082c035402c042007500f10103008449081d07030168001c1c051480402d079100510382c003d036100c2400d803000c02060503040c0f10a2000c01d200301c03043e0030644261030034041c10b80150b46403101401010b4100d03002404025420505a0742c000c0c1c03050750b0009034000d1034a040d807480c118140070b1403414407022a8400c10140d00400071031040d242a661750f2926592460015540e1030251643c0b0381440c680144803c42c000682c2c050341c0d02a1142c60081001c000d5000c4081c140e420200d032020000b502d004c1c0800841e5010401410301294910301103142615001001d0018022044520100403001402c01c2450761a44181c45405801600380c5440715003c10f846201d034090751400716070503030034006407948078a000710540307070191009890030b0f4000c0d258600d500d01c1002044401c40c2408a07440011402d0384691000c0e0102041c007800051b6201d0412801074500703001544814803800e504002c00c008034400c2e540c83d0360415020308002ca40d80d110100040c2450080c454842c03224010961098500c0e2001c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 18989898 1250 18988648 18988663
    0x50705010908030307050307080601051b0d080115140a0c02030d03050105040f050603060403030e011d01150f03050312060423060901081c0c0503040b04030305030f010504090c0311040e0d02 83
    0x241c9500e420550b450310030302d4580c00100d920705d0210304203000240340d084c054030005610480516000b0714024042145405040b80e01924520551281240424030798001030f08501500751500c200c554440300c0703100103021001c00380c60340400c20740101d1319540290160510703190590b401016250704100700a4010000c000034814144501d040641c9200c540c491485154003030113000e400382c10141c1d183d46043e0080c100341d00c40040250340e11500c9400c042c04844840003a0162100003042086002d00c0d5480d4403241c0c0d401401c8100043c400c04c10000da00042150b009400c6d00d0f0103410903039241c10004005015080400303610803200502454a2440c401003103109000469544081da44c80707400707081d0307140c041000d49046c8051407040f854181d400340d0f40c9070301000c2c030990031680b500d44c545991a01c99000b590003280410300c040140500209514103041c0980001d031020045e982c095102c0c0080141a0302c000b4208511088408585440750741003424502461812160b52840442c4001c1d9644003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 18991148 1250 18989898 18989909
    0x1203040309050402120703090203070905090f06060909070e0403090803030106031407092102030102041d01080f0309090c180307031401110f0403020103020f0c0a0f020906060304121d0604030507 85
    0x14a0744020540740f07454402d5618a1031402c010b03004035500c010040d4010546110260791603ca414000220b100560103503600c5034803240c000e0600d41502081d07103890000c0c0a81050312400014042001000e40000d0390300c12284150030b00c0e052600d139810151072034176103604201a00d000000011130907a1701900088140c81088046004541c1c400700c007214420214040c580154404811094541d01448091070005000800044c9403a917900c030a43c3c07252650419072070024103c580100220b440c180300c800a6291848040d5150104c504005403924800500a24800402096400b412074541e0644540a00b01404842c000c54980c1080e032401c5002c4410a01650700300072034120006400016102200300c41c1d01064201400d55006401940100e541c02c02000014400d21955150401240b00418090000e47e0080d401600510413450b030001e01d2a40a101c08109000000e500d045c0065079048007868824113008115200500005114055650080380402e011040c400c010a040040785c5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 18992398 1250 18991148 18991157
    0x60f0f0c0a020601050f010207080102130518130807030e06070317060a0609030209060612130507060e090a0c020c0303130807151e09050603040f061505030a08070804030512030403 79
    0x1540c103485004148038140840c8010b800c210010005800c00c00c1c503030002d654050050312803ea44400d002400c9800c0801034094000b01814100701c181800f0100d005248861004680d0f213240004507441040611200144094400650201810310803100301c0c1008600502998bd18501400c0017440d00d00032807801d900b5400444089103441c901040880101c0d5096183e0454803443c540800c1002c0a00400d6140c1050080242aa00c00700c0454500c0c80b07150040070b07920030036031035050a40c40d1000681185043c0100c2c41a40700184c0d0b0765814031b60740200c04c0c840104140914400c128108104005007030303003510000c242e030b24100c0602040388040c0d41082d02259040c503a0b602c20010000b01140001011070050469a8421151030010144072403090500d007030303a240c3c0d660115080f41e01c12201510303180b454250807002c01c5418022a0381e011b03080d07419800302508010003c1c0c0c48034500e04006108100000d020000c01c400703a402c3c0c0b0000c680100070b0b40c414044410100c3c5c100d5200300c60450008 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 18993648 1250 18992398 18992401
    0x4030929030c07021018050904050f0a05160b040308030a020c010b031207050114040b1f030c120302010b0108042d0c120512040315050604020c010606211a01031d060f0f 74
    0x40e100c0d141c5407084002e01b0b158600c01c503281c8400e00945c2000540191601e018411101001c03c108000b000707440752046004020a03042500a0300c0c0c418405d40081812034010401000070800c000d0580703030402d00080006035075820500c2c0040c0100308418417140c150065400c040103800040f800380c01d01034002c40090222103601e0b441c0080180040724000c05543c0f040d008202c00e10f1211000383d40d81420709001c0008a0b84948038014030a4250f40050710045200748504d0030180d080c020040656402e007800c5002e4102075941c1102030300ba4139418a40d00300381c440c59501e150b040200740210305800c5000c0d200d500e5160010f4003543c507401f40d800d0b01c0c00d105480149000180306c00840b03048a4011070742c0f8400001010820000c0c18000e840a1f50154090042c0c0c9079502081c03148000410385500d5410040306a4040210380511480300d40780058600b09070300a003040200c494103e045400d2a0000d11201c8a6080780051100103454002501c503d10070007200049105507a4082c00120369036074440d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 18994898 1250 18993648 18993679
    0xb0901240206040b0a09030c05060a051008030c0a11060d050a060f06050705030d0b0a03060c0e01020d022407030603080324090601020d0c0501020d020d020405040e0604030929030c0702 81
    0x640c00181c0d0004c01c003401c1c2d04001120010b80f0740c000d4130301030b00c64039002092000c1900e5291524074255480203e451b030302c4d8180001c0c804505840001804a40043c50038a800c0f50941e5482d05250030001d0640d041d41003003071081f9034408003194100d104050b420040c5003046c402c007000401c0c0c94002c00000e003101c05008101240620309551074076034440001c504c2c5c40f002440d182d000d025944429500000009000701c00907229000f4004140b60359514241002804c200080c64031524418800c00d5402000d4a40f01f01075032030603040c83c102c80740e010588180d2541041140201020f6002400040e00441400031a001e00b400308803002c1142174403283e642051200b000206581030360b920780564007150b00540d0342c0340113002002c1004e014800050600641c08180003d0b030b8800805070b50020303800030303051046113041c1c03103968070781500280204080d2500c0c0d0b80142c040e13444c500611500925110100c3d000100103800356600c5842d45481940300d0500c840032614030303084064202d11440402002811 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 18996148 1250 18994898 18994903
    0x106050f0102061b0a0e1201020309060c0405010207060302090310090503040e0a020301050612130501020a2003030103030206060d08090a090606030b090402061b0a02040603080301030203070b09060306060a030b09012402 96
    0x55000324244108003441000521050742c081200c010510a40040c41c0359075a850303009801f010021500003585da40380c2581d03003e05041c1c006000c005441d07018841400141d80c006002400d80d145400c5c016902c0e401c0000091800114142c0d200c001801c1c42d030a0307010031002001900448101d10707039018268940c4000b040583c0424060a600b016080c080340600c009456421604a024111020f14402c0b050700c859081ea031000c0d80c040b010034200740101c50408100948000c150b541d110180d4115415030b80c0094a03100060f110511400030850704406002804080b50a106002032603441c249590f4040ca0000d800503200d5030020a241030302c8010141048031103144140d900a0500385421818040d4480400715a9205030080c4541e1281400603102c501c20b560203180291882d913203940c51803040600d0000c11f0b4100e43e01c1501c1c1480307407040a450b410140c030380103034048402c0e42c0c0f2402c894604800405011803400d600030000e40000450484504c052448801d0109584044486203002640e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 18997398 1250 18996148 18996151
    0x106030203010b0904090201031d0c0a0806040b0a0b1507060b04061e0312120204090603061503030c0803060d060c030902030c010c0507210b18010c090506030406110d09050106050f010206 82
    0x50708a0f0100580803141c034040d0f03c4101b689205041c0003890107030482c09410b4502005407a482c09503c000d501c6249442c012801c00002c0143d03400800d80392400c3c1c4c0c0d410103078407030180000d0011511440301217442d0340c51100007501840701c2e01c0c84030748500079420104058681440c80602031817400001041c60003540c0d072604552500400201e0819103191341da01c44071454003503468100b1581070302c03640c0502030a00041c401000c41900200d00c00d41107080c000116001c5006815955080580800000382c0007114032074800d40205150307459548580114010004c200700013091075240c2a4000f024540503404001103d00950848511030300450040d114240600c0e001740c81076014040c00c101c0c40010326084a82c002c11000082d0080e102c60f5540017010809642c41071001c0340301e60907a00d51020910440c2008032040ca000c003a254900804160f2500c40504064101501c0f0850880100281001c40c1c100c03084500c9d0801c20f200350703420000d000317001500032144562200e4454818a40c80007595a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 18998648 1250 18997398 18997409
    0xe12090a15080f09120408070e07031e0e0307021314101409040507030203010e0604140a12030902190b0406110303060109150c05030301030c05040e010c021009051f0e06010603020301 80
    0x109079440c0c0f140c51404585006003080c4041c480c0243c6a071030120040040c00041c044040240301403400c08030408161710004143e0710400d450582d49031407615458074040e5070b50050101c0025044000100c040c114400c4500180d00045540c0210301c1c42c200e194000004812a4200006180c50750f19059805100b244907400020f140b260382a100c500d49007170300070b400601c01d90480701c040b0707540d6001c80d003955918440b5100f0ba4111004002c180044c5115092a25481e500079051002d625603401480208400080e004c1654400304142152280c00909034000ca80455000500341c0d11144601d890744140102400502c001c01101282040001541e00440050310340501d1981405d40e855201c0c0039a03a0b681040104071295800414001d01c010b6010b1402904081da1450400d1f06000607038801da40c2c1c0d880c1a070326001400301515070114501c00c010300e0124000c42d802c0a181002440e00c1c1400780c4811101084180003903114401d13a2095000010041c00c0e10322580e40c0310001d034128007013482078 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 18999898 1250 18998648 18998657
    0x207080301050102011a030c1909110a021b090c07060914030d11070f020108060303040b0d0209040606020c0102121309050109050901060e1b0a050c01020a0c050106050303070c0504050a0e12090a15 86
    0x20070074603e02012030701032440661420300c0409daa03541d42481901d80c00308001e0300d04400010401c8005a06004241500c10b01c07503904c2e5503201d9194041509032000410b030706013214004c00c100e000c002194005641031501300b007500444400d0b4001c1c0680f41d43c000501e9001161908124040081010050303548168005066a0000c22160019100a1001417546a060008000128400a03403078060900341ea21007200580703c42240e0280021251b031604100255070000e07070800110380c1e00148005042e940794151940350900c100403480c1808454000034401d505080005c100382480f07601c540c0c401c16006000740301c001d5499121001d001c4055a07070158590b141181d004c10f0151035002001d06000d145881032900300c41c00d00721390880c0c0040c0c40100c0003070f101603541030500c07600340500006050114042c525001c6940e0b91240700c00010702c1601c0c000c0351030b040020141559a0711559070070b8010000e9801c00200380089004e075500000c0011b110300b18120010a1400103481c1c04501c1c00345030340300c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 19001148 1250 18999898 18999913
    0x5010f09182006040e04030807030203010305030a0e0406080304030f061512080a0c02040c080f0a02030114010311041d01090e032104020a030507080d110f0a0206070f060207080301050102011a03 85
    0x460006180700a8141c900c82c4044086150994440000400c018801c2640c402c0060030300d80340080c410103002d0300c01e2042500500050000c900c0200465005008900304041c0a403c000c01042c042c018550241e0358901001c6000020b2000858898a905110300010080001c80101310b0200170454025032072110610003100300042c0c1444001d100c056400d00301055915410750014007590907111683e40018150001d00580b10070283c8000d4200241c600d095003558142940142000b02c41c0c18003d04260301c4030300b08180e81506400712030140c441107410b10000001c0070115440c0c0074080c41040f42d81c62a082f1100b50841c008003d48002c0c04801c1c442d80c40c0410f07070b440c481c0311001c40035005a03840701c8807540000c001a0204410f07401090820007038100e403603060f24043c221015542c502d202c139800194000210100202d2080c1405504548061704d070045800c20352440da0041c8402400c3c0762002514401b0720148001850481b01c0c00d030300a2003005401620b10b4200310035983c9450301b550100302c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 19002398 1250 19001148 19001153
    0xf0b030d050a08040f0b010621060e070e011215030c08010b0a0303120f05091b15070f0311010504030c06060501020312010e0901020c1006060f050f030f06040b120105010f0918 77
    0x181d010b60481d005d040340640c8481c17030b500d0f1010300041c2a8041c202082c00d410701d010443e0f02400d0550180c0800b540100b01003450440395480135000240113030100103590400002c168041c0d0300f06109a6582d0100304040030489008502664041c0000d984102d200c8400280b042d0b814080c1403c0b50750041d000140c3c8604c1e42d50180c8503d000841c00500007910307a40c4822021500e4840c02e03100d400041c00500c41c110450f45076140d080d5400c80c14a00030000b4a06001c1e0780c0b000002210b000d20380c08028842c611801d402c00f2507015101e403050002650030f00b804e0005140d4002101c0318450f01500c0c0804c11907a5a5005981d81d20908001c2041440c8a40040040c506010301c940c0e440380405001500d030400482c00075061170b265440f95128165a03040900c04143c0c403220014590005003031440c900401d103030416105c1e0000034031000c0d81d4104040000d42944079034008000c05c200160219540c20304200b49280039010074080c80c00d021a101c0c100041c90340c5c0e1070081c07038030703110108071111085c01c4981c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 19003648 1250 19002398 19002407
    0x60e040b0a090c09180204030203070b0901030e07030807020108010f080613020f1003060905130302030316020114090f010507050a0f08060d020603010b0a081b0306040b0d02060d0f0b030d050a 84
    0x241041d03124280c0800041c40701810300030408500d0680c1d5802800c1420001c0358403c50180f1200d010a11384103000910058400013aa0003d40f505240c1c00c03038546c3c0008004074081c181003042643d0030302628078000100104080506840c40c400d80311030060381c0c0c0f2114011040c407401d204031450380d8061000b10316994604040760765517a0003d00910309520004000c204c0c2000045000400a592800c04100386087c030310070a504900003294a00380c040007520000d50302e0102030141c40f0080c0007004910740c2a0300035400b91241000880240c1c10a2400510030380c0c0f04d0f98040788017102c55080c08000382c403481c401c500315641c0305603d40f201c0c0d094034091f44c01100c0c4410010600c90300034051203410b00241c3e40340e0f000766000f071101d4480300b0381e16541c403980140341010181808507080540d035082d4811002e103a060325400102a10001121158140000d00d801c07030104020790007101c0080d00d01c40e4480c041d0820100c07000b40131703030500901050078103250703540f05011030190010740b050044001e1903118 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 19004898 1250 19003648 19003661
    0xd0f050307090b0307020a2303090603090304080d0c030f03050402061c06050a0807170c0112020306010e040c02060702011a0d030f021c08060f0d0b0408031905040b09060c04060e04 79
    0x20307140600b41c0549840d05440c4990040d100c1d88050b9000f581000204580e000d900d0740003d161007044811154101708155980c082c0074440c5106090100014130035030740800c20390303000340407002c101c0351220400c00002e00303121614070301900000e074440254440d0354040d01070b2600072580034001c5840c050082e01e0100303444400c0e42c01d1250303007600c0d0007001039643d690040303450281c081e030300140c00c20900d071060305180c0d40700c03050310010680c0010016960583c1c0107094840300303940011700503a40707541d9100101d8901c045001041c1d40a403920b0140c1c680580e000500c540f003010b2580007040b0711181e4007041908a074a00d150070340e100707007111080c5c400644110480a8441c4981c01158894052210340c080410040b0a030140010120b004000c014681440383d542200d1003a02c0d8a510207400c0c0d1200a44c80c58010005010000b0007c0424060908030310350000760f03454030300204054107013458000c00041065528650034400d600208062064100485003115140c3c1c41e1b040381303108941c0500c8054840e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 19006148 1250 19004898 19004911
    0x6270109030605010806161e050f04030618021e090a090201030e060c070c05010c0f0f051608010905070e0c0301090b0d080c06090618121606060b070b06030d0f0503 72
    0xc4080d000000260180a120701916445020780b070186454500407281d0122440c51030100300004907480c0640c140355106c0e1250f80400d1800c141e43e90426403131540c0700d100301c3c0d0006180e60329080719043d180c400030a86007680c505c2140c903610000d00d0b070100824030315210500103034011104800310f1401c06903a032000c0c0c441e40c818140480d0081c1c0c80040340d0b04040c02214a01c5c00c40c940005d4101c02c0004030340030807000cad050908213195001007540740c070300880c280d80304000c0c441c0e404e4840303c01c00c0c040104141011607060b145411209034581c00410701814804170100c0d00c0748500e4201250040395a40541d2040310308640103810740e840c182c3c42c00090b0440310b41840e04500303a03048120100303110800502100304000003d0a0600345114200e10304000103041000145280004c039217030709408500d0028030b0441828044c0c8800740795900f182a00041c1c0c070010003076890300d08001882aa54005400041e0107a6a0200d55507240c0d0141501d840d0848540000541d4100f08103042e14000c00245800c0070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 19007398 1250 19006148 19006157
    0xc01180506220303050307020c03060f0c07150c0e0301060b0a050304080f04080a060218030a0507090c03020405100801050a090e0d08040f020301061e06020111040e071101050c090f062701 82
    0x5486107802c62051660303042600016000010403074000c4c0c0410402000017010350080c4914900940d020f600010081c02c07103090010002049420b0018105515260620302181000310f56a4180051b00c04000582624025401c1c058001412005503007900c24210898039400d2460f45c0755a030301c10b01035010001c80d0100b860140300c04150100100055020107105410059544080d504803803024107a40900030312949c0910b4039000003600110307000c01107540c2944e000c94900603100707040d0081e0003513821507038102e2503904408008aa1101d41349040700c80913140c061500ba00c8018400a444160750001d0380e40c0c3c0150400c0c03c007140314005041d4032034012155030f20b0314415a0300081c00d40b5000d80c040409524003282c4d0340710740c003c440b003110000c000c50300080249250b0321000c04114065480790310000100700b000150703c035020f944102c100700404402042640303001801e015841d04103c081c03a0180b051010440d42a00b030440c1202c2070340204911300c0358000c0080c1441103110080c070700e0740c50402 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 19008648 1250 19007398 19007437
    0x10c030608100c0c0501060f050f030d020d0e0102071706040b010509070c0201050702060d14010303030b04020c1005090f030c010f0522060b0111030a05040302040e010b0904110a0f0602010e0c01180506 88
    0x94080c400c03d0081c11410080230922442d200c1000100420310f506280329400400048034020b40028003504240242d0404404150181c3c2c0140d050a01c240d0120044000e40c40b00c5010203040071641511442c4a00c10071580c036600c510034040c15040841b1143c001c0f074050503e04015602540c050040ca610003040a0303e001d429110110640c4d40b41d112610403003009000601c01c1640500909514880c140d504600307000305042c1845e1344500031200c84000a60718004599043d00601400e030800080c901120354031200244400d0080a407403140034209071620f00481d500c0a4000b4601002000d460295040e4a0154441e14000e0100c8044941844100c10310101d0103201400540010289922403645691542c0180815602c40951118440e490049501441e40c1c032060f1454009401031501180c003091400882d031000f006070491807071924001e000103103c560540080504000d100c0645164192a200640b034808407501030310714560800006203e10f0400402800504910140f24103e0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 19009898 1250 19008648 19008653
    0x3050705070906090c080703020a0c060b120a0507030303060609030206040b030723070308060d1a0915010f0512060c0910090e010603090b01150f1407050609030408010c030608100c0c 80
    0xf01d6229038405820262680701e050601303a0441526a4032443c541400e62030301d01c80c40c40040082c1c0402000600003540e035004d5101a44500310004114000300d000c480441c1d00030704041780c0d1500c09110843c0060306102001c00c0c00c6101e400440c2c1103c0e8060b110904090824010100036040100510104801080322614101d80420074001269800d4103040d80d40e45070303041c000c22150303004040e01d000d0500308081c2c01c002401c04098886918840740448490740b22020014100320100d244074555041400002ca45070502c0c039050000c840d4115160404038119001040e29100221400c14101034240300c10760050800c088080d00450440c5001c10304907443d801440d9500d42d007a00081d00107550303190b00004000b104440305000d00502c0d400c00e080303d000000700611007a540030989013084000024094000302c0c0a06541ca0298088141c075020701e0a00d45d92a6660813a01c10f40703407d0340c2004003c108440c02846190306648044000d40400120540c1c9680942329100460b0b00708403503440da0b00302 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 19011148 1250 19009898 19009901
    0x20c0f0706030507031d1902060d0608030301050108071d090c0403060509030c0f120703030f140a0b09130512030601090f060201020306030c0604050603070c05011b020309030f01060e04030507050709 87
    0x25120740c2d20001900e06210b07000908880b900891a890982942c0103d80b10000006014140881d480440e051a4801d8800f044450050098800c012400d000e0003150200010003d9810f9420aa03603072344c0302d80da5021b0102d0310b00900c440035642e0b01141c00c00019503400c0a03840150701c044100591450039650340c0d503400c200c900495007450941c1000c00c0040d44298244520040d481400008003c415040440002140308000703005081c9542e030417102600d00c0007600841200121070300c041d480ca28000303021801810f4400e2039903214140c21000101c00c034003101c00085070075812100038516a00028414070980d48064866410721002480001d4500344e41050301002c4e00c0641e0015031070303090000c18180340c10801410715200c2ea005207c14060b98450745d06a80d032007540c1e40b070f102d076403803c00c0d0410360b0041c174884107440301154031460b203403034156000002400b5044040d000c0b00d0710140d86843c03c1c1d003211414001d0329a070000031800f01300400d101d2070150020602030030039582000c0c0da03060b202c0f0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 19012398 1250 19011148 19011163
    0x30a0504020a1d01030605010b0c0706030f150b07051e0312060301090209093009010c030c080f040302090f01050105120405030c0715020d09050a15020a0503030c040302030601080d05030a020c0f 85
    0x1001c070880f0900600420480b4000c090042905200300d0f07041c50240f0360240e803100e04501840007050707078980501c900945540c208100d03c0d032030562803d82d040d8031009507a10550100006440d544503a10f007214a5086000f0450840041e11028506049004400c40c0c8a004080c000325415034a800300d0a000d80d90701c3ca50a809105140000c0807402030805c05a100000502d2020318400240b50183c052050700004582d4003910910300030f0700b846d03031030710b0180e4a218100c2030281c010103002c0b80c0d00445084940080050300d00858034600c040d84c0d078210000e4448824054140094414072280d041c4503412041960403c1c415000d03682000c2c42c82024920345455544078280560408031030114140d0180300490540c2414500307a080241000b000c504955407512800210b04240c07160b1301421032081c820307141030380da00800713480d5a41084100070f10700790401e01060303209009180002a0701c203000141d070441c000054a40501b0355a0340d42510000b500b1540b5900c609000d40d0001a900e003002b0f11807071 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 19013648 1250 19012398 19012439
    0x1201020d0204090b0a0806040309061116031101030e030708040b0310080303070206070e100806060307020102130b181806090604140901050f060d021513050306070c2006030a0504020a 80
    0x2500c0780700c0810000c00802c5981b081d103c0360880000c0c0070100e0b5102603010161a01070500310b281c0240100390707914164440d03180e461060302481e8040700b0041c03550f24881da50b02090b60113005124115848a07168880ca180080211204100401a40c12003e02840c0d0282c0702c0013410144540d524030f1300d82558012280c3c14016088542000700072500a0303899500080140c0301000aa644e0a10250450801600756845220040700055200341700350111591602407a803020b00a60703450319080e0b03494001140304801052501d402c041a418254103462268481d10304050701c03074441c0007e210403101d02030603043d0010340719084528500000e03000030340500e200b0000004da62400c80d0f0380f6103c042010703000364400c0e0b00b4605480c0c09680c030b8030785007071802e440c100b101941c03079403030b016861a01e07074181c2d000301d4040c0180743c1080682c5411100d043c04c02402500c8605d400c00c4800d4542182c01e50003501540e0210301400400e8101c0c095901255005101604d0361003a151500d202c013900e4034040001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 19014898 1250 19013648 19013651
    0xb1210020c01060b090609010e210708060f09030406050f12040b040b090705030c0f040b04090803100f0b0d020901020f011d0c0a03030804020607111003020c0d0905030c1201020d020409 81
    0x8a845060240f0940006141581100d82007111610018051784a001a454104000303401001456501d1101c1405501090140ba20b2070000f5a80311035290f000790300c520b80703840c0503803400101c6034030070415103034810343d51000075610341404e00c40305403075540103403440181003541171224400079128040c09602550103000720401c03c0c0781c1843c100b1a142402048015a83c101d18400c00203500d0010301c8035407801c4100e0352080d07805208800700300100100c3c0c07001e82d40141404401c406010340d40b8019809071500c2c40c0400040c5840d45a0015184a54800e41400500c104401c060303031021a4003030300703c008052065440c083d01040400d0300b9208100c00c00a081c04d000858882001000c0011030300352802502c0040400b465501c0c0030b40b2200c0f000300701070300403900001d10b201000303201c0e998407000e11001865210303004020304000b4000e400c40c03468440ca6114131030610702c00314011002a000c84400800134140004c1c18014080e000300c004440350141d42d002e001600380d008039800030b000a403543c0c100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 19016148 1250 19014898 19014907
    0x30a0801140103060b0a0c060902090a0606080703140f1e1501020705030105090703080304050316060b040509010b03060601030c03110f1914040b0703051603080f0c04060c060b121002 80
    0x1011401810086085050500c2d02c03100b04035200501c011b0b64900c00c3e0030f08003400018500c0c104803000e0103910034003e61003480c0e941040710b030704002e6010000351100d5540d242e91581d14030350705078221482100c600d54181020030001e41464003508400e41e00c94040d00010400d940340044804041c134094503000318440200c0100610382d42e04010300d500808080b802401079062003982c058683c010340c003025040362000400141803241c00c00c02c0b038a844044580d06d50384958203082280081c90380404061003241020086005041f050065140b0321038024007404c2240c59040c0190014246180114281134a4003800c4010000400280c0701c0e919954020300d65502c10316608a2900c2407103907105091280380c2c80041014085c10090790150f804440c02c0560302e001d0ba0034140c03814003403114141c00400481d0225801c2561140ba00c070700850001c803441002d13880b4440d801c01d060280d0f020b00b01c001804185114041411b640065002d030802425034480480c2141c502e0741004003580a08500d2600000e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 19017398 1250 19016148 19016159
    0x5030a090302030d05120114010203040302090f07030501090504210912031701090e06010b0d060f03030c050d08091f090b04051b04020301060e0108091204080706030605100203040302010c050f030a0801 88
    0x444c0b40c0844071403130500d1070038800600c26010003406000d0740309000716015000311142d0081085a01840d001000c2c000f00d0b240401e11a55107550881e0140c00082c03c1100008203c90395000f8a030080e0b62000b66068101850a0384100c40f03907410881e0000c03c44811000a0340e944019240d1140e2030103980c6800e454540c00c01428a6084181d014485280c07800c2c60400d0701c500e01041c4c003070540d0f40c3c8024107650792695064000140c607464116817081009030b100041059000040aa07820380f0503800c1d600001d0041c1c10039103c050040f0783c17030002a04840401d0407803280100740340c417503c80072040010b040400340d201c0a0015030100c80403980799000801c0665000750308802013403400d404440940c81c0d981890700003026900c152841034140f00041e03000c25455041407142c214800030040c001a181d43e56103044607600c580ca8468030380406d26041e404201c1c1d09180c0c4040a420004d5001140352030702c0c660045401c80c20500080d1070714020701284600c5508144024182074030704d661131800035414072 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 19018648 1250 19017398 19017403
    0x905041a01021501030201090b0d1116020102010f0b0a05010e0409050d030506010215130b0c09030d0914010c020a03020d0c0308030702070608070e130e03070501060b0a09050108011d04080705030a09030203 90
    0x90300e4058180103c03801000182e91000c0f12005940800003440d854000c02c0d030343c503000b42414070749060704c200010490201103482070811141d1507000f43c2c02804030388800d0034241c0448a881c040c80f60006c0320001c0900c0554092415204500005000001c045c05c0540395182001d5080140f0000240c891040c0012503034100290a401c180346c0d2200b42941c1481052001403a43d070210046c100150131000600740c4e142d0a0a0b2040c088000d000c0d1a803500564000034410354407405101e01c2000420030741c0602c0c0d4403821800a88076400340c8085030443c159000c02048003c01c41c41103071142801000840014000700265009041c9a001414201e040190140c40f410004040004100c00032200c0302482d0b0300e00e4010115007280038800184902401040c5045205401c170181041d820241c0000d110710640c00101241211a40d45c00f41307040d110720045a11402c00c3c4200c1410743d1030300040041703441e100c070742c199049480345418914088080d5103e074210b400c5108540040b031441d003030400560509 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 19019898 1250 19018648 19018663
    0x2a0c01031409060105010f030603050610150306050f0d0804050d140709021204140f07030804030b0c040605040b09010507021c0c1a04090e070504020301030c06030e030a0e0f010905041a0102 83
    0xc0007001c1101e1501180c8640e940f0340510030b843c1000680910214014080d50208001e1034000099034003d140c00032000c41d564445108400c880300d102440700b0f00141c800c0c800c00040d0b5130024402d841d1040c0c1038040040a01e0054020345407010100000555179554034482d41c48103116401c68001c52401003081400d24043d91300c42101540100005880c0b00180340c802d5500681c400ca80b24058049100110300d00800d00244a226200d507140100521070240040d20499102d44906990782d40c2d0302c030040c031072030141c3c0c440d9202081c0103000c20b01c029499000900006c4006140940c205001c68000456236070104111031400111481101c0038007100c0328104001d8419501c41ca10503059210000444d03100721f00c90b0b906080c0c1e40710560310044034140001c0c0300400c00180155220b58403800d10881000040c45844003180c5485c0c1c02c0c4c0d14182c404020380c4c010210035114460001080424407c1c0c84010861241c100107503050049002c0e91a4440c20070040d00c6042e0b4004560310384000a440c1110 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 19021148 1250 19019898 19019921
    0x50d24081005070c0311010902271806060603040303020c030409020415020c0a15020f061509090d0c0b07030f0e0102210f0c16050d0f200c04022a0c0103 67
    0xc09007001100754000d10a15044e41c0c2c1031a0240c0c5510401450038010416124002e502859011103004000004020518441080c80307440d042e94580c1c01c500c032003032042001c00e0b000581103100000c02510f001005144e10034041e017400345c604005040f10038250707801070300070004c0c0ca40d0100d0300348180303102120903900380d4402e03000a064005040c40007a60b1a0781c0742c89010107281e040e0f0805282c0320b20070f20400341440b040074111060350503e101d10f48904000c003100715000d24541c50004100c9400005c0110b04940241c555509034540c41c1c0366840c0507200101103000b495114058003402c040f00780309030b01c0348104000005845140c020302c490700d0364440520350302c41c4a00034420302815a5541019513046016401465a9400c1d200418807452a02e2400540180150303001d0300141500200032410300c4a00303517a00012025283e1031011140f4a541c43c2c0401070340603c11011203410030b54003e0002940711400d100500388124010042500c50080d10510b40c0c10540c0e504802d541c060140000307501 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 19022398 1250 19021148 19021151
    0x180b0106050a0e040e0102090301060b18010503040b04020f0d08070501051008030702010e0409061d03090a05150307030c05160305041403010209091f050d0b061509030c01050d240810 80
    0x15812003000f04491601c42400d489030341c0c0d5141c041c1d20003400354103c4280d484050001e00010350307100c0600207590030494038200504100c6051361920343c403a038100c84c407a1ba4003400c0c40140ea01c441e002d002100f1950081300380c02ca004121030b0004682100d0250901c1e610034000400c039841d101e811036a500c1607580c0b18015942c814005180180e800c6040001c90010030303100042c0760241030400d100540711101d04c100c00400d00800f48061400c01000914803920207603011101d165590b418064a110807c43d00d02040009001141100b4404e0304119091000707407510304d00b0090a040c2501986003021070480c0403800001d8108080e0032401d5000300603c3c0120021800d241c41d80c40070854200c5c006040c1c088002d0b1140f4040c00c00e03016800040081d05002d17000704a0b12038a86040c0310440e5041c0c0e02c0d5440342039092080303040581d10304100d074080c5001074090300c6101d9140b0015a04e0f9041140d00020307042d110b40364000c0c0701002c80403035103441a141102042071480c100e8024200000c02d0003071171456 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 19023648 1250 19022398 19022407
    0x50d030f06050f09100915061115040f061407090303080c07050d11071505030108060f090d11010209060a03150603050c03070e04090b0405060a0f050f1f0801180b010605 74
    0x750340f04240b00e1103080090b00e049240b6a20141c560401c1d4001e500400d141ca4074121160040071640d01150054800d10b072105004011032a45041ea00c1c0700d88000d14051a0344080018001000c0c1c24007009994481e2002180d01f0f02404100c00030644100c91080005904940420901d58080c5480c2d4220f80e004c3c8010f880d1821503100d05446d000560060814403030307000420308143c4410494800244502c950803024100c2e0240000c0a6500a00c6001d07124805e000c04204414a4279003040c2c011100040107021688924406442403000341c00f07152025542440802800d841702c100800c40403c0b966400074001141078166901800300307070003042c1054030301400c00120702141022290003050740d0501848003c010030010f40900f031094002072080d9907400900c4104180041c1407800381c6514a0188140c000c060707a030800301c800840340001840504000308007000001d602c00e454a150440c00303000c005845e0201c0c1825503404d02009209841540074100a00c00e518030b5440c050300032883c2c001d160 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 19024898 1250 19023648 19023659
    0x60b0c030304080a09080d091d06030a0b0c1209010501030605070503130f02060904020c070608071d0d0609080703020604110405010608190e0d020a020a090e1011070609050d030f06 79
    0xa81c04010001003501c000000c0b07000c080c03400303440d036a8003c02c02c5104603078100940c0480109200301038460b92a900d081804004900200c424400d0721403000034004081281d09500c40c01000d00c80038003000c41141c020080303448038401c00d000083c4500c10050000c6400d5240d0b19001c0c0031503800038481001c0020500c06c1c410201806014140500d80115003085152502e0000035164071410403481c1d801440041d4044035000c002c18180121011925076902555401c0c4044d110982c14049150b1080003d44030036907280f4248101c0449107006450014846486d40d5940000c1c0d405004243c0140c0d1001e002c02c4100218034801c0c0440803070680307050146500d0845c0c040c101710f00240040782c07524960381031000500d006038007015200000c1012960304554811010b5201c400303c0c04180d009444100b008074108209004031440c030103d140c000d103500421502c100300100743d82000710f55400d07002c0102c0000320b2154010494000c1c06200a4030610038011800303800c03103d007a00c1100041d410711104110 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 19026148 1250 19024898 19024903
    0x31e0d0203091302030403140706050603120406020717010605030a050a06050606070c050f011e0306030308010b070c06051b070f090b0901080607050a0c02120a02030f150403050702040b150d060b0c 86
    0x612038000f015843e500e5500c0d0a40c1c00b14044040c040d0b4081d0041454428814190003c42c0075442c01c0d000c0d2030a404102000901380d104500428015900c01c0804018240c641c41a91103d0520b0400005403a902c0350300090070180070071016a040c0e804140c0c40303000d00516104581d00440d0231100585000740d196103142502101d0702c90144148000b20024500d03074000d402c3c02440c089811840102591040701c041c2c01441030317000c213900180d908400170400000c202c08450101e9041000445034918055049456a100062a10760031046da00340c0b00005a0802402003e02140560041140e013400f05040c101c501880b0b145100d010f800004101409001c95010341002480c9480d07a0b40c1c500317001054031184035801000f500002000c0d65400c50840c04110b240c0030740d20071410385812040802000c0e0b6a01c1d507902a5040d460614800700d000a1b0040c00144281403003d800402c10f81e201d03c0c00500c45480000d01d0003000301000980c0040c0c00441d100300e0005d1f00b00c801803071342421820083c59a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 19027398 1250 19026148 19026169
    0x20f070803040501090909050a0f080d06050105070b1b070501050f01050f040b010e0105090f120a031103130e06040608010507080105100201060f12060209060415080a060612090809031e0d020309 85
    0x6d02c02542d402c055418800b090107903a0b5070716000035842140e456503140280079a404a405410007038600078002c101984548103d6000b16084002c400080c0c4039001403864014980d040000c0d151410882c60780001c0e8203002c0c40e841000701c40d110b40036661404060100c031441c9221071511a07840e122000c007590380c0040340c41002080030300c0c0107600d4041040118650f4804003c0c0d15600c003500e400d10240e4400c0005180164612030766911540d4450031031000da40340660020111a124240b0003489507104036803403030790700000c01000840c00940d106495402c460056581900042c0c1c1800140090f08220020b0540205075100030041c043c540104904c400c1040d000d82c00581d1840a000c2d42444110b4054800022004014941da03135a1390010b60002e590b801007103008100100005401403505204220850b081030f2600300449501c480e03107000500c070b640780403034401c40140070380c1340c050b1030410424420582170720122041010280a06161a01c00040c002c110341c020418030781c07039171100303070190 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 19028648 1250 19027398 19027409
    0x10c0e061803030405040905070503010c0e030d030b0102100501030501090b09060c0f03100e010b04030c0f0e010e040c0e0c040e010b0406050a1209050a03050d140403020c06180a06020f07080304050109 88
    0x40d45503403078030300043c2c1948a40c1e48419480b60030280280300748035020640303800700d8108030f008000d4800e50b603400381c80361002100e85903816045501003140150103a00000c4000078144103482210f100c40950b1022103400781c00036901380c0e549205003400c218030000e80c19044080704c4014030340c1e481c114070040c106118207114407a0b210030100120381c1d0b09498140d110302504156120140660b100c8402d01c455400601c01681e036295003020010300c00b05100300f20301c00d5800b152030f2013426a090040080003100042d0040302d5041c0e1000000824082c08001c580c041c1c0006080c40e42d980d45440016640280c061304050880102000300300902d81c0c000c002c503492040d490908201341032010003c0c900805a9640103031460090054650405500c08024034440e000350104009011043c403d0350b4080d03200312001030150b848480a400c00d0300e0a6009003000c45a07507180ca0a0a05900c40490f001c81d5160b030200307001d6813021086802c03004041c8000c01c060011a002941014179180008001c2d0382c007445038 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 19029898 1250 19028648 19028677
    0x9060901090b03070803030108010b270106030b01050702131e1812200303010317070f03030203090102090303040b030f0f040f020108040314130303030c030908031b0408160305010c0e06 81
    0x34141c00c0d1030134000f5038020300c3e842040d203803a5039540c00c14902900c213004a00c0c0c030424407500002c2c500100000303094060003a040d5000d440c1c0e03007421030a0f40200654018507052140c20321040d001030340c03281c400d0000d6140348040442d144442c0b80c20b031403411801c0d501c805502420701100c090218002c03c02c403501140c0001007105844640c07441607840f4400116030740700300c2410081200c0d0602700000114104c9105200004001c1c070f12000c4c4640c980110358004041d265006840004039100340c02540d0002010400103141400c1e1000181c03640e4095032000440c804040100911310000c2b8500c558410030003001082985010b0b521203000501d020030080c1440039480c0443d0030300d403080e910840e505424081d03240c1c0d80c442c15000d03116400054481200020705154005041c00e00c640641076000d0790002001f070458a4200b40e014101d0f03452191314104642c01d002c0000c00400401c00303116042c840041c0ca031002e034254100715007540c0c0c42001500078040004c2d600ca02d141ca50340c040f56010000d4468 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 19031148 1250 19029898 19029911
    0x3070b1302030f0a03090b040311100203041508061206060105030a090c030f0516060e01020c06070501090506100806060609060a0f0207030209090f070911070b1f030606140906090109 80
    0x1009140d6200000d8080c0d0144034010420b10000c40004290040e00e000b030703c4080b440741c1d48040040b4503208038007000300108495500e251041c101700000d1031000d0620b00503242802c1d100d950b021401c09809189100103640c5509014036070400030842280070348540d024101e5403519000190144c0b00c003400950b2840c3d52580503030f00303000090388400046d41c1c2c0300c164000705054600302241d45451b440c8907081d8084100ca400030b01507009006240c140b90341038000d003011070402c03003c01545030000388066030155207451216000544c24002680303c0d001109003a0807042c00c000445180c280000c0c0729501039001006a030340c2e00d940d031109590b283d5005140c00c0a911250300e80c100d0030801307a03a0000f5000031400c02403100e8a500403d54401054000c802c0b9406a03696111b03000540b6506002d840c01d21a0400c55140800d1540c1803c5902288041aa204007240e5402b600c1641c0c0d010b0340155100d079035941040c41595500421645104821101794035903081202c00140c40340c41c180314a41c2071a5581c50b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 19032398 1250 19031148 19031161
    0x41203090503120a02010b0a050109050d02180a06080709020f0421060504060515150f0c070e09030706060509151c02030a06050703050903040317030a110a0c02030601050a030503070b 80
    0x101002426002c1d00382c800041e1802d501c6011070304540e80003c00765090414444041c109182c1d02021510142e6810a0162800f014088017814025040ea04104000840c0220743c2c1e01901d141c0c00703050042000607402d483c00081c941000456002000f00500402c5048504121101501d0544a22003840980da503003d1442005140c0748440082409041600b00018001240e003c1c5106a01c0d6005c260030000245040001d95602e4610101c8042c00600401043c10800b001420b007407039429044400f401e07225941c8110074942221700c4440d5034400a10304003005901d00841c0010441901c0e1400307581001c04050785050400403019001d89007841d12043d41082d1035103014920f9030064142d40b501007260400201a04048405ca03000c079081101140d41d0650002c202ca040725000079840b150400c2180365000320f0740c0050405111541c84506041c2c080100748000c3c080c0000310b89550111444620500d0709010301640140d03c105161101000811004011541240d41c04080c2220640e01c40 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 19033648 1250 19032398 19032407
    0x601030b0904050106030615060219050717070302040f02031303030f0204090c0302040801050106020c030d05030405010b13020c0c030303070f08060414041a010509040309030605060f03010e010c08061203041203 92
    0x146540c1c1c804210340500c400c1c0031065001038103490003103a080c000301c03185240d0110060800e20031308005a0041ca491001741c1412495084d80520030420f0362a10303a6907403c00300c0c0004a00310080403a0b0000c82d810400c501e8680300304001200701200c1503040d40792000c00100469070000f40035040c5a11107002c030003043c2c1113130b0440b4040d042c0701000b00400f85040710010001d4120340950341c2558644800421040c0c00000d1201080c1d200400820203210100001c41d00781e040503001f12155901c5003c41c0d44260f54440c00600000c010f07001c010303210304254007a1858101000480e600a8200b0010312407043d602a0b80c800300b44e01a81055600c40c1c80d180c000c50010400c01e141a414822840280010040c4403c11541da640295030750f408035988841c10416444420b803001000300790b003c4803c000041c21038000c41d130701c410014040b1104001c400042420340d24107800410041e5903502c40c074040c0d19005401e00b600804265a2007658403510385495079240319500a230040d03031940920500426108 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 19034898 1250 19033648 19033661
    0x1501060f0e180109020702030f010e0c0d06060503120901030f090206271203090102060702030a05090405060303210709080604020901060e060408010606050301060f030e06150f0d1208070503040b01060305060103 92
    0xb02070100320640e03680340740c01c0094110300804c038481e009500708400035020500503a2030300c100c3c40c1c0281030150019002c00c4001400f142c801c40791144c49040014896405100301c968105042c20802d5070b072444140018100c80906031080755003031404241ca030250310303a03005a640d080d94000d8a01c1d6600c520a5030a458880c8118565500201610885c55001c1000c005001c4209007a000c4509540b1100700903a26030007040b0000000403000d202c0d20406141c5500721640100001c2c9c00d481c0361103114543d881030780f4103042460701c4800d8074400b4000b03225880f12601c4020100700002d42044d05283d800503c1c0041c040c895001005400780032000c8030b640d1001107800170448500208020b5a6554001d000381d0401d10480c0040790225208031031a074005d00400c0c140c06485006018503649072552500c442c60352860080c0c20500701550500907450702520703449042c0c0a0320500981c8041c03d00001c046aa004020008000f0244103110014004480c40c505407803c03400e02084682e210300040300207015 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 19036148 1250 19034898 19034929
    0x1218080615060d0b190302010f080c030705072a050f010c08030a0e070b0c06010801060b07020102031c0213090203090601120b040605060607081803061506040b09060c0106030b091501060f0e 83
    0x40c0d05c9030792420001d01008084a200ba01d0700c2101d5000c118081d03c440f00200c0b100744055904000103443c0c54451001020303120b00c1180c1d13854094201c030312055141a129144c0b03400b0181512070a00841c40e1030040240390040918000400c00c01c941d0740c007061408054540e032180f80e240c814881b400c02c030901102e0054011342d21309944510034166055034501c800e105102495180c800c011070403111490032140c1040d010f8005601c0c007a0160003001207103000700620700e1241e0b07007405111406031442c0200c0c07000b00130940015072642440c40305d8604016044e0f2000c4441441e1110b01c0001805001406034007507042240010071b6981c480c040740d0300780b0424a0050524000180c80a40000c040d241010002d80680840b0701030359480701c1c2201c4408602c41c0156101030280000c014442f2068002c10203c1000780100b403e00d075422001c2402d5070040c1e041164581208020000411010004014200d0035000d045416526190016008056104843c400c01000100450041d11400c1c1e61151644 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 19037398 1250 19036148 19036159
    0x61608070203190311010b090105090702010f0203130203010e010507080c0a090b0a08040b0f07021f02191106100f0605090415030c05030c03070f0902090d1218080615060d0b 76
    0xf050b80880c004002449000700e01194800340140f0b01510148103c0c0d60103240034007a4041c1745d0900c070400141103401040340e001c540d25560416040c2459001440c0900499920701911944610404d0300b92000a00c0000041e031400003000986944001d0080d0040f4030309503980e6039070292002c1281c070414107030058284c00000107003400c08250f1254240348a64001e03441200c0c00e8031070f00360000240d030081d0b40e1840143d02c40e040b02c00202c500d84644603048903000e5401440c0128903401203144c1e034800302070940031440b2175408900c4030005004a540c8160601c00d10780c44641090711041c0c1d004001d000d60340c1048408101601039417241d0b0300003000d000c5010302090880b50740385044400c5c00c0c800e000306800703806030460718002c43c01d000036030606a41003002540003840c01c1005600081d00324408003503005050b00a0000446c00103210a58007984542d03e980d1560001c1100c1b0b0400c4029078070061640d4081b204000d04d44074200300c00c00c07013030104917034256031403170943c043c04003404001d103041e40d020 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 19038648 1250 19037398 19037413
    0x11060708010906090b15090315010b0307090f0807090f060e0405010b030111090a050d0503070804080606010906050a171b0408030702040c050910120f0203010b0a0e0f061608070203 79
    0xa0300100c5550403203aa800d4140082525078540d003040d503d80c008015048841500b1648551000e403014008081d0b01030102e0314030608441090790b000e24280d10090000100205204099502c180010090180c000704003024925080741241e440c4a81d2081d0b0f140541d80e203800214201c40c54020000525018240d18014206424128020440440140d1080d80f0345241000360740350080c00c4c1da200303520040900601d180b8001c248003c82419074030803611800100081d02c005107161010f40040c001c1c0d180101001c0c80c01c0d10016140039800d4002e6002c0c070609000349034009612016040c04401f500c00300a0160312014492070b5000301d0300e801c11009240100d808240c80c080080035082c4603000319828400c00100c12000d43d120311407003145030b801a01540d403090b03646e40a0601402130b9014070758000307110001c44440e4000c981081c1c20203502c10b0800a09101c0855100c040111101c0044905e01d8042c9100c04c0092407521075181450001c0d0a00300408040c010304c041903446503900542502c004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 19039898 1250 19038648 19038661
    0x4111203220b040b090301060306150801050105010212040b130302030106091e021303030804082106100207060f03110c010504060606080108010905070b0c030d1416080f01050103020a1106 82
    0x60350080c0303501581d015508440074580d000844a040100c42050044514040c2805100202d96121030060364256407200c0300040001d15030f1056081c03840c84040844140c0341403100c0f883c20342d101070f40700034115480408200401c2005104580840382d161205c0796507800c801106804503140c55001079895403804c2030000300d04549402c6a00c5080072144100800c2182c1300400b401c034054106600405100c85e0410300000f4020013200b07410900501119040111a4490400c800014603102d00d6054400040c010303075003001d0a20008c9102c0500181481e01d05040c1c0081040c541110f0400030142c0702c81000f2a0454079508a88050104000a1015103003904000014140303e218150000e000b100000600d1401840303000354059010b00a464818038005100a058210b00080345080c0000c01c0181d00000075880b61160088205804e0211072802104041d60401009210021320025070100040855002e603c18155082400c0042c0c5614022408460801c00d0304010a454403030902403100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 19041148 1250 19039898 19039903
    0xc04030b130f2a051509040c02071205010b09010e13120c05010f0218060408070e0703060b030f0402011b0b0c030a02070b0c0d0c050412020405040203030c0312040c08060108070608041112 82
    0x8083e0315455403030214580d01d00602114420394558061202d400307002e00c2c112841d2680242a42d4142071040b100983d44844150802107007100085815a640d10074543c114102514114014803902644100f503140c0b100d00c0303805914241d04010581c00400d400050280d003d410703c246855085002080b10800820954000303500c1f02204400d00c4030f10301c6102001f8a00300040303505651180f4050324550b840c088494002181c0a4507100905450b030b60042464060a005944075580c803c1c104841c03410980005412403080c0100704030404660300b02d10f0040b8a1580c0d085030018880203240303640340e54125041c0024003400c0e130300800740d2491509012903103c0d2500607055128042c43e0070002e52110f0360084ea42807040b8810300ba0100c40e0150140c0c0540b80c294840d0364402c0c0040e00703485c9000c088680043c1180c2c08441c401c1501140039040c0014410b1140355240900019002000c4650400b4409a070b218918400c1000708102603000408110007000c06444841014210600d5404840e00454 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 19042398 1250 19041148 19041203
    0x50d0204090203030d090803090c0d050d14041205030306040609061214010902040501061d010305100905040204060f080a060b040b01050301050d08070c03030804030305070201060e0c071707080405090c04030b130f 93
    0x9040c800c108019840c0d1610614bc040c845502034014004c10f20740810036a1186021801c45c0c0740e0480c140000103a005d045010300301c07100c1c40f40300519960f1800104000441c1c01c103030001074801d460400144800103011a04000c16504100c40c03040307031b0201e804c645015010070103000350400e081a00000e60300381c00482c21036402d0341e4a02d0700d0920240c1080110102e4000301d4048111a001040c1001010034030341c815a0401e00150000c511548c49100b00408008241d0002d284c580c0320400820a0020f01d1240441502c0110b505000320317481000020003030300042c0605449904601c1a100c00c02c50a03104803120154004140c0c5034440d640c0c1400381c40300c0400c40707054000c2030416000034811032041c407600e0f0982d080e1000f181541e844100c0b0051a40d001088200d0345200b082d0080000c0701c00031f41c0504107040c41800507950f5039051078180301c000900a0261290380390184024070004403005121a0701c5420490101d40c0b440303180c00c02950030104810050032080c5022040c4903288080304d0030303c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 19043648 1250 19042398 19042411
    0xe0103030f020309030a060c0507020411030709140a030303020310030507060305010501200727110703140403030203030a0207020a1d07020106050f01090513110a09030506070306050d0204090203030d090803 90
    0x24a94001810701c02d985a10404901e540e250304045501800500036a02820116496240003401e00d02164007103800c0b01c9004c507d480c088276001c020406800d52004422002c3c108045c0a5003111046401082c0d00d800d00d400010706041d004000103a0f56000001548001c641240840759010b582d00b9010700180000c1c01141d000641c00209210003108036144803100c0700b02e220081c12417034a040402a00c0d4102c1c107805104d254620384019581b11020b02641d0550070b81e580341540e030b03644140741c081d00054100700152140d42085c001003011030f03001b1060302d42c0200060400359440290744001015100f850704110040c0c0510402d441c000e515942c48144100f11540080004030381310710804c6010000c0d01e10302c900003070307903180240000d080c10182d020030302c2030710900440c005e60030704081d41454100e8810b16001646118041007400820052035811030000c0c2002c104850602c0c0104501468070403001e4044c6407102030410440d10200100c901402d00c2d644200010380f16840c0441d9158815100b0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 19044898 1250 19043648 19043657
    0x20403020907050c1c030e1614030106080304090e0705060705010507030509031603050903030903010c0f090b03010b0d09020307082d0c09040308040c03020904120f0c02130e03130e010303 82
    0x608054051001c46488401da540100340407100c0005d282e00c203020030049502003649825046610840402c0142540105030180301d0b0303403a00300640d040800c200c00e0b01075442681020010000010084100c0381900c5c0c1044011500700001504540b400c21260f1010740c00160004000c014400c042d07002e64081e52080e6401c1c000d5840780c806140d940e0141c45507045040c0300074180800020f004a00410382c110014041d0382c1400215070000c1d08441083d6004000701d00c020f4400b5030050342c04101900589150b10401e4215414281008598025101400c0c905070303580e20b00340c0555500300310741d50080040904070b40340b5400d0150182121641010013003680d1341c801810440b5001d02180f104c10b43c02010305407020790b9503280c6044074080c0c0e020340281d0301094a0038000c0702584600240c58403036401481d81450224800c1c400074440d00150950303508000108070030701c00503079510800704010050003401180340b65222003c9811741c46151030303810a01c2c01014001828034017080500341201d000f500d8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 19046148 1250 19044898 19044901
    0xa0510150e0c040f0e060907020d080c0a120f0615030903081801140c0406030e0307020d03080415090302010504020901090e06040831090c020601031a070302190207080c0a052103090d060204030209 86
    0x6036a11400c5107040cac1d010880680004103610141070107045155503a1510210b00e0501045550071107402a550010710342c0c461000b44101014a4107980c6000701c035240c2003001118035103000304400800313000c41d001480c10150400884209402c585041c0c4854612000c0368188460228041d074000d20820000c242040c1c0e2400384c1e82000300584500c2500074212201490560354121a083c13801042260b041c1061041d101ba0101503215000700302d4170075000094541080d004001d840c180503030104006a09081c4426500340e004104c03103811a074005a0281c403092000c0030900ca14100502400c10034100351241c0032079010140b2280f08496045030104404442d100d400ca8849400340000b41c0b10007400d0f4000f003da50503480300030358451681d01d0300500b0510f4034850b0060214035034203c40c0c0180c0c0121010b12400400340018148200300300c0b03501e050a8a8140401e00b051031a10a80088541260070f009500e40203008440d1030741d100130030100c00304065107041d8009401500040c0d0103800d1000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 19047398 1250 19046148 19046161
    0x1e0c0807120614060a02030c0607030c030b060405030a0605060111010c0203091e06180a0b04090902090105010201020307020c01180e0f04030206090109020a030b09070f080a0510150e0c040f0e0609 86
    0x101c0c080c19a2000d002e541d8516a4283c00c0c4410b9521081000b4114442000881705030b50040c00703001d0090400b0b59010481d40054440201561440401d69220303800401003000030782c0d80010510790702c550100011886c0d0b500c000060750110b61f50101b03130805508100c21415100c0e400b01c010434440300102d404101181640c584460020301014425400c4482003006ca0600143c0c69581582100028191501d845c0c40e61004402500594018000251211941011894052049405024280300850652138801002075039040034900b0786040c8292005003a400b03000e0300d01800040c244810640c01e483c140421650f5004808540a500600550703020403000c1c241030043c0c2111070f40052040b0b554134210344403240e4217075003d0400e500700c2c41070140004002070001c07078281c003c26203000602002800c60401703504014003440b20130f04c040d240c26021240300d1031907075001050f20503440c1d01c3e0840e5900d1000682e5203209580001043c408540701c0003034000c4141a0540c8143c600703440640781501c0f90b5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 19048648 1250 19047398 19047401
    0x106121a010e120a05010612061803080705070203010e061608150a030b09010b03011104080c060913020306010908010e0307060c080f010303050d020f040806040201141206041e0c080712 81
    0x18222500292000e1454071151818081d40fa401c003220900f50380e035a0290b9a651400c44d1707210392214410002261444060250500ca900044503440b60345000c44d611750340d001004084001d02c90b50038844081107074001c0d500c09500c10013416803500111900307400d080c18003490681440c1307000000190310740d00091140075501c0e451005500090315024040742181e42c0d90092030001030425a01d0b65881c1417008181e60240520048040c01d10b07041ca59490410501c3c0341400754074030280c2d001c0c0104100358495910703403400311080c10500700344c01a200d48400c00101c0b416441507114092960801c1002c83c41000044020700a0610440f420001e0320f640e04415201c2c0780048402c9035400c2180c50040010078003d1004001c51b10070250014900041882036001e0343c3c020350050100c03a8425401c0004558100e2140c00f204041810301505001c1101c514070202d0350014811303400380c0d44691002130141042d04210f00d26884102c0148144040070b180100300080031280000094403811680c0c501c003025 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 19049898 1250 19048648 19048691
    0x903030f090f0303071209060510030c0f0501080105040905123105010c0303050703060b0a051e040302060403030c0f02040513020a050906010e0910090908030a0b031501060c060e0105010612 83
    0x240019604540e210301c42541c0c10074903420380786c01d40d98941d14100c000038034910481d4400d07208101c58180b41821401c004640e103200e80c00c0208040040760040c0300983e0031254090440390308450105010400e443c1aa090007850314460420290210319220610301d009481c040e00394480e511200000620308050803d42100e10074680483c1500c140f079004a4484e801807a0f02480e80d00b80401c1048e0390702c01e002850350140e80b0420000d0004280300400034800c44903007002c2021121107a003011b013144c00156051107030b4817000701803054404d140c4080000090b89583d44540040c4100f0851400404200b4103803480b0400303d1041034100008650b9203440980180142c2041e520b1020b010103000502c20400310240c510782400519901c002186901d50003a03500c0039104a40c183d8032414130640c004e0035074982000544c42600110394200c0b10178014081c05045407600c1c0381903220003007582000c4004111407881d82095509100000c0780040c0c108030b51598821b54001c003000146951030010141500 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 19051148 1250 19049898 19049923
    0x7050403030503100503060112030908060610120e06070302120609040c0b07020d05030711030f03030c0304120507021201020301050a0501031a010c1a0114010f020d080f0a0f050903030f09 82
    0x280824008a0310600140d544a0048207075600d00c00e03114000285041030036400b2689010402480104046c3d0003072095008201c401d0040c41c580c1040c00020b2080104607500904006e545004150701603503d42101004800400c1a51000e06042c1e4009010350f100450501514102c0c0e004140c1e242444204c0078480c503001542c3d1402903007032a44100c03540d84007040c1030780d100960843c180b010480a0000b0180544141c00e486c1e850180c910505050545024840d000f0b500203104018490901e40701f240e41c403e03400306249815120b001c0c401d5445024000000e50800503a04502003400c20540c0198140d82c400c40c0e6103211196110011001d441c041140c0d100c1d6512101d82c7c01c01a940a0000010b1003841a0110242d5105e0000408000c80007607010342941140d0181e045010350300054010542003c505c041d04800c031904c000600006409000c1002c40d102c001c0020714a51602d0f40082c2c0c030b140c544d12061149040c071a0100e0750340d400507590000400810380204d244000c2c00548280c5018 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 19052398 1250 19051148 19051157
    0x1c0206040b160c031514060a15050903070b040801050702030705190309120f0309080705030703020409020103140a0606030506090c120403110111041a07050a061a040626060105031e010e060106110d050307 89
    0x50505270401d02e04404904c448060081c01c2c002001140e4043c482d88024002c03103150a61614502001d2609480000c0c00c2c2c4e0701950420000e1a02094001c100031440c404010540440130200f490221a20200c9600501000d00c203c01810200504684000c4c68640170342d0b0340e0315666840f03544540d2108600c0c4070782545175020180410050030290846100c003401414001040c0c0461107424055000c100c0b0400308840d0f41e200203201c0260076126082e000750040d508020203181605000700c5910590103144103281106000404041c41340d8110031104032140024000310706044440f03841c0d50458020000c41400c3c600c0c0422280c0800c00c19608629081401406081c035107485103c001c11005c1c0c0c20100044410003503600070744860060000918158460040c1342c01c131500298418079041038441c1540c0c0240c40100500d9900240200d0381070480c5034581380303010003a50158010110081110140e02641c0000604150015900111400100c0135600c0c0d246130b846041b2803500c0704803040c00224 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 19053648 1250 19052398 19052419
    0x2010b0108151509090c0d180b0103061508030f070b1b030106180305070f080c090103080901030209060702041d0d09030507060f020a0b0a0203061c0206040b160c03151406 75
    0x41c640180030765150b910302981d0354507045401300802c1d00c04000700e541004885c03000892100114451103050300d1400c1400900b440401d1540da0080680ea0600c80603205540300e215602c0c0c182c642074041801010f50004403590b92290a41c0c182a0307410a01040d154031a0b09400503420385006050b00319038207001c41205245070f083c04016149542c4028003400c80c00d43e08a800b02c0022000c1106001030101009130700881032070446500d06d01504520600e0041502c1801007001583d40c1c01a00c409441c24200581c03501e80d01404030b0060300611390041c0d8032906040d031000042445102500c240800c0c8019180e500404032000d0b02c0101092000600c2540451400c1000611030b0310181c56581592056a005030650386171254460b4041d6074442c8030340d030700000b8006d99103489a844251007442041c2d8440c0452181c001410324021403141180211001070f52040500080d00c04888456200e580302d0003050b100c7c1000e4236000c082c4201042442d01d4260380c47c201443c4400c9007445000e0060040310385c2c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 19054898 1250 19053648 19053691
    0x40203010b070f0309080303010f0312050a020a080d140c0307110604030c0201030c11030d0f060807030512031e040b0604290d05030c03040803031e09030a030b060d0509010c02010b0108 81
    0x103d60490015030421034080004100d0b4a0148002c44c000d107850044032401c141141030201120a4003040a014402c0800181022a801203880080160401c1c0625241d918580541c80134011600e03030107401e9840c0e4001c00910604810145000351856030340d1000c01e90f20050307616550740f000d88014001c240a40d800c40d00541c820f07000b0306010407140ca4884162149481c41614541062407000d03120b6441d08807664507044a4800d6400503c507840003462544e1450729401c1d19041c0001c0d0400303200000100240c03104e50091198051040d1806061421b8070b01400d02812101050740d05522403410001c8181203104c1f030300201344805840001e1408424502002c000b060b100c12001260300740418048004021003e002070300c000e29201002d1aa00c1c139104403100d1842c2c400720000c08c09120a4070038410701a1000080d2035001d0b409090009820070402d000030710a00404c1101c6180340c5c00c0c402044100d5006401c09020f410068001384200d221250044d00c103428122001c800500c0444545180d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 19056148 1250 19054898 19054913
    0xe150112080a03020403020d030305070f020c0622080a050703060b010c081b011119090504020f04120302010b040f020409050901060608060f0a03060504030507020907080f15180103030905030705040203010b07 91
    0xb8407141410010318056607613021807418060703018181c01003070342e81c0100440e6642200c0300212414592002d4044a1000800640140111100c1d13440240c40c800310000f80310b00c0d0b1030a803400740c60404200c400380d41180c40c01039035a130440e000c100c1e845420000750352440d5014519440c1c900b035100c51024100642c101400d69042c40c05424001c1c139648032405d1a2403040d80e0030003010441c80ba01840f0207600c0700c41d040900900324981c0558040c501c10001005c40001000956090301c44c01808101000c04509049024000030720030154040d2500200d041c40b43c3c52607000700308961802c00c2c14021603880418042c00c80d040d6108800200d8000700025078989800d100500c900103004144007407040d180d40341c140468004581c1140480c1e07002403440190700e0120b00c650b070b000c0824036042101d482c000c03480c1301c0c1228019058454115820484410300d6581031144100482d81c190300c01d00541c0c0da828000c280d03040758800c9074002d0181d010040f0312402d250085134141c0b021030040d5031034407805980c2d444 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 19057398 1250 19056148 19056157
    0x30c03020a0b0c04090c02061006082a0901080105040c0e0105090604030c0806011716030f08040b12011401052106030309090a0e0d0807021e0f030c010e15011208 71
    0x80850040c00035040001e0540c1e2400350003514441e00f00340c1c0350350803c6040012540085005810355200c08100b205c044c404401000584a05180040060f11080201024041c581000744080e1064140328042402c0030000361900743e6090340c82c00341599035413013400103c0d92550010400a8414044103046502450050014490142c410f0380707010781e283c40301281132800c0c1d0018101074210000412904400d2010382d0000408030015100c005c1002030451440300f101c1c403005000000010030a01402514001d40c4e00602900064940e62100481843d160904c2402881d032070059460301c1d20f040354801d4003502c0f0f02c18040c184594007a81c1c0e150428106d6070780100007550620040128115035100d02560500a981c01d11000c13440c000b980000301d05043c49082000c04004141e4204080c150380055102c400490b02c4000f404004141c07243e550505007091051941c5100c0061911903480c0154400050620f428068401c01902440d500562200a101701a0140402c900c0200440c01c17030740040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 19058648 1250 19057398 19057403
    0x4021e06040f090209040c031104030308070e06070f05060a0c05040918050706080703050606090d0201030506040f050705090a080319110118030306090f06030305030711010e1002071707030903030c 86
    0x150304107569180c100540c075a440c0c01420308144c01140031509030a20780910442c481c4141011701c40c1c02c00c90710640b041d85c0540d01c8041c04200c640c80c003080c41140610106100101c000c0c0455503100400d083c503c4954032050002ca17501d2107003d00084114039580f00e209204441582c2c3c1500c0e084c50802540c0c05400c03030f2102206000380c000c03501c50000e42e041080d80010300c0e0948604049181540c1c2c090b04480e8000c00300f80c01044204501c2d09141d44003031220381840e609080011302610b035a408107000b001240743d15074409180038107202804d50000c000c1c1c604e901c0301f100ca0150442c2c44600051f201c2c0220190040309207d1003007000c41345801119a0044a9011400041c0c0c2da03d09100d40040255134640603404266608130510800e45140100d0b90300d007680f83c01c1030121a140d6a002002440000e01c1d4504201c1c5614490342d00e08d81c00c0d082803503070111641c11907542c46e80d4000c18000940c44000e0440ea1004408450b1451002d031a098480c400d4064031071041280c503540f019a413400301007c04 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 19059898 1250 19058648 19058659
    0x601081302012c010f050c060f0c12040327051c050a051f0b060702030604080c07080303040605060a0e0103050307080a0509031006030b090c0901030213020405030a03020d0e0904021e 80
    0x50800d011018410301690309041d41803c00e0301c02410f0009060600d5080103081003100411080400381400240a900007048406003562a5103083c80d844c510301514400035908188a01804141940100b00641156140c500c180c00341c003000480d23004e5002184601a01b1800800c01100111480c03801d4404490041d010f4902001c01560344c9800d02c1e08101481c80801808512106254094462100b820300d040d0703510742c034005050300000c0d641c1800034001000301d4000101005007030001c0c412580100060401c1f283c482c01d20b0300e0900c010b020100c9900d4024112040001121f10b51448814101c9070810051480c0601640302c2443d96171010600c00140300c0700b000a5030342500c0801030fa20306100b24503000074903d0f05500c0d041c03004034806808440c90307a010000b4050f0503910100900c0c11240c0c1200c096002c8440480008043d006503801140d25004103000c02042c15008901c07507a01030142d13503c03031480d2840a4108200d003841540c0107500082206030003010036008108101d5114001042e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 19061148 1250 19059898 19059917
    0x21f03110a02070f09060e150a120c17010203010b070b060402120408030603060106021c11191a06030105071b020409080f0d1103040203030a0503190207061b0206060108130201 77
    0x1001a66400641001d005a1180c641040000c041030403090150411000c1070252a190403400d04061034007400c0001c90340d0102094420561b58000c03148020310507071407610f02d141e08500b03005129403800c0c810000c9083e0b403c40c5103c9106018403c40707060320108010281805480e445980303040400410807038100f60300f000341c000015146d94605204030b12881d4025500d00c0c2100c1030508012041c3c0c80350055500540d40d00441c08490208405490042e00c0e0800c0c2071400034005c5860510880051003003000f441141d4000d004038840d07522640c00100001910039202c900a044c03c0b500c0840d00e620014101d007401250801e00c47c001118901c0c001440820380280c1074544900550049442549c000c10004c1e503030b042402d49000c4e181e0054600d500c604d09514103500803d44910508540201f000000000200c00d08c0d016851b41042d800e4000c011526411103290140041c46200b00d0110003020629400e2810303480054424816401a511240603448191004212249913501241072014010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 19062398 1250 19061148 19061171
    0x60908070c0929010c0201030225031403060901060302071406070216120b060d080408030406050a090504020a09030b0a0b03010510060e0604030507031707081b1009021f03 75
    0x402a04a035401084000e603072030b10380b80040c0101c5100c0940f121030716464904414085201207418154800282454200140321b440120020b12800c0d41400c0c940041d42c8016a090816030f800d1111640b103621050a14107214054080502003150000c1c1c2c030002041c01800304030300c00c1d0042e01c042842070301013180b03c0f8822011507082100448001005902c0100c9403190307400190748502c01030032031020300d403200d040684a0b0191540300510351809142200310710b07000c2000b010300300d074005c107140001c1c1c940f01c80d101c040082c0154030562160380050a45200415140303450720031900e4500f22030700c9441040d459540c83d162000c1e001840240a907603201c4030071050313443c20b00600303129810249001741c580f4180200a85240140c804250040d403081c44240000784000034408150780d0411190301c410f4a1180c00c0d5003092141910040c020031010600c480010752090039004c09005030f00c25034000d030b44580390070b6003101c46410001e50b005213840a1041c1c108141c2030491000d150038035000c2401c00444 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 19063648 1250 19062398 19062413
    0xb0112020d061a01080c390f0d020601171b01030f06090509010c0c0201020327060a05070302010506040e1e0106050a08030307080f040b06040b0a0510020d0207080d02070e040609 78
    0x1c0c002c11880149043d4404150390150b6480d03400b01514142e94203140d5450380c1c0c5005140032500321307201c15100482d44941401038484c40d04040d140e800c115020b007050b40900c60b494800c0c0040f003a0141c400c00b000452000d01440400901951200007001c0c40705000c0354001c03002c86050302d01d038145940d466014462003014000d09000e803101036004181424004291421901c01616450030001e04045000040c3e034040102c600c04070034282210921801c03c250011013900c4807804641c00f4000150540c60550481d028051081c002c1c1c000300155030301d503403d00003038850620b02c00001fa0813a0340240100041920075140e2821410f0000411a854a020030a002d200740c12207099584040100300046034000412648248411151a01e07810a40e0b2032180d6650064041403103180c880083c50000d450b40c5880380c001b400010502001c41440440194507480d01403038080c0180600c5401040b5030000003503d00015056500508070203241050070982500c0c0900116241510b803080b101c040b80d040b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 19064754 1106 19063648 19063661
    0x91a0916050d0b04090f05060901110a0f1106010f080f0c0105030103110319060606030c090e010b03060a0b191d0904020609010e04050f0108060609040b0112020d06 72
    0x642c0c1100d0003404050080940051034004800f083c4264154104021409441070361281c0e11400c102038280c1c0c081440204600c4003c00c900540284150b020040c3c00d0024a009061443c1200240d41044406e900110400542d20703428004076000340820039000d855280100640001c800000e0001c1c0070500c8060b08071074406119944039101401030388000103107036401d0880c1e0410382c03034601d000701071900a010002e40703407000f050384950041038440251501203140d00303282da19010615000e80d10040519810206a082c0080d030f50046c88041d0900b07410040c400705417440c2c2814024400807441d034030520380343c0001d0000c1040c0d8903040c00c11608150103403082c41c4d40d82c8000d001a2501c4149200326908140303000204000e002d400740b5000e0680c1e108a059400710f0b01c910080001210301a0b501415513413003000104802051091190801c510182c42d0624480154807030308200c034003 = true := by decide +kernel

theorem cover : BRFrame.Cov 18884898 19064754 := by
  have h0 := BRFrame.cov_init 18884898
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18884898 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 18884898 ≤ n) (h2 : n < 19064754) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
