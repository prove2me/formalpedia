-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3073
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:34:46.397897+00:00
-- url     : https://prove2.me/submissions/d2eb70b9-8a64-4760-bc7d-686c7ce2b2ad

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 552517985 ≤ n < 552697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 552519235 1250 552517985 552518023
    0xa050106080d08060f01120b0a1703031602030f190e130504050c01031e0e210c16030f1425080609150414070306140603010510050a0605031f0305 64
    0x580e400b007110b8a00e03117960f0306010484131079089100100c564858420880024080c014950b00da078031a465108220340d0b0040b4031740c80001402400384000f001106100c4480c40210b192a4510a14412501490810141a1020b0384201458034040d4201c08440040070302845404524480d201000c2e06041d42e0584050181c40034a00c4154401c1c003400c05003170001c81d003005ca00211009407900601710035200c1e42c141e011340c65284800880d60059a45000811074040317488000024005081849245584a001441e10410800154051000140c2c1e03504000c08410300d03115458010300b002600258110f010329a52180403003403040b40b403510309a03141d4404959460f40c400e21925a5010f1401890410460319070001c1d00183c3c1c45440c0140700b44046050f106d500f543e071f070345070801e94100e030048030184040300e410410345040900c1619804001056007071000ea01d000b020036400b880c02d0103590108100040011100d809074002e0302147c503c40c26034116440e0b520304005444410b00d00ca00320b04010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 552520485 1250 552519235 552519241
    0x50f030a020a11030a0527060a02060411041505010c051f0903030501050f0913050a1a01050103051b031803090d1103070b0702033304030f2c01030507020a050106080d08 74
    0xf20000588000c1c0c80d16841d401e141c100b040c4440c10100a01c41c1000201c10102049119203845540140c6481044c2e41c0091a0034241460304020f1140d00c4603a05005a280c00d00c0e401c400c110210744602122002c1c00d0503e00040b103401c1c03480c01c01148950380c1d046054984188410640141e00c603900d21802035034100003070790700c3d40200441e01c66006900ca41c001032800c041a10b95441000c00c0003150702c118120f0f07490108980e600c1c254030810410221007040244010061942c0500515500140003850422008030303841d0607034814000a008809100300c9001424140502007040380d108500090841c0c805031030911703154181d03182149165001e0302907600c00050504030a0309981d82698000c0c050070300445030360000071181c51f65030004080054160003ca280900003000c69009038025a500d036218200008081c00604a8001c03215502c80207001011041500080e811514030003440c002c00d55403907540049241a444001c060215441c04000180004e40004d25071040d03109034841e1800c5507 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 552521735 1250 552520485 552520517
    0x60605090d0215040816050a21030809071a07060e03070507091802041e06050607021305330f04020711040902120a0602071406010f1203050f030a020a 66
    0xc022051480d81000c0c403100040c00524011038181154071861900f6403c280e5501036031480d2648080513881c402c59480b00c20b004ca07080415a0001400c080e40124110301c08500c210240504c803202c02038100641c28002c20b202c52000c0c0940c10003060901580c194401c0c55081119141e0b0003110202da80c149060684c1c03464510101c2915281508040a44541c03441c00c4602e10140c00071031700d01d000448004c00b800740140e03101c3c40352a40d0031440b082c1300b00c6d10600c0d0301411800c558150708128461501030160074010781c1e401c1c1c051050700108a401044948031200840390070309009074011031176440e000113142d00c1501003101e20400001290580b1540074a5410b2000724482c0e1503001d855052480d1082200b030419030001e000070317413010b06104c072206e200e205514103000b4440c0e8225000d50300020140706009400e54030b040c015030310100bd031009500d00b8034074a50b1000303144144810089003007804028180034005843c07004603a00d070780c640e8910b40703104000b00035404800b54030b0208000d0310500d4500 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 552522985 1250 552521735 552521737
    0x4020a0315050a0503070e0702150a090c0519091e0e06090c06040b04031b080106090b13020306180405011b0801030510111e070c0305061009050403050301180b040618060605 76
    0x4d89000c4d025002c81814042904440500108224254032507540300e440d0403800503180718458041c1c1da6000a80352014508420850225400b40348202445052841c5400030621010119080c40c2030026203403a100c00c100c1700c200c64030880d24031b1591405401d540000008940030384151403c60540303180841403c10028640541d02641e00034500500c030034000105020300b8845840440c01d03210f2103946d0359051440c02d4541c9604900340c05c0e600d036000d095060800600c1d85001c0e0144000c20350071841c024010401e10402d42420314050705416000c6000d105c0c0039403003565035101c0c048818001a01301907019090400a2004036140d220b80c402d400c05401151141c03600c0303070102032419441c14912540d8644201c1c003070f0005030240c440c02c02001d000101442d070000000e41c80b0704081c0c8150b00d080b1103011203a540950040000b0f034244410000001c1d0f03c44110790540b18000c41414800300000507441c0101911400a60814608030010818107400040910b4400d8110f50030301c05c49d80c03140360840741 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 552524235 1250 552522985 552522989
    0x6070c23090705040e04030e030c091609140d0209270102030103020a06180e09070b070510050106091203140c0618010c0f08010302090c12070c0c061d010e040b04020a0315050a 77
    0x400b1880c4008100024440c4648423030059000301207075440322110000035094401500d9011020127190b034886107071a004042e000c002c0c80c101e00d0540700d181184000c204940f25190000f4800c141a00000d00c4201c6102c1000e00d040700010141400c0300b80c0303048d030306000f5882070005034414007a10100082c628401e44030529040c2601050703444041c50b1441403d503a01020301100f0300b90054080109800146001600d44c942c09035004102c81e818000b0b151044a4040e004607082004251081c00005184030300042001d51524094005d07030880345680406004280340c400d65401810248180000c942001c0c001d0710300d1040082000e001d514109880380503041403044040303520b003001080940742590000c1c0e84010140045480c1c0244685a108954004c035000e60126000384003100501c054911120064136240c10300c00349440180000381e40d0012031003002e90410200356010700c05610749070001c440c4594058820354480704100307409000b03030541c0028202181c00c0084001510b00c2c0440722581 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 552525485 1250 552524235 552524249
    0x9100513050405070504021c05060d081206030109020d050d022b0e030c10020a030e0406060819060e090a030e03070f0e040614070f0f030b090606070c2309070504 71
    0x10800c100e502140040c240041081e03400e80544c690005554a540c002090140c01e003c0c4041401c0d041c0506950840d60702822050060301803501050000d41101e080782c100540c0710381401c056984410000e40940302501000350000e9800c5000e50402c82c00042c02110700c0030540a4403c021007140086030310b080965425001d401044030080341c105d020300000b0504e036001400782c0324141e03c0b070070105600403031391403a103c016400b40010509043e8414010740000703008803824070006142c001c004101c40c01c09000405c0303840100c501001c41d442300368002001008000100710407031500c184403503290b5240803029004034040441c1d0488510700414a407013560450140b0000003820a5035124001d94003c008841e0207946402402d0040d40d1407040510500f503a903030310701810030a03040042004190840000900d0704060081e030169841c5070409a0040050b1541600c42900b4103045620442d25449424400360100c0d00c607032001e114403105119910700f5184400b1035182d402044031188924030882c5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 552526735 1250 552525485 552525499
    0x4050903041401051b060702060705090d12020307060c0f1d0a0b070318030b070e010512420f09010b04050d150c0206062704080a030e03030c040302091005 68
    0x201c080030400c40741c515010010f14001c3c0c1020b405c5100044210650010f41d400c2d0ba0100b01000b0044d60b04015460303001d5442d1424905107514400859510321101400800c02c00002215440582c0300308242d801d030542245043c0480c400301e040182010410308900300008070a00e006250f03d0304000ca0079511120f01400c14030900e454003548131010303000214204c041141150080101d26000c840d10809036004180105032070918140240200314400716a605004084c0f051205848010020341c0d0f04c07005007022215100150282d41c0010203101c010f82e42400030441d1a604a9031014907100b40059050b00c900380314054400810131750003070910074800c4144080209008600385404c55440d198801c05069404055200c03104042d03c1d024010a001603000c00c04002513031804168400640d201c28840d90928a600e001341940210010070280001000040b00c03040a4403a6219001840840003541c0d00c90410b0700e07400700664030070300c0700307a10580c485c0010402a101c1061403070211607000f4820 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 552527985 1250 552526735 552526739
    0x20907111908190207030f0b011401031406100509040222090e0d1206230f060c07120807050f0a0302120a080a1805060709030c0801020a0806061b16060e0405090304 72
    0x50460b5280c0f41c01d10f10440c001d4041c0000000e00e007881151791140728140f050710b158180342180b0b030307152024454107040608254140908550342d4014540210094036018006045941c040d28148900300800303400c64400503500c85084003801c0121980c0d000740c00481c08103a900e80340c82c030543c1c0c88034044030440c0c0c1100c8070f445071050080700c1c804890340350408045680f0b552849400c0b440d20101440c405c00b07400760020400c0c03906d0481910300c140c0c0400ca0f841400c1403440305d07200d139890341907014000c4045c0010001b00140141c910580b184c15074401d04030340390f401c0384000c0c0c25242c001101085015101e20444501da468a2006523001490540c0d50543c995681c121b1f028040d10310078200e1400e040120500d000414028404240701c1e140702d480b5410014030703500d44003015200daa8042d40c7d05074810311070040340c542c0c082c0d1115003080c000c489807070315065000c28005010b5032911002c69144500a1900422262108034004407855501c40ba41e28401240034841038446c21030301d44026400410003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 552529235 1250 552527985 552528007
    0x111070503032811090108090d0f0c030915020102040812030402010f0e041e02040501020f0109081812060403020c0103050721020a050f0319060803040b03190207020907111908 77
    0x2560710350306055480b82d2012455456410111410304c2d03010707910712900081c06941d55030080c0c02c183d084448640203000300700703402c00c004001202070152441048000e400744070605101d4401c1030007404980c4441c042844c51440042c0c000d51091144a00b0340c0540280b083c42d900c055425640309a40603140d21519044168080310441001e00d60194807569811104040c080310320304101b031b20f00a00c10010798840c1000c002901c1d00c0190100c6149680c1803201c41000a80c006040d220200c881c16540c80440100e00c0004800010510070307040c403441404100300a240e4005040300d0b00d00403e0b00c04100342d482e011801c4a0000403070010b401503035045421441c401e04c495004203040c0542d881c01070b08014054010358020307442501ca141051030403414807004840745200320f1005001007401189014540024080c442c00002e001ca1003135002d60b1419505500280c0440302c003181d004200004604d4010409485403805c0c070018041ea205496103070100c94400281c0c15503594112500c0d074280318900c14 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 552530485 1250 552529235 552529261
    0x9050604020c030d050702060115020c0d0c051305040b010f0806040b06031903020a020307092d0f02040603020711120a0803060d020d0c0e0a0218060306280503011107050303 76
    0x165400690800040910389402d0011308188001014082500c4c204058000c1c80c3c0310043c2c00001034410304c00e4512203155000110f481d407042050f90740304265041030800115942095002c280c0100c00c0c1c1074000c90102c1a40c0c00140f050344908614020350b41c99180900220f2524000d1005990101020401040d03010440d140d01c004c0047c103e429081119020760342060004000b10050303409440480308615040c068203001c1c00402c3c07c10050141c0c00c80b807043d02072003480032510401100c1c0b007008148000e15003003022003010031798040d542c1d2075882e64000d000f50b010001c20b845403030480714401d129250032400c0c5031a40c010030300104800c00305034952422a900c054080380e80150045144401030311180b0081e40c01ba4040c5c0002680e036450090402240d000080040310380f1441003240b07045d0007046003180c440c14802130304c10741e4030380c2e880c0c8000c107c0320320ba0b0404040581b020a50340410042c2d0f0880300c8015103000f034000b400112070a0030062005d000c3e4120050040c0c00920020b4a00503960b0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 552531735 1250 552530485 552530491
    0xb03091c14070c0f08030c1002030601020c01050a1403190b1203030712060e0108250302010801091e05040624051305071e0c0201140a09180207210905190905 69
    0x89611100596200d44418219030a176100004540010402d0303000c04106000502d40c2d601101c02c2546140303000c00c0000d48450010311181c1c14080c010886d00702e0184141950103084c43c1002200c2d075203046c28600301e000150300e42d08445045080141d5440320b801c04941038401c80107202c00031400c50300c840074107881010035015002d462942e10000003c041210303141c010b0091052034003030050b1295280018014017003825040c08100a01c40782040180d030301c038090310b0444d021050b00003000212014200c44084041c059217040e02e04010600c82031000031b42c0b0a00c54001c2e41107144040044511b078620f00150300b4031030960301181540144150a40c1900005e9200c0c1c04c40ca0170070201040035442e0001e00d11240b8600d400541d5610a004c11941c0100b29050014141080241860031000303006001c4038041c050181d40c0b0483c072070122410070303068041d01c001c594400c0c00212425202c2043c801e804103804a10800a03c0e00c60740040d040c10401c4a8071003d840d58440710350060f0911240a001d00009 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 552532985 1250 552531735 552531743
    0x70f0f2f06033d1d0a110d0510150906020a140309030312040606050f0d03030905010608070b031b03060612040c0504020c010f0509120d1104030c0b03091c1407 70
    0x40e01034111031031071035840382c4010740002c01e848412460551a815083d4101d0107501c200c0c0c4050403103091811444a6010032800030101b54034a030002040c585000d8413950255150421080c02264040c41c00b003107050381c80088816062000740b91040354106690f00c0b82c403002d80c000c8100d00c00420141c900c444041c0c4400f130308407841d0a180c03c02080c030b1540000007000084032a507080c0400c0042a00034070700242402c440302c00f21016000d000032800d00c00500000c050586c1d80c0080000c1003002e401c0079004285400a590800c1d544001c0000103a00882d0314070030046841c0501c848854100054070300680c000380c841401e0083c601c1e207001018a001e0400e80b5000741c40100000c49560b90b000030602020a000042001420071804200361200070307281ca200b43c3c00c0348500c1c509881d0f400040c0e46a03040035100c00f140e00d8500c1002d2011500c580c1c3c01c068805240d203a00802d03600303400d50066025000610841e248502d01162a00d9441d1f0481301040018070711441c41e02d900c0c80030001030940da03409 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 552534235 1250 552532985 552533011
    0x1060f0806040608060f190504020907261302040e060103050316080c0307080901112a0f040219140a080106120e07080106080c010914010503040305070f0f2f0603 71
    0x6134019a45080b0084030341c0c01700000c0303a40c2000308000800d0221458941a04014401c0342440c1d8001005110020644420810141c14a0701c000c070001c5187c1910343c4040350f4510300b80c20119662a580c09059206900650504241510702c4800054041c1280d410801030350500d24110b0300000104004541a1500d80d003c0c84100713810f080034001410310b64402c01c80203542d0401500094004c1a08100c891080d0f045004010a0303c05084507c44540740d40135400031409d0000b90000d2841100142070710380151002c0b910b00030b0440352200c890444c034800e4440080c8002021103100c5244a149078110000d01c2d144010041180180c84d41c40a00301c0216000c142c1d1401f038909240341c500c9581c000716940c0e45400f41040100310922590a06038028070b04030a031503041036140b4100d526010103050412400000240602d031140c4182c03072006500c001d4202010b4024281941917071042803096540c0c0d584bc003081040e503000300108a180c52241c500100b010707080041000385070b4000504022410310 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 552535485 1250 552534235 552534239
    0xe180a210507240c03050613020a030906110c07050d111c050f06070f1d330301090f020304020d060507140a120c020a02090f04080403081801020c030601060f08060406 73
    0x70f103080d1405002e01020600701d010084040700703078050f26031182100341418500000c1c400c260700e6540d514090388084920240e95543c180303070120001d01a90300e001d48003915204c01c1c51004101c5034010031040700c4160845001c1a1244108402e400819030004c3c5840700030340d080740383e41c140300d00725a100202d030207450400115142c0f82da40c2030400510150861f500680c00304801e454000c00480342e207243c00d20b0500d1391441790002c1020070304440445113105500ca2501d8440f5041c0a00d600c0704d5488021074004490141d107010070322150001e0258a10050401840440000b120f03c241c1e4810364000344000108a0251a03900003480c020f0100380401802d00f40c82c1e4240b10000c802880c40320041d680300c0040040c285507840407200c00d02200021034020300d10304409640c903500d1241d08600b5071141c5090b19100c81c940a000780c49607078001092004045105070003040050a03100c02d82c0000c0e02603a1661800b00d01300758843d9400d008140100d9101da00c2920144e10421546500540182000404036 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 552536735 1250 552535485 552535493
    0x40605130f0305070b0708370219110109081c060e130b0f1b0c330a050912160f050f07080a0b0705070213060e180a210507 54
    0x2907001030007a00481c1c80014072008200100d180036070b0140840c41c001469050004150081030b0703214200358059a20002254040201c21100e01d03215004210304560f41d400d220ba051141c44001d402140100d0100c0030248140341040c05202c103826801043d071868880c160040804544811441c01003190380c3c1d04021804a103180102070203240c1c2c0502c600340130316252a0180d80400001c0c1210207414105050194450118000d070483d150603408050301c44240c508000e00c1e01c10341c44581035410007012031210103442c028550482c4841c407c180c407a540d0341c400c40d181c011f5078000c3d48c0780000c9034080f184804140134900301901851012206044039a869519441800408001c054483d50040030b404025114100038910007030020001510b480207840c0c8030003100d82d0b070061004003806130015400c0f0440d600e1030403d070000041d0311810021a9250810742985610480e09241001071174244071176170700030000c0c88103442c0b684030b0740c0d03d001e81e601d803910540740c00045848202401018041e503030000d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 552537985 1250 552536735 552536753
    0x9083c10050c0414030f06150316060815040216152a1b0302030d05040c181a01022a0d1709030105060607030e011103130801022d0304060513 62
    0x41d15040c01072549403401c0248050148010f814111720070303800003280c510348003c042891070303003d034040651010742074104003c241040d41858501041e001c1c5c3c2c40e8080781464000170b41d0390080981c20303127809540f00302c00103020403842540c5c0e10000300c2c0e406416080000d1904101d4800c105a02200070441003201d41c540300019107840603028401940b4440c1c410800d6008443e011200c96829059001302e80a4a01035240d05c03880b001303412840c0d01c4100050a002c0c1c0004e034000201880d52050805841d8681e0000041144203501c0320345030f02c00390007080309600c00030305078000050181d02400309250390010112a13924020041e90070111203c000400f18003080c120b24a0360b6913901550b035580344950105821030b1401070416100300024456040800d80c03000035801840c1082c20700100202c102d0409500d140110542806002084000032400402c1074001d81a45845100e0b801081c001203008655141c6507541079031103250313050001074041001074104a800442c5110300c00702842c0c25850307010b04 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 552539235 1250 552537985 552537991
    0xf070e040606050d0c0c02010504031101170405012a02151003060e061e01030f112b03090f0b16030509060d050106080f0103030f0c0503040905040309083c1005 70
    0x40b030f8020426010704010350140310221a1035290642886003141d001070064080c40c0009461054800000282a40901e0000c0610b07403218440c8075080c50549407481c0038014010148070300820752100c2d82910a44c8090955034840e880d00600a45d003c85480001c4110300101207446e103030080040080818414464070507068280c1c40580118607010200c80c10708800c400c8030030b02c100071100040020500c030024404241c0d40c0704030040e069500000001d0018100d008881a40f1035410f210180e0b8210540f000b29405840394543d00201e958600c000003da5030030707200b8507440c00c40820107a8200c9410a4000c0c4025202e41055410208100c0104c2e2207034010000700e0481e036503500014003c0c40e80001240b54028001c03602c2154070740c1165401800844088820070501c0101e0040c1410801c0500a0790068841d5100030020752526007001466100c2510900c03515015919170320b04e8500c00e06c4029155801c150303c04500740c400c2a28000d0b080119001c03826098040c5948205c100b100318047d243c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 552540485 1250 552539235 552539237
    0x182e030c020a14061006020304180203040f0b1005031002090901050d17030f19200a26180a11090a0618050405010c0306050f190f091410050105030f070e040606 70
    0x180c54a00941501003541054108071b05540c010300081041ca2014130002c41030030882d52000d600c0340c841c0d103860f01d8070000c941d400402c441c000e5020070030800055406001107035821000c403102c009101422a0807840340701940d0707400110f030100600075410003946043d02140320fa00bc01d264031903903c4031801a80c20a0307584026404082040c415940e54800d4680719920340c6500800601a26a808181c00340404c1107544000d0800300b0395000e428065000700c02140e030f42c0c8410952201c454580e940e10208200d0300180f244240b000c14030b4401d01c002482c5014294841c03c8582052490350401c02d01300c0c401088c11003200e8440b40041070341150a1315506071140c0c48240400e941c14103103820780c2500d4100e0160390806240c0b2900b002250749100340700500c0c8070140d40034410a445d0030b4148607a44d2150b0000d0074504004800011000855130185017000e130744800c002c0030783c0c0360b084115100360101d1081500050040c404500c440d55051002a0461854201880c02c2c80c50a0041025103032654041c81c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 552541735 1250 552540485 552540493
    0x2040305070509091c050915070605100e010909021c1112030c07060503040503040905070f0801080d0e010e1914091e07050d090206182e030c020a14 65
    0x810104100c408042c01d0308942c454950f10300103040550311014001d01419417141107441209540c02001116030000014002100301c0215140010440c5e00401c812103046c1e02c0d0200041d45214891000015500c40140302d065a900c0c000c500405020b00c02c101340d9100c00d4032046400400c1c043d8120b807264034401c454aa0b1444010020050030a5030329043e90100d40040004407955030010031008290340c00350030b08130348075152030178242c0ca54042c9402c03150b401860314090000f4907030400c001c1c1d0103000e000d5840e00306e5a81c03100071041d294031040722200d002c034510340c036964071942c014a11000c5c3c001025120284c2580c41425200c60a80640d101c0203040782030a540710002d091090b0f03001d5000500a1141201c40e100c0d02002d110485c008210904200380880e440c2c9500c0a1034001203445500101178549610341c0c50780c80352800482d030f2113540c03240021000320810016042c80b00d14040110f02c001620006240030140c02508140c062501140038180001d000507025030303210180320981800034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 552542985 1250 552541735 552541739
    0xd0f06090b031e0d0c21390803040303240501110115050909070f0f0512010b0112201920030307030c0e040c0c030e0607080403060c110604060204 64
    0x1160070308444407448000c3c240701d500e00703141d02c40000030000c030303013440e03500d040d00d0340f5601410000b02d40c1e9980a100c0c0c1e01640c446186030b0003180c0c025081d407800c842040060403410f0f021000700b44625620884a01c8061043c0c00b0398000c00c034050043d55029000f8200800c0e10a002205408403480c001403030030551003c00c4003481035503030106001c2c03208038200000700005a08801d00c8514422030780304e15441180360100040c40e440051000c0d1008002410415041d1500d070f4242194803107860281e0f070f004000755011842c00290501481801440684030905180007007030203100a801c3c0d2610070481c414603c14a07400103980d100043c403035041246105040b600c6810002080e81c90100500300f60189110300011680c40d0200840342c001c501c0e418001403441c4010815102c51001f0125643e000786402d0740003070b0203900140092034441c4260303a5540c00c0300010080100b280581d5001404500d801c3c4028800a02d107a8010740e004210350500401d8a00a01012441c05100f141d040314125008103007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 552544235 1250 552542985 552542989
    0x6391609050105190504200a02010c0806011403460e07080601120c150503040b0a0608030901030f0f02280206240a03020306070203120f0114060d0f06090b 68
    0x81d40340504400c641400000c1352400c0760600711900d81c0079651282c0d40d1800090341050b240c1450480305150281859290940303018040d00801011691501280d40480020440c0d885286544501e400102060b411904d4406000400401030900c0d40459841c2d0110049040f80002155171540c68007889180040c1c450b01c0b23104117032640c22100700d01c40d0b803000c02c0034404d900f804107a840c15201452502c502c000c8860070850254000b0360300c00480c40a040b2009400070b079100005620842c0a46003100c01034542904410807108144079040c01d0b900144822050b640c4260040e1010009040c0045007502803100e4003c1240c0c0200300d4034151a9030b11507100c242d0160511407004041d00780c00078180f945420040d6844050302c00420526101d5564800b11081c0d0b03c086205003d90740290446c1c005180000001c2d54dc0e81c4010b81500c0224200400a40400008420241669843c02800701000b140340240101c540081c1d0503030350100d456030781c0000500202d101d103400070a06000085070444040b41 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 552545485 1250 552544235 552544241
    0x3110303281103070c0c0b0d020316021513030302040e011214060f040f0f0b0a0b1e03030d020705030d09030f17040f0212031204050a020f06391609 65
    0x107846810b064507002188000c80507a40d100e181c0b4182280f04144510b010380d120078054001c86040a0701040c0e4000b600039a80c05184501c591802c21181c1000c0d4180c142d036075400100900043c440c080002902e03200111007002c13011352090030058100f644800740007004520903084021842052245802030110000740011400300e140081c110a05181c07a24503800718000b40b0140412094002c001c0802c1014107009a07002e82100740c0e080305013003401004000d0189001d4061160340b202080945070f0405480071020140000d006614058503446044065040310005a0301800184842224200b00380901c0860324070030340c0c0d10300c29040100d8014100c40586d20b0307034440c0c964030303c0108000038001c8000082c003582c04a62070b100c11011034000601d1881800184604c43d00800244010020700064036002075200f207c9c00000510230406010303c0c0e00070785542c0682548168003d019501d00350480603005170007454225030b42240041c100e0b00c1c00d204004017003250007411104003e0ad0070303244 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 552546735 1250 552545485 552545551
    0xf01050a080c04052e0f150e090603161401080c09010219020a05060a09090b0103090512031b04030803041703070f4401051801090903110303 62
    0x15010314805003080d004556600d082c04009014940e9080400c1c000602c07000304440c00c0144000e4122452180851014511450302c22080002c02d00752010031a140724010b501e222480c259100c0303921510400030400301c0e04016241d15094000c40c408119018544003946001c3c0540d240703480000b500100c001081d03444010404020b418013800210300980c1c2c085580c001038402e03d50304003050406800041d120162561000c0e9001d00e00040c50549190000d1411040f5504800c1c10404000200010f409440c070b42c00b001061034004640740151801400051034006a060031054044903128401d02a5a44a900241ca0900e400300030001008100c204950110890075084c1d801c6040600000d08085c41d00500001441004070508081e56003c1501106071165a00d0494050310400d1403001110100c06001c0585042d420001c69141016400014142200c20000d81207070710300340c190b10051a6440c070440401c080d504007102d006000700055801560351403001030b80d048019110100f90391010b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 552547985 1250 552546735 552546739
    0x91507020c010818011b090302040e03070308060d061b080a0e0d020309150c0a060b10020d0806060d020d051006020d0e0901091e020c03040f090e120a0311070b0f0105 73
    0x58808508180d0380702d0581a003010701341960415602809549601400c014400c11909001d41c04442401903800364a880460b402a1420001d001d01180c14607103e216690016001c600441c0100d0003034180302041c82003040c00343c0000604820b023009512840c3c5d104500041c00142541e0611210750783c58490380d01c1c52550140213000b00d440090003e9124024071042c40c0c400c81d44180d800d80b8103001031781140d28107040c2c04160380d00c5080c24a408001001d040749100e01802c4c0000483c2880c500024015440c4800d40e102e014640d55418100032244d0301415146001036000d00c1445282a414000c032401031502284101b00c0d5410020020301d005144103484007042144411a01640c50741d00e42103041d40c20500002c200040c030f04e5601c0c0e40e408404486503050600c0003440a421800c0400907106940200c0361462400d80d90325081400d40f01ca00d9614200d6800c090f0040c0d84001d000fa0040c01ca0403183e04000c109840d00c0740d4103100e507800011b01554020712100030010102d40b403400980c090001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 552549235 1250 552547985 552547993
    0x9040506030a030e01120902031507030e071217040902030a06080607050702180a0b060316170106051215120705040b060a05040306180804030602090406061e081504020309150702 78
    0x10f4400400c0b00c04528003550601943c0c80d9890003030040394015540a9401808035207004440c5088640401c2d41180c40c240000c2c5010f10440d03080310007041c140d045401d03030303028000c21010301e49030030350403145441c01a040f5400410000900440c41d0002d10301c520684100080c01341e02c0d01c08201e0070048000c200e002048020451000140d0f03516101401c006c64410380f40f8900d51340d0084020092401c50700d40c0d9803007080881001081406d002074241240707031a27580d981d4074000802c040030f1000428002c8401254060100e10a903044007403010781d020582c2009404003940d600c0116440c00c040d2080680d00b508402000d0003681007a0041c01000c03002610301500c0c001941c0001403a030300481c00700804854070b8002d0b20b05200c48a03c00034078240c1d0003000e102d507034503034a151000096103c00c0c42c0500039030403c0030002da40c80c0940d2441c80305444814a1101a021442c001c5542404c02042c0c04920010000c605401d0307100d610140d03200318283c80040180700407007200c4c107250080003072509086501c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 552550485 1250 552549235 552549253
    0x10507021207140703201e10090e18060c030c04122f04050612070b0904020c03120712090206270904051c03020304170a020307060501030501020904050603 68
    0x2500050a88101c0c01c0c520380551180c0700b600d4a4190000c07026140c08070380c4201c82c0c0100501400409480010001101d060b480d01802d8060001d00e40d0f03220511200e40a0f0b0725191016403c0c090130341429030801c2d181a24000d030b11401c0120003108155641e0142e50304031200d92800c00d00412841b500020b00002c039906510f060384078065503119a000300d031400c151880b03104081011034100d0800390400d0000c20000f20700244080100e401d0b06200691080e030501002c82c406040c541860b00e40360000d00b0241c2815810040609090f502c410500742d08560308214081c6c0c1103030144041d000445140d507000e0310500341034400a1040b100010b642e0703091854020200016601c440440b90b8105c8000e01008504142040241d1007808081c00c0ca5005012501000100320780440e41c400070107641209200c01c0080128114202e01048a0007030418212240440b600d040c4940608100b5104d072040301e1625200d60b450105482c401c0e8022103c1e42c0d00810308150b68078050003000d601c06426801440042 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 552551735 1250 552550485 552550487
    0x30706031104030318080304030803151c080307110304030b0103031107140405040305070602070b070f0f020a2a0b04080d260a0b060a05040e0a06080604082107051803010507 76
    0x44a584001024021101c1050f81740318008030346440148216025a6251a079038185010581e00403143c420805e212640d4840302440c2000e6001ca04141d08010f0a030258030503134408006620107800c0e082400f050010103100301400700f00900c042d502c076040d81006540b4625003e022002e01f4243c40707545404c00d140902203081c84a440020078041110040364a484e203007415545840707039840140001e030000032600b0500040d032440502603046a0307611421740c0304c5c8810031070700c1d1400a0a0700303005800854065001c1641c8074030718030095031603141d103c0740e0400f1030f40500c0e00c00005901041c4002d0000c40c0401c00750740705104084050720142081001c241d95588540410310111546c03008110100c00443d03d070710701907444294036400241c050350750741c003100c0000350041d0850300c240c281e0140f86200051003041c4034001c01e000c40f41c82c88000c00c403d4480e566400380d190841d000d05020032440c590204840d1113441c0765980200155101e030707070752140ba00c00343ca0b421105000030f8500981c14a07086c000342d5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 552552985 1250 552551735 552551737
    0xd030c030305070e060301031b1401090902091f0903110d02060406200118024902090114010206060114030c0c0f100b0108090604050c040b0f0405150307060311 70
    0x1a55240c40c0002d120750701c120059941a14510030f1a4004c84040004810441158990a81d41c0b0009106410300c3c0d503101d01100003803902c51221800142c050340100140402d40c0c01a102d5040020416a80305940c119081c62014646a5410015030311080802c1809280b4040724204a01910f20700c040d404030341c021030660712a6116030010040c40070032051503083c0740c410034803403440d2503002440150385048007441c07041e4110701c043c0c0c0318500301e5661680b00241a0341c05030803d0300b0386e034011000c2503200c828841c44580281107880848610042c85005a9501450718041c0c0455030f003240c81c8641c0c4500080c0760140050806041c020754200ca05240204001030342d03400300e001003c8540e0741034901140e5007051202c24524075240305841c941da141c6c07c1180c12241294100303a88000c0c1682d40c00e9800b580e10340c00ad580c09042a00240048002801c041c1c0100894000161104070500009804101261011100001c440d98460740164042c6810b005250007800c1918091081414280c102412 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 552554235 1250 552552985 552553007
    0x1005150313050a030801150c02031e030d02300f010306110c030d0501051216060c1a28020414060318120c0d0c151a041802030601050d03 60
    0x191600400011880700c0c059890000c4550710406640c0c5408032841c002d03041903000e000d081844502005008580c034030851003006c07503580050043c06215541203000342c9503200c1c0d107607151140c0000c010042180b06140010585800f0f00c4401c04210440c2001080c030829031000d02440030924039044c003400068200c2d14a05481d04008006098641c0501c80701282c420300da66440c641c0008504071340006a0784c1c4c13204d4100d03030003a2503060624900014103070b01d40318034255022022402c1c1200313000b00c0d0f1041406040361807040072100c0b040f4060b40701e00e28070380c0401c58000b04c6940f0391408014506910100750b409564807404107604090429030f10919811005195500643c0c000c00061070a030320485800e1b4442c4190010794400c0303040403a000020f81e22841e04032405103d40c2d014102c02038884d00140a0f500c0d00088010360511403008518041d01081010605d10340500c20103105503030360343c4a51300d0218842550b40d20880c400d4410305050042c142d100902c9410700368a0302010940100b207500e5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 552555485 1250 552554235 552554269
    0xa110f060d0509030c01090c050f01110307060b0105040b0f0717030603190204091b0609080318060d0f11250b0708101208030105030f0d0912050304031b0e1005 70
    0x10342c55889454440c03860007041d407001829802c0440520130310402d181c01406944007950a1a0070a0669005541d014441801c105060303104000d0760000ca2260740c40215014014901289050390310003c80c0c0540d00801ca40003810480000c1c4074040062104002c1041d02c8482070700790562502c01c0c00a84c40c2d03403a08414801c86588a403000c1c0440da507607405140b01c03da006c0c000a00d414440308a01c0d82040d4580100030206001031400b01d000080003080d11841c60022900e041c0030b01c030a805020b0150084018219016100d110803900c008440c014501c005650440a903241c40d40447c4d010580e401c4e07520b24812603607040c80f4102c042202200745c0c60b4003608504046071540c0701d00c40c54068464a0740e000c410100c0da1241580104840140110b04841084003141d09000050380000c3d1102c255035905404035294120030040b0010400b407012040d40100306881c140365507900e4895071410110440d030314107c07811009114004a02c0c4620760070180c5409080e04042c201004140b0b81170348050911 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 552556735 1250 552555485 552555491
    0xe150402061b0109020904050705090903070b0a1a0d080307030b04060b0901032004090203010911190f050d050a02040602011503050606010e04060306091b0510020a0f03020114090a110f060d 83
    0x70000c00825006020f12071760140140d4002e02c0d0600300540ca40b03a042c0500ba1152300a040802c4c40c245001050f106480c2d003221480c032042c4c80d0080c0c90401405484100e0600001c034030403040741d66584808201e25180229015584d07032a040d540141124003680840d40700707604c4c028041c003e480c0c420094500b050070a0a0004540c0465401c13504003110001d1032042440d0005400310b03203810103401542c101d0321445070a011101840700300519500a2041444140031842c82d03c910351032041d13200400902540c10441e290400d00802e03001510000c548034028580c000a04215445d42485070f14110301c82e15250b050510b0440e80d5140c0c403090301030905070402031505015070450382e440e80000011580322000300100040c07860b01511690007143d00d0f40c02c0b20120040080d130b41c10007060032684030245074091f0001e501d480c0e40742401e1440904080c4c1c119941c0781d0190144c0c1300542022406580704400800b141a200d20701141d1010b101c00505006103410800901d040c2c40c0c0c2c20030f4500f0300c00204004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 552557985 1250 552556735 552556777
    0x9060a06080f06030717010207050714090a0f1506030603140a0510091104022b0203060a03061509091a0c0a080105010c05010b090106030902031209010e0d060b03030d0e15040206 78
    0x1038917010458005084550200b0311821112105500600485200d03000b80c4e8025561918007403105841e042109400050580000f00100141d9216641e40c00f041c860024205410344560800000c988e001040820b81e034040c10b005000144510100883c0004001c25081d85150380d81b544454000c2c6480a40e86c1d212041041000031160030301c802d10f507001c0d04c215101c0011040e0b400d000f868036428404007c0c1c8103100c10a00300440d0003124450f08001d025801040c0c510b40c0d03000c008107604018907500c0303c8030030404200300c0014000d201d6068012601080d0181130f42c20301c1d26803040040c0c80b03401000b1040008142c1c2c1030300030078900d044410034207101881c02101d0400b98090010504003e40c0882101c001061942c3c1641c071540da200d0098040b04c0c0e502d4403e65202c1181e10807001036602083d800034090210385015000001424820b6101103007020710b48010a00d59005441007520458442e416140040f03c2041103a101c8030180781c43d50f1550070103402161003841201d440944400c480300c41c3c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 552559235 1250 552557985 552557989
    0x6030c0a08040c05091e15150a050c011418030901020a11040e0607050307090b030103050a080c0f0a120305090d09051216090605010807020312161106130209060a06080f06 75
    0x403e00400024050004a140002500d03103164003040b180c08020000f030000c60b00d0111215040301c045c0d40080d015892480050300c0000c1641c001074500002c1080c1000201d1503000c0a0140d02500758800003c0304050800f526143c00410040c04800444e910a2100c500c0c03aa9000458009031500080c0020000c800078006c100a041819094000d5100741410b12050b154040010340c070a942a9a5003086981c840b00d2080292000384000b420950010010740c0210380454010215080820103c511a24510b072049082a40700102a54004000d0104217403140d018022903600a502102402c0d0090004c84064101d42c2c46000f510b00a800c2c400105824103c2086200002454000965561903035401440d0281c040f50044500103141b400200742224000800d40e0051108a131046030541d07644900303035611100b001c8082c8200030984c10040c2c64010144074a500588044042c404203540794014007109040140070140104685001048103550018129802022400350884a82c50f0200 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 552560485 1250 552559235 552559253
    0xb12010302040c110a0f03230f0c0a0b010303091409010b0a2111041706190209030a0b0a020d0c08070e01080a0e0607050c010506030703080405010807030f0e0109060b06030c0a0804 79
    0x7050104d4031882c4800e5041c0190a404c040a0912a64074030020040303c0141e9800c1100c40c508084041100703000010450b1525400381101c003c21100301d0381146065211146201030a030710640125036140d20a00823040c818030f1003800a0002c1e03804200071351401d44843d11a1050034996400c0014031002c2030405a4050549140c0064408042c04611145140206282e04c50300c03404c0d6000d020002d051110303e1003c954a03120702000030280243ca0395540308c0030043d600440115615004492074070000032402283d181c001c4200354001a115042e003205001240c02c0c0001c100705000f41c4000b007060300e650010604040c02e0082c40c01c0202038442400450150441500000540c0200c00402002c20f40c0140130340506174036a0020300058071486c00303154458803a0702000c1c000200030403050102d940501040e5800812a10f00000c1014001d04920101d0710045107105050b516407284000340300070f03402080d00a003000c50303c03945923007490f048800d0284035440b8160180201da01c00101840031442d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 552561735 1250 552560485 552560507
    0xd080d0903200d1d030a031b060507090816030203101107060516021606020c0909100c053001090908042c012412060b0705160b12010302040c 62
    0x11600c160000410032145440c3c80410100b000014410060310481d4909600201c000c140e01074082e01d1001e003551012078404d400b14102c400800e1100c2550400220103100f01c92041c006907450203001414854804e042204102012031803911914042c40540d501041c6803011401c1d0309800034000032211446400713402915405020f00745028104403d600c01486406040181c035404c0d1245110841c0503110040d216002e0000140d110781c40b1a082030800300011500b15031900200d4a80e200c2c000307039a60985401300d68110010b031000c2004c1124004005007442c00514840441e81c1080043c2c003884154101449000c99040d100c0110405204420f81103c020b400180c0c02503460301c00d480641c00d0b000c0007012074414016659000080d40611a92950700c1c5450b4244d08000700b11424001102c00c0f50a8411500e8042d9449200258243c424001001004d02c910090544441c02007100c10310810554440d100b0300b28100040380c0c492440c0c62599042d00c2d4111000100500840342c115400e42d114 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 552562985 1250 552561735 552561767
    0x21141312081810020a092702030a1b0c0204051b0306060702181e01060905130c0908030a200307020307031707060603081e0a0f0804021c0b0907050d080d0903 69
    0x1c100b20294165130000c145032555134441c00c0c1e01a58621581c40c076000c481440d0429900a01c070340c481540c41940040d40c0042c4004008154802c0141d10030f40c41000f040c2c03040000c20440d4884a085040c5030041503071000e26840d40070042c1000c2c840c945218030008240300e00c00c0000003aa1740c11940d41641c08000500212030a001c90302d0803211071021502c0d080a1080340e00d0301c000000424900c203403880e0050300c6018110ba04088004070b12040901305810301076040c00141c85001c07803042c00c02c201170490510740d035071850041c8503c65101340303c044428040c0e14030b0360820002a00903803000129041101c0e40000310003100905002d149880303014120340100407a00300440001400200c4016062a81000c1d9044007031002c5130048406500c2207074412004544640c0309070f007040c0d01031002503a2042c0041c00c07805d01540074070b04660503040d07140070803105080344c034040c0075205508116490141209481d01d03603516826455021550140c0302402c03862070344070350f605001c15100b5107031420341d1203070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 552564235 1250 552562985 552562993
    0x2d030b0108030a02010e01090218060f041814070e130302010b060316030f05150d08040b070b1806060d060f1506030606030b01030506090105010c0201211413120818 72
    0x41c0c0400320386961280d6503080042d8201b09209400f031406108480e0b84070350042610400e08042411100d11801c0242500e0b40700a540c02e00a4036a15913000b207103225400e809400000301c40c5032420700303004010140315402c142d1003650309001c0300408608941d04105400800800d0404c940340807809014021480c1c1c0d0000e1002c8148815182402990071291a5580302404174810518a072021510204ca01446080203120303030030000e0600c4601e030590580140811071629496070240e000342d030300151381120b402000f142045103130f6041d080c14609c140c0d07150024000c541030800c0025609083c00c4406058180ea40300c40031404a110b92040c2c1d10504c00c100d104051503130341c4402800600d5a4411200840c0c14054944a0b42d80b1034450184a40340040494070180d0a20004640b5121212022411b103c045090540030f10340c140582401c136000c00c01e010501035001c3c1e200b500c0c0a81d000d840075202450359070707410002403c10007200d6944075503031030710b4030040d50b8404c580c40c61100304640d61141360007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 552565485 1250 552564235 552564239
    0x90b040b0c0c070311040e21161b05090603070305030a032712020c0301020f070b0703020f030a0c0210090203060a05150a08070509060a060503010311010e040507170f012d030b01 78
    0x20301e807902d0a843c10003c80303040103642c0981e04240e4444040004d08c0c541c0010f80b01c0103944203448040500743c2c0c4070018008403001c41701a540c140d100741c9462000c040610510104000c1840c0520703510ba07003e0400d4010708280b0b4659900c4503524010040f44071b061649600464002e81300c026407104003a1410043d01c8132030708440c204040c1e25004020b20314018003402018500c0e90905000311080d051100c042c0d2031908a103610341c0c00140300090400410540c003007003c1040300c0e04190185020390204580050144681a0040d00e028800140f404500d800d080358240960707000b10b0360f1507020303200d0b010105059950b000e10010540c107001d45c099103d104400007003000880000c48600760303641910500d0f0107484480800c50f4100e42407068000286082005100042281c1e4883e419850103041c0031000c0341c0c28600260513100100ca8500010314500505d14600b01c09115494008600300321040055040c0a076a00788241240600789201481c580c403a103068450715a20401580c115415a94a503 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 552566735 1250 552565485 552565493
    0x7060209090106110d200a0c0602010501060e0604030b070c02120106050307051c03050c07050604060305060f0d2102030903010e0106030203070e150d0510050108031309090b040b0c0c0703 82
    0x5046040568020341000001082040c01240074018100c4904020a03440f000800110303000b01b0200d03a560000003000c1105148107004006a00700b20f4400c12251a206060080c028211041680f211081003000c05e2030745e2194031000c00b217400303683c1c111a00c0c000a41d03461409580d40210540000d42000485812902c010b406605c0b07682600c0003103041e00c0040355070b0070030400d40c21910503070314030b025810560403000207006200800c00c5c03500c410281c51000e980ca07000124a078001e80d22520200c0d840d41c04004803807500d10b4201d84518821580d17902c0e6000030b500c0d0404603401d1031908903140002c0e0034500c21024020070a80d032000d80010000c0c031982c1c40784400c850190041c2d00c4220b010380314068022501811004801c0d210341c00b4040d154552095010030000c4601d0142c005072014000d0b008000d807601102d024581c080c4c64400025540c0d800c03541d440c06018080c50340700038035051901070a5000112680c00083d0032036080640c800c41520b5a46483d0301d01d1155100402d118403950303030000100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 552567985 1250 552566735 552566737
    0x2090a06090f0f03021e24030412080907030b07030204120c170307032a0203160512120d1a060313031812170f0c0a1202010606091415070602 62
    0x107102511072044000c0c3c0d5541485221000c2030000a52007540b1401001c40c2128411b034500000000814090303441214451640184264800500c0b081d00c0c00010003050003100920107402c8071003864000c180b894501c001c0c0d5100c440030700004041600c2280460f10192094055a0182c00c820b15101040c1c106446d1040800285100b400d201d03031540701d10120481c0c008010340d41d1182e003603127400c4a09610403140c40d607a05103000003030840d18107000500003d81c50400000040c0b0741c540c41018542c0b41424104500781c0000c0b580c1c10000d503c0b000741c0b81304500403002501c0881c0da80c00d02c04200c6502920711021401805040c1c190000404410002c142d01c80913443d91141e8026190007e056400175130202d03442146024250020a4003803d21000814150541003043c440da1846401c01c44d08500c502d800f94040d04030400c203540003525003820302a6110074503840461341d00082050030700d002e10207060390101e840745003040000d02420901940750218110381c80340c08090303002e07542c0c0311526041e002 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 552569235 1250 552567985 552567989
    0x2100905032a100204032103021903050609010e010b181c0c03120c0f0b04150227060a02150a020d050708040b0f0c03061917070812031015020102090a0609 68
    0x2e90b1150046280403140503200702c40039650400c1400783c0c07407400c0b4200100814030140340042015400c2011240c402100070704505114038a55001c00c80381005010030a40f03007410b0304205c4a000d4160b00401c03801c650304049454a0b882c100031561300446031070008800c0601e1591325101c0a407809006070801c00203441d88000c0e284103402d14510107030742d400d049408000d928001840040c80c406048007052001d100194407521446a0400801840da030704410f82c1c00590b0b20005045c5609103850b0860a040000f00120701c00b5903150781041a040e1340256a50703000003184400c070a1039804602034004903011621521101c8078144840c1c100420f00924401d81100e050383c072041e02d28081407000c9074164100e13025504d000c00382815a1101002c00501500005641c803540030f00080008084100c0903201d20910702070005030440c00e00d060902420100c0810b0342410722503040082003003001024800c28155201001c401c19446082038050b0300a10076460803540c004411800061070950000364002 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 552570485 1250 552569235 552569317
    0x1120308070e0307180b13020c011404020d02010e0d0803011d0106030209010c1118131110081302150d09050d02012d1407020a060c0f0210090503 64
    0x80c981c1c0e10650219400c0300c07108a00350381034200450030081d6980040e56000d0384840326600080e4103036041c002505045d02058040441c40d00403681404490003131245c108034055148500c0b180b490117600103001e4802d110002070500071248901c0e8550340320121709140c401d40c8002540d90340e5131660058103407a48000701c02c071140c0c010140085807051007402038520940060319040c425400c5583c881c0b0040c0da5150603150010504d203804241042100c0d4081d0207151208142800c012031400e01c1e001e02c030703d5070102078018415002240380f82a440402c09600c0000e9041c007107110072051002542030040d18a2292a01780d0101d6282d8441e1150340c890f061a501c00c4040b80e403d401d11030300590030780b454803c0d4100d84a9040c4000350b1404440c40340c1c08100c4144000c0014461014080244200d0007501c10700016888013031071104001c054031500b80c20701d05c0b906090025804071007000b9a945064204a04500d80340c0203500b04010042050720303101000350040c5022610303441c4403a8640520030607800 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 552571735 1250 552570485 552570497
    0x1b0109020411040303080417190503061809151506030117060a0501180f0906051614030f1807030203011134030f1214010302040f060b16050a0b011203 66
    0x884900b400400310340c1200d90584036030742c165a03540c9441031505141c9071a500001c4040200c82c0200c4203503a803200c80f0360358a480342a100e060480c1400400111084841c03049070300d0b1002e210f0300310400207501d000c2001c1c041c16500301e95200900c0f10034803004031a150703401000200002c61280c2107202c100488000310f0080300d84598810841009440b02841010304901805610015100e0075800000d51189160700105410303078030b0344c0c0b42400c448045407040e5191819081b0682d4241e40b0420200c510b11882c1c200c00c0c2542070514a0151070399003d460000c2c03001144201c1120a40709100650046030000c4c002c00025911002001c05c1e940030080f100070010400340d1200d220b510803100010302c0c016107642c18480b641c0070b42e41603441781c0c2d06144100c20702c808200b800340c0e00c4805000c1c0455498444800725025451441444180c1d240d02c0c000b016580e05188090042c0611002510800c0707000682c1d029403281d0038141a030600750000801b0f05901c0000001140a0703025100101e1314500ca0f90399a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 552572985 1250 552571735 552571751
    0x906050708070801090c0212030c130b040f0504090f020d080c0c0109080703030804030c14010b040c020d020d05030c0912011406150a0503101e14011d060706021b01090204 75
    0x448041d103080b10028045844a40180111071965000e42841902c5004540808404048c801c00c1134004480c0d03440107003c001100828640386402d800c0040040c807100070300b401c1c00e1101a40d2049020b01803140596510380200c4184101114040c18640c1c001c1c2c5052120300d5541821003c81d071003084102d1142c402c08035407107039a5110f01423050032241c010014000103811550215041100034105804011000c0400300100c2d40d160111918500b17450000142601d86405020542c2c00b00031140d01550001d110100280c1e4004c21415511205072030b046a4980c0c40e0103c1c0c503124000d81710072a030841c5400c805880520b0301540940200c103505140000150754460030400c402403034109079175844105000d4441c2d5036010b14040d5410071017448141561685440316065402c0c5052028007400c0c0304141c3c01c2041c07003800c8406800c1c0302c0003880c04140890304140407031035540a101300350303002c1d50000483c00b061000da42d0656214001c00f600721a4640082d0704184e02a00d0750100070b92145245c0111 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 552574235 1250 552572985 552572987
    0xb0d120315030b04480b0703022d031201030c0503010513060c02010f0e0a0c3002150a120509030909040b10050a0f14030c01050f0c011e09060507 64
    0xa10700b200d6114483c411140d940c1c0d0703544140200c020650101100310405140e0031494003000d08441e41c0031946a800501002c04002040051607034840301c0d11503801c0200c00c000c00e5011590b040d202e10845c00f0a801070072000406000000c2280001e006400086000b4141d0700e4003405850407640620310f0340216944400815089910a550382c84d083e0b0300f000a14400510150064483c41000d8000051240c000d03a9290b010381d0040c011011070754111004886c1008046011540500368030942e9840c00d219807002c5845000d14241c155105407500031000007195114107a810050300107040403038440c00c6622001c0e1031041724411b4443d24a04181c00940d6103000042541c0030705400420011050721a070f2191908040d001d045408110781d100004a00798480440301c2004200d034407c0620310071702d0030014083c0d00c0640f410540c4aa00b0402d000e014580c0d005090314150314900da162581c079005241101e00501c00e40a03010040b07080c4001062084a8581c04070120710302400c400d00c41681c0d820340c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 552575485 1250 552574235 552574271
    0x3150720070506071203020c03042c06031902030106030615080f1204180e070b190e03070308032a09010e0613090c02011d0a020f0d20040b0d1203 64
    0x140c6401040034880b42d800300b038401c001c8000d01e850b5420700601c0d186004230940d055600940040050080c80c0480ea117114000e254644060400b0b10041100380c1406800640ca40030350300c800d09070224040f406002503607001c0d40030000555200104200d41c0010004400c0c1180340c9100b00b040c14001c071622024140f4001c20444d401114800000f4501803c043e910120500750340d5420b0322540e690007030192115020800e11020f030504a04907a00c800c00710a0703045100c007000c04011f04120096800401c00c1d1000200001940c1d803064180d51203a40d0301c030201520640c7c1c020300b0807034072001280a001c1c2d1080480201f41c440340c01c0c0d03111040350030500c06000706842080040782c5c1c40c21450754200000b9065174440e4219002e50f00c004100228804551031800c1840625143d20350001104c080440c03a040007100e01c1d4078070503a8484025030300382d10f51000000740e400c0f662101d441c1c01c031003078029a03580764042c0c2040000207214509042c0c0a0900348020000c035644e590100386000902501e00003481 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 552576735 1250 552575485 552575489
    0x518190309091a0f060d0f0501290406081009180209100e06100e0307060503062706040c020708031b0106091407030c26090105280b0f150c06060d0c0e060315072007 72
    0x914122f00d41407402d2011910710348000c042c494030700410705021030080c400d40181081e03030314a15803821403107210740108a074904001d003280e802d000390a40c0401c0280701c080e50803540418103d0740350000a600d01c1e0282d0b12400203030fa006034513026200c40801c820781c203d80a14061801130315203c1203942d07450480300c1000b803100000b0f000c5c01742e0903000031234515154010025030340d400d1040d92b20450382c4880e0300c0d20b5a080346000f4450380c54030b25022204480f09206100042c00b108009001d102c4409041026105014101c0010540c440224800761070044075456511203114800c1d0203604041c1c0c0c610740703c0300e8082c3c600100075400c180204451405030308485284801c22030f071070f41641241c108000b0007401c0004103650404441512040c0c130380d072031a25400c0e01c03040d004032072a95100340f41421410004002c1003684a0a4000c15400c00300d0421014081502c0d010384407007015485180009240403458411100d486208038204151158004503401c10100311141c4003403034901201d02c076500c82c00d00d4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 552577985 1250 552576735 552576809
    0x130b030d1d01030c080c0903100203090102090f0301050408040303050c0309101707020604020a2303010e03250f060207061d0115080304050303030a0518190309091a0f060d0f0501 78
    0x1100411304842501c6c00820910000404407062000101800d00c00c3c1e81044400d84090395020441d00c400f424400c0149503110320880007000350f85000e640e04d410b540070700e00000d403c0190102e400401c0d508100f0848454030317070041400040300303030785c840061a00720110001c0ca6441300e80c8002c190351a0000455a01480c0e004000c0c074001303800c0442545441d40321800c2011801c0e1002418501d6481c05e108111013061850055503075400c600303500e804141e04441e18542c00c02103607400d0b5008100d456452181041c1c3c4a000540d81d01c01604000d0701820403902e00300445000300701e03103800c002015031181080f03c110210b002c0c2d0032039944030760603107a000768840e0035003680042000601c00c40b42c40d0b010942c80440f000c80300601d880081e421a1070410000c1c0c03060700a9071240b0003142810f0f0041d2000c0018520888244200003451184030340561520146602400d286441110269600d6090307a044040d0400200807207078044807000081d00f820b00ca0004591619070070240010183d104d00381840e030704 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 552579235 1250 552577985 552577997
    0x606010e040b1809030706060312091a0d0b01030209090f1506041d090a0503070305040f0e04020f010c1e0b10050114041224020d1b0e130b030d1d01030c 67
    0x1d8502c0100c03c1c0070b004002200c00d010030001d006c001060303031242d04043c42c003684c4104002c1007561409000c00c085600141c1031100c0c42050241241410001c0f0741040e48240400b0421070b00740001a0040d00400100b164001040e00030094088100c070b254611804258424400d503401c00c0d41401801e20070743c0503403076400ea0250550600d110361b242180350420302d8401160703038082a90721054156002118100c1c005080098200100f0302e484d07000d00b015001503c01004541021b6002640c800c0c0581503140c144581c20140c41d084c80680c00c800420401142540c40340c1150300c1c80c2c00703200090115100c1e96510171074000450194410380500c648a0129030400e8070301410200d0801e0000301000c400ca49090f250700c050362010b1443c1c43c4495011039001d00168441c038468041c070b410b8890204443c170069401c038640c0c803401544410410700000c2c05039101301c141c040c002d8010028004c05c611440d011f100300700301d005045901640410341c8070401d050701400102d40b0fa0046082d40c08006001000401c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 552580485 1250 552579235 552579259
    0x150f0c05090303040920040308070605010801060510122901020610030c030f0501090203121209150c0a120c0e010212030103110909030c0a050708100203010b12091204080606010e040b 80
    0x14007507012004941205080e142802000c9803100340d568030a41084800032700100301441004624000e007405002c0c031074002c1c44500d04040114041c440007540640c10860400304443e601801130388220039980c03504440c901c10325003030019916000b80c1e04e8401c80c0180325010000d05182412a018030a8036880010555540d141d0707181c0d04c101100103d01620b280d5030300c108c1140160b5040000144041c5c8041e192602c030216055010102c200040042800b60050844420f00e0306014411640c40452030784010b8440400000888070300052100c4941c1d81e80c60a070342400d00e00d401c075036521840c0c3c400340e00f201c20007110101c140382e00d0300086c44020014544e81d46115224684192280d60011001d001c480c10440c0011642c0e20340b40d82c80c2010b45164000e90801d01c80e881c0140055844103112260a41c5154544055410b45101c1c1c11908020841b4000100384d40c0081403040400016014109c01d03215a00d683c00d0310f85501003a900d160215508241c0010542058020b82041940080503680d00384 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 552581735 1250 552580485 552580499
    0x412110102120a200324030d02101d030c0102070605070203070510020a0302220f09110306040e19050d0305060a1404050a110703021b04050906010b090a03150f0c0509030304 76
    0x1000d030003013080380307107000c280e2604072004405503226070460843d07100c15451102c03c002e001c01c145104c0b54002d81004241c1c480142d00001d141c040c0c6015158001307150200c02c101c40803595218850030303240e030200248000040c10150042e0054a002e03603000c0000d074580c240140da4a1180c40d030700600765000036121840440055000e0100c4d48410b00b4003500c0c103010a03403030300054070240188005001c800c410500101031012000740251003507400800040caa4038154404902006140b14030454076000c441400070070600c03002d45c10b0b0038070780ea611210444502c0c14070740724400010101d0000b441c140018241d480c043c2130213000c4034030841c0c1d04072017504142c0038000500801040c4d144526144c1400c00070341c85002004044c414000e5000d0300360042c62800104590324034070401403086007080144010358401050013411144200c07465a0f507015007801090440c1016403024003451554038100030062010307000f1448103188901c080040c00305140c41a00c150080742d28298059000307000c144000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 552582985 1250 552581735 552581741
    0x1c0e15070f0809150a0905010608340b0f0406080622051b16051e0303010e0a0b060d05090d090614071106040909020a1202090a050705070b0412110102120a 68
    0x300010f2819a50354101c541c0204110300740680300b880c40700340e540c2828810b100083c4680400b0381340310009440036070810188120901c2c20b01c200c403c242d000f659645916102c1402c2d060005288154400340c640940c0125200b240d00a807068002040200c00080c0c40d0785460f0114104800310340c402142c400190903000700c004c140003462a810000304510160040c0e01c4400a00f003040c7e862484500741c0311091402600b018030a818100c4280d031841d8641a240d03001000303030b030306444404050740240d80d00c00c510344025191031101030b80c100000151410b06180f5942016204000b01c07421140d42d04002d00c803ca41c0c024191040f41300080e02c0101c0004402c0319038009200709401484144101410b0700005205584540d120880e940d0707440c0c0e031010840c24680d002c84024002c158602d40200965000b06030400c6004111199450343c403000550385c180210103613040d0310703000040f08140703251501d004032403001001c0141380032440c0c1031000c00d12000140210b580494024402a207580c41c0d40e450380e00a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 552584235 1250 552582985 552582991
    0x909011212140f070f0b0109050a0b030307150c02030715090605061c0b0907170105010603060b1e0a050c0109050a050f012a030204180606142502061c0e15070f08 71
    0x480500840c1c8140403450040646012380038001001903d4100200580300300c510b042e080c54040c0d013091003400d000c515240f00482400701440004188500c010508905610034248001d000384404c820705803500d00964000322201e842002c0810190321031808100c1040003140e103c008003242850504005004240140c0d00b01900c2400c81d40d8803070325034009011220444c088403d00fa95500010802241c1c140944001404038142e443d240203146070030313005041d00000e01000300210010349402c009100b403044940b5a5152402000f017000189400d0703446881d03024041e2407500c140b08440e042100d061042c40c58080c4080454a003403c0c4403032600701d81c41040c3d5915002e069090200041717081d0081d5100c2c0345140104030000f0290304010780900403103c1c03212009009141400280c0742c1040541d0f10454482e00403040303955016052000500c4c07031143d40d03000451100c204462809a110a4002c40e0940f1556000d442640707180c8800e0000c200d60403244c0d070000480c01880646400e028040c260b030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 552585485 1250 552584235 552584243
    0xb09060d020109050301020c01022d0a08090a0f14011a0303090d06020c1c181a0c10061d010812040509100305060c0a030c08060609040b060909011212140f07 69
    0x1220f0381e501c0300000d08a0f04020306018640e5000240704800318480003600c1d003003003402c650400d2000907010182c070050142da4160828080301e0000310b850000200280720041c0d40c0140c0504450b0303d44e01d405000e08080c462005940d40c2041c00156202070000001460010f000e002541010080420401241c9a00700f0549102e682000101d42012060140141c030002e030740da0b2010b01c03004032040180104501d4490045090022000b07114241c00f5404082c6a140341480e120b844440d83d0240900f40007e585016202078600000010102280c00e001d11182450000300c1d05142c1e0384020700740c1c076a420a60035403d100001c000902039403411041a41d088034202e03118a00d110784a82d1114070b072901c1902c41443c03003c0085415448180e05000b486446141d5103826a444e080c2000070030002d000f035013051441551039400400e110b84a210a58100c404020f104030200c0d60350b001e256840c401e03401b405803021b851049003410141d000d218100c0c41030700003412141c41c8c1300d030409900b4101e42240030212 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 552586735 1250 552585485 552585497
    0x11060121020d02090a090203100903020705040e031902061b1206100c0602070503041503090302060c0a0201020706050112051204080322030b0a15080703023003071a0a0b09060d0201 79
    0x4405600ca5081c11403245981180011b08a290b50040500d4101c1048580c40d401c0e060040c0400065408100c0c0c40841d501918046080c48403200700a0a41c000c0650010703c01d2a00ea4060141942c0000e169010b16070b11115441103a04003000014244180c000540914121101040590820113046600c5181d13a01c2c110600a4855580c14181c1e44668000e4034554000304051212070103c0821003060302c040e0030b0811120589680281d01c600d00140b840442d480040707106400340e03001703404072100306901c96802c1000c0d6850341c1c6480c1d54081d00303100035a04c0e171050002108901011f00101c1d416601008029820010200e00f0f640703071012001106114259429030020008a54080071802076040c0b01c5e01042d078440d519201e0038134007003a5001703e0355070340905010000350b00c0710280b40d0700f1081412015101040c4100a1000814140210b0b0502d48800604002400102401b40c13500344a080e01600b9a61102c034052010b6800002d000c50b0301c05618408502103150542014a106106041c09 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 552587985 1250 552586735 552586759
    0x50115090302031b28050a050103060509040b04061b080f0a020a0206190204030c0308030a0e0303060a05210d020a060e0d090501030c0c05030a090911030c160606051309031106012102 80
    0x74510019001102d80381c0b041084011b0100349000200f0340f000e00000e20701005000e10b0f10340025402c1c0009040500050b110102050a015803038110851500d540e02d0140f401c110604402041c0c0d41044451444c2c0039011000b0070342544044c001c40b80030501a50042003192540003c0e8111144907a40001146500b088008005605080480001c5025500c0d154407443c100c101482901c1001c0130300c04442d0410010003803d5601c02e5844000d8400c19a0303208020710f01800060103128a8444a030103600c1030220b000f5882d50300142034684184280700501829003811080c90391411580c0400c404154004014040c030b510a074002c0180b071200303240c210b04002035500c0ba1415580030a82e01c000180c0f01010500c102c220030301400004d030450160280c9185403e5940804501840444402c108008901d1300d017400030b15000300020300002007601c40c0074901c0e00503503002000b00c1c0360103c0110f50b101401a40808003c42e00b1030494900c4541a1100360304000055001014140102e034080c0341890701e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 552589235 1250 552587985 552588019
    0x200a0501050406021b010e1b01030f09140d031505011103071b050f01080c25080309100f09050616030f020409021e1606090c1503050115090302031b 65
    0x400c2d000720300400005036215000c107003000d544145401c85504c0d90303041042200c3c0b240c100084a00034800301501001000c40d0030001200604000b20082402c81c0c00e004a5000b4090503d1000b003e01c1c180104a6100c6002c0c68815410740b221100d41c0d0304c5403181644104059401901030008030031400003940d162800039500d181040003501503882c3c0b140c030802c1d400c3c0028180ba0880318030f05002424901100d1405900c5c1403018403540c000e2241e207990403120780c0e0b020062010741c0019217902c181100e88134070741a400c0c0c0e80e480c00c3d94203148500500701040e070407031070741c00c0d105540c1e47c9600300e0090442d035940c03520f8240e104248110007204142d5600c0b03610b070081c5c10302d00c050700107003078117200c05030f520101c00100350324460031131103050000c8400300241c8030080c2141c007403d1200c95002c400842d0084560800807807019880d03204d0882e500102c00f5554603a035060340085e06031003070710318900c20b07080300828121504115400000e426501c100c44048440112031046290400c00078409981d09000c040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 552590485 1250 552589235 552589241
    0x52409010c2a09090507140303040314010c12090506070c081917010f080318060d06120b0a0c0c02060706110f0301240504030f020f040203010b0c01050a0c200a0501 72
    0x210054001c03194400b1003280307031180d840c0080180342503402481102d50a4a500d03844070000d1041c0d8107107100c0b400c4004141d46050003550019a04490300c032004c0d0701a130107640c0c0604094003400c0c0004034012134000d4268400c0c410300e101650400020442560345407030590b9503c01441d000c0d103c2030f0091008140104412366103080d45015503840d5040e104030105048403002c4182c001098904400e042030000d00c60000a03203c00c021110601c6507030280f0040032580d10f100b244440003c6a06000300070901400c0100b4040f800c7e44543c403070035110b0f03890a28400482d154510b440d8001450307500540054940103000e400c0c414054080010304282001d0849503d500094220082410220040055031a010100040205100d0003801101100b00c4010a04d00c620b00000305110114110320042d511080080e401000700a0320440d52540c650101e03190580141890010b250300707280008030841d565000d80c00203800c068541c000030041c090b406d04661454510550000c0c842d08000c9408a40240 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 552591735 1250 552590485 552590513
    0x1806140a0537090204050a09052404290a02090f0910060302091915020615030303041202010213170d02030715020306030f03270102031c02161515052409010c 69
    0x70000882080601e0000d042039001c3c20688945001c02a12b60751002031013002aa000758801c2e410244d6145d5121278142103400c0390740c1c40d100000044200b03c41d0300f013181e00408603d0340c121500c800c0c502c4000c0c100003100a081726034001d020a24541000480e002c0c0d000b50003074020042a008100e503020007000750b400025070000300740441012141c160300390103000c120303004010104244210072001000c20749d01e2101401c0204a80320848143c04414400c0d81900c081d0180b41d04c0b029110f030360310002b01841c0c1d40d070b100ca2505a401150030301407084c0d00000441c0c80f05540300842e103043d2906916808000d40005207184d405004000042ca4504c200340003d1a21580381d2001404c5440700407040880c5072115500941076500030072144030300518050386001100003000016981d010707031021441c00d00b440700741c0c003d0410307200300885502c16030142c020418a2013400c4030400320987c2d40c01004200e0f5107000c050711400141c3c07a02da0229141c2d07040280000081030410720306001c21075441a21480480d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 552592985 1250 552591735 552591751
    0x5150d20040b03010e0c2806050307030603061a010f0f0909112b0b010504180f0b0312120705071212060f0b0307030b06090a0501031806140a053709020405 68
    0x112a80c51170300701f075500141c0c07d030b1201200361900c200c0a4000b01d0345407400f801c4103200d80072001885152194020001442c2d0000c1c0901c0f045204d20101141402c0c010446400304031041d41d40207100c1e00c981102c03902d00c1c030a991885c0a45203003092140042a001c4004204600c0820600000801050720515001d4140c0d5980e0181200b020301c140440d460010311604122041001700600a0101c007607034407140d4458400547e038000482880000c00e149200740f600341c0594080c0d202030400c10800391400e94100d40c54090305588491040307905d07116201c0020401c4000070340860040b8424404804911100000000c2d840d4407102000d00c041500d034402c094805000041110340c40d85030080100b006400e550345800d00920000182180403103006803070405503941001200400c3e65484040440d8000000708007004030462840640b41080310172445003070800000c03400d9500600c03414080c1d00480800c10801c038171404041c401c00140100b8000000d0303203c1e2141d202590303841c4102400b40d442 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 552594235 1250 552592985 552592993
    0xa020d0306050307030f1b05101214040c0b0a02030c06010b07020103141b0d02040b0a020105010302030618150c0712020106051801050310240905150d20040b03010e 72
    0x15610000c0558440b42c00c1103000e074111520800c0002c030038408200216910144840035600c01441240da0603c1c03540c403042d440400075444140071508004907441c814905c850601036241640300d001d2a14206480003811030341c03400c1040001c046000c0c058141c4103803601c107070f81c1f6100400c00c00c94138040c0281c0000c01044000500d14046603058400d510420130b2100900d40c0c9803416100d1100203144101b00680a5180021502e02c04845039040f50041c240083e034040d11a58460300c024000c000900040707000348100030114090800d01146111000d282c2e01c010848840c0070780d15a80001400342161080d80c40c1401040d0025032401d841c02031030741031940001030300c62901c0104145a4004002e580b09401124014001c0303072001f24229222045a83c80483c002000b007040000450502d4454020010500d8011a00040580210380142c40703d001c0d40c1600d10f50381c803c203c000301d1400001485280a41d40030304802155907108440203000800003e450b11260000c0307829144010035008203a04 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 552595485 1250 552594235 552594253
    0x303120108060f01080f0705131404140c010503090c210d021006050f0a14010c141b040b0f10090503011e110f07060522030e10052b0f020a02 62
    0x1051083c024010080b8400600c030b11a010489992603017240d01940e40180c1d1059050b0400e1031080d007100c0b801e40c0101009100600d8541051325103201d44401800090040d01d14811710b5600c00e80c2540c2c0604c1d5290060100b2880200402c00b00c2280340340d40542c1c110184030844a180ca090100700c0a1000b5030700a040e07071040320003401e1700711200398010900c945108544540c7ea42c4654096000b82c650190843c5000265030006031244e2010040c010310259035030014660034038011880352010408600901e8048005604100668010040796034105489400051261802c132490701400c4449060090f40c032525000400e00303503101c200d08903092550004106840380385911910300540d01d40d544040c00d10800c00c03240c401c0b51195110150203242c031800803810350701c003a48510584024101000c81c5021062034007905040c1c003558014820300080c200b1f44401030240045520f48103080d03c15030000303081c004840c11145902180900380e00c2d40c500ca54090342e0b50ba03200601010419400410002c4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 552596735 1250 552595485 552595501
    0x15040305190908031608040803030405031207030501061e120e030703090f030302120a1404170c0d0209070f020c090906040b18030d0b0d211b0506070e030312010806 72
    0x1048200d00070410084800400c08000c0210568110070310080040003d031000d0f00b0160490b02070390f0071540301d07400000240000c2000000050100405420031f1600607503071031106808132642449400c012900020f481c40c09002d001810314100315041c01c151581a0b5a0b0103428121101e07070f5400c00050784001000d07420302d500305030480e0080800c610f20b0700215040d590020b49501c89080f10040c2d60802203001d0300240e00410440c0c504070312800c10107448a42e1107c40300a042c0f4000c03a0031130701e8003c08402a0311400c16141c050304107900a000f030351580d220118200d5894040c10000f02c110f000747c01c0303681810303a50500c42034000e0200000a06807030500707041100e0403807005446045c1c104802580ba00000f0070110a641c800101002d00080c00ca10a1020038100c03a68028020207001d01d4115404000c1c107860302282ea12881c81d900c61281b10030301d40800121b0340c00e801000d0400d90156000400b002c0c40340240401500703010b81500e0500c0380003104180000ca080c2c02461031600f000d002c00080e4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 552597985 1250 552596735 552596767
    0x6030c050a0e06031216050a030315080109020120011503080a0912030e01030b27090d0c02030601030605060402090603010b030a0c0f200717010203041a010e01060e0315040305 77
    0x150020309021442c90070204000381d80c1c0d101034204582e5084000c64866011081469a0310034a074001c0141d4410000e54034000b402804841620308451042c2d04001c03d15800511502c01e100b94180c42e0030082c17004d500c1508038440440000841d1701d640700c0340000d502c0e902908074040154491507250707443d8280a603014180e239480c3d8001d1200c043c0003034048800700c0d9015107001844d44081c00c00241d85159030021811100d822020491a086102840d1031140c1400e0560f40c0b00d000310703200352000b011060300c0c02c45094031b82c003801070b5041d1700c1140180f01003009540b209412440040c0014a0f0543c020007190312600242e121040c1c0b50070100c100302001c00c95001c6c8031003009403403074015507020044001a0010180740c0442908280160003900301c0401002443c020f8160304045000350b42e0355500440c080d600488046592900c1d003503440c9003070524070f1003881c182d5800560079a0103070300342502141c000355440c0006a05106850205148154240e91240628000d82d82d090b034552070b841900794a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 552599235 1250 552597985 552597989
    0x12050715030506010503241503070201140601020706030e030702030a0807030311030f0106050a030f0213050109290a0c0803010609030204180b1909020301140f0a0e1c030f06030c050a 80
    0x50500301400c000d1245e9110044991218405550b00c038200c1044418140034a03805006581000122820503103800d1040065031040149a000384548401d030450904112002d6500e80c4c0507030f001440a02005010340c100b61009a09401168100b0890390002480c0c6040618141c1e05a4000126078007415414002e00c41e601e0741021503a85103050210303094114480500c100c008020021884407082407081e0032006184650318015929144100580400b01420b88100c40c08a101a50300080c0400070122056410704910760286106613080d82d0498194040745a40e02080100a10703e000036207070401440c06401c4a80d00e00c0c901900b0740c418001180c000398003412420b210b00d40d40d0000552540042c84e0701078072005291000c84500c108800180000c802d001b9495402c1442041f411200d40e417240b485200001210328040e1904a44a412241421800b140f503800440c0441241c1c40c000c20581100302882c03400241075048034403100c0484556400480f141d25000c081007203149061000707100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 552600485 1250 552599235 552599237
    0x70308010909080412030c060e101404080d110c0303010609060909020c06061c06050c030402040507091d0c04030803160e031204120f0507030807060c0305060d170412050715 76
    0x2220900544403404140100d2045d0016801c119480b1010103216281012071b2aa000c2c07018401d407030001c0ca5141e11500c80c0412021124945015031143c020003590740303409070390401080e61801c284211034002500942c00c00b8042a90300f041000d45240c000c00c0218002c002e83c0d07464100d91801d103040188482450380c41b60040720b0041c0101c20302e0a00214880317804c02da08135072220065041c00c0302096680320322900030b841240b5083c01c000c00340020100852240780f080f00d0420040e50b80b171100303403554041401894200c561041312085503214402e801500100b0b101c00700c50400303513a56180b54040c3d000702c900900001c15001041030541d08428603140c006c000324081e18005842e40c60207401d60240d40300703080000d594a1f00c00014844501c9980c0744042e0040151b480054807418050b1040d4007805c003c94140c1c0c609140301c403004c2e100744190b83c060314008141070804503898980c0d03181c03801c00e600c1740c2c508113000700000a41420104c1240c0c1c18148114050a0707032901d002003000051600c820764134 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 552601735 1250 552600485 552600491
    0x9030111030123010e060d020c07060c0c06030908070204020328110913020d0e060f0a060609060e01120612051605061608121e090109030e042a050703080109 69
    0x200c504540e60718401180c442c050011102800850b004880003170110501613007001d40021038085103803c0390010411401e0030f004a4070b23199500e181c11202000840c0000e400403681c2c40d0280b1606100f030304242034143c01911018240a215000103040780e1050b20703406d20554200440801c00681b62032008802a0680e404200342c1080c4482c03102e0300c2c070480503440d10664082c50b40d40440801d681c1500d180100c203000c1000341190b42c2244995442064580150443c2c1c14400500b104246001c0c04040d2043d542c1d4203a0350a19001d0160340000703152003424180309090b285034035403c10911030000100342a585c05200c042240c1040f0341081c84202e094240c1c00c0b442c150500884e12800c0440e100c80340782c0b8001e01ca40103541e040600c038502a080c0464031400c0144144500601069101480003c204503111419110b1403038503400c03a00184401004560740400031055071a1607403000f4801080401d800e0b0390741440310f00c1d2480034240c691401012540216400781459480001203000d810340403410 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 552602985 1250 552601735 552601739
    0x6090a1e080c03031813091e0b180d0e0d080d06050a14010e0609040b1201021c09052503120917011a040b03010b0301021b060f130b220f02040b06070f0b04170708090301110301 77
    0x10740d00d4003402c450b41801c2c031500c3c4480c4800c80c0c44000200b0b0200b41c201c0ec045468504020302000989a940714030703403040c00380300030200b83c85094010610306144161500c140168000041c403105810910709140c3c0f0591b2604012456154040c20010b03140710745000680e80c0311140e00c107d210041d28411604a070b403815800d10001400090b080310105a1140c5146402c4128181e00c0400b20b100d4000074a00414010442010764100601c0c00c1600e034582039143c4c91140e464040740c00c032141d244111414443d41c88403200c1c207080c0340d0311064181074060300200344200d06c0d0700400c0c01c0e640209402c02034405100002c104d030810901c0b55503004010441000d24030b044c482000c2e402094071060140c41285240081195072a42024001d600d40003070000004030714031803c200424280506c1c05074000d606100c286911480c0031411505200e0b403140d0380c0440d08006489413903c1e020010011110802d0a2050220859500000d0003800c0e104050907a680d019040916082d00e441c00c1c54072402030414001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 552604235 1250 552602985 552603031
    0x6051f030213270308060a050427230a020901090903020a12031d0f0706051905090307050303030f180a0f0206090a1e080c03031813091e0b 61
    0x45503207200400008100800c15880020480d800000e080a400d400d8090b00c0c2e04154200540328420f5078101c8850007c6603a40c03081c001917032540211080e0800b120922210400444200400003600540d80381d5901d60301e618a0024408160141c0c000c554402502001140f400e0002c0c84e0241400d02c000380a100d03e2a43c004c0d6642601000050840052118050050b486076001200320980351140c20100c0044062090701c0d1003130a1410813840c02640800700b82240628125061800c241d29001d0f807088000d82c00300c0342034001c00021036250241c24000540b80c1d41c100080c500410310b01d0004901410400d000c880c90003100111144e03a40c200c02640c4010440d101d200300350403501a1220340c1d4800b54030b0009004250180c1101c480e00e0340f440024007480c0e10b9504070f0b50565003818100d4000032085010155280101d1450303150b01c6003000002042414410800d901d40302840d5408684e90420b5540d80e00000e60100303041500c151010b8070b80c8103007c64540583e8001640c503ea034030700701140040b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 552605485 1250 552604235 552604249
    0x1008060a200708160602070218090d0c05031b070f06021606270303050306120a1e08040801020408030a0f051806132111064306051f0302 60
    0x107200340d5210021034198280040340c1c0031144141e04520081c1c0c0400c1c3c2c1858918000c0d08205002d034000c175841d00801121055990906006020020041112080a1508540344102d04800302c409003c1031149030764251000b01c01c100c507610740c0030190140310b0801075200480c0a09501403003c561214100907001e80d51103c102090f58580e180054170141404036880411482c4685008400020318000043c55440b10180d03004150840c2c141010449680000741c0d00c83c180301c001303814028407000078180f111520601c90503041c80746024031b04083d0f0700d2040c00e0881c0c00c40d920103826508001020411164820f04449940c200b5091103824075204c41c261082c281010200c3c1402800000703081003900c150b007903420340109010032564504060b000003800d0000c0700c840c811219210304001c00f440c54900081600d6442d528603034032508860500a83c10121010307420000018002000900c0344144010301800b50203008080116540c00c0c8103084070400080c0860b10700040e40308010620060351664 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 552606735 1250 552605485 552605531
    0x1115010603020a092106200d0f2901090b03150f12100f050106020106050d1e210206060102030405030a0605042a08061f23091008060a 59
    0x101e801600c3c0d040340f81c1c00b62002c0d080c6802003900c078201461440540407100c4400d0b00c80f9841800309114100030000c02c024000c5074802d6200b0012000d2180c183d5095066100e800c400498200216040d041c041072642c1b504c02030701d0502800245030544000c596003104050f0001c1c0300d4800013031724600c0e052041140c2121a00040e038400c09131039105c1504c540d80c186801041002200030790715031101040182d07000709003150b11600a14148400016618010310030b420840c0c1c0f000d4810b4551030703081e50341c0d00520300c103c1d4518841d043c0f2142034007012800085902090040c9000d220076032860a810180c54940000c000b581194410807050100341c5000c94586280e6a001c01701180b41c1d221803402c115040c03501a048200d411518100a034128415040041155240d2054402c0c2d6190484003032100000d008400780c0070007840d1b8080041d1002002c02c2061008451400c00a0340d84410005200d04416150502d0060300c9000074803040c2c00902099401103140e410402c1400303103040720070b000000f01c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 552607985 1250 552606735 552606737
    0x30b0103030e04060f0801020406030609090b0f2a0a0e0306040c350102130b03012304090f150c05162a030f030305011e1505071b050111150106 63
    0x1c02c19004240c0c84642001025000302c03c1400c000e151aa8070a50003500284100c200003800c00100080c0100f41d0300c910045070782c00c54403219042d61030350050914400d01410211800042a01c04c07120201c400741c140041807400a45644e9441590100404440d4011403580c0319820070303428407000403020607255085582e82015001c076540800104001c6420850703038114541111001c0c1510800d040d13005140d816143c80521403026121444c6281ca400240070311400c0300302100c4646841c81c0b1100400f40700f0140280003042c00e920f07a680300f00c80c40e920079400f10b808520985c2031409003076140c050104130314040d01d019820856071180643c9220300c0990060310102e6020101031341d86034138001100d041c12250039042e0380c4503a2440c000030600c1350345500b17a0000785000d001003404504c030500c00090039000200381c0865400c100812006a2074140b0701000c0c0507040005500017288900300700603000040d08400049490b007c000b400038941c1503c15152504032640030b1904c039070b9051220307042d5040303 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 552609235 1250 552607985 552607997
    0x60f0806071205071b0b0403020724030f062102090c071707110603040803013312020d150e0f070c0332090a170316080405120706110601030b010303 65
    0x40c10419145c2851101c1010030151803000018244801981301d180940e02c02d43c01c44071181d680d81541c901d00090505c034110544801c50b013090301079100e40c102c2c4800642d926130010b0501e03036071581c005000368102200c031000d041c00c60300750303082d89083c20100360b009010200e4503245c60440e95a0006800105c1020000e0030400f10b445000e0281807614280740c00d1000d032040707030f4a0800c1d042031f41054100f40b158a65041c5114500b5150b049440b2071a0b41981d80c0c0d1640c0d501141080909590750740f080700d0321814281c5d00340a41c0e5024002350150384000b5140641d00381d0024181051416020001400d00d403203c0701e070b041440700340d0b40d0003a001900e560b054502070890501e541103440984801c403005000c0080311240c01e4154480c0c542c01010101400c5411500a41c3d444102076000d180d10f03951102d8070b03002030142030340d180c01541500303170704a101b01e502030b02d45a00c440000c0c504034400300545a280c0d0080805000d1940c00035188012500d049005201c69031469031110445641404001c0401038 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 552610485 1250 552609235 552609241
    0x1060507022e031a0102191a070c0c06030c091712040f0f0f120b0c09091509070c0b071809060801021309060302060a0f020309040e011b1112030414060109060f0806071205 75
    0x504000611404118423410520700d05083d080108140a5603c1c1503030380c50101180010114002d214801000d01e09442d04c5100318902080201c1440c862500907519000d0020f070358007511203c50040000e450781c0a40015064180040213030031012070b40005105c0300801b00280140d050341012003032025440500c0f00c0a80d5104020310215000d02c0340c00540014040d001c0c0030f882d8501c2c6804640004058a0301043c6a603000c00c1207031484500d00000e00708034040d078045405207200c0c40030107801144400d0280c04403580c86040d202200c4140c1e00c08031041c2d5021942c420140c0b02c1940d0740d001031640300c3c0103220ac141075400080a80c80307a01681030a12a180c0d004521050081c0282c40d1032840c000d204110b1080c04494aa010f0300135601d01003003500c036208400c40614003801c035116028140400419012083c40001c01e034070741c0040c1c001e8415480c1c2d030301031a50000c410000f03680a020300500200700c01e40b03002002410102e0b10381224029030002010400f0b019401003500d5182c00c2d2080002c5100d032 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 552611735 1250 552610485 552610493
    0xf0a08070309031b0302120a0f0b100b030903070b0105240913140108060711070e060307050a1d1302010503190204090603080408150f01060507022e031a010219 70
    0x80701ca0b40024038081d10b1840e084900301c13003600d02208490003511503405100c002c030500d503110003001100030184440e2a4015001c507a28000940e8004451031004615585842c81884c0c0340e0001c0380c40c030039503600002c1e00c1010492403009150050205890000040800c00328000070a40c54100307080c1404c80200702690a030380c0342c0b13145c041803c090200030400174002c0340c900b07907100b1024003403150786200703800c0400c59803403140c81c000d41c440f6160405031041c1400d04000b0f0f8183c641c0904203642c54480c5040220344e070365801101a00400310740902d00b000c11641d07000007000110060058004032005008840943d03001400c40384c2c0300b14030301c1a241680a29040303410081c0519000507011070300d040c80100806c022000108162680c040864011010140250310310080c1194080390540602c0c00400145009401801031913200410402c08070804c14420140c2d00205003403071612080840606030615058410001115408160100c41400b020000b0b503403128841228103104084581c000300f40 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 552612985 1250 552611735 552611747
    0xb07030306091e1a1c0c05090f0f06031c12060b040b0a02011a0a1502100507030c2c0d05032809080c101d12030309010e0f0a080703 58
    0x190400d14030801c40d82182c0e880440303070a070070303007042c1c011143c901490480c0100c0c14018066180400801078910342d0078042e01c0c0401c0b120317241030885811071180340220b560351718407070024444c42e00d43c0350905552030044590031000101901e2113000781c0141500011080340040d1b1095007c2c40c0d810221110125408003c00030301c1c85d03a20560420000ac90b000c1202e2030042c00074a4050401d41c006c3c0b0182040c881c0981801c01d216020903804040000b0800c04040500005501705983c0c1c01aa4260708454200341d0946404807025030010307540300511000c854114010411000f800350401c028003c000030481500701d110382405110794521000c00382001000c00171100c07075410380c610400d070b1003162032741d0b80003178050b1078507140c01081420704081600040040d0100080c20000e040369100c3c09502c400341e8030300e100300000301104034407004610707283d07115034036424602000f204c002d41e900d10306042200d01711102c0180c8062150414a00c414505100040e284500c1d40c001c1c5030903660f04054074003604d507 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 552614235 1250 552612985 552612989
    0x80c1602011b0303020d06050603190917040f090e010902090123030a08031b0a05190302090409050d140a020c060901030905070906030302010c0503010303020607140904140a1503020a0b07030306 85
    0x210103602c00c0041016419009000362126000c001c0c00215140c10400c5420b0004413441e8144c10001d0100c00d10210b200c0c0c20025425002d1108104401101d85c02c0a1003588143c124026846c8900400c02c4429024850030004800030002040390b050a540001c8026406200d94200d82d4049800c00481e2000300c1e200d8001c0480050072039a0710401071516058907001201d040c103150740c05144008006807603a04690704c0c000c140d61600d14104d80303e41d6201032900e1113000f01c0e08165003440640b042d44c449108001c00b09001c1c9009040c42c411400000300700c4002d02500c08a1180103000c1003264640010f44441080d000f11140707a04d0b680041c00403401804400c0002d002441155000200101d8079444072081d640603900070700c02e28280715400e881500c403e10000b0300503031162001a40b4284210720401c40201c1205200c1c1c030f4120351000003419139900300b100207140403070b0400344100300300c480c841c080381e00d56852000b2082c0d0b842c40c0c001a031104402e00c5007440e0506c00140040815100e40e02100c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 552615485 1250 552614235 552614267
    0x4020d020111030c06010510110a031409100206330d051005040b010f06050f1b0f0f0106050a0504060b031306090203150415050906010510140307050910080c160201 72
    0x207101c2040c4c403030260b600c02c001e01c02e00b0f02420384000d1070598a44128241400402900010f005900d0340359012100381c041070725030210900040c0f244961a650760260040c0300c4c259030303008240908040c03803280c4c0789402644032480349420fa00c4000b030040c42d503608078072200d03c0111080d010028250500506010f41e0700c400c640c0c2c05203403504200070003020300010740c16507000401040307034161269000e84180c850002c0e980d080c080c05106100d05c0131a20b00494501d0510311041d16034051804a40300d01d8000d091691103410b9448a1043c8020700b406a880801018221002c1c84400e20707054046405200c0900301d0b40c00700700d4451507902404045c0e0007603e80340e0b0b0f010f4121441c92191040b807611a202c2610100c801000c0e60114130f40302d03020b03401480c0c0280600c6024199a920341f008000200c69800c0e0b625091000032042e030b040e0340341d207403028610465080e120300d6995040d01e0100701c03c681100b00050148485d060a10840348501810358140c42e0084000d00a240414001a03a00e0440c0c10a105 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 552616735 1250 552615485 552615487
    0x30507061e0c0c1a04051207030c0b0306060301270e0706020f01060b0d0b12100c0e01051801111614150c030a030504080d050a0c0e100c12050906032802030103030804020d02011103 79
    0x2003001c107c002102e10860703008400140d8403d0725801800351910060f102e040d407050003030006200c1840002426488407556500d80f1000f04014403410043d6132418490038131682000c8020048181c040c030102007000e40b0500200040c03400c1c035080d400301340071301010112015074a21409406445040420307844142e10f008555a03651400a10000340c124440d0200000e5000c1086c2c0d800d80d4003650a452174440c010486000d0030507008011508204001102c0400b0320440d001000072111080f55200580008104254440700090078807407800d10460400641da039003005603100031700e004400e490030403899203008221522503007446940c074050446c08680c03880c9024140610070b00c466225079020317021034441d14031000c0b40d4000c1103204a400421000460343c002c0107540007a24004000d03642c02d8660900324103182108001c00c0c1d1a80080301c2c14100100520490100a00c03015100c040340b80581405519541c11030358018010200604001e01520354400c030141168081c80c100f00c40c54101004032 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 552617985 1250 552616735 552616759
    0x607060b03120f12061908060405150c040b09042703030e0303150105031f03030c05011a061c09020312090901082107050106030507061e0c0c1a0405 65
    0x26001444a0264544240300b0007401c0c081400d074600c2030703402018400b2007442c100709000e009580d8030040104550b0380441c110700c90a140713000381e0388841d0140844000800c0c05250600d0030914042c038800144482c82000700801035030741c000030111000d5407400c05003103403103010305004600a0003807442d443c4132000303010a254800780c3c09603030200611802594144000c654074002d0340d07100d200c191184124182203028115082d40943d0056411503102c4031004485540329502c8054071800f07400440c0003e021301d5a2806202c0c0034044e0900004400010421025403680004c40c107101d40c0c0d45180d5003c1c003e83c065011409241c0c046950140c018050f00e003640e003030809503070711640504402c03440b648000b0004607000c440010b0300c41c040c0003184031103900c2d12041d25030030483d80c111072400c9956640b00e83c00030001480a0094400520349911103200c0c840025811a0701c110b0103410300810400c04170804c50104074440c20300c5d01129820f251100040c520081c0f031589900c1907030002ca0300a041c0440c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 552619235 1250 552617985 552617993
    0x306050702010510030206040504021c060923010821211906050a0302010302070507090f020910031803050a140f12010503060f0c13091401050406140d140a020607 71
    0x8480e10540040d80200250f0f51820340c008140d805038040070f50444030520052002e42015030042014503035034088032000c100041d004406464081d00840300454071040088140d400d01a107682c5010142d10700300720341e0340c10212240d5607a140c20403c001601d40d1196031107501c8101b50116490490040252600303010303c1c42804a501e9020f440c842442440350b0242d00a24203140b045030706540b001000540280c0c039580044010790840381d03080d20580500c0c034001500d842d01c2c1c0f207081c00b00403401801507161002401082460400c1c60458001e25007071100c8503560402c41c4104c008070690604041d9180d48000760300b20768131301030200118075040e4005905580d221100e009050240c244c041102c140da80c903041030544800d020350b44c1001001a0704040384100400202502c030000c4001c0b40954a0380d90b0f14141d030260340507009446802c4542c0720050200c1d0501e8000c11010303210f00b0840c06540025400480d4120b4134004003c0e1003045582c800310a81c4400b40245800250014203184d201c82850034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 552620485 1250 552619235 552619241
    0xf070507230a0b034c0506040303080112110d0f02090c0702090604090624030c1a042c070314220201080603010b060f0a03060f0605040312030b12011a060c0d0f1403010306 75
    0x541d080011070805e10020702407400d0b100310360070340c0da165070b42c00103d900c0d158039031144410840c1d04aa0307050494001007560348075030380d2401540b4040c06450090900e180184907160501500c1400001e00420200c805a00c4400d0303195046401074030001102e040d5801c011005180c1c030412048000f41c52002c903030480406a80742016280155190044d290303848460740061030350420030300d0303c101c0203100800074041c26a81105040c1c04090703220b112580b002c0340d0400603102c1199207501003540c2e82d040b001185030300c103130340c9a0013414606416003a1852002800711001808002410032034020002800da4a083d00540c00b0b2a00c050209034031401850502203a90304a903890400203860b228001070340c0b0000c04059001c4601c00d072102c0d0702d800c2c21600d0b030804c500314145400f1f0925403139209081581d00e900c1c1d6181e265002d03103000003822400c1c2c400828940d41c181e02c109489001d00340495405100089040c0009800342e052641f5080e482c07107000e80352500118801e0031b0303011012000209010542d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 552621735 1250 552620485 552620611
    0x909070306050c0408060103030c03030e010510080d0c110d0f0c08011b030501030c0e0a1e02040603240b0a091a1222080f070507230a0b03 61
    0x80420b0096684080e06041c50303004610a0200d694490401000468002c1c1281c100c418002d1070003140f04405040f21600f55041030340d030709456451611003000341c0d2074140316039000c030401440e1138410312200391a00e030020000000d9203441019000800f1081000007038a4001d52688000c080300110f50b02c00c2828001c0c4502100041403000d020000d40c0380398400d10505050369032040414010600f8502440c020450003030200802c5590f5046001c0d110704000840307802920040c2000d80e46505146006099408040d14107002c0400b092942450100c2130390384605440140c52580d8480140c0320040301c0107a101d0340244818148034403c000d0b40da1703041c00140501805100c40551035200c45c2c8440b8003981c075000c0507044038203043d0104800284128000c1825212104045041c103550ba243c8600b0900b050b800000d001010003c0035482c2d0000c920030015060003100c48a01d51883e20340300c030035a4400109106e081c03100d1104400a0070100700d41c4940b0200c0c0c819150451042405400f423100c0b0100c0b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 552622985 1250 552621735 552621743
    0x60909090312010e070f0e010507050a1b0b04180f231609080a032f1f0b060f1c060e0601090816051c050105070503010609080c0607031d09090703 64
    0x80c0b0008220b829482007140d00a01440c0d440d505440d034001070841ea0240f42e0303031701181009020840d80700451030802c420b00c4450b00859032840301c2c030380c03c0380054208000750340205800d8030180000c00405008000c4103e00c0d5400a00100f8805039200b480c030b00800800916070300021041506501c60138107440824480c03654010321b5000621440c90603a604003651140c0710542c1d104609210000f03200d004a0300d40c400007083c80f0602000c004140801002020111004941c40b07080c410f81c100700384c080090203646120804200c0061018041407861180360516100c0140000d41d6040b000301c506007180c0c258604807020015942c0742d074400b1081c036009441042c00100c041038007080050f008103050b04a21003401003c2407403850182071156850716600f4251003900d88203108030124a00307024a40c0b01345000d0f40c4555680d814048050254161604009a19071001804c03c2c000c0d250301d4111075905415060801100d40a0340c2c20b00040055503035116044000030b02402080100091f9039010703640b10b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 552624235 1250 552622985 552623017
    0x2107060f020f030c0c0a0503030c0a0e1504030b0403120f090308090111220509151206010f0e09030910020601080c01050c0d11030f0307091701090309060e0609090903 73
    0x40d80c40000c0e40195820b84003140303020004940300e140c0f04070007480010058015145400c03102d894403811500226105200c00500081c881800d55008090903144c403000c41d09194150550340d002c0b1610b00650000802e484280004a42454002e00902d00d00550300c03801400146d64810340070002e0b001d420b00440c041008040414a901c2c810302951500643c2840380609040618110301d02c00003e0003809032107180400800318281c2c988541c06403185c038884070710844001440c014004150760090b10503407560030076001072140c04d000c0c50f0740f40119000c1d002108400d0729444003260a501c91020503a6119802d440000040c1ba000b042c1c41e4104c7d81300d8402e44000180810040d141413090741c0d00c0c148a80c00480401da8204e0103103c3c140b2092031054100d900b01011040340401545c003d42e008404a5015a010480d10100342c10540c00c495112000307000100540d600504190103c0c0030300c5003407150441460303007580c4961082d9a006000100070140e6828560b4646449a010107410340c48003030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 552625485 1250 552624235 552624251
    0x1b07030201080708090d050d090b0c13120506161106100f06020727090f0b04020301050c2d0c030d02190306030c1e0308032e1412210706 60
    0x2006000d0713548103c0041001c1e00706526030300c10072141544803020003682185d5800c40c81c0003007a006540b10744544641030069503a503800341040301100f500e80e8800c0c03000b44000c0260754001403021034080d4200ba14400c0f01d004842c0070003000e48258032480c00120040c400c9404011610f44019194401c40b1151031410240c2c503106c030400c985074902130150000f00c083c1010100c02c964800d03203e005c1024175032000041c00d1001036680c0740c9034500e001e40036240b0714000030503c4158a0280308240e080040701d03040c2ca00c0d005035070b614508141804078898a4041c0405002d044400d8043c0480c2c60807000902540d58882c201d51030003009401181a4a82007400040c1410b4024004d110385410749070030408600c496440c042440001200d98480c82e03503107102e42c03070000002598070405540111070340107c3c88038440f0464207044509038030340c424404140300d0701402c001e0303e1800c18200c44d075a8000c0c3c031516810b8501c400e000c1d10f03211700c102e085810501070701c0500141d199203d02924216202c1c0b242488072403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 552626735 1250 552625485 552625487
    0x60e070810050108160c260403050601151403042a091104030305030c22090e15010f090b0609030a060605010f020a0308070c050a1a15030102040e04060209061b070302010807 76
    0x910111030300880b81e41c212007010078690240d8a4071040da03101f60500902070107141004c0030031102c80d0581502d0984d0200d410b00c1080000d00243c1e0250a00864198413080724200c0202046080d1503401103030000080032170107010300c1410b8654420714827a2040208103541254008140240c0f25400c1201d1810404518200340c5108941c205c80c0c240d503d90b030071516603c1d1203104503030000d4044403968400c24040306051488483d10801000c0c241000641a00014032050510314002000103005280c440148071015640d8010002da4200305400a000a40071000c9425031144140d0715916220f02505a030402450740c001401740d030820303640c222034682030314010307a51050840030060100b0000c1000602c160311404681c41010f00941c1101c002064540b18542d07400000c000700c0e100f0f1803823081001601c8030441900d001a5605074000c61501e0702d0006110f40e1110702501c010902d41d00060a625140c0d920070507101c14075005c40030b460750300b244440d1a81e170711881c13403008a0100d843c3d0b400041c046 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 552627985 1250 552626735 552626747
    0x30b01140d110f190b04060305010905091b030c061306020c01020d0804120c060c0315060c080405040f0b0603090a0b180d0c1407060305091203090d030906060e0708100501 75
    0xc550001d014422070500700c040000c10014400d00c0f5401c0000119440d980c00d2070000c24000602002d03184c0c55440303041043c001d0a6981c160010040142441c0600489090015095030401c0742c0e2107410560100400c002400c0c1450301055952000d808a05003089180c41e809200032900582c088a6000300701400580c2c82e0b5460003c48804103c09000240110746c122020500b4840c85140c00801c90260350381d00800c84044018401c00690396403040c05101e0801511040506118104400b20200720380e80c8880320300c603a028980c001ca0315070f00e010340c1112072500446512103005080c2c0303840c2d1410804c0c0c1640c4990b400c1c000c1d90141130ba10045284210a03071401c012600700b1001521102907030f004156003503005000100c40d501d4106448140c200d030144100383c0608860751340030481c1c0c14000c0001c1c0c070f0001c412002030030b144020028060440400111248000e004e828080303441507031401d04800500044e40b042040d11099400c010509621802c010701c01c1040a2079140305030b0325a4011244 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 552629235 1250 552627985 552628009
    0x91018060329031009140601320613080a0b0604051005010c020102120c0d090f080c1201090204020708091e06160f02120c01110d080112050f07030b0114 67
    0x32240b201106039030101241005502101d201400301c607a1985510f90520482d01e460f4000d0b01c85c0005240134652020f404e01c5002c0c0100620300704c030050119405041c92010050000030a444100d50505035110b032240c0059540d0042400b403804605540c601f015500c54100e0351045030301c140c0d05c00010f6054a4503200700b90142d02c14120740113860703041000541c0d00140d0824164154411000010321030306a000080c4403d1030780340301030607203650411800f0703002c0422134101c4550b80c01c0c2d014044c0505580002c1c005841d110443d03007a2088490107100700d0060440708800b0790401c1c0009007850500010200611808000f0b032406900090004504081140d41e61340701503010400b04002c12122400300000701800d4000ca06686075101d40d6800111644110704400d88660441040c0700f09a40c2c000c90161084283e20028200410711400700a18030001409081551a1088068000e100c4100040c0c484c1400716811200d0003507c0c0d00740600d14000920401c88050f0f2141c0000d0038070f00346001c513095 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 552630485 1250 552629235 552629261
    0x3061d04080405060f16140114060f10090807030602091005070302070b030714030112050f19080f0408030d0504170f04090207021903030e030d0e060a0804080910180603 74
    0x300b0507050400300a0386a00061038040781d030314180042d2001008105105024500c503000202d8450085920790342074899411100e4003502c804020081e05455000300300e00306280480d00c90300060052003041d02d0f108003941042e86a4031440c0d20220401a00d039005100880d02281d4076990301003510002c03a00c0c0c1c82000001001604112010407200240382c014603000300050901190710108004e200c56180c209911590300290011002014001d051100c641e01c08003210207801c0d5044082045800074017101c3c001003040900160b210b03001090f030002e641c040e002d0407090b03a540746c25103074052000e0031040c0d6040d128a240c1c1803000311890b11800c102c03070005001641c3e803810580b80c01c2990f4002d4009260603a0061101200039220a20441050010b07600ca600e40300101c40d86070050600d8000e03070304c4205007801810f6044030740c03698030380061390a06206d61521042c0c45d075851801070010b00501040d80c0e0420950b00c0d000042c160404440001281c0e10b03101c41500782d5680c0f80c00c0b02601c0008000c00c03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 552631735 1250 552630485 552630487
    0x120f06070e0a051305270c0a0e0f04080a03090f0f11040213180204030816150b13050402030106030209130302060c130605070c1206021c0e030f0c0c090703061d0408 72
    0x112180131107070490340d03100d00c1c08103a00207580154181c202d200c02e000308894000d03402510212501e841c0c903c0e096030240c22901e200604c42e2601140c05100c5000c05040607202c0c0e10302003484200c5601c240c00aa080f203500000f52020f4045601e040840c1c0c00c110801100c030400700e400c000483d401c1c617100740c5000e54100b40ca4058034900c0c00d09155a425484820702506c0c40d001c00000c8003248548000380704000c1d20100e540320440050038201e80345000c5803204482d9900b0509025403541e00c200980e51009030485000034181c6951000900408a69000070342100d045000c00000d0070745407848d500c08600940a5451076070320401c000059202d80012000b400181da032050041500c21006030002034440d61030316500d5501c9042a9401b4000050121078060f000101e44000111000380200d590080540900c6040c15a51505859004170410255040404140e071454104200504400d01da006040741059040a50004000d0100c41c01940480641982c1c40156680c00c0f440d034501c100d800410b46 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 552632985 1250 552631735 552631759
    0xb0102010e0d0309150c2003040b0301090f02070b0414160503060f1306050c07020f0d0b04060f0b060403060c030509120301150917010b030d14070b0402120f06070e0a05 74
    0x150f009140301c07001642c040440030a9003030085400e2251180c1c44180d51100402c00b140c0507030b050a102074000c41011290428841005060141400c2d241950210840400c00036640850709000740034040e000b8150000e071009200600c60312020010300200c002054aa0072156225034000c0c9040b10322509400d50700030b8000a900c1c0f00c1d4918140d812040a80401c0341400154035010260364041d030f60030144420000741c22007103141141c80c8214026003034410110f9040d00362503c101f4050001c102400c129101e02c0003008614542e0f1280548440c014215a150741d2a800c1000040003002c041070301007413410700810402000040c003001c4422805103c41d01c0c603800e046c5010481c80c100d24584061101408011502d01d88142d071450700040303001d0001441e51481c0082514000b803030195030052065030b65000324008410011212810b0700f000080303265403114030100d0301e824004031042d10b5901030030605002c1c205000c108640110420f650f9141d0000319241007200c180d80350710481c4d500034400c03804 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 552634235 1250 552632985 552632987
    0x6030f090102270f010c031b060e0111090405090a020a090209010516030507061b0c030c05190c1a122406040f0305061b040e090a150b040b0102010e0d 66
    0x4558449140000541011040c3c40c0849072220894601401c03060025500d034620308040c0364094404800b440c0010800c229030b14050a07441082e500f002003c1a10219103041c0110364104c0111107503808020800210704052703800785a081008003900c02c0d8146800716085200006041201680003807400850a1070400b91000075070180100318140042484160485404079080d9011103002c0d840d40da5540390b03289803500481341c01d200e80c1c50b00d03495a100244100e40d44403601c2e481c61a8141060041111a414480e15020403407000c015521181d00c403440400c99000c11840031103695040100680401108141541c058580d03000b892404610000b114003811500084105e40c406000a400000d180081034041e03000741c0110501a442030760402c1004010010a944210f403801d0242003002d22400d00701c031361311545c41100441020000840c4050106124902185a0081c404800240c400a51030007030714074020032920440c50204030441c0c950041c00fa500c3c0103a581800340c9203290207280 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 552635485 1250 552634235 552634261
    0x5030708060105190b0f0d29130603121e08010608061c210e09090c1203040806070f030b030102090a0513060506030c09030c011403070e040f02190206070306050603 72
    0x64040c0b000104050008030300340b80c4401031444403006d251070ba40e1002841803d000342ca58940355024003002045600c00480007181d690001c0301004c644115100c0088800c00001d02210340016220654101c12001c6e4141c000d10070030010130341117680030001001d00c0c0040d560303200b09102c1d110210704440300080706881d12030b8100c120035034034041d0042c004205494000c4e196044d06040e050490040c285c120005401c55500300c400d031000c0315114014501955904c8c0c8034201400c1c9203010f240c4560100c09802c13402d00640f40600340140499031640340220004111105544503040441d141000ea00d05034101030003260740b040f1020b003414021515000070301c43c0390b1500100100b08bc580d520b030081520b41e1224011401840421005c503264901802054200401c84200c281405142514148401c1c3c44a040e80d40c40501d5050031400030140d000460081e00b20b8a65100e1554400202e040000d0342100f004142d02c4003580c02c4448668407118240c0c103d0700c09001d111340c4294103000007440141c100b0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 552636735 1250 552635485 552635509
    0x7030b071412130311010c0203120621070302010f03020906031501020f03071a0907031505150a0b031005040509030d0905160f061b02012c0a060e040605030708060105 73
    0x80d95140c60a500d0400b26005420150703201019041901900e82c181980302030b51030b4618080c500200b0450f501004060b580c1d2181d0011100c018000c3c03000202a0359801c812181c900300820f6003e448900112002d9894620304d0100b240840c05551400510070312034070a41e0710490001d00120301d035844441048500c96001c81200b4118458800034103410b8100313001615405101c0d403030003054510ba0348002c404100c001081c2c2e503070682c400e080800c08a000c02042104562007884005101e03207804a00803400780611740d0454211070034050014a05c01c40d100203600c0307081c10101c00b0ba038058903101040300b914802d80700302160364801e2040c048295165403203107a00c980310388111054401686024660303c8440e42c41b01c3c070746644c0e0300003c01005400014507004403040b40ca19a07502d490070350002c1d114000d1410b140c0006400100b000d04800d1008809105500b4000c0081804607901d400007801230b900380e25018060b60901c0d00000321810002919001d44940a01502c1d0030b03170030300081c444601210 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 552637985 1250 552636735 552636767
    0x91113030b13170d0b03030a02060c07050304080a0b180c0321120a060608070203030c0d02031e0a0609060e092806060b120123120c030712050c0307030b07 68
    0x200b9a440c0003404440390301048101d2480c41e80d464030000e40e0040d04694402074a540aa0000c01c00c0c2281564003207990340d0310401000030149c94480604041c3e2070b6014a81006003644a1410300d0400d00185c04800c520035291040320a13014079201f402c864441d100200c0d0305806610441d00040322100a0284499105031a0106400d21201e040200388018082d9030140030190745103810711485902107100741c2d221f041400218514202a44103501a215114451f000c40381c0c0031000c50300c0c00e20348030b5052150300c00104016038182442000440149024818030158500e04600082c4a443c002d17041c9203d2500f070000780c0a0f0440e0002c60344284110005d042c210040d00c82c424130b00040b00da215030300242c104040c4c00c030740f600d0b4040f141d850328210680140b203d030902189109400314a5280c2c52249400507213910035110210702d9543c1c901341c07600d9a500d605000ea0314021400690340801d1000c158041c02c100ea100006403000d054945009000150844c00701c01c0008010b00c0c01220807904045d12 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 552639235 1250 552637985 552638011
    0x1c0201090308090103092907170406111207080a0e0a050309040513020a0303021c090b09010c030320090405150108010306091a0723090a0306092a091113030b 69
    0x1c0c5030f80b45124203100c00c06016080d50b40f80d0340107d41c9061807055030340c042140e061a41b042c49121618141d02200108003c0142d516607015140c0d1700718100a9641d804921513486a550400c500c0140c0401000c0320403141c550314102d0b40341c615600004071540402d4004016514003140a0706101c06841f00508070003085c1806164540182c80d000c7d2050025402540030702003485802e2078007400c149a041c0c0b030001300729050b4010701800c9428011543c1042003405e240c2c0070380c0e105160a0707025050200c011031070348a0784040000030040c248020884068111001c014070340d2401841050000c815100d1400103048500610004501e6030107460103502a8080c3c10800d44056a0708a06980480e240b00006003420b4524100e180f80380c011051031583c0358000e40c144515100031400c141c41c04d2001410720350300c60072102c060080c4461402d52a0492034204102785104036a00c404005035071062480c1c5924050020050120680a82c0d600e00c00c41140000c2e091724607100c044a00001078070414004034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 552640485 1250 552639235 552639251
    0x24030606090d1506082b020c090106020a141501050909150406060302042d0b061b06040312110a08040501020d062301080114010f200105061c0201090308090103 70
    0x2444444964140d8840c0b10040c11043d002403204041e601c25521070030041d0301c6541114640d200c0c507a042c0340050043c0503000c940186603c012072070320b2126a40c19400c00d1442c0008607240d03a000c104598101c2c0142d85081541c544070b110555154900c003920a0b01095940c0148014503186c0c00d480c0d0050b20040c03c48401410044207000f2110b410341c0c080f00c490340d0b500001c200b181400d02038641020440d50301036002e0000ba00b000840310440c00907400380c190366018080a940c1d1900d00f40c0c0d21482040e62681401c5200803049642e411042c0c4d0140e0114100740c100040714001e40c0600104110ba0007881410030648400982d44200b01400454007035401780900e481080481c0300751001800d04c008035030304c1c044604401d00703011000304202604014031403006000c3c9403980b414216a000b020710301400200614503045070300c281102c0640c00003445d0700080c26910001500712074040d034401c642075088032403800381c80011003451180007800303c1c9002004002080046000d0000c0060604001c0348810b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 552641735 1250 552640485 552640489
    0x42c13051c03020403170306030d03150f030804030c0b190315030b09010c0906021603020d03020f061006120c0e220606030911180c091f05182403060609 67
    0x41440001140080c3d4080743c10014441c1001c500810f01ea0052001c07851401c208000c02e495080a90310075041c10348804c1d407071150a107540c00c504020300c44d60034100965600c0380b501000aa005200580d040b841e0081d01082958400c2c040f200e690982e07291038017042c2075040096001c0d103130b060344d419101c23940c03440d001000c940c680c00403500ca00400000060354102031807010b000308145801441c03c540c007007680d540480c0c0c44144013170b003600d804644d44130313070301426150480c5050b01d00c4009001c03e004401c00d00255170f845022000079a03070981c03100100304055400798021201001841c60000e103a040e821802070404044081c1980d91007074030340d182d005990030b00c9400e5456641c0421f001035640c0001e10148048041d81241028044a00b000023a48003d00030b0400c07000980880307800000059a248c66a45080c1a040000880042410344c00807020018101e600615042d5102007003411014a552600c40d14031902680a81c0d040c2c2c040b4108510300c0c5186400040c43c0e41e07080102000b50302015 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 552642985 1250 552641735 552641773
    0x1c0311070f170316030c050a05042102062206020c010804061d0f07030309091103220c03030e030d0f3e010b0109140d030f02150705042c1305 62
    0x90080207801ca80f0684130b4a40007004c55101b0b200140400005000047e034140e880800c403000c94150001002c415007001921071010340d080b4000035403200c00010710310b0300c184801003444000001320001c4860541d4510041c2e850b02d881200e0f081c0001c1000c4000b80000d500780d4803e401c1400c190441ca00b8410300006c0052920164000d1400c0c2907218400420800d644090031030b0250030811f0040c05021140c1140c2503090002030701c0240301c030059600c43e4120855001d00d124149030411a28269280d1b6402c015001e01e00100089000f80602c03131b80d608515000704c078040c2c0d40700c600356218011070402e405a0b44040b849540c482441041e81c00412070a00030510400c15400c1d18100001200701c0c110b00003610601595000551401a01d6a08902a610320121060701900b604003402d2003124400101d04083c1880310000210441e10140701c40594024007034001c2c2c40f00e103038144a54220000c07058821403144503100500800c1c010000b4407a8035a840d690010505c10b40881e041d0215401c091001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 552644235 1250 552642985 552642991
    0x31b0117150d0803011404021c02030702030f0d0902040b0111060f0907050414150d1a0402040207150614011d10110709051f03020f090c04080307051c0311070f1703 72
    0xf10081c080014030035110642d9003a0405c1300101d60841c0b400300d142c7c520580c1c0041d00081410800d601000050b00b0700d000b40100e03160b1954204000d0366941c00034407124014403045c0000d034040c6162405040707103940608030000303100000038020040c171365a55002a1004c0401810811980a0000006140e403900e02a1300c1030344040781c920b003542d460010440f8080d50381c44c015282c07082523550955800318a0322100d1000100103501c03524a5a81d6030300200d4082d2003190340090890440f9214001c49008a90041d0180c0f21400c0071240b051084100440d42d14580640c24603110003107000e145200c2c90f1801882078207a5103410321070f5002c4120802681810602d5109d00703900b680b02c0d01002900c0c90302c9d15940780100340100c00c64058a04540129040d032280f80d0f1443d000d000c05001140d032103103000c025038006016060480340c0e20601440c0c00350300c1c0c0c461806000c0000c040b140380c040c0040d0081c019031415645000d99203081c5041511403c0e2481000b040686440c0d54120700481a44400c8c0c006604c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 552645485 1250 552644235 552644243
    0xc020f0f01050a05090c06120604020f0a17070315051311130e1b04090e0a0b0a0c090905040b070c080c24070e0a050105090406050a0f05031b0117150d 66
    0xb8280f8200e05120150354004000c074050b42c04c0341c08140d4640c0e885806440442409030502d03200c9981c0c00300860000d208180c40c144a03140c4c04128841503a511503182c450100341e2414003645501c400d0720a5060320405003814541184914040c015230410901040c001951920085503500055003215299480000344001e600b120340340600c403c0c09a44465500540c4010301e043d070f405004c0005400c20f00460040740b08090721910329140700c003820408003240740d030403214080986c14100300040c003e144000d04140400c540203000544d0411074803d161051fa00510900c001340d480a608950800d28001e0031a421082400102501300081200d20704400110016005025402c244a80701ca00d00401d03400230880b204a9411a54441da84404202d40c401c0c01d05503100c078130a200050240c041d5401154201c0d201600c00107034400b0350f414120480340d0a40a80f82894542c107146215213810804d01030120784584006d01041d804105003e60050500f41501600e07044071002600030103907420203407 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 552646735 1250 552645485 552645491
    0xf020304090e0c2e1106060d032006311b030c030305070209090105060109030209070302040b1233010804060f02071101180501171018140a0c0c060c020f0f01 69
    0xc0804540e104400395801603604060f85880000c00f9203991b2a200202014040c1c2030505002d020540141e0703900f0810412040d8922112400d0700205036940c3c4102c5d01c082001400c0c141107038140c40345500200b12070b851081d81c0c0b1094800303030302c9080703050115440c8100029035807607001000c504600354581c0914030a94400c5d5442038540104040b1140142c0340c00c3e026490b10040c02100da8210340b0100850340d06030782d03241007950b07000320540c024000c580c84a0614080000c510116010503205d1030301c114464007910340c0d040e40c210041c004090720014045103d2a0405524901c1d46c004c00e10035a00500c034480220360120043c5e21042a070b0000c060459014442084042d0650317004131701110300680745c1803214001c501c0c01000800c600030399041d00c2c0e0070680c0d02000c1400b9806c07004080d005842601035804804840320b002c10024694982103004207204900419010421801003412903040d070f07541c41601c035015840c1c1c00700030070100d0340b4001035201f401000c8000d0601030284280c0b03059804000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 552647985 1250 552646735 552646789
    0xc07050d120f080123030f030c060618071b080405040c02100b0603071b050f0f1c030b0d030e0d1e0506150907320c0c010f020304090e0c 60
    0x24000301c0440d40b40c4800e008015005000407000801c0c2441c0040400144082c140d0f4076401003800c10040e03a0b0a1480380c00b00158071004000c00155150064800380c600002d8003180144110024038192001800143d00d0101c180404000440200d00980203811241c5482c0d52100002c2c02c0320106425540580c01c03162800030400300d10721525401e00015141ea5180d450981e42c0101420140c42c0a13a100340050703142c034414050b0400656071040045000c0f646190750011800e0b90390000030321036055034000380c016800c2c00f600c80c0c01604c01588005c0d150060540b42564143c1c2c4503c60205c1443d000441e645108000c1380030801d64034000390700d03240c0740c03082a241ca04007142880380042144052800b0b10344032103215250100c00d55441003c6140c4829001d500c800c55003902c400811520100c14007056401c0c141e448840000c1852a06e03010440b400010108010340c1c000b0031b40b040304809030300140000c0041c9441901f11520300100581601e0000040d00d00080320a0b40303100d108010b40c102e184807 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 552649235 1250 552647985 552647987
    0x90506010810051516060e0604121e110a1502130906030206070602030405030f0304061a03010b0904030809010e0703050c0114070804050f0103090b040b07081005060d020c07050d12 79
    0xc2190024041241d110100d030400004c80e040104800c3d89016814000800c011a242810b45260000e075004038207002100c0d80e00700180c2d940130282c4068070301c00700384810074988500641d5504050308001c013507054404000002540c014103030034850100360048651840c00500d003030100c8a00424180001a104c140c401107902021031940c00c00040c80349007420a001580d1000191001d2913401140540d0742d44d03661070054114003500c0c18242c12407034040141300800c209074000805000c208420000c049a00c003081600703130380c1c0d05000c50340c11000b900d01084c003180c440c1114662008560002203201e2080050103454070315030740c2c0203490300c0e0082003583c5015a4400c0341c10800e5030300c071040141841156110000144194400d2500c19001d10030440b00d164041d8101a141c65008108140c843c48c2034185200e12580443e6072000040f04100002ca2154400021800b610400b400250130700902c1ca168030000d51009601c06d2003482881400a0590b646004042d10207100c0c100a40840900080c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 552650485 1250 552649235 552649247
    0x51602041d0a0f150905060a021b0304030302030d050f040f0f05071a0d060b12070f1b20030d050f25030c03030e0307020f04150b0c0a15050402010f0c030e060409050601 74
    0x65510084c50800e058540401c5000400a80154a2100042c2d8811003050b15845c2038042c200c4003411b500020034000189900440a42010304e0401400c1c0511780d240c1110b2030301d8000c01c8a0003803664210b050b01c98042400f0b100100c0e0940c0c8940100d400941d01c94000440c1003840407500d5280c0c03a400a1011a0341505014982c0208100c0c040e45042030002c01c0c0034801c0000040000d000c10185603403a4110520414003a4106000842082115503490034026403200c88416001d03980030b4400c4140c0c1d52810b000500c40700720801c541e926401c000c2c2c121342130a401c1d4881203030000d00c1d001d050f0011031f44280b40499030306802e2003030312614840c840a1402401380d400200b00c07100590420711000c030168555101d030012266044400207040b400301a02101d001c0015040740400c1280402d010760341120006a040d00c9034000c1a40d0303080300c107401007188203a0340d04030390090000346540141d40000d80554203699a6604c079003030000c41d024a00c3c0100d40180c000390310841e0042e0719001444050b5030001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 552651735 1250 552650485 552650513
    0xf0e0f010603110603041713030302011d061909080f09030708061603050720010b040b0303070812130b161407020108040b0604090f0503030106030c051602041d0a0f 72
    0xa0028001c840c030b9902d480c0b0700300b0300350321000c1d001d0a00040020100318841c0c04043d00110f0140440d0f440c4d084407809180c3c0100c040c0401c078095840d0820194509030400646a86012820000c103416070703032018800c408461a101540e174141d01c0d011030340700103403416000d000c501c1d564555854482c3c640c00105407411900d0760115519070400c1c1e0030b010742c2e02d00f1100e06410240301ca04001c20640c0320070404031000782486900103040b950086510001142c19006051480000c83d42031102c40319400405440f0703c00d02c80001e02e07000d400c003c080000ba200030b02190f4000314030410b00c081905251681c812012048a0103c051500b844942c40301c150040b10003c540c0c0803545005040420603030000c1d01028002e0700c0a48172007545030004003240d0381da4000c0105580d100303c80c10300b81c1d5044c0c81c1095683e0001c2c040d60b0040713810001e50301e2003144224150760003c110700103034900740121a000c0c04028243c04410903085144000f02c2e81c6002c100300300300ca1100e446120700040368240c0e81492100740e1010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 552652985 1250 552651735 552651763
    0x62701020f120112050c15071415070504052101061d10150c0323070503040f080a02060d05190501120b09060c220807151b021c030306090f0e 62
    0x14604c0303404030380b0010f0750f03084095041d14030541000501607074490380e000300e1400500000400f0000080403c0108104002048a6100b18092344941c8010b41d000c1c01180900c60700703d40b0020080780c00303100d4100c80e1944950300c0400000d41c903441c0c4031420311400119102228617184d980920160601441d2800020840c584000d000c0242c0d5210040250001520141c20420580100303d10310513040345038146c004c0c8034007026686001c0d610700305459401174458001580300380c1c04000f6903400301281c2e0040450b8002d12840c80d10b5848140d001c000c001c05803948412005100503c06000d546218441c080c02e5151540351810030145809000701e0001450241c10742c2010003807081450302001900c030700d03070640b503c15400003069540003c02e4401540c04914544100d40c00010058134800c001900d19000d0750f41d0404000402c400d5103504181480000c1d0440764040004501c03140e001d00d0892850702c43c1c90003103001c81c0c2e902186815180c2c0441c4625000e9074400c040710031141e003001900c10031410 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 552654235 1250 552652985 552653009
    0x10f0c0638030d0c0602091504090b130e06180102090d0303020d05070f08270102030408040617040507060e011803030e03070603090c0308030c0706020c0c0a0b030405062701020f1201 80
    0x120f100020005001014024400b81d00030858100503071710400b010150407000345045441e65a1110444003400c1c041e4055402110303c1200c041810005014200d442d07a0000010800ba071a0b1054210780103040d00d40341d40684d582030050541c80d84c3e41540c0010907602071740c2d015864440d0302d1810001c60b40050240c00030710081c0c1d015421103541000c4903a500c20a806c51040c12a491180100e44002084080881340d506c00002c200c200324864000d403090310065a10b1084022049289481c080400d4402510503440b2040070010580b054084040054040c9030494031680400c011001c076076040c7d0030843c040758104000e05640c4c201006200000c110515061010942e1501c95000c0c003461030101529a0701c00100080f01580e0f0b40080340c915540c0201d0855031651035030500b986894040d0f00040c4142d0b0400c000150b44000308041d03a00468001018200c1074482c8a18080510b0f20174224a051025407400805451401e1015059000f0100062942e41030085410740080405812803102002 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 552655485 1250 552654235 552654253
    0x1602060708061014030c1806071502090f0603040b15010e010c080315060d0606020106140618131a101e0e0d060f0207030e0906010f0c063803 62
    0x2501c845001e800081c01d81e514068210000800c0351107504464006210150020502001d110040010051000310440740c92404c0b5800041042d82d10481c5409003461042c9002240701c0d011990092540243c002c2500840c1c40601c004203039030b0b810840781500e101600200b013000044a0840a4851034000d10300900f03a509003500107414400342d40005401d21034040002401020000c80803da64600100706a45401148010001520f032500544005501340300c070000c3d20955403840750a601c68000d000074200181040c030119800c0048a80c41d5020340d607a10340d441810514840c00140d0410790341007507088000314046c409110500e070243d108000c1403404d0b00582d98007002e56803900c0c400614020309050700850004096402c214406000580342504034500c24240341d00030003080340f00c2c1e100d0000076130703082c02004001541141c00a010076880740040020030301c90345115200c82e108400005880c14101c40142080200010309510041007045400c1a604038204003000300100314000d00c1814 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 552656735 1250 552655485 552655487
    0x903160623070f0f0312060b042d0b0714060123030109060f020909011403030304240c030911010801030b1b12070906080f1e0402010e040f02090118050916180e16020607 74
    0x4403ca01c10000d80501102b0f000d1481d590000c140f41d00d00c0030480c1100b880a481c0c00e450040c039031000c0000c817150303103407030700c5920306c02101080c424100d455070403840002c0403c0c1c60150700c211000c85182c0e50705540c0d560703c0030000b805c1880b61000300c2c5010000180ca49078132400340300c003490b4181c01003200031303c15580400a0307076000000c407a84507a1000c280d9150710f034543da06101c020701001141d10840c1c248a66119201d9142d405070700000e000c0c0400740b0b0001d00d264015035014201780030181405100c400014400710b000240514151505400d02c1c1c6080c04034003008414000640f540000100c0d180c000f0000030f0b038000c488580001d001a42000141404c4020410403600311140c14141c100c080002425680211480035851b0740c040c0050005000311440340c8000e40c48002c8250108030181c0503007078580e1110070341030145c2d030016060641544842005040c1c00c401a5840e01c04c2202c8002180404102000c0080003000071002044c0303913051840342d80161581c0423014808551210302040205 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 552657985 1250 552656735 552656737
    0xc030e0f01060810150315021309090f0816080c01091103060702060402040b0a0e09100f090f15090507080d0201050a091110030e120903160623070f0f0312060b 70
    0x1360ba00700d040010405032025206000310680c3e400030300b4a0800a8200d600035106400900000c60082c81d4844e000361200d0307415080318920000a800045a41c0131280000d031880c0081c6900c04a0406000c881410b1341e840c1d0600b0703030242640d0401c40e5140c605800030840207180d10224284200e0140641e071400311002560b460740104080c7c0b05070b031a0350006241c1d031945c03166000901040010074000340f07885812540c0e503066290b00380c0e07115854040381891882c80c40c8031352a034895010640c1c0c8000300c410f0f2140001249030710004d0040036502d6141c0d2000503401c224060081129102800b000082c0b040c001e401c60f20010800500780303007840c0403c000503d0300105005401c0b800c03517594006440c070040403402494140c092015621500059000c4402c162001e405082c204600315003040c16a04c2c04003051030b0181c401c107000b18505524203145103010490780510444c03000354080c18161280c603180f20200340103a007a100300368030b4049141816403024011a030301034810000c0c80018544034000041d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 552659235 1250 552657985 552658003
    0x6021f0c050d05060402160f110910060302030603101b0e0603011202040c2705120714121207030801031a01050109060f0504030507030b0609010801110409020a11010c030e0f010608 79
    0x8040c3d4820000d241030f56160705882c0140083c04100509040d82e01e08104003440f000c509440c602c4240284038107503d026801c4502c175443e080940020030345880c405401039040507000c55403600502c041c0948200007442112840d018010b044540e56000181c0030701801740240410b40100b004100500c640c0c0c02d4800c0030302a25034140d03000148002c1911080750307a40b00c010051103036104108000103212400c00b080c4400c0e0f440880c0d1480100140300f049d11baa454051240c522181d60080c6a03540916162861440c440810401e680c001c41d000d0341c92003030b41d5002c2c8600302c01045500780140180050b80c460048216108000845103505281c0003a009002ca0f2007044104500d0400c60345407544a24140d90055600404a448403510f07071400100402d4122503e50082c11414000500c2d03050500482800000382c1c00070900c3d09041c00122006540701103440c10a00003c10380402d00030a003480f5100d0b0501603a42c0010b1000a20f011103404e101504181c030255a061070418040c491001c929450 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 552660485 1250 552659235 552659257
    0x304050607060f0f0c090501030504020906240310061101090201020c04020d0e19020108060105030f01060c021203030a0504060605040b030c1309080f0304050106090629090a06021f0c05 81
    0xe00d4441c2841e1042c0507000d03000035100400c0c20902060501003541c0c1001c6096032042e2a14203c0d40c1d21074004408880c0b08039000303503002603184049003050402000104981c12040803e42407070030076034405081e56000307580d074000700c001401003003221a905c810f07004842d00400c1c0003406500103d40000755145542c0c12903910565000680c0100004168024403807003058800b0f036280b2540c080c00c3c00c0c416003202101680452985000101d1940c464800c0328070030814071501000c20b03420002d085840c3c441c05201240c001b10304007102002d0316000c02c091881040e02410214440c581071400f013040d40c0a07130748168041c1c0c0c00c200e80c540840e0340c046944228004107403195451030380d201403d000609800031b0064100c07600020001e01098500009621460044009028042e92007486c03000b1a8141d1060b40401280304c0c00c0c01c4000d0044080280da080c0403101040d04101c031000000ea5100e5050b8050b50159001015004003005202d6419060203c5090b0410001118441c003030420b12039804000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 552661735 1250 552660485 552660487
    0x501141905130f180e06040602070510050112020a15050409150e090a031b0c030308040f051603053016150b090f150613080303091f06030503040506 65
    0x882944100103441041050001d841261640d46400108a5030311303004200424000200049040340240140700c000b400d810010300c02a9520307280c140094011040803a0103000b111b80c0c00d48003103001d00629007c1e1a081184010444540c1304000032200300d0750081851b50745400000c4c035029000000e9400320791b075441d00400e20441d61455030f00103964a8209008140c5030b0400d12400e03810018107821414440e8941c14681e511003c0e001200300c2c0102c1006016403421306050002034858840030350024441d040300801210b8680d500c5081102c640305044c0040e00e4420100b050040030002c2114860300101c030583c0c0d8079080860001110081d0064000032140020100840c410070a0f042c1e541c50b8200720210850b0b40b0b078a4822010300300c41398031a4480c0822030301081d042048070400d00e0142808890440180800800384409604903140408603800914000228800240020740c81540150301610252000e180c10608a1850854900000c1d2404109100048002084806031502160f82d5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 552662985 1250 552661735 552661777
    0x315061f020a0b01030503130f0b04120303020c070305010506030111130b07050703080f090a0902090a030b0903040e090309011701060903260a090e090c1507020d120c0606050114 78
    0x160300d042d6507004001d14801c1000000410b1001c08405403a42ca01414000072509a4131603900c0d5600e15140151540340340c0402042100100b1030b041031442c1e51090602606000c514070a603410b07e90715a0040c2c5060b5182c0d001c005040c5000e01c46c880c0c0d40205c54501500300503290045443c13107003c038010170341681c20010781d800521600700101d4000f50323032101d40a0754500940400d09031541104070014010006600702181a040070b000762061420094110301096241d0384444503900030140240c049800f00b0030010447c01c4c0c040742218450001c040c003d5598a0504000420001e40380304400d402101c441e00507c850381d8402e10300030403203030450550303000e4050320261640090131110b24414400380000d14101c043c1d401c21045012988034040d40c07950381c0d0321600100c6d00c9826001e8003e034400c40c0040d0030902e81100030081c04c0c0003030018042040c0c04006649038001150001b0440c070104050345000001c2059a004c0c1501802007031070511891125007101c00da041c02500010304904c1e40940d41 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 552664235 1250 552662985 552662987
    0x1e0f040317090c1009030b1b091504051305040c0b070c0e07020a0302070f0819050a021c0605072d02011b0909050109090521090904060b0315061f 64
    0xc82100258010070341420308002500740c0e40c6a541e010441c0c0595103001203c600140103010b103404072900120703e4000d5030788a056194202c00c00b40850301040e01e0901c82c0c0504ca032140d124040d011900040655030300d80c1010200000300b40c0c0b80800c1091a810b1004020018062101c136504841203e505551a6005490001d44079032140d080b0f0b106502002c030402c2a400c0d40010a4090140260246c1e1252034603800f0440101d407031400b41d10030990118200741600041415882d80c418081e000b030700c40400d03180d400141c07840405102024110f03050f03040b6405000007403203400c0c0c002680d8249041c00700340fa070300604030110a16002d80105000424494000d0303000b174003d02500b5005076610900d501060b41d010708080c605001d0019071528000010840a0316032207051080344c0c01100911040c00c0824001402c2503c80381440e0090b0320030b07c802d00c0191503009015000350320402c0081103020340c035018145001902c1000072003c4c001c0c4010321080d501d8050740640f030380210507410304800c030f90420 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 552665485 1250 552664235 552664247
    0x60f030b03030708030402010806041b05091906030203090d0309020d150209040e0124030b06040c0215270c1e040207140f060c130b09040b1f0201051e0f0403 69
    0x203095805010004082080100c07000041d03214501c04d03200c1840075210241400100d42c03821285410340880d90b021610464059800303400b03800e43c010b10000103401c036041c3c120f04500c0301394403100200b0b40201c01c0c0814803105009501100d0707400d1404208450060300021040c0090101c003900607464100c900a0b881c907182c04980700260040c0060101180032001359000700503800300380512440185000c181004811403400440c0d410401c0c0d012540c865504101c001c2c55107000d801b00750700c101c0450001d0348908040346031045020440002e191a50011074040100351100c6501480d00810389081456440c00c00c040b584000d5007103440040750b200b0020400900c160032000d814a2041c40140c2281c080000321241e800c0c40540070380d101d5407200011074a0b5800740c68110101c1d8611414203002d01da0f2040f0240c010031000a0003c0385010030003000c2003610050280040d40703820901003030b08015409010303403508641c03070342e2039003c05074882e2400c00c141d040701411000c0e0194049010405240c0f00d41 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 552666735 1250 552665485 552665501
    0x8010e07030f14010303200c060d2c010c030b011b060e1510060302090102032508040e1608060112021806040b0a17130f170406020705190f060f03 64
    0x9000b0043e6031808501440305510034442100021030320851190141241c0e00b031502c401c0c814400501a070300c2d9140412034140c0000703040208a07907562010700120089203c0c844c0610343e103001c480d041084404080c07800e54408112910a15040440c0b103100b9907032080c00c140300c44110040c9401c03c0216032920764041d01c01c02c600006903202c2e40120009020b14088c1c058001c03503c100b280d042d00ca58a032010713810f070301a4900150140c0c00900c075054012208078442000b1141941808a040c2000c0d940d220b03864204d50040d1209011060070400da1034100d1150308030400c1c031070070400b0f9245403a0000900202d8031806030070100d0f4011a8060301041600e02c0e0300c2106200416158841c3e840346200ca1a9400185980000418264003480c20004003a45140074512502c80c02c168004c0544840c00080806002100e1145c0c0f4604d8101450f2804806171019010550180c03813400d2a0408011006809101707190076900e840c841041880464001007089030601e0411004042003049c09a00404000d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 552667985 1250 552666735 552666761
    0x10501080711010615051b010e0606090a09230607020601050916030b040606050c070f0303140a020f060c0c0c1c061e150513020c07170102130f081c08010e0703 70
    0x11545e800f8950381000142c50400c400e08001190007000d812814243c2e80e21000d04413164104001007001400d10210042c2e2000b0b25000215120b10305903600c11007146c50390ba6084d100c05041c0001045241b06115868000800e03100825243d4104000151205c0000c3c04a1841109007030310242500d000ea00014001c11004108003d956070321178010b852039115800d5a0000d0240381404101c24040c0c00480c400d607501582d440e05101c02150760326a240e480122094103600c030303140c61311403040c40070030500c2d201d8194088500d440390703081040390385069a24101c040c405ca800f004079a00907060108000c007c10780010001c541c1e8804820707594008001e501a01044900b88011048070301030491401c412108140e03034400300c10341e030034801004a0042c03170b8090304580c1001400708001707200c03c000c08500c040c022000602e80803000d820058144000d51000f055102558010840c401c0148000401d130002e0500c3c4032aa0007028000400b9014140201e004818118000c034810034469404400d0f240d00f1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 552669235 1250 552667985 552668009
    0x8070302030a0e0a050d03060f0e040f020f131a040c0210020304031812050c1c0303150906090b0f01020d0203040314100906020903070812090904020409020d031d01080105010807110106 81
    0x6007407290f19588031810400102303051010000fa61541040078a0465401c60851a125101d03680c803665440340c02d85003644d018440081602c8241c3c0c030748250101c401500c020020740403100d01d0260b030503c103208285511135440c0c40d070600009900883d0108544401070401aa2552207243c00e443d40f0341c01e68800500c110b540480400c80400c1000021820790041d0225281008c192b070411410541d12280350b0160700ea80541800043d00030b4001c1540440341d10403c104a5071540c1c1e0800498800398031401980303480380403c220a00300380f030481a011000384050440544500c00c060742d079101c1c3d48001043c10610300280d47c00400c091017400c0a0004140c400d004908050030010013a4201020803403190090030320000f0162000206000da01c3c0c0f03049520790512110f0002c003d0b411400801c00d980050300c0b50401e070010b9454114050109100340c5030054204483d0147c03111908406000c039040c03102c4040140200e03a000042e159028007203150001c001e110061115024140076444000d466136 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 552670485 1250 552669235 552669253
    0x90512010e0609150f160c170a0c030306080106051f0c12091409010806010b0a021204060f08010e1902070f060507082a0d02090303040e01060c0b061008070302030a0e 73
    0x6004134010140c10b007000350b8240b40752240315404105810568140d10394406884500c00118060495000c41d54003445100720b228041009100c003548c05900c0c1c030000540400b051504041d007502c1070802401e03081c4002c2040314104408910843d00d244002c40c0208040d1002040d12032055500c0d0b02010350119446410618504002c0c1c01c00c0064040c480d148100040c541d184d0b230030035041850407500131000500f06646058051081940a10301401c2140520300c4510308412440c4010001441d180e0348080c0840004030006040180603001716900e01c1000702400418002c0d2607803040d52038109000165a401e051900421480f8003d4008042d6410b02c01041503968005042e0381c4510316405030a60544c41c00c08001300f03846001f607030b03404440e00103005079015000e465019000407480601140c1c501740c2c40f00484110100c00342d00450000f00c60450310301c00c01c809402202c0e0440020364640c0503000102c07001a0000c2c40c002c0420040540c084000390300380080d900030000e40c076020000e544a41d4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 552671735 1250 552670485 552670501
    0x6141806071502070204061d0a050901141608070801030f030f12050a1505190905060d020613060e040908090d03140a021b0108060d0f1a0a05071403010501090512010e06 74
    0x1d080510300741c0c459450f05400043c014183e0001c0a003150040c8d61107001381e0b4030009010000d081c040c6c0450319565850003c10301c2c2d0000081890700800c032408040301c01c4102d0030070040c50480e0041400d81003220030740040001500c292681034140c0c1e410b06111138588070140d8101c680d1103039000c145a0503814502400211030152340080ca0900e0b40000041446441c0c00034413092715000481c44c80005030001c0100b01d06142940000d8101000812042d40103013590000307034094014a20360520300941c6c0904025158000d418400041c0c1305a8080c03245010f2600e43c0c007514000c41503403d000b10399098181041611411285041c2101c2c0000c40e40c443c030211000960f6000b0310100c11104007101c0725152070660042110f9442000018a5000c050752665581a01d00c1a000c4084914590f017801000075034469010a07482000e0302e00001a842c5410140201401d4045140310001441000107002d00d991043c210803d91394103460300303400b421032801460300500030721001745458010801407061003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 552672985 1250 552671735 552671737
    0x1f1e1a15090307451e051302011d0a050402160f030503151903140106030c0f030506011208091e03240f090309120a0206070303020703200705090a0207050d050a0906141806071502 78
    0x35230003030380c55403da2001c0e2203901100c103409440301540100001010491807400e40c008103900040540096045055aa1904c9081d203414a0031000f02d0008001c1010241344482c5140400c00b088803a5004504159240b00c24034049010141c1240544a60520900004d4005200440d84400615032a903a6804491034000d05030104072000c2c01039800020745240d41a40302142d058200701c00ba40762039000303410807254100f880070800006245003a18441d40c1ea003440340300b000041c426080010082151548100140001c00c00c448601100c01482030804000003aa80700c05000c0e1120031124103020212031902005000c002e510000000300c1408069042c0c0152800c90300c01c0c0c0380d40300c10366801d03203607030fa0130f0014442916600d600050040245181280241350422510040103191005a0f11000e0410070481500d001040001841d5040c00d94440c0c800b0f4000c2c9080d14200715450720302c00d4804d41e54807603115583e69800401002002e245ea480c012204107030b034806801c0b010b00040d88000406 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 552674235 1250 552672985 552673021
    0x3161b050618010603050c10140c010501060f030e0a1b0801050a060501030b01020f030d091103010e0a02010e0301150b0c1f1e1a15090307451e05 64
    0x194401d02418040a0702d414000c000649502c4009084610300d02d400b07000e40c21488044060800c019854150140d6024400900400e007440c400410a5810100080c25150303120104000b05441c000e007203012440013090b8642c42d00d40c024030604050800b2400c03180e4010030b98015030184e502e44818011010001c0e440342048a41c01c1e201070050400140069885686040035a84170ba041004465040a0994040b0000c0361040130312207590485280402e0131a01e10186107009640008004001d40d0b0b0031120240d0740c15022402401a401101110805007040d840f81d0b250f180070120742c501c4440e50178800750301449400c142644c40b84140d103400001030046038402c02d4080c601c44060b242410003501401000404a803500e4a5a0391188184103142a5004900c0d0f800c40d014402ea6216039000d05c00e80004200c803826a0405991103808801580300703441c1084d0480003140e40840e170f0002d03000c1d0034081c82d01140100040714640c4201083e0a850b041d09290507003442c01c000c100d0041100c0d554046 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 552675485 1250 552674235 552674251
    0x506010207181d060c03041202010f061811180105030903090d030207060807031a1c15020703091203080f0406020903122107020c0d03030b040c051c0504020603161b0506 74
    0x403215070300701d80c2513440d41016107200002030810800034010800c00f15000368042c2e07261000046040280042404850190b0048803c00180c1200c0f6002a44140580c100d100c0d204045c0c44d1800e45022a624040d011450f4450b05001002c000038403e101e0500540b200c200b0040c5c50310070900f2007450000d4850866000e150040307130f02c02000c207035024420311500c41401e0b24401c1e00350351403000c04108040380c240381040c611800310705402d18000490411111100c00c2c04c0c108050703201c5445103400b612000980c0c201c2c0c5104d00e0fa960b00e001c0030070b902120103500700d00d0a260203401c9480c0c0b42031281c06442a10101c0e0f406224401c00700d851901114024036034031200040c646440c1c6800110512855015248500140e0050702140d0892a18039000b410705842803c0c0043c54450840100d002d03942e1814002c40400d002142c590300070350003130920403030060700d0100800151410f07900003402c601020740b010070b500001d50702c90706a55005090706041c81d4503441030b041c510703417907032420300d5850b0402c8403814 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 552676735 1250 552675485 552675521
    0xa15081303050a081909050d0906020a0b0106030209060c010207150e011802011b061b03060608040503162909010e0f0304090e01060b030a020c01051612050601020718 73
    0x9032080381000c10441140e54180d4a003441c1c121002002c5410080142400e2000b0600c1280c5414680003842840d40e52440ba4001c1c2092900e040c2c03000d000b00b8866444441950070256450340050141c03c03507141902c019003030060f2500c9800380825418003588078a0a0f10398400034880d014001c800c814070b1034070501500240074076003000499600780c41c24069110b900c007200003840e400541c0546601d800305450b5000403040f0710203e4943c9419074080c000905104210b400011000c50307407601642c0054500c5041407074075410141d40b840c1e900c0c0300e0003410101d20b40d1050701e400708000c0118074030381c20502c507003d410140b003513211803240041c3c0c02031380d45420940c43c1001c6480e14102c00304140b211005070002440c1080e00c0c1c01d80105c0503204199150074103550790b50021034500300b400080d600031003011000680f100c40170f0342211300b110006840308900350700d02195008215408090500240c06020002c01c1c00d03142c3c0c000507454a44990807480815103182c00c48032415055601101820481c03a1440c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 552677985 1250 552676735 552676741
    0x50a3204030b310f0201030b03101b05120711070f08030a0e091005040b0402040504050405030a260604020d0b040204171b01020303040803100b04090f0b010f0f0c030309020a1508 78
    0x400c51040c1410b003190700010080211601140d0407000025130940103044c0428140d411100082c10503020400a502503a40c841e170600075030b400074101402850340e60400c42d1820302c50810303400359400020051170400201a0230041c1d514400d0204600030100d003190305812071f85070500d442e2a80c01c06012000064901d482911951a100d00414000c0994100d0b0520130b42c24101400007811344121400c3d08240c080000140f0341e1500d12405110b40e014202554032603101c1140103001ca09001d00d08414036481c11504d0003901120351440f07821060841e0016540c02c120503400000c1c00703425440c4c942c00352000c100000c1212030305001c0c90f00114070909480c2101228562600440b0700000c1c1c03640180d00901c001400561000002d40c2c00103a43c0c20008401035458485c41e40c164000c2d0800c810040d00d500c80c60085403440d0060364241c003001d081880d6040081c9000400700d41c015101c0c1c501300f0154060780e40501d4083d0380108807041d0040d114040355915883d200355104442c0380b114000519801c00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 552679235 1250 552677985 552678031
    0x81602010c0504051c0c0608040b0f0702060601052d0d0b010c080702041508010501030602090406060e010f2f010b0906061305090c0408030703020d030606050a3204030b 74
    0x4030401c908058403214245420301041c01240000e18004900300c10b15803100d580030505000604004190130354500ba11850a031800410302d40c4050011200d840d070380001e000320369402181d1554804c01c00e10306107444900c030200f046014081c080c82c445101307030300310305081384845850004e203450340a9600030301c07200218130b004580200c80342802074040801449503100510740b64000c0d142510310024490112501c80f0701d01421200301ba802110f03c06c0c0d0000f5140d080b81890300078000140100c0c00c0007010b107174000001a108880c1d50b1501001c120a1009425000c0e0409403140308503840040d0124415440c4000306000b040d1501d4420f11500c1c0300400a49649080f400b1a0a00c480d5030a026641a207000140300c14140058086407008806200200c0d0030641000070703055443c001d9004043d510581030015080396043c1c0c000d0410030404000c4080f410380c01040040d02031100c0c4450282c44040107075900d41080565101548040b00000c00001f030003248885980a803403032100100c0c0d02070460300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 552680485 1250 552679235 552679241
    0x1050109050303121902040b03100609090506010c170d0e101d10020c0a08030c120c0906071127150d120e01180b040305010f0203070503061903060c08160201 69
    0x60a80c21107030000010b44017001500d8072080d0800e40100c0135084c1515180c40001c5a081298000454003146d84100319095124040308028113201c83c0800440c185140001c0034150ba01c2809070a800d4040e0403206003150711800c076000140f841004104072802500302544038041e0b100904c28a50600003c0c204c0300d40c02c41a080c409854030310051002244401c20b003006500400300c0348142c0d01130242c894010030045030065128070f51400301036688481150201e1074500f80a0318810b111a001d000403001390700e03150b0445da40c441e000802ca20240303003108001104090b8100105284c14810030781450303514003004515002e0001201421001d00c80307241032014032061030202400000b0700c11034003a03000340602001c1819102c1807504400c40000480310300c1c4002d01c281d0040c105d004001074100b080c80f100b0300c10040380c41e151904c19071031414108401482d0b404040c1500d44503000000340000c3d0740d84400c43c002c00a41d1f126006100011120801400c1413900720b60700009100500807000034144188 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 552681735 1250 552680485 552680497
    0x908121c1b111203010b0901020115050310020705010209040609091202011b030903120618060816031e0f0506151807050d0b1e030d05041d0402040b060c0601050109050303 75
    0x4a560703891204a048100c44881d200b120482060145103030340004400f0140080d80038011070300c210340e52169079800090031112256046441c80c024514140b01d1640d001c04e003000c001044010241e00d810450621303900a00c990101c20f5481441e01074001899840b582154100c035000b0810700e8122a10f445007a0301341ca074260070241c02d071742000d00e018441a0180d84022109070280c40d01c541c100d044249080e0448015800c41d1040129000c2e103000182c5c0f82e070107014007801c00380020340b0b03804c182c00041031540b8000740401800f0500d10102c1c5a0090b981c194441e80098201002915803000760a0180c0ca401055814518009803680e40e04100e003840c0002104540c0490041c0c2c1013a6240d41080342d058100b110b100314a50340701d45003608980d890840400714030007603010302c2c645440c0e074104251411450141c3c0303a007440750600c01000090112544c10121100d280d506000030741d00c61002400610f102140954444000b0448101669001505038169102030b00c50240c015255820181d03a80248 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 552682985 1250 552681735 552681761
    0xb04050c0f0409090632150904060e0102070803132102063409090513030219060f020c03030907060e0303180d0c08030d06050f010c06020a0908121c 65
    0x40004210124044e4041c64560b8081e520004460300b400758041c44d26803210b0812400300402801035606514681403054002c82c00318103821882d084007000c00c00c038a00003040036240503503445107100b129170290100c1e8030090380200c10780e07501e1500c0031340640001c035a200c094940710510452200c0070a0340c181c1700000c1075101e0b001850a82e642803101020b9101e2908176441c0078900140280d080a000700d0141c01e01e0020b520780d201e10b24200f070124030855a000b0300c24074519010340310400100390086000c015609481e40c103058103001300d0501c0310140c903220303414982c41807000807101c0c0d014902102541c01820400c050303500d500d07500c000480c1c0314115510156070540040000701070280484549003022000641034101004854807a0402c8004603801107030260030004112221208a115083c0548001c542a0460350035050000b0110078048900800c0b0b140e0004010f1402d40c060415030b00100200001c4844081e40c54a8025a54121444103000f8002c0b00c40201e46035080350190200d05040c0e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 552684235 1250 552682985 552682987
    0x60504050a17011b03090201030f270311060103030e09070201200d0e01180b0f0106020d03051312050c0705041a060306010c0c0f0e0108010207050c150d09060b04050c0f 74
    0x100703022196801c0346002820b0305503581d25404801184c5294021a04284607180050104014000541555604d10140903044e1504201d43c0304807040d00907840354100010305441c1c1d12610340c42d041e60b140004101c42c0085100d1500001708040d0301101070051118180c8001010b0388030408142d090f9480c26100c03000d014450700e903062464034005c014184000200ae400318030fa40c4a0f0140340c0c2184c2c84804100010303100b031142130081c400755800c40c9030840b0707000c0460074449d0f142203002510380c5004407100080680302d10114240c0520024140b500940208011210304880080a040c2c0e500100003041d10340a440c0d4001850300d401d02c40c618a49000e42c49011038200b4603010809594001000705060042c1074200351301052210507802d01a002d0801c907034071094244406404070120503401490b0583c010400e00d00052404550700c07825180a0383e405010b00d1500d01c10031034a008102d01400001c1c540440181401002d4100034a084400d83d002c201c1d94440e120142c02d18403840d0140c12500c14 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 552685485 1250 552684235 552684239
    0x307060e1b0f0609040228020a050c09071e0c030201060f080a06020d140405030706050a110a03110d0e100f1515030207290601020304080c0d02060c060718060504050a 73
    0x20280d0824203210b000401c480e180804880c0050200e8021030640d041c00001500c0c4035130491017014000786001001e00003031103460180c1d5907880e51092051510b900038004a4045a81030380941c02310801030902c9203501d40c131000d4403130001f81780104015017903005609068000954210790b0320010240c40c0c145000d0181380d00c6584034900a0341c419242e003640b55580c3c0320581c11210001e5085806103104c1ca0203540e5544031801c0c03210989202400c220f10030351a0010801058a00c501102c218014a0602043c0c9040b154070181d528001d61581115460a1407181500084080b4125420055642c02004144400ca182030219002864031200b800a140030038044800075014020880825260251403c00c5641d1030891400c03c0400c2c1e50040c90210881d41c04000d1441d038401c1d84a1400e2000b14201450700001694454280070a9070091803818550303c1951510400c903040449030504491283c1403903071000705440c0c1980c00e000704541b5183c2002c6405413240d0700f03c900700e0340000d161055482c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 552686735 1250 552685485 552685489
    0x504030201031e09140c04020412061a04051003020411070c0e1909080304020f010c11100c02032506080702100c02010e01060b130f030503031512010e0307060e1b 71
    0x450680aa0500c801d4101403c804074240591600c00c3c1c400d038400c002070824100101d14141030307650b0141c07040d0300502c424424020201c840901d142e03040000411034002c404140185224025901d0750028206402c0044540980a03814104c920a540810020203c044400e401d03004c0c01071300800030040244108940b0a02c081d52a400c1f400d101e030340760740d80c000c80d014030021100d60010894400101208000652070300ac0c6c1d40450700d800a0800c144030000c0c40e41c030b0000e1941c0e4003c20510034082e2020385100c051080303078010690747c2d003c0d040b10091080f20790b603001e10031311160241008030315840f004101036100d000e0032806005190001d0919401112911024141800412003150b684040340000d00d0340034010b013402012040b1000d903542613a41d41d500700107204c98100021404520b1400c1000500c000b0499910071411102c1c060080d034218000f422440d03442058100c0d40d8206088038261142c04002007a2086c4285020824a00141880c580346d0b80001172102c00076001059090944c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 552687985 1250 552686735 552686741
    0x5041b0f080a03051b070909140f0d031808030a05010305071d06010c0807060c0f090819110105160b01081504020d24020c0105011e0b2203080a0201020307020616050403020103 77
    0x60021030544608503405622846c054907a40020f21707d40d110400e1034107110700d10088000c28100c900182c20701d40303824a20345035a08425031245040503502e0b20307880509400742d2401000c0030b900940c0d055036800c2101c00e24025220a010a84841c00382d920000f80495034020480c11580c8a11082c40042d65500015981c0e0703901060251111001040740c40000340f4107220b14800c00c0c2841d03d0740d00302914140c500400300081a0807c010641c040c020780c4c0301c45016044e04410b41c650006010750320000c514012a0180500440c10b100d228100c8102020804541e40706410b88003550100c40c80c40c00c1d4010480d003009010741e0040e4114109500c3c0002088000354147c1c0300050001ca48050000c040c14402c0c1240c0c07103503000c0121655a40c00601c500c031402e4a01e001040791103841c140b40c090520316042d8080c82080101ca07020110715042680e00c0d20006d036118011600552865110000044040c0c00303980102c1e1040010301500c00090411010040c41c9400f4000720307511a820181150700550003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 552689235 1250 552687985 552687997
    0x17010203040f0f030e0612180303240a0518150409170d1d2401030827040614010e040606050301170a060e0d020709020a0806210105041b0f080a0305 65
    0x10405401212070043d04c461006101d007d240482d0b600c2c0751302e41200d03203a0312a082c81e030041c1840d070400c005020304206201140c0c8400403507210700c50f8400d0042c070005241c5000d04d6100b01c0d0454400c3c02103442002550f600310b482102407880c0f8070112030310ba400b04012035030761480040c03000c541414101180c102480107007190512600002540c3d144203c03003140b0050078044000441d42c0030524000c1c41c1040800745454081507140f4190f506c3d41035a0342d8020034010b40d0199008006145183c0c01c2682041c0362224111078050302c2001640d481d14000c80608140e280c405001c95044140698141400d01c00e01080f20300f1030f90341a046074244a515041ea0944803950300b0f0910541080801045040c4104007148070b4000092030b00380340d45c03200030f401c180c4c01d0350100320046e00c1800805201504411444d501020032078080c41880c00407210041c0480301e030036a01c0e00f258030b860104800c01c5400b2640d00549005080503405055035422a07401c001814018001150004107c84000a0041c400303806 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 552690485 1250 552689235 552689237
    0x1c110d0203040525090606050f0301090509070f0e0a05090a05060c2a0d030b010f0207050f06071a1005040b0307030807051207050303040c14101805060c010617010203040f0f03 77
    0x341c41c81c132611540b000e4181c1c0501e1403c00508074807041020f08981c0c420b040040c551b40c18118241841c00c00014014001445203400071903d0b132000541d040000c0c40b40c500640001b91000000c6515003040d046188030840d0a60340852030600407500341003000800c0c060142d4004000c180c1c07035a40f030911101c01d1b00100e400003180c5081b0b140c940c0ca00801039043e072600080d8807004008000d400c1c0001019a003194011a0510510b00c0507804800c0e03000c610350055400c281c4588030201d03806004510385208000016103c1c1200c040d0040c8000440c0352401d005071404511600c00588130000c003c221445800c0c0582d140d448074004000040000001e4804140200c09407150803001c03048203409688480700803202500004100010007250040810250541900c031261411401001c100ca064074828a0302c240248900221049107516801501520300600700303039151751041500d60b002e04074a000d044807a462400c0c002401c003105100b528400c680050801c41d460242d521811241010754400b50 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 552691735 1250 552690485 552690493
    0x20915010909321905060d0804120b060312040e1807060903150c12020309100c0c0212060c04050d03020c030601060c060b12121b0709021c110d02030405 67
    0x1d642580c512502c0d582c0c2003040305620402c0b07048800c910046810b81998080f08841109004a507400380c1c8800c4101044010001601e48035000000c44540150714001c22813040040e01242d8800313500302c00c1100354400e00440300f264503010109500e550b09a007103032507402c505100c01c102d00c088501d070803604070442c2d6400c1e040d45030040070900e041c1609900070328040791041c28200204039203600719201071400c3c000c080000b002d000000030841708100c0320900307031182c000c00840c40c0c0c61b60602c80d07150300291502d001c0140b02c103000304c041e01004144000740d1140c8036110852030744450104031213200704291001c0616150503c030801860304011071040d000c51041108200654a040080901030070050b1185001c0c85041d00d0100c05a0340c101d030301c0c140540c48042c850407040d0000902c0d011300f500c1002800751103c1c408a0008074600300d00b204009e00c0c1c17090081c002800e20f2a64001c080955403007500d00e4800e81c02c03114440903100c00c4214a02c210b1310400c80104034104c5a400b440c1c0003440340d4262 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 552692985 1250 552691735 552691739
    0x2060904050114090c0c03120402040b0d210c0b13031205250509090f09010b1f020d080103081c020c10143d08250b070209150109 57
    0x126003110000d0f005101c8403189001d400d0000d241030f445195106290300f406901c0c100e5050441a101c1c01400c011070002c0315144040713001c5680710342006403100c10142c442c00c3e43d00f1050600911681e89540101c0b03a40203410385200d05070b486003c0055034560000d103014071a440d00c103102005036108440c02e40070483ea00d040c1140e003682da8040c81f030141c1c0780328584081603004c031280f0031034840d232004032113040c0f02080000c0f185645803000b065a00540c00300741d2409940d1b030382c41c120b8094001a2042640701c0d51030030f500080c650307050302c5400750302225508485010908030b8007540e40100030300014280031000d21101c0209400200603061036081c441c5d0141c2081c01440145142031b481c0250a40002d44a2980740b10300790206078031903400301d0031400f1210b0b20384070700f00e040e84902907014130041c000c01c1c200d100f07140340c0360700001042c010b00701502158a0180b00045164030307180301c2c0010b051140810880050740783c020703509540c10181c000f071065045c3d0b03c0d803440c1100500420740000341400401040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 552694235 1250 552692985 552692989
    0x10e010b10112d0a20060319050a02160602030109110c0a0b07020c0a06080f0709050105040605210112060b030c0108061002071e080f061005090c0d0914060a050405030d09020609 78
    0x1001583c900c03503002020724005c074903031021174840c134030000602826081c000c22030008076003680e032400d0300004440040c407512400a4a030203481440d0f5008080002403401c1001c01405074000c60488007400020132075960784000341c4006104000c07138241141d00c1020094081800d0703000d0607401440500454400c24411804510509110351101021490100401110702420703020b030351b84103c1c01d140ca450002e04280000c2c1035070059010302030070030030003040030070141400c40303c120131540021401003410740c4d41c0c2c46c1074074a4006400701180d085040c00003407046400c00041d85810a4416115500039990708401d200050f01c0c0750250004510410354005a00b03000e005440410b8a2196280b000c014205040549031046115402c07400d944000200101d00c00600070f09002d690048400f803409032a41c1e001d04405000780d00c41962070070724112000080051554000390001000c00641e12155074041c900001c46a0480e8080c259400c104080a1140807580c170109240d807000b4803042c00e080403e80 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 552695485 1250 552694235 552694243
    0x150f0f03061a0301060206092802010207170a021905060702040509010902090106030e0c1507060c210609060b0a090e09030f0f0301030515090715030e010e010b10112d 73
    0x329200c06100b002005120866060050301d9100e074071103004102d80c1140d050300d600b501a00e00c40040704d040441010200710ba2081c05a0b100a001240001d04034070445c0e203226071100301340c4c00300f203101c0c0ba00c0b40040228a040c280e01e0308121980203207402c1c1451619021700000c0d040083c50ba0949540e03441c1290016030301d5152030b078040d02c800e030303030000e4240703d214006450540d00344010381c8255404036100b29520044000c64184540c402d0300030454000c4140c5c2903821705c0101011103001030080c007846003009029407000d000c0341c80d016000e202a603070352807101e1550b101300710350300002607141c04042c813241002d03101d8980c001059004403407822000446803146a08142250111024000010402e0280400814101d0f9024034170b204c601d070810301000795070b5001a20800382942449001e1850703085c0680e000780c4000341c02500a03c0340100c0001018000c180819581d0300c034003a004c1c220a1034601c100300c01e0303c2c0040054010320076410390300d4800d91511a5003100318088890000c0c840c0300007800340 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 552696735 1250 552695485 552695519
    0x20d08361b0a030b0a020c010605180907090e19170a0e040b040b09152b0c09060812030a06030f0b0405070e270a08130f150f0f0306 58
    0x1402500d601091050411941c8500c807004500c620380104060020030013070b002e019040516214016030b5001216012405400150301195000310700342d00e143e00740146560428031411a2600750b42115464403d004111988400405c2d244d030b07c0054a00002803e07040500714560245681d050303640c0b864086070705168442c00e01c3c0c800003510000100c020341814011500201341c211030a0040301c02030300c0490544080102801d010464181580032941c550006907540f0030a40745908410700340310350b4420103e6403c290106d8460b1700703641c00010242030038402c01069603881806400003004594490055420150400044580d00c030000030005002c47d145403030710b510481400040c1d29050400900f060656440100714013074007810403000742025005030b000c0f008003040902c02102c42c0326416243c10b01d45a00200b4519000991099a01c051360400f0700311100d0b402420f1010744c0312852009921f4106c1450300215459055482e5554002c0742030b810360700014640051070a50f5841c4282c603002440c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 552697841 1106 552696735 552696841
    0x2121f0b012c2205040b0f100303050301230613050a30150e0705030d18060e150706020406200c010f0507050307060b030c01020d08 58
    0x94010403d1004100403c0140f4074052410300111503055580d900100903410000700c00801c0016036200f40d80d416900d15045901e005c03043c0040c50300100854554061403040d1102e684c4078100500070354000c414013510070601e07120501041d015541c100c40a00d42e10300b0304600d862074400c15000d0b080e0021218400d04100141440c5010108004042c14000e007010340c0c001ca4680b0020740c00c01501d40c22402e9031851811203906131006074212148841500000804022090088001049640014042074200602c5180c010800d130b10459044a105a01050600806510a012122207142c1000721074414120005d0650f42e40302003800300f410811080d034440011881041602e103001d070301c08100e81c0c44140e2840d100000d803405041c914002c2c400d1201c0790200b0b41c80090100c1c0004916142d50030543c54002000c0d00d914296089114100a03210144c4d8080c0d08500504075000e6003 = true := by decide +kernel

theorem cover : BRFrame.Cov 552517985 552697841 := by
  have h0 := BRFrame.cov_init 552517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 552517985 ≤ n) (h2 : n < 552697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
