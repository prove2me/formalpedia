-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1475
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:09:42.81606+00:00
-- url     : https://prove2.me/submissions/70e1ca36-5c89-4f1c-9c33-9c17e3971ace

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 265107913 ≤ n < 265287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 265109163 1250 265107913 265107929
    0x16090b240703030203060607050708011a0d0f0b060102030c2d070f0501030f11030f0601091a09042c07030b1b03060d0302030d02120406060e04030927090305190513 72
    0x45e913a500804100306001e1088001e02c0e078032600382c000c641468103402c0300c0c01c01c1ca048407017214411a1300d42000800c40408401501c44e0700d83d040c0c14004103404070401c5034400f0301801180e1524020b00342423450090413030002c1c100c803801c50884c2d0b030252035a003100008500d100c00050100741e080c5449801c00319002e02c1084d050581d98582c03074105070450b402200144200118480e00c0746010490300307010490440d103076030010300b03183e0b03010940d1707004545840844000303070420600f86000d40c0705000003001400d000c511824402007101807a40d030f07004503078841c02080502401d0281c0c558130f0000032482c00901412640303440710184a4020b8142d40959030b100e1811540581d0305200e6040c00d85c03d45c487c840102e060307280006030808911701c0c10003920b801903110391020800c0c1d55482c01a4400000b05440040c001401c0c00b50407c52890f035444c40c034003000d100302204d003100c0b0f5184002c0011100364030012400304030003195456241a150840700c0100042e401c0075031034074025a401c6060a00140500d1350 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 265110413 1250 265109163 265109167
    0x3041502070b0c100501050301051006200d0f11190f0309051c02030f0c010f080a18060f1a06040b130504061d0106020318090916090b2407030302 64
    0x14054401c200c154000c02c0416880755071109221003050b1148418038200348910301300000040e540c28144100e512903094260741010103800d00404581c052010a0382c403508004401c05841c1c4d10700f06004c100403403d001e445100304503a403403001506280085410403540d42028410946224145400d01c1540e81d100749442598441841d05032201503858100b990048840450034145d00001482c0091490007107080f54002000340010a0795460700b050681d0000d0307600c02042002d903000f40090fa40100c0101d1000c20b900700c8160b45480402014101914400c0c0c459040c60725103401485071007200020041c3d81040354001e08003203225031186214842c0f2010000600030b4142a0074070442010345001003040c0301d956520444019000030b5425050b10a00400000041e00d070300000c2251810001e00c0510b410b0041c0c2d140810201c1640149400c1c518000d00501003022003c1c1100f950141c10614030002d41c0b1400f64060105403e80d01d01d07214011184403805404906408043c0c60b00650715140250b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 265111663 1250 265110413 265110449
    0x3010302180717010f0918020607020105070f05010903021e0606090408131215060e010f09051909141b06070b1812030106120603020d0303110906040f030c05030a050304 74
    0x984160320080040103034020381c8004100113407103801c84002c4513080081800280c83d1425440d07c68052500029400b80c02081130a0055008101611402c0e000f80c03088403074892543c0319182900d01541048005070404016402c4808038084000381e107242d078200030728041c9401f5000c55408600a40042c040300742c003240b074200c4441c0ea8020b40f0040c0c2455090350040c18441d14122103200000e0400064140c1407860206624000d4000317036048490f01300302c805003140390448071002448050030071400c2d0304122041c0c0041c600b4070700407410707524410407038585203d040042c0f00d0704140180400c002000300034600c251740b0707a41d41800c0e504400c0d0800900019030b202c010b164030781e060f5840312906040c00f84002001d45400140040d5040303070030356120400f22003109481e140869846000c004d5026401207281c101107440303a44415000542550300515010000000401d69049940101445400c00703006004112090400f03000401d13050b002440d1002c0b0fa80d888035103a00942c040c4141400c001d454403 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 265112913 1250 265111663 265111667
    0x4050901021b03120c0f0304120311040608060301050604050108031b0a0203151504060605160215030109020a020705150a0f09030f0828022d070905040215030103021807 74
    0x40381c2114001010030040554140b0a9489421202d00300240c21200c0000501c03240780c0c0801c0b05d03c240d03400c111035440d541d10740d41c2c0e010500351140000c50425640ba607100f50b000c588e0000400250140d82c81e042100d00c2c01004041c01d6030300081c800c0380602d040200400c0b2420001082e10350089072000d442c50202c0b4411000d501c0d090050070082e50511516001c40202d10301c42c50464058004c0e9500083c05c01030110a02040e02c0c00c034421100010401c01510380d0180404100303200359440113006006680c030042608815400a81041d14a00d50010f19184180e0b0104801c5004010995106d440b000000c8100c2c1d540340280c4541c034040c000c42064441c401c1d44580310800c0903603440745010341482a81d040000c002e4010640d5102c0d0100382c001d050508000b8003a0903040d194007507000700700e90728400c4441101c60800c00511b0f058400d010b50b030298140d00500c00c80020700203214001541d482c0030300400443e0358505065120f13910080005101607101c062081800181c00e0b0104c1920b500c415000f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 265114163 1250 265112913 265112917
    0x9030503190e060f0403020f0d0804150b090411031006141c0f0609060b061e09030f07180c0c1e020114030703060f081b120304050603041a0c0702010e0405090102 71
    0x180240d0b0b0140100300300104c920f29132414010f40c025400c40d240e8040303840f12150340342e10011031003000c609503200240024000c100940c11940c0d403840b010a07450141c0e00414078000043d41c0803555056444482c3da05400c04000d541c600c4400041d00b030101619207000030a01c0694905614054000001c0c000c010688001c403400e2881d51001030000702114a0a00d01d008080740b15080300c01c2818138640c10b0142c46d015003600c600b000f000254158500e260240e440007a030280c150150580552840c5071100f103800e01c0320b90014550081401d06051680c11180300300c0c0d8800c0448001d00040e41e91a0380480c56010031200910364a0511700f08409240c00183d07143c0000d842e00031901600082084160dd5141d007182e801c807000313500c6045900341c6598070715848210070150078050102c6030b12084d00c0c074030f41a20740c5402078060500780c034609078541001c102264005c440940305d20904140c0c0c03c20750244490059846080c4540742402d060003540020580520f01d00c1d02c500c119141d401007a9440400c0d81 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 265115413 1250 265114163 265114181
    0xf04030b0103031e0e100c020a150305220519050106030803130302100e0a02090c071703190c12020310050a0f050f060901140703090e0109020702040f0903050319 71
    0x5056a501d694900c0d004101d070940312481c03c019006104442941c0e4001c5e01180001c0b10300030441c00780da41384a6000c642c40500c406050768003120124000400010144810609403815a000300d032900d40000c020290f00315402081440b00b001d921074101191021810b1860802c511041213468840c604185000d08400d401c05030034402d00105000e01030480040072800c0074400c0d02990fa00040110101044035050020042a6000326845000501d00000f12070750001d0340e46210750400c00640c841c2d000d41c0c1c0782404091a07410300001403041d03c5500381328191a440c0c007040e090050850004c0c0051038100805040328a01d600480850400302081703ca40c409041e010b0910300382d550342c03400e002c0d014155902c0b4060040d400007018617a0f030300b001c10480d001c041b810303150f40d450144c2401040140d5480b090094040144454000c40d103211135010590007002c07420300240c0c941b11540108811240e20340203502201e846c05200100094204042c1ca510001004417140b40c0d071501645880036000c3c0c80 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 265116663 1250 265115413 265115423
    0x60e0115050c0c130f050709470304020a2c13020d03030c030b01030e1b062118030a0f140906120a110705060a050709081524010905060f0403 62
    0x13404007004080260703c10364415100041c244840c0c1c54a00054910407007a0140501d41c000d02298008290044003000202c075080700401144500350202e200c01c842d483d81001420701400006120a40c0703002c8107a200906000280d079010800555000041000b410546039241c0c901d000004d80704011640d140701600e90081c046151100b0503150040090a0180141c40480c0c03801418040c25480b0307115195403030b607581005000d80d0114180b208071051000c151158402800c01000961a5441c010403054040d030001c844600d00300554084507205100603000620717401403090000155004a4603820f03034019082100084400b50640401485a014210b411181c001800e0414100c064002e500c45c001d03081c820080c0e101c841d25500d00c2481000c8005e0141e6000c1000300b030110005511103500300f0100d003085a0181e41e0340c4080ca05100040c22003038010401038081051219501681c06040004c440c21111500c940d000043d100d0380b031900445014030700110300a10704c54807280c103c5001e15000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 265117913 1250 265116663 265116679
    0x17040f050312040311010c020703021c020a0f06020705040b060a0f12140f0c041508130209040f02030f01051006080606040b13081b06090418060f020904060e0115050c0c 74
    0x80740100080c610b054500300e00064102000154070801846014480c400a5018000340703480c680801c203a6001501e4000d5008441ca204003005039a9046684001d02054409401141c03820300c01a00b4803a00354403c0380240d08002040c8000d07580d6a088032540002410303d004080c40c1680201c8002070180d0f030f0b4854103450b00f40c01c00e04020310340304020321a6110441203602a900c10001007400c1c011032040c00740c0004843c81c0728880c180107500039540403d046041c03400902403500010000003050741c05540041554006a0a6040c02d1000c9810318503c80001d102a061096051078180168420a0200300c03100f40400c0761070365000120390080070554003003915191141240104000144280b00ca648100c90183d141c401b4460720002a801c402071003070f810046071070240400340a20329007580712980300c00c0350000040c0c6641308410b90a907041d04016180c002e501c3c1440100c1322903070004a8000c40c40c2c0010071400e034001c54102c030320407600d241581d141d10b1040c040320f14007812504016071120b45 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 265119163 1250 265117913 265117927
    0xd021c06020f0c0724080c130b0408010f052202060f0c010605030d0c03080c0c010b0d030e0a090e0304151808030304030311030f010b1803061e0601020d17040f0503 72
    0x102d5018091012070b0303c06644900307030364483d9440914600d850400e07110000f003000f0f10810380540360443e0f00007031a0000e45d10308002510400c4011165801070032049030041020700161401344034501d00da800c1d441c020013007401d01e61220003042640303a414402d41340186440d1011074981074142c031504140000c8803a210f02107481000d0280c540da0040500900c10100c40503e00d9110710307107030408a90192568209526031041d40c1c90280c0c00700da0301480c15034071180b895083d031b2078800c1c800101c64002d0f941c8100300c04400c01005121111035101189507410210180c0040c60084101d80441d90200341c1030803981e107101003e845000b01c2c1350f40c0c0c00310400100000101c03400040700441c0308910941c0c04000b03654075802020014001910903040030b040b128014000114003000618a4280d0742000c480a8101d034130020385840d004540303c41c06962090000035190700310ba104075070005030900117001c484040c00d20082190034100c80e081c0005074004046024003100001400c0d079150440e05907a96810 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 265120413 1250 265119163 265119187
    0x40b0609130203090c011e142208010615080c0a03150e060306060a03030e010e010306080f010603061d0d1b0c09022109030706020d060b0a020a0c080106050d021c0602 73
    0x1086800c0c00c001c0c061035611701060b61060000c3c1000804400100521082d0607a040b42d2031502d100220070b00103410030402e16403140c0792a03080c0f0484125401103284070304019130b1a082d9005a80008621501e51070fa0364200c58001c01c00355445003d0141c1d09444801c148002c50241c40c540b1814019501280c0000c141400620043d500c2400c051303048070b047d41c4600051149100c0f5a21016002651095007428075610904000383c0418051402050094840c1d000a0400c0b84c100d40403412a9928241082002414080c0341e0b100c0e80030002514904c0d4440307a5258940b000b0100000c20020b402c19201d10b0091822003800d4800d401c00c43c245881903d47c03101d0402944552212540c0c00011041c0480c1108400162842410303010065030070003805503581c0c8040c4d0480748000d141c01d905e802000c00c04115000c044c144485840c1c0c0148051902801c1102c0440310340d030030400c0142d041c4001480b0a44a8004110b001a03050700d50103220b086d0140f0400606012100c02001d66000141c0344100e40 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 265121663 1250 265120413 265120417
    0x18050613080c010903110607030c0507090c0905030106060503010611010609020307030501061101050709120609060507090e0708090304300309090e030306100315031a0709081b040b06091302 83
    0xc810300704503072409000e24015a02c0c1034652000814407008244034401e1410500050614544207050184000d8010f5544d01d0401003039410040a0710b030350b01803c5240d203610107892002840d00350b008001450a1440050062205016243c00d01c08003c448a540c0d03e401d512080061603240c4d002c540ba4102210000e001d00802c1c850000084c03071009804e074400906106690003000140c81d900c0200e880c0c020032112050207490242c0391140e491000201203905030003504d06c58003031036403816513243c03c1ca540070105210103090401003007040d1080103402d61300041160305036a0440038080402d2010340b00a0501505043c01700c1205088110107400c01d6088000c24040e0307074aa14051007806458804d0320740c7c82c00200e6180344d0003000c007850000e03254002d5110030000100d02851581141d1240c468050303030844040710804c1e0500d00c00c204014540c0c0a417003040940240c1c000707020003181d0704445250b0100a154164400c0d5940d50088043c1da50341400c4512101e000350100011500c081520700080d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 265122913 1250 265121663 265121669
    0x50405100509010905370509180d180b0a0c05070501050702090c07050f03041e09060b0316021f02070506160507110607080c01090c0e010b0a18050613 66
    0x1410103032030100403041c02041640c0040106039600c1e51098500020056003c0809408078a09600683c0031400c0c0c5100452002c400000b030b6211a048507e400c0074445030805c01850200e100499164070f1905400118030b50300c1c900040e01d07040308001c4070130aa04541410b00d5101c1c03103c1d204001011040f582d00f100ca5402510f001d482512a415501c4d001900c640c4200500294030040c0f0303070f0002e50084130381c80242c04014041d404a0307a01c074500b400c0175407866000350080102441190522500484030054540203410501014002c240c03400042000f24003016100078207400180340c0c4140154820400840b01d820190f2801041007903c5200701c009601c0807600340d6141c09182d000412035125080c150b0480384540d0340d003d240c00c580c1e40722141c4002441051070340c044010062030f030108a0032000303018804501d000001c3c980c0510702d480c0754282e490398000d800540c18100100308002400c01600c030382c5659401c1c4060a6840e0425444207500260040707640182d02040740c11880032130345041c1080e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 265124163 1250 265122913 265122919
    0x4081e12031e0a1a04020c030901080a0908040b0706050108011107020f01030b030d09170d020705130212040312150311040b120f010e12190f120e0127050d030b03100c050405 76
    0x5480788101030100347c0c840c28044d54020351003000708400652280103143e902c0407144030000303841c08040d0382c0e002185e40294868910510085849070510145202d4640106043c0000300894081c11000041901541e100a4072803640742c4038004240c1d02a030404850b07148020b0a0b01c24080880030080c103042407a000e58003000501c0038040d2020078001034005103203801d0750024403850340340000b004420609407000c0d101d855028002a00c0c480c001c40c000500072440703030700c401d5940300d030701c501d108100c1d0b00094502c0c1503d107442c1030130404980007000c50220b510b0300345c40110b00d000280d80420800744111503c5030b6070344240141d0140082041d407250200c807940005a42a461541e0310800d294001c503071509082d015055001c0040c07034080c0c070645080400da4141182d4403c0030441c017200300c5007015460031242e5124902055584503a0b0f003555044112032122250110b450340b1626541c08100e06e0071014154ad40441050941d02002640300034040071071300f403100c4142420028101e030098400c082c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 265125413 1250 265124163 265124201
    0x5010b1905030103021f1707050315090f070315030c090b042003060d031202160312180f0302030c0a05070504050705040b07030e120d02010204081e12031e0a 69
    0x1035514414000c490482c1d40003011914039118030301c1e40d40762841083e440041442012a5a405c48000b084103103489203046403030781038503460000c3c060b8480910440d055442003080c0010081030746040307401c40350008050700c0d0018041c00415000380316030400c2e41001c1c0102c4112480014002d4498004014042040c1c50030b01292182d194902c088048c42d91000f0000f841c1880003034100d06106139044001400381c500b940f0b000c40074007501ca003240c2c04100000d80e000004088181413541008120281c0b880794001040450402c00340b100b002d040381d0740c0040402002494480a040c400c009807503040c4000b03400d03520308990500e0038035a01c000a2103040e014608160000e426140681c050b41c04944504000c1840c0510654040707441c41c949225403a88000f0007141004680800c011240c0c05d40000c1c1c00051780c9608104200b85409184002282440510a00c00071722404c08554249a4007050072000d803a43c0312101c4072040440071180142a2114000400410880c10b0300080000d081040d4298 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 265126663 1250 265125413 265125457
    0xa0b0613060303081503071208030703061e03170f030c1b0129010917070905220b0406020708070c090c11280b011508010801020c280605010b 62
    0x80140d0300e5912024004c1aa5400002e107607800044108080c800002c040d50b0b50951030b40760224803110804400c0c3c820400c080300300840640c140c030919015103c8100d9080c0e540030700c0c800440d03500d200c0740070040c443c50580c24181411084102511070094001c1c0806440f480c0c040c2c86880d151b0081700d24000300340c8e0708000080c80b025041c0b184070381485400652080942c42c0050075211008058a028100f002410002900c01d094200c041c807403d0540c0c000d800120b00c2c0542450a03214050b103607071060501d041e52461030030380030700d50039a0059010484a2442c0c0e1a030070032500078080c80c0b1002d003c0410006511041004c0c034820302007510070f008030803c01c2c00640803048a00c0d24061030320b1682c5601400c101403a406c00c2c03051050b003c540100c1c14070030030329042e035600c1300c80c510030ba110700c60106002c6154224a5080b810071400b40050700004c500b041c00d4900c1403980c5182241c50102030362413a01403014513045240d2040c6015030400e03020300c05940c1d14120000154000b969400018802039007007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 265127913 1250 265126663 265126699
    0x307060306120b06030f06191d07030b0c0f03010308071205030601120e0705060c0601091d07090b21070302031b1f031b021501060804051e0705030a0b06 67
    0x40e189100c02e159400c2a05981d1200801e40c007810fa07981c544559928068026003c1040c80e22840d80c1e404404c50610041042e20f007078035005e201200081031010502180c0c0480040d44c10116038200f0041c070300b1a11803c0c408902c5104040c25141407680010010007400000c4006003050342c414406240c03402c6c0c1d580000c46003030000780c0343c5500007165181314054030003290300010000003c507001c1d9850103513a032001070700513070200c1d50702c4a003130304104010000c4107200d1061481088c40c040b4884144441606600e4846100e40201d903c040d94404502d21251074480c1c80c0800c041a0400024041401d07410f659520201403000f28403d10401416103485010303181c40c020b03808000b500b07041c44001c44481d1200840d45000b03401007010341c1e84410807030580540000c00544405900a46802a50104080714104058101e0b400b442070101c01d0200141d80010151202c00c1c07050b07525140c000c2d8040c066803d0031015400300b40c4c90303c0340341c156406100d0b044855a02032841210505846400daa004c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 265129163 1250 265127913 265127921
    0x803070f05030c09210307060e1204080d030c031b020616020f03120a022104030807020a0b06100903060c020d0201050604090b06013009020102010e0708061302120601080c03070603 79
    0x100fa03e0403e428408003a0506101c1c0e600000f06240440a003c2c414180c0c40113031454200f440d080d189585c5540d0702c5010010f045c0803042e102c0301c00b10501403402d400c04080d03651b100c203c104504101030b558403031010124402d5114900d16030014800c1c40e80c004192800070342c0c540050700d000701c002c000113202c10741e0703a030001a0140d414040711005c0e5042052940000d8402a0020040700c0115000c04c481c00c2505040000d4044014070b20015080034142400d0041510070010b0042c015503105400003404960100380b440c3d401074003202ca00810f40c07501c071003c40c1c5220403540700400050516403c1c402d400e4011440900d4030780542d00812459454408001c19034450f518041d013402580c0c1c0114000b03500c1640300042d800b211420240c068200d441e001001d4100c1c50000c1c1c001182e5404400c011580c1c207000d184100e060510040c585542045100c0e13899080160075046034842c61301c410021034031101c005000300007a000030b5a00303540c0d6804955845401a40046102e03004180001c58241e00a07c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 265130413 1250 265129163 265129171
    0xb06040b030d020d2601060207080610030b0a020d200903010b0f150f070f11090a050402030c120c030a050f06010b040b0d020a0908010515190e2d040803070f0503 71
    0x100502c0701c00c0e40080300391517400034605400c0902040c00c910708074820301140500e000b00415801042d00c3c51a2440e46400d002c00070f481030342580e031212010400b04074072a030b03460b0b00058924001a40c41380d004900a00400c104503070305502c03000181e1225484902d201c01360100c11020342c024844d030940c600420000e030300e00d0410b49038004d008080ca0381d201458100900b4500c40800213040c40c01440f52a070070310812104c5000c0310b14100c00d8520102c207042c103e43c007035007019030407030300388810300f80380d40085c3d110a41d0f0342c041030040c100e4100360f07000900108680d2050250140c29104044880d00b0074984030790400c07400c102c19109000000940600300c8080700c0440c0c40040c401800c0510000c1490041c0d40a503a2100421100450200703036450288182801030f0b1001e03403400c4142914200b0310000c5150b200040c41c0d080a911000c118100d80002041d510406045000001e0922000043c08014491041c83e91081080c0104410019400c0c021409003600f0b48802480206408003226948000c403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 265131663 1250 265130413 265130417
    0xa06091e150b01031107050708010c0f02030d0e03040f08070512160603050402180a050702060c040f050609130c05040303030506090103020f10020a080d0b01030b041401030201200304030b06040b030d 87
    0x20100803008151035200c42d005200524004c100114940040c5a103504200c40030741b400d4100349020010381c0e00900c00c2d050066518245602c5403110040301079100d014068080303007840d88554980c0c1e20b44800b401120040c10485081d5a203468a8102c00359582c402401039501600c0c100010036507030500000c2c0b05d01e248031281d002c5102e041c10400101d02405000e40100e070000100300b0060b004a609030f03000b43c8180c4030380100095a242c60302d4003c0c50040080c2030024820780800040c40200711103070040060781c03001e480c03459480034004081440c80c0c042034014982103180241c001300c5103070f00030024401c99019a4040c022a251003041180e0304200303100081d44894034581c1d04480341000b641c030f540740080d50b0041d14201526500c07110303015804861440750035503480000da00c4030343c0c02d407207040410401510200481d41107000c0ea544040410f02001c0e040c803c40342241c132000300304650101a140000c100b0740b0340f04c560f0780ca4400090b10060f988184a0ba041c0340070510300e41400503012203646d03026 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 265132913 1250 265131663 265131683
    0x6060f14010813230a080a03021206090603071e030c030c060914060a03090f1407050a0e04110402091507050a06061d0402011101020c1203270715110a06091e 69
    0x4024840e6284c1070114280d00c0c02071385401d1022921040280480304241c0d00d000d130341c07040301402030b540440001304a24490018541402a00e1720009085000e035408604201d000c2c41029040c0b125404041d80001c0a44120f440040100304003261401e0841c0c00a880d010f8409403143c0d600c04008000280c1c17a60415401c0c0800e004440c4690420101d0b18000c17084540741c0c1d80c42d41c84214480c2c9a846600541c3e42c860002080360b41496031840d030080112680700768960800d41c0c0e03482c84003c11003115a10843e0045040703502036070740100300c2406849410000e9600c2c011845c202c0e0700c0e000c2d01e02c070945460746059800038841580c185440c0b5801c1801c2a402c0305517560758010f50b4004104030010802e59402d101028003001c040141111002c0b510042544a181807140d00c0314031554941c101c00314203040910f400340303480c00150020507242100d03905040c004440004981d0720984a007080c8c02c41c800d0320703030300f10038030030304d0390000d502c0c503000303030441031407061061000010800070440041c841050 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 265134163 1250 265132913 265132943
    0x50105220c030f09050a12020a050c27010603050702010f11030a0908040b0f030604150510081f06050703020d0305070905040504080f0a110610050109060c06060f14010813 75
    0x6600c1080701000340d0078001240640500710307208440c042c81c404c9809501044240f024080b6a10303660001007403a00c02451458602c3d5180c0752600400ca45c4103010b0001504c0c06d0451140000003801110120400981e0542e52a000100640000e4a0b2200507501c1c0c41c0d100900a6030303a0040040032140441c00c103255403901c8003240d0051100c0842030310a044103100229051346107900420780c40c2061052140c0383d0900c8800c01c001ca500001000c100038100040400c20703a00c0c2e4480c0200c40e10034034105002165103184851483c24024804a0f0b40c5054400f40410712681150107080b801e800790b82101c0951100441c280c044840954051012401d213420070001c5140641005500c0303441100c0322400c040e2200104030a6070407089410010400417201021405010800d06034410390b0345245083d202e1a1800281a1248a010395001c00c071400b00401c05020320b80c1c00100040046d2502560180e5844e0515110000c0030800d0600054600000c91a804540800d0386102d40d002070041c0b080c074178 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 265135413 1250 265134163 265134229
    0xc0804060e0c01050711120f0d030f0506030d050a21060312031509020c07030804030b0103031220030705070f0b0a0c0815100915081b031b030711100f050105 69
    0x540041c183d900414407442e07c7c85110040c0b00040c14424020020090f0025180d03010301a102d100204003013151502c001c10002d40e800050700641441c0d01d00b05141d5803401d101c0c003224800d100141c84c080c0f1159214004092500c103a000404403030003940103003140c40c50040110b0683c4c0030040b400c0007201007000f050014861542c028140d1054107000c851907030350340e60344550a0707403c1a807040d81c20300807072401001410b810002130f83d04804220340400000c0000910002c40d0030646c030307408010280200005107014020012100d50360f82008511142155601e040052514111003401410781410300f00d0b180715015125040c061110510412050844503060124121203081c1045c100b00f580100000c0051900704052004400c59603080e02c42d01c0c08002e1410b0708010f9880c8424410b17010010441b100c480303000048110080c50704119942c0d112a0803c8401c1140c04403454801d00815080326210310aa0340b0071542400d0014041c040b80c4e90305d00812209040030b9052140c0f4120022042a40031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 265136663 1250 265135413 265135433
    0x4050708060910030c08010b10050f03040b041a0f06040b040606020613020409080a09090b09160804050c150c0607020c01050706020d18060b090a02040506090f0a05040c0804060e0c010507 82
    0x20011480f0b0680903580e40b180da041c0711481c0e101d89416559400e10720004e0406e1403091060041a05055150039840b291800f05403000802c09800228043c0c003080400c81e14081d1064809841c82e64102c0a050201c844921070030207941e030303521a6180c03180c44403076820503004000496001e030f0003410403075880f6041c0c6d0100880843c0126802070741e40000c0400914403030044c041d0a110383d9103000025040c2181c102c101d5030351201c82403003040c0402c02c004034110321940745031300000540b6101041d5111444d06614204614018990140c0c01e80c66075004080103a0241c10941070040441e041500c42547c03da8594855500b4103002500401180d408143c4640003000e89401c000000560b0040c40045804e4440d50910111042c507216245d109492405c0d041058000b4a646c0c001c62410f03241c600060841e204228881d4024042c0e003454030324661f42c4c1d014001c01403001410600103272400e0580103001000445046904601d08401c032012410001146000c2c4039040c0c54103480c201c0641c032101351031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 265137913 1250 265136663 265136671
    0x204020d020c07030b04141f0c02010e190209011d0f04050304030203011b11010b06041802070206041e0906030210120e071e0602160e1f0311040506040507080609 71
    0x100d03000c02c805000076104100c990010342c0141c41a02c42d605080c82c008100b20f021107010303201c0350f0004180da417041440480b056a10f041c1400001603020b0385580a0b405004090011038146c082c808070964100002030480058a2003100c040314160b07240d40116488103580d00c0d0039075441d40c5680c0018005114422144c0c0c06c6400303603044a04043d640d80c0002d0a490008050345c282c104007451860306d06410404030040300400200030300c00d100755440400c0c2d190141d4400d00d0b07544103506076161b8155400364102e4034015009044a581d41da01d542606250b00e0a000b29900a0110542c8c0000c00c1c40f80c41c8101025640d00400d01155155007070742c1264180000803a5406042e0341e20910440424100400b200038100620b4842c4080b41e50300d02104110010b030300c0402903403c44803140700340c003032a40010020b484517146840309035221600401003a114000f410100324010080c0842440f0b450506015060001c0f2014000f641e165014041600d506844a50108149070046180e5151203a02e1543c8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 265139163 1250 265137913 265137937
    0x110304020609121002120f06090714220807051207120c050301020c0c03060105101b050c0901060315060e0112091e0c210302031b070906060201021306110a020402 71
    0x240d03e00850709904180d100300303018485603800250440c0300d020b42c1e08940ea022020024002e010f140800200b103074858000c0c01c0c00108860711140e0240c07841e03100182c802410746442066251540011600041800360007800c006104641d800502440c01112086c5c145200c00c010b01030040ca40fa6900213828843c21046130708849401c000700c1c281d2400d2000e000c40d80d0300d0500402825410030203060410006800c218041c04164500c0380310075801c540d1950160f410001e10319030301549810403a0030305801d40d250b160f10003000e10000400e20341c11340109200c04010305c0d032903c406580e40420340b000880454414041050a035003442d044d0070b640d02c0b20b0b540d00d0103001e2500b000844250a0400f007080ca10045816a0321003009114165210141104100e200f200d007865000c00ba0f10040d50324090b16103503201c1c0d0a16001407600700e080030300010008140b0f659080c0079071034540750064041d4000600c3e08103074040349440003c03074034422031800000a43c1c5001418204909400f8007019500150b074103c1c2c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 265140413 1250 265139163 265139179
    0xd020c01061a030f0a0e0d0c020a0e09060a050915070f0210060605070606080f12030a060f03030809100c0504151b050706020d05030402060a0305041401050c040f09110304020609 78
    0x3054003480c01084200c501e20b91040e59685000d0010508400c4081c0061000364504003848031003150014080c8130407142410400101c482500c00070b1031001e20364115003001c0301d0076000e000031000001042801400d002c0d1003070050343e82c0c00146569401c1c5ca07031106004180d110300883d040a024504115a0700c030148181c800140000540c0c1044d611503520140002e800018a0400e1110602c00c910207880c49501806001c1c2100740455510075110762100d40210b00040868503920390382c1d1181009021a00d15642c03d00d64034280076100142c2141c84c29928001c10071044c2c0c9a035080e21681800000f9a00c070107042c107081141c01601c090300e600c0000c0611142c2d001c02c2c0050420300d4001054288604004c15030107003081d10080c10000d01501a1092040034024800160b59078030641c2c00c0c14441d442e00003803d6076a402c00d440501c0c1c01c4100360707089520700800cac481201d0404000740140d8119401000e0f4455480c1110403c4400c20300458242e02d400b40045001480c0c000c00510503100c00401000c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 265141663 1250 265140413 265140419
    0x6100e01050d0e030c0f0a02090c0913090305180d0308070809010e0f0309010f17060405060a0509090a0b060a060c1106071502090906040e0307023105010e06150d020c0106 75
    0x2100300c5103c4820003040c0d41c004569444050070401510781c1203003040024040011699010a07201c0c2c0019000020407903021456600503222822281141c82040009002d2080315040191803640301c40702840300320100d003004103071908002da5484101030703142c1c0d03c4000c035650381d1804840140001d48811301c19500e0b860000b2070a03404110980000142102642c0d13a40e40d0000090302d002d980f01070800c240211203a40b500101482841d180e0300103000d0354040f94595980001942c00c1850f5040b06034890240824054591000603d80144510031004000161a00010042890380b240700d20800100c1b40078104000808034540a1040e07038026001c0343c1420810b58507403040301019447c154080d070f40802c41500c1440c08189407a0805001c1e0f174108940d100d00d0300300c243c891064660103405007103007a41d05d800540fa0f090001840340f00c000d000c00a010700450406000c0c0801780305540002c0303403a00100b61a03151500c0c91400a191280c400f9150040c1d0661b8100a034100382d42514441d543e070303c000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 265142913 1250 265141663 265141687
    0xb040606120503040f0801060b0315031014090607110a031b05120c010510120b1509010909020108010b03060105161707030f1b0b0601121524050306100e0105 69
    0xc0340038450382c0030b50707102d80c201800102e02650541c0110340580c181101000100d1414003180d400108810310b200944030f50341d010915141d0f925004880c8240b400400c0c030194903c00105601500002c8251107054441e0304003207400c00314210510080b900120110070010b030045140060b800c84205444100a5064075014184140c101c0720701d40740f42c00050842c04118017840340c2039104010581140c526030800700f41010300340384000c00402030b1060502003040389001c8100000038a6000f405c0d110550f0b1141076000141c0a610b04c1280032514440c0003180d0700000a05482c41410b040e5a02410000d645981d912241d60b600426200c032038011480722045180c080041030294080e454003888035043c0074000f05100c280301050303130303c3c01c0d1f4a08141c000516640c1d0400e401c54424a4004003c2510040f604c00038114200103044401c17550030002079020780d00110380d2281d0300c4c1580e0f00c20b200c8503a080039203851008071082c550040c150001c81c00007602414480002140c1072501c241040d03c501c0721 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 265144163 1250 265142913 265142939
    0x80403030c0308070201060608011a0c0708010b030111030408070618050d080610050306011e120905010510050616020402030705070203060a1b11101d151f050105070b040606 76
    0x41500080c1d18100000705240c1c000960315003080640c40200921031514030002c016000601800745200ca60502c5c0c51043c103070120950301014515010780b5141e0346c0e00e4940c0360003800c4204003107019500380040d070440c9202090039644610342101ca600c0c64480300745c2e02d280c01441071551200b0740350707036840700000030810070413800401810a454820f098207154042010501d0114413100812008008000050b644040b82030182c000f00203011a43d40c04416090300d40e4040c40700324500407480c00f03a80720280041500304501807802d8684090700203449005000d101c0c441c001c815007010540c0201c0500604041d4000c59000340d2502e441400d041c810fa0000341007800544601041c1610383c1c8459001c812181165500d030242c80c00c5ca075000c010b0460819803200e001c502c041d00e0455481d00c481c00d07404604440502c00c800c204043e14501060500e465483c00c0080c0d03082e0204a90403064403140402e201d8040040e26416110542800c006565113020b000b8004c0041350f100e80c5514000885a00c9044 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 265145413 1250 265144163 265144169
    0xa090b0901021603141504030e09060f0d03080f0105121b060f0f120108160623130609050103090c33020304080f0313030f0c0f060e010e0d05030f13030804 68
    0xc0d2041c0c01c80c010b1501c25203880199141203a186e4205014000001c0d0402043d030759451003590750903a550b03504d100040244003268040b581056400041801301648041442c1c4292490070180c0c4041c0d80b00c82c207020600c00c00740441851584503032001c0b28480c0d03802066207034805008041c0340c1303022041f4035900b00c2600300e16205542401c01051020502480307918150141003000700501411517171900c1d03160544480c0c481d400c203014400e01c5860b0120910a40c141001c0e2030302116a580f00c1040944415191843c450340b400180c0f4800c0c08165903110f80544024640c010b08042000c60a0041d003103103801d114030f0345880400020801c280c21a400b0140c1c2c020602c0c035038001c0d5458914252a450500291070034078109a0020422000c0301c40c5508042400d981e0000781440c0c4100302e82c0b42160340b8070303030a0f08a0810b41c00d00c0000000d07010b501c500890107104007030340c0b94a500300451042c4002c10240000040c001d0f0001e20094918564100140400044180b00c6204203980c03a00ca0714080c5d8806c3e0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 265146663 1250 265145413 265145423
    0x4020f1906020f1911240f0a0e0306071d030c0405040b2509030303020c1c051309090803040f1505130210020a05070b1608070606170325030522030510020a090b0901021603 75
    0x20610705d034659040150065900b105402900e10352178601400dc010080c802c80e202100c80c1030241c40c403100c0c4c0f806c102c01d00030104050003c00c4071b41028201890001812070344e080281d100400001c0700d10f00001040c90448490f901c0307151007581103070740130f0b000b075042001413600740d2141e404d42c05807032004102c3c141004101c90f100c4540e03a200b038803000310f107440c1e140c5c000025003401c20444100089500007143d0b40580c001e903400182444901e80311040203180500405001e042009010350580440c9000700028030880310160312840c007001c04d903112204440042d005400405040080c644404000d090161400c10242120009503440781c0c0190020070043e01c00c0c9543e02004c1c000e0f03419102c0c80f140040403820065041c425081b901500c0105805003861680d1012458a801c0500441c1541c600410000910361000c080880c440408103c0341700131703100740c4921503403e2260301c0e403842101d032111840d642c1c06080509054a0400c00d5000d2603c4604500c1480e100030041e01c451519540694480c07 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 265147913 1250 265146663 265146667
    0xf021c0501050114030307150213090e2107060b0307051005030a060518070f03060b0a120f15031e0b2508060904020f1906020f1911240f 60
    0x2908109084540503000401c064411049144003690700200b41c60078a64070003024519140da681201000e405190364260940107000d00214540b269504151a06400d0030200c5840800000b14012002111904a841102c04000460110b61240c00030342800300c0240c12640503d507210007203442207040142080000e2000700611101c03a981c7e0160345c1c02444d0485080d501018803681500c1d0005024148005108894021800b0305000b070b003041c002410004482034581000c0c90014242c2c08100441250303441c60445243c000b42e11610800c205030f100701003806655402e60791005503410200303505048a161352110400012004643c1521441c1103140d12000014081c3c1950030070304c0f200c80a0814441d52004201d42c907101c2c041410b034002d4044855421240c101c202242120300980245080d014101501107481e41d00000d00080f000703500c9044030b261550400280c10f0602041c0300007854200b0b40c010350384681c507000003007841c0100500c0070140324048078018100c51390300441041a07e2100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 265149163 1250 265147913 265147969
    0x20d0617010606023d0605150c0c0a0b0a0f0e0316030209070c03080714120f060a080303010b040b030403111506041407020a031110060b090405060307030b130f02 71
    0x414041e406a5540380010115807a6026008161000c0110014158002d01c500c44178400c24441e04284001c081c054400901011118400f030b2641d441204204010320820f049958907040110a1104965044d102c460400200180031607000888180744010003090400b651400da805022200300440140079043c0020300e184107100a004d4010101c10a001010b084103010075084030310180d2040151400c9078440b90304000e0008140142880603039220300c0c00082110f00d132008206940190380896500b0482582c41c41d800355288800d0180b070100503400d00080003044403800246820610a040882003d40301034416440d141101c0a00811450004180302d99410284180610305019841c240e4151400150182d07440590340c00007000c0000608007001780c1007080c4000e0b0208030f0f55160a00000340d8544012016070002c1890034400d07443c2002041c810710b4009903c1d030071203900140b116640d0351290b03030030108042c0004080d90305a5400ba070000050f0303a000101440c403a21440741d0320040344 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 265150413 1250 265149163 265149167
    0x504020f03061014041a0c03030403020601080708010902030a0204020a09080f010207110612060d081b061b04030b0f09010209060309010c11070f090e010b04050412110c13020d0617010606 82
    0x482414240c09001d04d4038501244014800e080710140c0e03607403500742c0340030b00b0304031840d80301a11511300080250b020110910040640c04202d07503040301ea1040458038465240c8c07842c0f6003210b48014000b54903138040c941004c01410300d900541400050703824081c1103a66240c950504040350288481100d940c0040d2134010030241444200400324143c40b81401c004041e101811503130006807d080c481c148000030130040040c08421151800307514100200c50003012402c20f582c400301034840c084440c440309001001c0100d1030059804072604440b02c6c00d00ca0b180c000d01c100a850000d488081195020002060303e40c4407140114000e100d08400041c00b681002401444801d2408010303c0b5038100b42810409a4440c40032003040d2400141c00182d106004200c00f801406948002a00142088108030034445540381d0550396000796160300d03a080c20700606c403a860700703042d500555200c1200c074150120b0400d10780c06008040d4001c90700040843e2180641c0c0c500d001c0410880501c0d0703444030800d001550b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 265151663 1250 265150413 265150429
    0x180618060f05010b0a0e19081e0a0c0e1f0e01060e04110405120c12070e0703050903190c0501060b0d0f02030402030307140a080a120e030a140904060504020f0306 71
    0x56800004100720f50400701405003a124002c03d01c0104101c80d010440d80781c0c0c0c1d01031080b0908000450001c2226a00d1100c0d5454195941030004c150030701d0041e5a24022000c540d0242003980001e80134405414520103204510018001d0070300700c1c041004081508400c4201c0c400540b81028000034190b252250060000741c012801c13600607814405101c00000703009040d81c0980d04129049404402c010302d50a182c030003d03401c203503813085072580000030340100464101c06503440e00360807403104d6030342e2042981500c00039202c42c10207174810800030480c2d0b00e0100a00405420610300b038003990740292115800e40f00190440358400900041c440c83e91901d49c421410b4505101806500b0b500d060340000e81c982c05541e00180c1000c50445400340190300c1440521202948401c1036510340752160001400461161000e8828074903103002403585d02800001d88104003156a1580d003480050301c901501d07038100d11912a00301e40c0328000424240c0c2c440c00589105541982e4864881c40c015080040070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 265152913 1250 265151663 265151681
    0x111015050405090f060136050402040c0507050c090c1c0510050a140f0a081002190e10030e100906090516030c030809150d0203090d090b040918061806 66
    0x6580010340b00040400c011451030b0454140c40c0045407017a4200d0803601070301c1f01b002d10340301081c00031102424200b0102c0c0d000301c0c01a0300a0751f0070080021041010784551080ca000504164400301c0101124a070503140300750b1100e0646812803d003003440b690004610366401c0250f0b5030b907407210100280083e03070a440f18010a400c60f04000c2140c5080103002101004c0c0d41c4103030043c1e400c0c082d00c030207640701d5090001c001d20680b021642c54101004c02d41000790010520114144e60139648030040a2283e00b210420003070040c150b01102c0d03000c5005174003d10b5020440401405104425104140386103c0c3d41081d6025200c041031846e80340c50076900f801d0700b2803050300f00d4000250303046c404a03060290003070a49a000c00d13120b40d603d0746140002d014110b820942c3c00300601c000368a1019010036006140124208012a40c0704c4001c524180c602d2800c0c2c4c018003c0d20b1400380010040303e4001d0b00143d851440c800c01c0207a011820b5244c5505071200011000c1a08058954100070010300b842181a4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 265154163 1250 265152913 265152931
    0x51f0e150316060e030c040c120b0604080f160914010504050a0b03011803080c0313030c060908040f050906120606010e0a0806180d03050106090501030b0f0904120f02060c040501111015050405 84
    0x400413007450181071403001c9e0b20525a1613556620003a0b490b02c400b001c0741d024166040845002803c8a00c98940e075886010300d0040d110030103440090303a003900b4050034001d5081911aa28241c1c2031005101c01443e0041c020000b60f501c5100462990f14217100d0300c81c10b011449002c100546003818040c5c95031070302404403900c40c1c00402c10008030520015036651090b0b41454032001035031440c2400b901900e00c9841c00f84c04003000007400204148002c064404a5030240c07040051a40c0320030030808800c1b0155090517441d040728001510543c4141103460b1004001071000c0e440c00d468080580c50a042240c20b0688a2203210a15000711030402ca511566031071440c0a100d50360400c440205010748030f10802d4103041c0c440c800310309182d4500d0301050061001500b00e071464a081c4c2010004c00ca9161101004502200c07441c0c09498404103c4911500340441401d2400e890030307004440d0310b4040840310059028a803007003c00245680075030268000e600a024601509020800046071005050a00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 265155413 1250 265154163 265154171
    0x31b12020f1903050a051207030203070e0612152115060a030c0501050a110f071401020a021c0f02060a02030408070b0a080f060a05060d051f0e150316060e030c04 71
    0x158802c0140c00c055050b45407424503180c590042c01603605000b500c05103940035040300700300712002d03038598051441065207644200b150b1100c582072116500c188454a45812a140c0000380e42100c02d030500f0b00b442d44081c000c0507005100c0041e11800d450840c5450449800a521920b42c0c50480c408554004804031103142d20705c2d155a4589a60350a1841820306210010840b48001d078014005c400c0c03e0030801003a41c014404c0800580e03142d011a0041d42c02000c1c1c0125000c44a510008003003034507550140944158174202c00d030304407041d540400d085403102d0a0f41200c50050311004058140900c580d001940c542d03042c0716442c1e040049542001500c0803060010f001070701d070712200c0075030040b003800c80303400741c607141d06d008100c42071056000035800c410000382100c00301c41c0c0c1c0c2d40300e18880c1e414400072100d00c41d480345800e621041c003271182201543e148004500c3c00300c40014541c405030340040c1101c0034000d01c0303803c42c00c00b04e206501000100d1140155206a07040a200506090b901120204 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 265156663 1250 265155413 265155433
    0x4020f03060f060c0d0809010b0a0b070204060918231f060602190201030f0908030106120b031207080a1b060e0105070c0c171009052a06090607031b12020f 68
    0x40c5d0703032400c3d1804c0ca4100007851001c90540c4900707501c440b00b0000094024041c0b1a00c50152468a44c0848400c038011460440001002d070620310818615031601c0304002100403068480c41d48502c1d01000a00700103100c990400c0f0703104401c00951400901c19510302010014a800002c200d5959a001c00155001845440000d00c4200b0f603c003005582400c000403075940052001004000400700100300e15400800402c0043e008203075180c042003290414072003054598285a160850016002520201840410300041c0000b01600d422031061405096144055441c254005038241d8242e480030340d03401c1c180c41d11107001c0c040d083d400719103424102c0248190f0742d200010018240b1691500c0d0f80c980700b40a10048050006040c1d401d661b9806000f030140300d040c02c40d10303140300029055482400d13000026244003a03c1c8040b0703c0c1c1c00d004040b01d00340b41c0b0350703010300000380d0000c0d00131820080c4040c14040d901c1d030001d040740c135024041c0e0310801c102c40501c18003030316000e00304140200585c13000c0214 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 265157913 1250 265156663 265156687
    0x6021903080a0906050406020306030d0903080910050f07060c031b1202030711060f160206010303231c050f010b0c100e0a02060d1406010302030c09041a04020f03060f06 74
    0x1610a654549030070761840c2d98400c5602c0c02440159401045141001e09010500c042500031354080c2d1004c6090383d01c61003c524081c1e1302c81d0081e10004128400620032100c0f0b910745409180f2504516050003444c11000c4d0200940c0c944c030403030084270520f03174992011a0f5250b141c803a000e1100352103089043c80308000000584825010b41241d1b07120340c2c0010000301060f10a000c00556111407404440250403e0702e104500c2c7d040450300280d0050040c101c20030010310000c4c02c24120380d00f54032108118100415140011504d480031840d60190030409202c0304400c0c180c071103a03004c4440200080030700381141030801c00c0310b0603805543c00c500c0a000302012200d002c030b40441c003124100e40c0082c40075454914181009102800694801400305052a070304400307400c00d20381c1c08414004400300e40e80d41c1c4015000c80c0025a0681c0a10b4003d2080f001c5600b400e40c01070a0642032601d801c0110801d900019081e0b07406544111170303025004c403d215440c105a1017200c0340e200121364450420502c06c42c8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 265159163 1250 265157913 265157953
    0x609070b031320060a030603060f05010e0c13170a030201050604050c1206040f110d0b010201022701020709050709140d080f0a090e0f01030b13110f01020106080303090d090602 77
    0x2d0541000320f4002c520756006000c00c0456200058850ba80350081c2c100007030002c3ca00791009840542c24094401811510b610565040e10022607540324652aa6520b000c1c0c2c80d041651003444e030100e8400046081d943c1c042d508024100c41d103000306008180740c5002425034001505850095042c0b10078815100c0000043d110034151544009540ea0742e10800500901906400c480c0a107113410082c060300100003004000880e0044c4040c001c0d00c5417100128201c1c03040b5100c2008034651480018003100442c52080c12404051044a0b1980d03190081d44d002c0b10390581d48903011504440c4100540d42d00000c1c5400051030071180319000c851541c441035007070710074a070b004014100d00184440c8140c2c041c06034140982150700e00200c3c1450001c0c03403500b4a03d130038001541e41c02c15190008001a44400c42114407a030300c48000810200e0395000d02c100d16140c000e1090555482c1c141c00304100c0005c002561141d03081c04010031044641001c0600f449045805c4801150007505016240d0803040301c0d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 265160413 1250 265159163 265159201
    0x7050c01060515070302010b0f1c060209060d090c23040209032505101106041b0807060c0c0506070c03120c021f0e120d0804020a0b0c0106031704031509050c0d050609070b03 76
    0x9106c01c042c1c018545007003744101d0382099071244020600b5510081d65030b101d003e48500c41d862480300e441e03d40d040c503603090000707640c4e0541081041043c1c0300e1508240e0060403003140c0c050200c0703844002030707030321041c0c0c07454800c54400781d007c1400420441c0d0300d00b03040d081c075608000c0d06140060701680e215031030b1034440080000d04020440e2185601114958040030000c0134810141ca0a250703e6400040108040d804141c0d01c3c1890380c003001c42c02d1300c1d04400b200c40c4541d000c4110036038035241d0365400c50882c440e001d1400074402c00d1000303140503803140803070203805540c2c15013044c03051500194060900c01c2540310b814015642d0314210405050009407a844403090307800d001c80256594030000324550429004140c000401203080d040c80101500400d040d2032007061481d84a0500c05507045860040d0f1101a00419600e034200322030300030541c41103807598041c03003e031a5041003082c089620902a42000c84141c0d00c140304000c242e200031f002c8040502014840c0500d1402c001c0e0704469805a001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 265161663 1250 265160413 265160449
    0x110706030b06031f08060406020a02061006021c18091b03090b1302240a020c010f090905040c0f0f081b010c0b070c0b1302040b060301030b07050c01060515070302010b0f 74
    0x40c0115111011325414401410715004a550b80c0c0303050700d0000f0194214183c944090f10030034003c0b03081460010011001c3e510b183d401001c807603040302140141603050027841000d002000014081071154402c100340500700c0b030100410402940c0c5001c041104409804008051500c4c865400103200102c5039a0410303011100a4503108082c0006246051400410310070328180800b00b145514000c0003030442009141c09035409404441c0055414070050b001140005070241020300c410b0040c0d0384000d800034058154404095110b03100b0101c0d51000b034206100900d00c0b8901000100070400602d0142c584840b240c50b840030300640083c100109500004151041c94800120010b00c60308594a203182c01c0040a15603080c0301c1c41c220011034015000b64051400c1c0104114a8100002164100c0380e20107085012075aa2a41c1140c440c3c100118140055480309000039540c0e45040d00d00390300a5400101302d40d501140d141c00390851340c1d40c40049000c1c3c5014603031160159201c90510000b90825 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 265162913 1250 265161663 265161691
    0x40f02060a27030b0f010e190204090c02070807170d080c0d060906060f11030301140a03060507091418040305090604091406010206011d010303030903110607110706030b0603 76
    0x40564102c5880c1070245180030100308111076800c80e5000c0b100c11640224a0321103540c59000200300e641c0070074000d180e6012008030200b1102010701d0000859101d61400060505440340407060036141528801070060348411014045220140a86002400420710100c4240c09000449845030030480117003003401040e07800500d850040d00304440040d00d40560030400c0c0d0380c50310070f40303801041580503070b40c000b804802d00f0282c1d050144240700034411884000718296031070b0114010703800c50389010140d0003580b000000030015200b4007403e401001c050b1116007004d81084407c0380b80350400038074188a4a0700d10000240c01030240d0b00709411a4040c41d000d5606c02c40314001c160240700704e034000010149082116841c001c0030a0405000394000d9094410a0f41d03035042084100804049108116804100400020340280c2c41a80c01038403a0511007602c514560b001c605014084a000c40890300280702540f000e8070030300c1000080c207182d040070050b501c0301c1404a030540c0001000c0007044032070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 265164163 1250 265162913 265162927
    0x3050c13020403061d060a18170f0d050a0b0a0b070b0a061211040c02010b1005030406230411150a0c02030c041d07060806060a052113020108060603040f0206 69
    0x400d80465000c0c540040701408445d1890041d40543c40801340941020300803503010030b03c00f8242d80241c41c00341540440f1651000e140791500360004000702c10101c240d41c010040c149010100002400402551317501c00980351418a4801e0240c3c0e0b1a0116a803040115030000c1c0805964002525020307600514940c445279070f00d82b000c9000b001c09420941d0003150090b401070030406440f202034204103094038240310080c0000001d03400ea40300e0352002c130391000381c0010014803544070b240035652290040d10701248417400900c1036400c20b500301c40064030340082c00c401c0100340024400c007003488400c00d50700c4280103000e41c3c075150410700074156448101310b10409080d05556041040d99803811004000700540d00c00052050700040d054070880c101c90140500c00103040d40030b81603541c4111405040189461105c1204030b0345544200e8504d030209a05504200c1c07107248c100c1c4140e05c1000711b54000c01303040d01c2d580005040110003c00903481001c0400401000480c560800003000b50f05548064413002c03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 265165413 1250 265164163 265164199
    0x2030601110712020a0914060607050c130501051c11061b010606020102090a0e090307110d05060114041104050f04110708031311040506181b0f04030c050102060103050c 74
    0x30481c400741c1e00354410400e01090001c03d0540b5190124401c480180080759512582c00503100300c030034640031161135100015140d040c00070051001512031030507640050703c03c40005414060146541000564850040c01603040008199041c1601200f40e644c0c03820071503441903140e0f40f42044984c0a102e010642e0300d00b80c0a071110100e10004680001e02c5801d46030403009000703400000c04981701d610003000000d016900141182d00810350080918605900c5440e000c1240b1948080c00b9048665128500702180c0b040c00014040c040a82e503131000386031804100030590f500c2c010b000d207010a0070441084a507035200501070903d5012345001c60851111180c1d800c01d0300030703a400074201e88400010820000d54507940b5202913441a101c2603048440d0030f003031008a9004a075034642004000e0503400001011200003a8850355144c1620f00c0098800b0382450103401a00458081d84030101c1d061007007115001021026180030b200400c1c10303614545032903aa9220520007280600510110721500761 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 265166663 1250 265165413 265165427
    0xf0c100509060c0322030302060a0209010c0b1005040e01180f140f0102210415111905070605090f06010b03041a16030c0315031106040806040b0103120e010801060302030601 76
    0xa1070050070140c0380c8408440300360301c80c0e205000c10b007400360b240030a80f88049151807101c4c058941550003001d80745e5a080d80c91000b0750102c0400d506100700e000c2c20b038001039280e070805886085d124181152003481c060605c001d480c00c2e2007100100b40d044c03080d8a022040d41a041101c00b03908001903564215041c00c1c0514203210b031401c0340304240900f02810b070f80e4401c150010145040d40400c030458000c00c85000c150740b0a001c2c2d5009020780300c2e40e0314511940345160000d11340354120250f01890000d0072841d074428032540880b90340c040340d808a000410700a0900c02c141c1d02100322009421100e0300075400315100c41050003107680945001c4041024040800300a601090312154207107000e040c4101e455110071015607401c0c001a08240c56080514400e000d89a003443c425440e1400640c01d5075140303a00940f00030b050a80021040c00002003103070042102500480c0030f040da01e00e942d41542801034150320681d030b03e1014452904071142c40c699120301440d04450755890300607100e84607180100d40e44 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 265167913 1250 265166663 265166677
    0x90d020409052a0301021911010608030301081e0102070305030612030405090c0c160e01060c0620090a140105070b180a0c0609140609010806060d0612060b030f0c1005 73
    0x240c80f41220100645004640c1501c002900680942aa801c43d0003018241d205104104c0ba1041145003044045809411689812511080081020f43e1900c3c0b44a00d140c109900c910b0b4241c0c0001036011070040c14050141410602d031000b54602441c68074090918030000c1d008901400d1242d4000d400c3c500c0c01e20648015100040c402e00050a103060700c12030f03d0b004407183ca052070103441a001954089001e8070011500942c140e0030141e07103440010340d070707900c0c2c2100705403201a124801c050300d40500c0c44400ea001421150f042c1d80318040c010504ca5406030a8101c10411400401403403000e80e0030006031204031340d100d41500056a9502c0384d106001c0e817400b07141d005500c01c1a0984041000f03500141003907a0b521345c1c0d002521591400c200c1d2803502c0c4c0c85a00364110004002002e2035500c04d9010b29480348014186905d81030080f0040c41c11180c90303070301824400034821100000c0009901424818400031002813010640d5101c020380c455491290710340c440c0304182d00b040380306409a0141c0b510 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 265169163 1250 265167913 265167923
    0x606040806090106051201090b01050f030708030c0102040815010f05040b0d05030a080712231005060d1406090402310f06030c150503070305090304090207080909011a090d020409 78
    0x1107420640390b407074060103060207030a01c21124180c4e0788030082d505124202107650002c4403417030b083c2d03c3c01081c8440d20803420139458050180c4132021940110810040c110b11a140000507990751403d0b080a003001304520b94400c480001c40010803840790311321401c10179600100c40000d009050000059804040240c009000703000c00708820500d15000900c041c8910103940b281d03c4003d6000700c1c0142210480c4880fa5401400c0031003010303504204c0034203d070780100040b10714503040c0e0300c400c0007a249400845400000544440c0c4103840c10b10950081504080c080e00c00320140e05007680001d5422101580d00503070140c008809440c0142c0d0030a030b801900010080400451841028220250100f800f003a0ba20012140f000581c4250920310a4041480c42c1d49042c20342e110500c048018110240040e4640d2006001c0132a01d03060300d20060640c1407080b0345d0700341e40d440c0000078880e040c0c00503032000098903030390303038004252200040c02c840d030442007100c2c83c10800c1c1044c40080c0003011041070140c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 265170413 1250 265169163 265169173
    0x5060d0c060807080108030901021b0307080601030b18031810030f0204230d0f08070f020a0b0a081006050406030c050714030912030a0215090307140105060f1806010806060408 77
    0x500c00d821103009070007040d0981d941d44131681c881250a5481c030800800e940140d201013100c1300c140440040800c4010b1004094414099403102580e00d40a000e0b0000e07151030191780244030381c010402c0704c0b2024280080c0b020394100312044510710070040444410500030707a40c2c1c0e410341c100035200740d00440e1050318040046483d940c4075611341c003120355041203c0d410201c1c0544008921b2804689040c0c0082e4840c01d4012440c0d1140e81c3d598a60b0040c8030125813500c200ba09620040c0d0b0341090b100c0252105000450721030240c003400500341200900020040e021404041c0700050f80481214140d940500700070071481444001207a03148207004024210000606410503031480120007003004160488100c5405000d00c80081d03100d02c24103980e000545d010206040d80c1c2542c00710802e50051041094030300303090150312000703075085021340003104030b942d580c00b000440c2c50035980200020405035001c0032089403030004c002540d800030f040241803240e503a0020307107030381c2e101d03070850b005085502c00740c0b1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 265171663 1250 265170413 265170419
    0x5070b09060115050405060906161a0411010804050a021e0910080c06040e1303032c01051f0b030c07050d1d12030d0c020c0a03030e090705070b010905060d0c 69
    0x503807580d40038042d1140d40001800d1001e44140f1440685003982d0004004524010208041204075413060b655081201403c01056021030b003000c0740d412038020100d0007041546400e242c44280c50003c0319040341448003200500c401300320001180d070324640c1c1c142c0d26460302840c0c4c030b04030758042009046210360100b5160100074500d1825038120086455800c12100082124010001d643c0254060020100c48050000f4841c2c102c400c40e40045034020704000549880f5004d12010302103030200458a9078071003140c80040000240b140542c0050300c0c031008034600c42507141d10b002e25100c2d8804c2110300700004c404190b10111840850b20090340c0213040f128201a4a04d000c0c4c402e10400c8040104a00145107117951410400b016031001000d19010b540b503e00c190a8071390092240c00d86d00d00440c45050500754070f0391650000e00001c2c601944500c1c00031950101000801c0d42c0081c440000c026080c0100310009084101d16415035a900a020615a03500c40c0401c000b400034180142c24080d0f009400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 265172913 1250 265171663 265171681
    0x30f0e0325030203010e011107031b080d1505090105010507030302030a0b060412050d2a0c03060e33061c120f11070305060c090411030406021903090c05090705070b 72
    0x1c6012684290000e1080e0340f10b00c1119070032180d1842a860b51080e040144a000a00c00d90b01841091203001c0300070070052154480d2441034005001c089052030790341025000401440032800010070049405039001e60400000170003030700440d10000d00303050b0048007140b4030004d0390f001090b86106c0540415107a5a41e202c4104d41c0010514040c0d510740141c91074280040c0c4520300c1e40f0100071a240e20045400190480a210303040d0a100556404200003030110004625000389105000a00002c00a201000c0f1004c0c40000444103040c0758684404141500b0190803114503a00c040105d902c0304010f0602d074040408038003800c000500320002120201605070b0031441e07c406230900c640d100d50201602c058007650f02c107010b00003d4031aa201c4400100074034001c40c01000c402138060700114058603c806004859003003034808071902600030804948601a04060300c41500c40e62070305121050450f110003e440c02e0600134240108141c0e40041c4400b80100c00712895694032036940001c5107404240 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 265174163 1250 265172913 265172983
    0x3070605100e0403080610051c0c09060305060d0609030512090102040312020307020102120c01230105030105100b0901030506010c050f06060901050604030c1e0f060207031707030f0e03 81
    0xc140d809894041c0003040e8009010541445a030b459265000c0c10b885001c1000718195000591302c0400000300403c2c0021040d610080d284102e12200104030011260b102402c0c241058011000305850001006496600c2054035020340347c1084000510700c116040480d0340d485a00c04004004050f0014042d070303803d05500520031603003d4401c2064000c0d0401d0704070b0300c0e441036400180c0164060000441c801000c6001040c40d02640300c0009070b00322101100c80c10914008840035800201c010040001c0c0c1428014075034420078a0502145603414a440600f8501813012441d042550340c0d00000c400364098161140c207030f5000f200301d90240c00c00c00074055a88108482041c0200c400c0c800015050070990182c8040da580f01701c04030005130505a0806000012103030000c2c1c0ba80f28150002886181140c060000c0c00c5241d000e0070380a0b0841c18040385010310407084501245040152001195000315484c0d04182c01d8034110008500c4007001902e40b03404010500303080402c440140e101105e403000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 265175413 1250 265174163 265174171
    0x1b080f03071e08011d091c051b010b060a2109060213141026191a0913030c12030c030506040e07030201050d02040b16030e03070501050f0705070803070605 68
    0x520a0342c0c0241038801220303611021701c036811120f9000c41d8140d1460b041d070041141d00c000100100e51840032100d01e640300b0003450a500720302041c0000f0b8281d0440351100c01e800106040a4000d0140300800000b2415910440031400100119078100915140110718084a2404140c0c424460714009007080402035001020f03641c01c0040101c0300207003c00ca12403103c410751000801f080c0807001c00307070803e90f007a105540d0101d0715240c03480d62541c00e07407002c50324582c014155400ca40c0c00c026403520713503c0110740099005d10a2144864000e412a03a034402c161503001640c400307010105c4010b49002d680750703202203c0050107e1440ba40d0001c40d1a456407200380f0782c5c2126070301400349071201c42c1800100e5140050415894215600510255000700d00400515482c080c005140603a101c801590030707004a109060310000760301002050540c45440d00780c42c004220080c19010b45003a001820502c5070348081b00100c41e0220b458414450706000640040c088082645d41c0ca80c1180741400037018121 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 265176663 1250 265175413 265175447
    0x8091501060915211505100c03110a0c0b0d09060c08190b0d02060a201f022b02040503060a050f10031a15030d02060610030b011b080f0307 61
    0x2030100b9005030302c84c00e00d00e06000410424544080d4140001a000d0260748074601010000ca960019254031110000d01900300c0c1555003d070301e11054030380101030046a0b0310700d05250f40003c0b01c1d40c003c01c000d940c03040211384510711169a02c0390304c050070a01400000c00c01426840c5402e980215031a00000000d2090401c44181c1c0b8500084d442031400b00c40480500315048140154908010b042860041c40016014200101107444000703081004003002031a5100c075030002c6280c4880c06880440303011682ca6000740650802050b6900c4100904462640ca0f007410031480140204800c035904a9020b450054180c03140c628240e44174401802040d40c410081d1030000c00001e812820302c008030400c0d01c0e03000d6150400b000e030000020781f1084000d095000003a480d440400d0f1950350400256008125a8002d40039070300d081000c10184003103107083e82e0107043c03c2070072002080ea404800000c11041b4174551580f10b017081e041c02020f9016012100c10522400021301104c0d0f5003100c0604ca500982c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 265177913 1250 265176663 265176689
    0x201060801110a09090b0103090209150418050d0f09081b03060c09150306061c0509010c020c0a0e0a02070b090a0c09060b041403120f070308101203080915010609 71
    0xb220440c1c54401d803280c941c0007407200c02d801c1c4048010381d00488111281494045040080303a000100e40c06019900c42440b280c0b0101c5018071400c06010741c290460001c0c81c00c2051807600e40b40e072500d0f031200001d00c0f01003041c0603089001e0540100d00c0c100160140d80100e40c43c501e1060382c000144100003020718400d00c44d5000083c841d54040d02100d42644001d408245030310002030300c240a0390000740619901c40b20034440e160301a80c1104990700002d0f0759840100361820285601c03400c41d01ca1481100c110340140b418068582c541d1040d10044030012030200c5000e90700c0c00501c1c0c000303004104000305104518414010101e0300080c420200900942d1032885080d99551f00740c0440d025031049029020081c0b2040111070000303070121810840140a40e002c4011904043d465680042601a007045000c50034005160307000100da035001c00e000650894190619a8625a480303000900504000000001608007801032000301e03e016240f202010441d40c60303036000782c038400050040400020700 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 265179163 1250 265177913 265177931
    0x60e0c0109080d052a0118120c0503030c0717040e040b010b1806030c0c0109060c12090b280626010b09010915050310020d150b0a030f1103070201060801 67
    0x808200307110100401c0c1c03281890001d181c0551004100b081140e030051001c0080d10203880c50b401e0003103c0c0130b89a24000d0b11f07650003403450440e903080344100c4081c0030001d410360b0f400d0028000004580d0406008000241c640d1010f14000e80d80e0380c1d01d0051060003071404100090b0031003950100e98000c2d4811041003a49a803500c0300800e0314041c1d10304119001c42c94072400c44030750030140010b58005020032011441d01c03400601c400d003516003c4404555035039690300d0000072107502607482d00041c3c600d01c1c402d001e201402d8556a40c09107021304401e600d500c0301940b40c1d101c10912910281c2c83e04103030b5003e00c00e4950b83c140c0c1003a8200c169007101400c1040c4002c84464000602c6035090840e8024502c5074142d0800c1d4051000f01485c400191414110b16804100b99030b040003507030710a21443e0f0f4096030b40d10102c6070a1050b1b646888950480101018052051440441c10b507040300300d240c174001400c118075a07103100150038000302c1c05403240c0c4008240207086606400100030703112802c0c020310007026 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 265180413 1250 265179163 265179179
    0xc180b2d060c06090f06090a0618020301050f01180603030507020906040b0901090204240804140709180c15050a03050a0221060f010905030d03090c05150c07060903080f070302010603060e0c0109 85
    0x49030728a0705a040700c1200b80021b421a800ac1021814010340e003066843d03661302180c00c46100780c4029001d1450a0010040c5495000700c0403419612480184001455964003520900070110001c1c4a642c0f40000146103413140e80c0001d817848401040c108055950310140b45c001d602900810036000c040c0d43c1c28003050308031000c07140c3c2013414135a10401155200e80790300c1c058807001c2145185e1801a101d00144000c840d005104da9903990000d049000b80d124607284032410030342e6001940084100442c4c40040d500902500c08081b12810b02244640c0d404040070000d104001c20080d440e100b102d914079110300c4009000d4400c80003a01e05982000f80c000040d101d468142c41070a61690141d02c001c0c01c0d5038460b03080240d015118084404c159a00c52000035480d43e40c40043c9200050086602c1d240048200107420003403440b41008800c0c02c0c2903031582c655170f100305041c00d00b2248000412008261007548108015038010900300031071407108c003041d40c4864001c04410b001410701c81012414038 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 265181663 1250 265180413 265180423
    0x705031c1401050a03060203061503011e170312041b06120b09060609040b01050408010504110102070609050a0501031e051807051c030309030c0503070c180b2d060c06090f 75
    0x200000c4c81075020b1842c5541d280040d500003050a90807900050341c16084038100380185001e000c0f40d4103011240e00080c401c40203000c4d01742d4010f64141c0f0710f12209150120010003200c15058240e10805907560351400e01815203050a148017a0040104000180465000390302c60a68910404d042c40b00000319000c0102e103d0301920050360000c030420490160b03191070b41c00104622818182242055030b02c100882c00c540d01103d0039100a000061111850369041c4412005801c1c1410201a81c03401e00001c5145812a0301680341856070303d405112201e0005042030b4000d05440d4000d000310320303010001c0e00714628170816502d0b60f442039090100d028904031f140800c8070b000740045085580142d480440180003007200903001c0c405084621004524180f005241e051302500e4168501da01d81800c030003078801c61407102c0b5042850007192100990301c1110041741403140d200ba074001084807104500703a000200144a070700800c0010841d4145102040d0144500100c205032001e180761100b82070341368 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 265182913 1250 265181663 265181669
    0x201091701050f0705270a030606030b06010305060a03030215041401021b0c010203040533030106080708010611060a050411060c070315020a1b0302150a0504060e0c060d110705031c1401 81
    0x501c101684c90181b9940c0d50303800c08003482004000700c1075150b4a458000071074041d0b400a6a070403001e2001c03c0b071196091700a040d000b01c02503407016482d61440d21b0003511217451200311701c10503681d0404039040c0040024804000b00c0004021541c0f081c0d04038440ca41c04c00e482c0c4422249000d007986240c820360002c42550120740b4040c1000900c02c4004942058070b01c041002d0781e00c50024840a50358424100c3c000c1c40c0039055a0f22529018285400081e1001605901c140c0400001208068070304402081c46034200d40301c0703140031865480754070f0607034590b20388040d20a42001d0702048070144180c0c009a148122401030004966000c0040c0f000416072040e4902ca8002c41e185040c40c01c060101c07098080c0a483c081c1c4161143c603009880b55001600040d144c0b8807103a0345490511003803103074920810241841440042c91000d1071200440d00900030082d01407215580d031044030804401354811100d210303a10009983d6614071350103c0000f05550311300d6010b07032140b5090104140b0703460a1081416 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 265184163 1250 265182913 265182937
    0x4051006260703170301060905040203040f020f010e03010510180606020a170403060c080a0e010b03120c01060f0608070801080f070306020706021c0509210909040201091701050f0705 80
    0x100d0800c4101d9442540e281c00d540d000184a40407000011440da0300d0381407480f00000c10400d96951401038002d0100304c0340d0300501c0c455441042448002039840303440340c1600f075060785c00c03020020810005031420b100c15117065801d5400d200401c0720a07030450300e020303064420103903103940c18030030f041c4000c4211407a078003942015a00000046e804600d04200310056071044e5140d181c41c050b180e66070b4409651340600060080340121007400946c80032409220004001d54008100caa440f040003c1e56908007c0142804e1010016055440304421740011000d031034118214142c0075580c0000400d514021911080015120000030070744580100300741c1307116810308000305002403c5d0780b1401c00a40c000c070422203800f40e0811078248104030381055100b141101100000c1c1c0c5150202c01c2a041402800e17000b41c9585038400381c0c4051010790425510608416241d100542d030351840165089017054105510f1002d4800c1060700c006015081603219030a1609034400a440d10340003650903020b18000e00b1a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 265185413 1250 265184163 265184189
    0xc0315050111071703030717160509060d020708120106090e0f0c0c06100e090d0804060c02030c03030c0a1b1a09011d010b04050705130605070201030207020a0e04051006 74
    0x190b200d600881146411041954030032940e9a10030020130124041c00e0380c0a07040401003000003a00f11110b0a00f0140075a02e00b41c0c00d00c0c01071076468004103980718110901c800841c0c440c009844181c240e40d03200c61404021552444e2505001205400c42c4c0e180c40c420343c201400201d4010300c1210f00504a840041d4103030042d4032030f0782c401c100000f001040102d01740b205106c00d000c0c0d803500300022802401e000f820062200d00348030101c120482c00030310105072030340010340d1782c00d01aa00c034580f00d034840c1d00800002003410311464103d00b14410741c182d1308401c0c80017000303102052100c2d400a180350800c0d502d80c0400f00360b103140e0740348000480380409892400b2110306a402d41a5a071030041d80300b9408000010400c0010350244400741e029110040307969074800002456080070310030207410582501340365003060300550f40500320560b14000c010400002240380811640641c040e129902d600400d02c070181525181d80c02d0302510101c07801c1c0d030107204034178007051201c0702c40c45840d05a80a02c1c8100d1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 265186663 1250 265185413 265185419
    0xa061b020a0809040b041d07061b110d05011d0606041e0b01090e18070e0c09131103011d0a0915110909090106050901090b01020601050d2301050108010c0315 69
    0x664180c203c0340c0c038260050b840754036800540d6281d20a541800c0d5080304690350341c01900258504e0080340350004d1040c801100c030348644a901b0b10f03042c00c0070b06078060780c0c450b4607101e00b0001c0b0329017808405004110350b090442000154025000100362122440215800e50f6030380340411003601d41074500060080c05070040302d2104a056000840d800b94103041007103400c0e5840403418400c11040316480ba9603030384403200140740c86060040300d0040441c1800034481741480c18070107080c0c0c410f100c41e01c1c0c818528114121041100c541010164019443c50300d43c8940c0d4032021070044402480c90100606400000520001c000e032088001086e00092840c0303103003000f000da4600074041103051503c2400c040c00154820b6403121992131003041c402001291403840d0005006030070f4010b1704484044c0d410503040d0384181c0d90002e4410b0450340c0846149900c0354182c1000001100704210604d05080c20584544035503405401050407035804c03170020425030030350304011011107100900215403400844410 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 265187913 1250 265186663 265186673
    0x171005011101090209090321010b040504150801090f060509061b0315030105190c0203030702100f090f0507031b0e04080c190c0e1014010807021603050a061b020a 71
    0xd942481d503031000000c2c40214a400060304200221b4400300c80e81d000088a142e0140314007081805440e06040604040d410802005003d0003180956070142d0b544600c80c00f90504c0f10404540100000c3e4002c00c419982c50500c100080401681074410303d0809000c52a64100010400d1203424072100201d60842007041c1550030703906c06408401c0500f241422000f040d9801e00c240e6018810796520041a4000300381110155180c903204203003950010310030492020f4000c147d0a002502a0400041510320b140f50a0018500c03a8009440b210040860340d040003030000d000d0041e41d006a03032500d0005280c0100707519000c82070042c1954200c0d80c401190000321340704050103145803c10705980c180220302c1c0d80d01e80880382c02401640c4810020504004000082104503002901c071562002503034184030f201c80140410114050402c1448400500000d100303004298a12114a1270886116528200a552400c0b80c1c841903500300d1a244803620f060040c0c51402c010021990060a004c1c24a80c0318 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 265189163 1250 265187913 265187927
    0x1180e0403120e100e0708070e040b0a091202030c060906060d020d0f0f08040f051c1217071107140a0e101e031103070515070201020120090117100501 66
    0x80340260b43e441c1c1c030320f8400c1001c0c10b0002c0c1d074920581d0500019030b044142141458104c141d4818025034000b0038084c000002c0040103030394400d400007045503454951254540c02003021040140203a050004801e601e80d5011008000c038195600840b0440d0b200c24010a886100590300d00d54040102d10f046401420881d052540090040004460704844d40c6c46040303070003900759002c44013144002014032500d801e405805008d0702c02680c10081e01e2910203078495810f030700040c010f8216540e4400105c041031003400c20824194032400140b00904110034007901a07a0303035444940260050b00c0000c81d0b22510b1a07003100307041000034080c01443d1b00c1d2842e401900d14014010010684c3d1400707020034141b51120800043c2c8803150144094540381d402c080340f01c112a0802c0b54800d03007008004000b26640d1007100d044c80d0f400c9810540d601d8006200607070061800b440010f2203510a42042074228203088084d04500e942a00c522054408540c03040440034012521b014403041d1304001481554410301d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 265190413 1250 265189163 265189187
    0x1c0f030915020315090a020403020105030c0f091003050106090b030603120903070803121e04020916031805160b0a02030a12111204060b030a051906060e0405060601180e0403 76
    0xd9450304000c100c956003001e0364000c480080501c1c0c913400b0340c40c140d41410384030107500107190310045040a0950380024120710000e80b002d0041a0b010403c0c11240c80b1000844068070b82c010b046030303010150100c02801038807007446801e01103007110000080c2c0c2e000030403c8902c82d880003030240c0391455806040000942241041e5a054801c130500030482c1281000100203042001c5104511464140030a282221a5000d60608081c908091100503103850303200a4108009a18130200e000300f500080740102030070302c40600c0910f1807181400a010000c50b03100e8a900a0400f42018107442d040300c170141d4800c0b04c5a07800140c1c010040c24030303018492b210038084c4070005000031030550003081882c8043c1d00462520a949240402480100140c52044503141c107c240e0103400140c1a64036071945071136991003000101e0f20a642c8020410059501020141680d1100d4009504140c01c0103a43c800080320902d002c04c0150b000e220b8034440c501d41c0c00c800c490610701620010303501d5584c03c4403a2004a1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 265191663 1250 265190413 265190423
    0xb0406021e0f07080105040b0c0403020d020108360c0907080106080402010c0c0602030903070602010606020304031e050f06040b06040204210f0602161b030308011a07051507021c0f0309 81
    0x10b492000d070700d10a0010400514440c00046140d00309400c00c803081d101c01500f81d01460303001308410801a100d44560741d1007203409080c0440d255a5240c05407091180c1d50100b408140000380ca91400c1c10104000c4071800c5022108994102c440001440a140402e6542001048111004004051296034042d81c4548103150481c03400311a69a030415041c455000a80960400720b1860002c1c1401c2100100038213480c07000b40709480c90084084e48a214502002d481c45100400000360a01e01c0e029102960754440304030b0310104142d081135600d03000f0560f41180d451500b107021606900c1c0c2402a542520311902001c0c46404905d01e0104403207806c4070088a02200c404080c00c003050542c40503003000c24581010040003220341c03601002c0d0000c00c035500e1600724401e040c1800480d50140469044d5000060785001d200e804041e0740c50940507020004015215204408a043c50141c0c1d1007801031100d50201c405180d0034039031221050f81058a60400501c21520b6030119a100b6000910214014 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 265192913 1250 265191663 265191673
    0x102040302130f0509070b04090b060702120114010f15030c030b030d09080c03060124050f030703140a0c12050a1d0a0311030c0601121a0f010509010b0406021e 70
    0x1d50100345244094004840010394030701001c500c00d00e6030700400340d2094440020f011005d0804514903400c5c0101e00440d2070040d0303580d490300020307151101241c070155002000003120314082d05155002e4104860f080c20342e400301a000142d80b60420480c0015035a07400103038a850701d8501c000720b00819200c030300c1c0c2c4105520303145259203d840c1441703c1003450202d07a640660b0749003090303212440e000c90090080e019a00400c0100030020699520303001c2885001442c44141c0134104044500d80218454880e000b03400000780003045405070300030200030b4902500b03428940c0d03500b6001c3c01156450503081c0080f450039094181190441ea02150380039103503003000624500740c0114410306d0945998403401d10b610190004041c150400e02c07080341d8181d40c3c0001d42c0350004440d181c6403160010b00c542415034181503018000c126064100f913102040b2680741e40303058581039034043d051000a00c0360f1809500303003900228040e91501c08031400e035115a001000e800803c03071882040c078424116041024025 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 265194163 1250 265192913 265192919
    0x30b0c1c0e070515090d020f030303010902043303091506030503030f100515070f0b0f0402041a06161a010803130602011a0d11060a09030c0902040521010204 69
    0x4681000c004002034003000a450090309000a19003450364008078440c100700414910310050900485110311010b8071560b100719207d2000c070b4080071059038950b9050001200102c3d40402d254082d104445001035046c1d8069680c03000c0050050b01d120b42e10851944c46400c00c880360303029801034080c851090020090450400461030201c940c0c640044a0340c2c0c20000030b12119400c680765040d00140d00528251150b8906400200c2030120010341460404000c1802000d00035090161002150045000c3e006480d00102280b42c80e41d00302c2e000c922807403904074100340b1680710f01244a10b450b8040d00403482d00501d001150641c1c01c0c00c04089403140c40300c1240304803021010400350b0003880108000c5841d071100b281002d8100b90143c003c0c00c21a0314240050103214461700b4159041d91056402140100050030b140d00c0c0e040c21585c00f2500030f0740008005014070740c031200e01c5088078010001081c1d8241c647c0d2240050744182d01c10150f0200483c80d0351001141c130f40c500c0060701c2c00d0f260001458a55 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 265195413 1250 265194163 265194187
    0xb090a05030f0d05180a0314090603040f032636010207021804031d190605030907080105010e0610121a18060306220c03080301030618050304030b0c 65
    0x2200b400704600700503010448007100d4885010307007034106a040300e010340d40c0c034062441c0b6070381c3c0d910030903025003006001d40c031905041420508075425620080c20306c030b583c0d140609001031181c418a0080700056240700b0040407076043c12000ca00040c03112138007001152210184c0200c5a2550380c0c0101c00341c1c0b000790300c11840036030400e80e0290426100001688401e4180100b05c41b8901c0101c44023141c0d04d04208101c000396012006003000c0d000c20940030401c50b40039002c281d41d03d0b0050f80041d501c0c40d00140208240b40c201c809540300d590030004031060307103480d801c45c0c0e030a80f8401c2c4503116100030140041141c0d480c2140360060038054900e8409000b80e020b000b0501507a0b071f4914000070526050020340e40318180051103a18591b041d8410b039203103060020119076212070007084002483c2c801c01548076140c4620300c501c9103c0d071304101d00010403510707414116500d070f20030700c422524240740c6540107650408200c0404022038014024505282c07a6850f2940300c3d500052002ea10150304102e0050790107 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 265196663 1250 265195413 265195417
    0xf020a02030d26160f09060e10050403050307060609050603010204050a15050f1209011d1005270102091003090c060503040606090614040e06010f180b06121e040f0b090a0503 76
    0xd4001c000564402c4c42e000041c00804411281e90200039602d0000c1c40069000729414504003401c2d40c0c83c45c51040200811900c501690300f00420300e020000c0c44901348a4035401c000c2c04d44200340400c001300d868010406080344550310985422989880e001c0241d042d03074031941c040020142c180a0724046603480303403586503482003202d070076081203800034407a01c42d10901c030b1a580341d00b02e9502c40e2915100c151925075900b0904c2090f003030040c0c03200c0006625140da003400324051300704280d210300068484d0780100e004c0c0d0850b1483d41d0040118003a0340c080300e8483c3c0610000940c20824881e403082c10020110f907140d100400075600591250320000b400700c4c0071b00c60f0a0091003c0d20540043d0394441341044242e44150010689580c007180060000c0c0d00c403504c0c180103e0790024480300c216006c03030980d1800751510500090f4802c0c408105c8180e103c04a0302d60b42e20420000081e0404019007075911030005609480c0502411407088107000000e40c1e2103503042d041050300e0129140b040305640c40c94170303507 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 265197913 1250 265196663 265196671
    0x20705100203090a14030f0d05071101060b040617070503040227010b12071d01030f060f061806050f03041203140a0c0f1b020f0d080403050a030f020a02030d26 70
    0x90f13018001c0e030002d04c0451030081ea07201da46103020714501120100d0803106800382c4030350710b10344513555800704a441d40240015040300030100000c0c0102607450074003801c0d030342081c400d440c04284803800f02120800702d0740e0035500c170b60119190a404e50715541c0900c050f11055005d0300890804003030380c0c2c10820008840150080c5810100705a4071600b40c2841f424070100580348106002d81c1405002c100c041238600990030040a1900281307001c031828400020b400c4680c841003000c040c1042c082885e6070301020440c0541209445403a1a9170740380004ca690303118500103c0107114080c0042000a803002c00c2c921840d22040c5404140400a0400d162000f4002c0d142182150780d2894229030031a004060303480b55105904100702100003840ca00a143c410b0440024410350b43c0840b031010b0303075980a504104440d040300712141c541c2c1d2245400d61340c445140e00160080340d0900160744a10384006066922598060050b04003105081c500f52921414031175009030b240c564260456000b4040c1c600b103449 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 265199163 1250 265197913 265197931
    0x30b1b03040b1509070e01050d09150608150c0409200a020d08060f0d02040504051c031a1c0b040204020904020a03050417190503060105070c140405180a0303020705100203 75
    0x605004441c044886400f6141ca8000c00900d010007a0058000d1680600300c042820720760359904100c0810700040c85164001407120440441c400c031b03e01d00b15442001540c0801049132440910914880000d050894250118001c208024031051280ea0480400e0040c0203081005084006820b4504c40c0c100c84910b0300145e10204101d0340c0c00d94465031998101e60b056403080041c0200001055030380b0b151000103801541c03240f0200c0d080007030800c0390041750300c0042c07400100301510501c0100501203480350681003480502c10a4011700d8860b050414440d1150301c8508648425669401c1c2824020416680b00398240301600381d41e00d82c0c1c0010000c0b405681e034001110b24140c500403882c560b00c0d4941c6020301c0401d00c11202410360910f81c103410302142d400c05903241da9403440100c0e01c85c802c0c08ac0c010103807070303a100c00090b80c1c00004014400040742280c0601c80b40d62240503070782407801001202080348c2e111610b65408a0702035402031076517a005c0d80940d0304030720b00c05070f00c50300b41c1c0d1050fa0039060f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 265200413 1250 265199163 265199183
    0x60201050402041d030a03050c04090c020f0114060d060905070e0109090212070608060d060e030a0c061407021b01120203090c01080c0c03030402120a0b01080102130b0c07030b1b0304 80
    0x402c6103070500c211040011030102071801455554a900d90f2070050307400e0300092503515404036030940c009130152001000161340c00c0c0101105090003e4a843d05694900619807d1078000d100c0054071018081c4103130300151210b50614002d4841c500035048038581518640110030020444401c0020340502800c5036400c0440d81e14454818400000303141255214243c1040c0c0d018020207038407208070745c3c11403412680c81e520b522090030f20744020a0381002e1158107203c0000d54058031600300351110302c5c40c1e008500400015501c414402070512046408100581000076521071035079140000762000c1c40e06140c0a2809148440000308980c020f07221560154440f1941c6c2d04c440d80c0c0b02e098107500c103011110030350130056502030341035803404050701c02481490201001c480300c1004000c410303d401d0b040b401004513941e56080c018000d501001c4003203800c0d20b603e080031484040312022220881e004800406100d0b10f1a01c51010380386014185040c1d40c540784c1e40a4140c22101c0018501850054840c48 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 265201663 1250 265200413 265200421
    0x509070503101404020d082110050102010c02070501050f0c01060b130f0e0c0d0f020a03060e060a080303011a09030a032a0809121002040306090b0901060b031b07020a06020105 77
    0x545000000c1d1004011070b8203180c0300200e440c1d01c3c98420f0760800d42c180c0b20341c66010028601240300c0d000d0b100c000d46072400c240c0c90350b00300f0f00d48040000b400340f1079140341c1500c0d03581ca0300012800d07503403200300340700240c0e00502c001c1010754484c1004081c42061407000030300380850004005c1c01e480e259403080c0082c6201143c030582c1090441d00f03150043c5100450001268904414030625000c01414030081c154003040410381203560381c210760f54406a18004568920030703104054010143d6002d0020342900c00c2e0000f80460500700d10250944902c10f00a6007160b18000c08a440810200c0011060b55014414400707142c0302046034030340fa18804c3e1101c216004c19440e02011045004500d00341125400c0d00c02c00200354403900315855054240c501c000d1500c90441d8640ca081040601040840d03c001400800d02546030712101d280c0b44100080103080d00c6142c9103900783c9509000d10b0f40541c07400c00c0811444000d004d2003001c0040c484003d6420601c0c5500040d60421203070f40b1080150351580204 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 265202913 1250 265201663 265201669
    0x2301110d0216060305010807030f020d0b01180506041107060f06031a01060e0a050a03030809070f150314040b010608041103120a27051005090d0606170a120f0c0605090705 75
    0x40014140502d1308106a41c901020b569a80e1401c0c480a44810f014454003000d5442c0c10f440740042c15001101d4202c656550003240080005075042c0201191402011520301c0c030b040d001c3d8a85441c28180840d0900c1c03c2a00d8000040005090001d40a95200000000035148040074001962204140280c0b580340c4800034090080d030b5910b4a01c107403c109418004d40e6502036854050702d406280c42c411aa4601d0305c15450081319130081104041c0800300014071010101c9001c5480d101c80d901881b11684c13454180d031003600c0c25540140080b035540b00500445105a0913143c1c418000c0700c5c04882006542c000c41c1c100740c010182e03288140f20000388204c80f590031140c013040a5580c000032a01d01d056007050400c4462103801642d00c0340324004419480c00303200740c00f6180c42100041040003030003068940f12000342036511840c01d030070510a01194070f02a000c14070b890995040002004100c007007440483d41000320540c264103001c3c0801c21800030031041e105da5840344042c1401044602c5c108410 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 265204163 1250 265202913 265202953
    0x20a0b07030809070b3004050c0411030c041203050d0903050403020f01020c0d121103190305070809071401140307170108030a0504090e0309030d0e010314012301110d02 74
    0x111503c5901c52101004200000011107840e000c0d182c580d40e071650650f850031031140b506601080c0c1c4070098442404180800418440e103001e10464041082c040c8605161265001c2210a000c90460070701080100f030113101c7c08c08642a201b446d040c0d01e4000c0607072644003103d18407013090340054000316081c421030070241d800d051003040034001080843c00c0540010b2224405c900003c15441c00190500384c143c2c02400600003610130b203003e40c4d4546100f0124140d062014400540010b41014040b071603181c080c85103240100d0304540034151060a0602d034020001d840c440b51410880b00b000240914010600954021007507691040c1e4001c04132190180300403010780111066800402413807621070b81060490b0300300c6006100210740e141c50a0a064114081c09551680502426841c2c049540d030246400300d45038426241002082e02000d1a0345e800c003424018071441040100c990304a41c4401c0520040d0385405142180088000070304803420170070070203034034009640100078143c0840c4000c61 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 265205413 1250 265204163 265204171
    0x212150a0501050402120601030e0c030f03030a0f18140705090f090705010513030b06060c0601061701120807030c020f0402160b15030c13020c07150f021b011803020a0b070308 77
    0x5042d414083d580510f171403006e1001c2c10b0366050560b50200055118000d100b05d01c540c40c001030030381d03c0d80c4007114030290702d0790700c00c40c2d07811061450944400310062140c4070b0741c40304032042d850601a07601e5554504081c550741d003200503124401d2900c0050340350760b240b10766446262140003189a41c180001d0452600c03103030360001814845c0030300090300b503180707006172010032a41c000e13801c140e5540b500404544144280f00101c0c045019210003c134003075070421420302c09140c030b01c01001c080c4e030f036180032003005207122440090261030100413400100707202f98280814038ac002040c16580010350030015040741c1c4005459403489115103000c0042c014101e802d1359002032102c0012060825100000351180c00003107049204a1080d04460003000540e4182d0301c090800c282103131b2805860301d1181040c6442d49100030005045114103a1032507102056110b440102c40c140c580080c1001c00c01514064824449025030726002500000540d0318110044001e01c2c900c110b032690b51a8504008200c1c2900070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 265206663 1250 265205413 265205419
    0x12151b08070206010506091509060a091d0915071b120e1c0b0414071d060301020a0f11011401030f031412070f030209120c01020f1501030f0212150a050105 68
    0x10f004000e04e1712510300310762503c801190600e95451304190400d040c3d01604003202d4118034040381601070315070070040350401d44401d0401040d034429001800e2030a943d00710780300c8415411025201801038a0840400e82004060400c0403185e654515100f200e580c0c01304041d140120800502d00b00c10707030031441c40c0d4071509081e82c0e0003e0034490700382c201030500f02025005000c4000d00e400030302800156810b50010200e0b1400b5241e5865858030000c400781c0000b0a80030b4404120008582e091030144202d076074200007500d0758900c080b000e4106444040f1480c444200039500c3d0301c0f010740c0420100314840d011310b00c500307040c491004c100e0400910340098008210340808082045105851101d00026030001c060710340034102005506088006c0e0146010300d0b90000e0750726800c0b00c503d140c0410000d090f143c007a0300b207a0100c0c600b08850b0303548201202c2050540c50041d001840480e1400b004c01032086d00180401d51030081002d0007a00d4845c3c400140c903941400700044c080c4540d858010b150040c4411 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 265207913 1250 265206663 265206673
    0x302271f0e0405150a05040506060909250b0d06091a0306010b030a1b110c060415050c0a0b130303060503070b1b0705030316050c04060b030112151b080702 68
    0xd080528034044240241c8691680460014003000001c1140204a2244c50040c001d603080404511016110a0f94112000d00070303000050100c0c1000451244a040488011724613035418000b00fa1200701030142128403001800b01c08115100c8100042c15800c3c155840000c0c2036182c59015411180f080c18404101e41000008000da960300003012030568030004051503680e2509464031300203010317060922040503003401c915010039410443c02c0050720b90103800d072000407071080100a01c0748a2401007040d40320032021040701d994801d5025001c1030781550211000c1d00c1040c4c40b03006816070b08540515115802111100c2059450b000704030007400b040d001007001c0b83c01c04d20301690b07500580c080840d04800015150038400300030062a0000d010180079170b1360f0380b801900e03c002001496802600c051003410554800b6043c00e100322000c61706405503840c1180d082c58071008401004540656000c00b648105084803813641c45070540305e120b101c40c1e154100d01e0f1444054004c2e0001440300e0195040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 265209163 1250 265207913 265207951
    0x13050c0907050733020c0c150f090613030606150801060806130221070311040e0705031e010f050909010b0d06020d0905100f060f060c02010c0309030227 67
    0xd8107680c1d2203036210120384151010304c0c6201c0c444c005240040403d044a01c840802003078000c0c0c0c0100042c101c0340c1d06032100d4800380000e12010f50b000301215500b01d84208040607121081c50080c100419005000350b01c0c0451066400c080e5201d550801c0e1012540c840c4104000341d0300e02407030741002c1f0090034248503943c03419402030403803080201014050100d141c8010b5400074a6411682402c032083c0c00d0700c0740c003c0f40c1e00e00403080d401c084624401181c0390071030307200ea100145030580b000c81c2c00c0500d902501e0784d41d000040f40c180d040944180301400480d05007560740410441b10034041c10502c0b2040c050903242008100340d1201c043e202100b1a490000c55000a844001440d87c50715013180000d641d03100941c035283c000b4808036001611500440700055802c0340305822070400707101030080c1484829107810710182c016050384180c00200303070030400400065001f41c074501040340c002d0034000f110b90780e80d030003186030001d414600b01101100a9003014051041103886508080c0100c801d10404803 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 265210413 1250 265209163 265209167
    0xc0f010c170c190c0618120c050307081204150e10030c03050c0301060f0c0318260f060415090609030e012307020402031f0321300b030613050c0907 65
    0x4e0b44c014901041243c41071070741149940c56000740140600202444610300d14240480340040780c0c003032540300c0c3c01101c00c00600800006107407441d07000d84000962600c0d1424680851183c021220602482400302c0725085941c1c17070035036054a150107514049004000428000c0403108020b00010300c550051006100c441c1e030080507201480040c0c248504484400d00f025506994a030740680d04054409070301103403642d0996254621036220055a03501c1c1c02a180d041b50b11848002c07035071916a8030400028012a880d44842e1030f03411004040080c001040762541c4095034010b20096010a494452105003545c1c8881c10643c101080d1203440503d0f031a0060012080c4200c20020344500d07004008107813150342a10030000c841c041a8600c003100d0b5074900c1d00c0c5440b83c600b140030b640c40d40301d80d64071400024000c025540111182c0320702180c102185240d03200750085240d071190310255941d01e04171440e44007000700c40d002d940b26900303480c03e20a03030389003580c54008010300c00c50241c0030071b00510180c1c036 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 265211663 1250 265210413 265210433
    0x308100605130312020c1e01080a060e0c180d03260408090d1401050708161d04020a11011a0f010e0904020402090d080316200c0f010c170c19 62
    0x21364403448032131400540c04812450007103681c1183d9801407130000e501c81121240458650082c1007070300d4090260342c40000c024211080f610079000385901400004424081c58401000c000401d50007030b00c1c580c05160003090980102402c201c01060064200701d000499244505d002c820300d608401082c1c1c5455a00e656590107070104080c010401c40c01020104840004007011006515000700424a0200c20080807040181c40802c035400a569511440390701c074000ac0c901210500b03400201c0403003000d050100070b601c80c502c0401081164001c02700080d1080c0100300c0103030880e189140d803008200d01008140c00d041c1079624107100c805942080103445036110581e015404503401a00c80c00c0ca84003080300c00c0780c3e1307100042004100004102500026520004110031a90340e0303081910078032802c004002a86006c04c460380d0b8082070720b8501924120111000c1c0d0001032600000030001da03a640040a0018815401111300202e02001149820050022000a0381c5880e80b846091911036000030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 265212913 1250 265211663 265211669
    0xf23060904020c0f011d0613021c080a0e100201060602070306051518070806040b0d02190b0d061e05010503040605060a15020102071a270a050109030810060513 70
    0x146800304444045a41d01e03810b66030282d940350141e1300000340142c0081e00a00d031401c04d100c0c45182c5030318a217042000c0000c0551180e010042d4080040400d5001c004129440789202000298020b0b00c1c0c0000410107170140019804030f44401c584a03c0388001c0080451101040b401161714140c402c010055002940f00c0c200d942210300041d0035200c01042944400b080002c4e0358200400c04821161314040d8084c043c030421080c0c0d42c400042d15414100000d071a2020398647d4020460b8520030054034103080d040c00d042050800ca40d81c0d0301e544070044110ad070400c803c10481e5582d20a810003c03400d81c000b420403000c05040c44440240d003801e0001e0814040a4006800c9030707034810019980c2d841b11215031028054404c882c0340340d03a241c9103000f8041c1d4410001151f001c6040c0c80d4404240b0038200f0414055440c0f4a101d80000e6013030000c40c1e0703080b454041c10307407001d21604200b04041082803089846181c041d61340d01001d0b1600d20251601540d542e0f0289003041340401c0f00d9454442314040d5441a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 265214163 1250 265212913 265212919
    0x6160509030309060a0801141e10022b020106080f06070f0e0303040b0c0d020105010510030e07031505070809030c03120a090209010b0c0c0d20030f0703060203010f23 73
    0x80d80c50480220b0319502800c000d082e040000015020070b916000840c1504132000700d00148540142d60b814060024408200118002d0302062140d000b840c05441c1050402224412554a001a5561250004800a40d403040040c0e10020400f50f90340c2030198002500b50600140f4540c242d22481a680d810001c0211080081c500790a4411030b00c2040128030203440103040380c0d11540c66040807100e590142403590994440c11012083c1d407030060060078100e48008010f003110005c4002c0c00e0f4068400d100d03006209021b105004000284100110406c03844540350000d001d00d808900030f41440c6000d06141d40783c0e40140503107203000c0f400104591010180c01c450600d50f494246441018000038a8000d5000b040700002181c0c030b030740410107014442e540e40c003181e4207040b1000a0001040010801034481406090040c400009081e0070100c0c81e80064100c54540181c0c00c00d0600b4400941c004a40d00358000004000012218001a01030005100010301c42c02040b40b407ca0400741e24240580 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 265215413 1250 265214163 265214167
    0x30a150329160e060708030c03012c0c030a020705010f0b012007030318081903020601140108010e070c0b07020a0318050102060f070e03010c0e03060a0623031002070f030908061605 79
    0x2244e45940c019101507540c13003a012522030070584001d81386500709018680803c12a491b00b17081c018444400740c0c442075204c10580040d520f580245280541c4014204060241c0801240b000540309102d416070610342000006400184100014020311600706040807052417482c80201124011904030304030307a030500b0111403521003000040141100c0b03902c050380701d000c2d500071201407509403241c0d4410303148a80c0c00e46d5400c9c0e80300c415488900340c0c180c06c0140000c1070701c001032004204000450f5004503140c11700075100046651703101000d0030110788290058000044000c10142c0040d036480081520880d074041c3c060500b00001d68562000b00700034140c009120102d07401c1070040303940e040381100c003030000c2c0064100c284018004410003481d080c082d126000020340452407602c030394002e0f01c100c0c1d400f10001d50b10033400d001c16400507c00c15641340c001c0c0d0b0b00c0e04c821003183d0f01c020a001841400300b00403603d542e040184c4502c65070380c0905070035008030080240c1c1104500700f161854250b410030907 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 265216663 1250 265215413 265215437
    0x60604180b0310050c03040c0806070903030507080702061b1203130b100512030703081006050906031005180a05130525090606090e1f0506030a15032916 67
    0xe803422100d010343c4401d103440c1c2000d1018596030b0800540c42140903040e51400c140c0d40e4000c543d40d40d1002c17a80703000007440c15103007440000e2050b00140300f0740d80101c0ba41030030044c1e141c0000302c3c40e6009030102070145128595450074500c09004200300c040024000a00310b10f041280c2d042d6001c03003848021310440c06a00064141c08030188400041d20019001e48408940442050b51381c1c0d1125000341c020510303140020301150103101c4082e007501c110303540350303402c100300032051000756040038282c909500f0b02c4030070108260f111000811240c000c9800c11030818107017013004008840000d000c20750706817102038180004c02d0000945440f61400c0c0003d0400c220b41a20f2202e0182d41035402600b0380c04d040880000700c2e15801003825098941d0300c00400c40e01e0f19810f8000c1c05603e0300c0c0484206188000200708924030309100a5070340700c50029000300e000d0248142c00300d00d04402d80c2007100d0400104494401c10107054006040202d0145c0c1414100d003415281000010708841c829410001044500 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 265217913 1250 265216663 265216669
    0x3021902060d0509010209010e1e060a050c0f0106031703100e0a2c0601050105130612060302040c031401060302090d111c0c14090705030604110903070b12060604180b 73
    0x68060310b2401508000c28140200c81e01d000c5c1d440b001d07484d030000d01070710200341c12440c4c149819444103d170343e115660210030790b106000154100c0c0e070200040c007a0034880303414050818000c0d83c081c080d50100000f506030651030150707182e124400c400b11004005004006031603088126003011788000310420700650303441b0040c042c0030b00b140d00600c000241c00307900303100400d03c018070341000c40302e00c14025039801d6a01c8500460391801101020303640040140c9041061900950400c11444041e0501080040d00ca4003c01c0595000111900000e951899501c80101110100f9409072607503280039480c0680c0840080c0807280740610103441c040161402c181c0c036a440c0d4400c201d07a10980e09132222040311a00f0000030b150300906c19600204e1b0700d05d0138000d282c030304024803506c101215121142562101c03800d10000b80040594502c3c540720421601c103c5075003c1043c0b4000307010300281b02c3d64600441d00b0790130b9050805491180030391014001480714007400340300c105001c200c2002c00a4040420000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 265219163 1250 265217913 265217917
    0x50703030b1215100501032a140f12060406080703110a0f08071503020f181201020c1015050102060105100c1e0219030b13080f180a120302190206 64
    0xd550041e2090101510707296510528444c4074411604003243c4260b40c5000540580d000190414150310340503a403040140710100c000c5450305401d01c6c00c40580e098515107841c482d480803c02c661000c1d8081541c0c00042a80041180c1c004e01c00e032001d2042c6460040c1c201e913114a2804001d01000c402406443e580d2681d4203071000034036400e060320000396070b501d40007a00d0340301c42c0c000c81c2e482611910b8900c007114000e0003140d0740c5860a9020fa403800c0c0d0507095800000d4481407850b03a004005040c5128140c4003400607207010701c031002c050034104081d40004c03012100e601b5141a10307140d2102082015a030007040e4181181c00c02d44810600442001c02142c05610002c401403c807084004440c68400d004445164000d00c01d40700c910080010019007400d5000501c00188881c00384400540c00111101e08010740602c50300b003090801c0c480d001c182c95140c0000f040c8492000d82807004444070314114101d90300528904010725a03140458078020b46480c02d2540108244481c90701000c02c540325041 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 265220413 1250 265219163 265219189
    0x60a020705031204030905100903020a0315020903060f071b05120f0d020f03011818140f0f1c09030c0e0c071a0718081510030f050708070b0a050703030b 67
    0x440c0b1120740c41c04d4507000c0c0c1303a107080e401000d0040f031201e0422082d0501406800050b660001c0c1645007007840c543d140c58184110703075610a4103540920100101c2e4038100121070003007803590200b044624101c0e03001041d504103143c0e800146500c48600c0c1c001b0500106041000d0401c11b1415656140040c80c400c2d0345218103000c82ca0181d200141440761000e014001c0c42c1030b140d440020070051103032050880c1c1a6401d103994810321900c0c1903548000144c0d8034094601400f101d40545154210350414942400701001c44028250440b45c000403000302a1414566140228100200745d0303805c0da26080550b04a0b80940115036203e40d0110f03a21662500070b5410103a03011035080d00d0f9000080f041d0808920540e40d1401081510080c0c02c0407110110410080d50f100500909010400140d84042160080c00748105400c00d810702002050304200812600c0340a00028400380d0b2800301458030b00450380d0700c450400002404210502580f00c41299a129010b01d0082000f400000000b541d03505419 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 265221663 1250 265220413 265220437
    0x12021b03040b03090709091203050604060b040801140105040c08073c08070201060b070204180f0308041a10120212031611030304050d29010e151002060a02070503 71
    0x300780080e0b8520030304011441020b03000c042d20320342a03035800040141c03806d1001c001c0091419200381d0400034820f0303006030380c42000104007042143c0d440340c0c1940d503503000360405061a5151824481201c40000801c0d004020940d4204800400c0c4480240b0321003014280504018414050001a0781c801c414000445110b4090340146124403441c24512070740707109101e010035807410019041d5401031103004125803500720032901e81000c544c02c01004002d1841c035611055040355002005c910420040007403e40319442d45040c0c1d04042c1060b1020034000090791040804140412001c200c803c08803200b1101d501800e01940c1284d80700081d8100c1445122880074030010444241c48000501c0c50b00d0a0b5014000e018107003464032003459101c0c41640980d40d040008442d00e20000b850a085040014034806080102166183d6005000302c4003030b8800765aa0100d00c007071203031110141103a00540a4201d50207080311488150294449100924000000d0f501140a505116052044913416a441 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 265222913 1250 265221663 265221667
    0x91215070903020405070c020102100f02130e042f090924160305160503060307080a03030609050a0902030d180302040908070308091218010e09070305160203070312021b03 75
    0x40c800c0102006154441603115a0514002c50700d141d006098907880103406901400c81460003590903c00703003140d44c4e0300c0100c040e400c000700f0414080a009803009010f0450f400445400e003406d0803030340080384900210412420328840d0041405c03540300c0c5c0b0344910064070304280310f0340c45070134160400008601c40c0000d20900841d168000503502c000c14410000c52441030100d1100413011800c540048030141c0d24000f030b40b88880350040c01a4041d550106006040312001d50301e8001090402c400703940200c01083e119182400f07600f10074090290b2060311074004001d0482c0da900001d0b56010300c1043d0909100035184403140c03141c0c507035410310f000e150013a109200c600658588100e0341d500c100c8090300040d51318408918000c1c0301040480440948040090820482100010404030220101414407805860070031003515003c0c0311510801c10350b200020b96180894106560384402c003042d4045400420424000a0304650042004a04803400684910803030103000881010340201500501c00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 265224163 1250 265222913 265222921
    0xa051201050a06150e0f06041206021306030207050307020f0411070c03110306100b03090a140a110a1a09060f070b0703060e0c071b1e06030e0c0105091215 68
    0x1500705500400a01d4010004681d880c6404146040c1c030851000001da01804c48a200307281c011019082c01400402c124545603507441300849081401504540085d00402c010418040b030a943e40300038031180c14103529101207a59050b407640301c1d503900288601600746c068a810b8481d0b80c0000c0800f030541d0125a51406282840329640b50503104c02c54600a0302c00514104e4200407610300d0045601d84181d96245051a55003e0281c20051540f007a80c0f040c0d060500100d100c04030210218843e660150059625909062114003400c3e904240036010040040107860507082c2200c117001c1560060640f82c0074601c0c00541c560ac80c2c1c130302030421703110046200000e10219005050080603952010000190364890007081d0700021960034150075424801c0c18042101803440c0111450308104900c04d290300c900d421000d0308510103403190107044246003813106980600c512801c94541000801c0d5404401c00001d09920860b44000d01980caa00702c0c280d00c2c0c541c104411005e2255041d22030f02e0074130b0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 265225413 1250 265224163 265224199
    0x30b12030c01150f0605030c0904060e060906030d080c09010903050303090c1908030703050c01090605101502060c0703140d0203130b0a0e0c19030f050a060606050f040e060a05 77
    0x445003589951034081c00c3c00b003080c0315100c1ca6003100c41380b40080d800030b41781c204c0a5600760002801d4000001c001c100c0c0c48005d6603244a044060005d41e040c018071818948103000e10002d000b00711902960200420841c082d40000b00c05600252186906560b0700c00b2400488903401103078001030681c807010013070041082000c580d40c40c22090680768908190301c1c8100f0445a03200c18861405240c108100500201e803241d402444007440f500c0021402c1d004035a01c05c82115000c460721214548031244c10701040f41c239040c110704d0407003ca200800c80c40c02e00000c8a500351041c80c0004088c0a80c1d078450581032856101035a402c07040e00001151203142ca900b00602c0c012000d00f04603004548000040c490742010703c03907540b038400c4060040c40802d42003001d00c45030b428030300000c40c3e02000c1c10000000040d64a081291079a218030040c084201491501400f81c503800d40181b8240300d4140002e414408216007503500b00c40450049001c1901e410340800e42e440e01715080075400c0303843c090094000038 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 265226663 1250 265225413 265225417
    0x6031b08040b09070e09060f062b0c051e03010e0d080f0612061807060306030803040b09070f0602010e060f04081c140412020d02030306010c0b0411030a1401110f04090c030b1203 78
    0xc10000030320715403562020100a03c003610302c0304050349282b2210154140c2d4294500c02c0440b4ae104440707080c0c0258803440003032110a1a41d00d03001007607500f121131203800c0c01c00f07000e00950b6200700c100a04020000c00c001030655800284400700d000e4001c000501d1998840320581d0341c0302105030a840503410090888019400c85903100c000138400e030200001c18034464070602d030882c0d41060060b42591a280d80c2d814019030003138141c2155103d5202d022807840c1e10f8905070700044c04076400010324010040c140c603041a100500714040b04000300c0401003c03461000480300500190f03821108840c2c1200802801010101103e4400c014000104410402844c0d0070540d41325164084a40300001600101c0e03481c80122220390002e4241c0305150001092220070030b0b0802d10a0b80012009500c01c80420320b42449190b080d00e0400e509141c20140d03007001e101da13031031007582117500a02c4e20200084001c420704c1184680d07840b4540d00c03580f222402e84070358440c481c405401001200b00101d6032403070070703a00d17 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 265227913 1250 265226663 265226671
    0x15130b0a15080f010e24100201090b0903070809010f02030c0106140102010e0106230103021e04031209140609040e0709020301060e0303041503021c0f0606031b08040b09070e0906 78
    0x10401c000045001c91943c043d40a0481d4110b034a03003050355039150201c119090381d00c001d0341c032404c410a90300d2005548030802c80241400650000460070001d0415040010300949006440d4200f00207000225034070b0412507101c94001c0c03c107a0051010f0590492842c0f00780c030907420641d440e080010070b54019013603020003009000d074003c0c45152140c04c40c190032103c444c405d2149503400c001b5002480c00c01800040c1c0640f40c141001800d00c40410003501000e40ca81c0440f007100c050000f0180100002421000740b40079561500700070350740c00c040c00d4006c81928100c61502c6401c02141d40c4503030b65250380282060302050402d41b2116076803041e2a03c00b070741080c0144070204034500507001e1581000800c1c1c03000c4840c0f480101c2804c0386100003d800a5001d06c640142c01c9500030102038922081d4000c128100c0000a00020138a203050401000c88010b81d0710780380c0080b40b11504880107540411a242c019401c0700d401d44d90758441030800e46c64a0a00d0b4050706014180004100320030202146240c46 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 265229163 1250 265227913 265227917
    0x6100c0c060c060e19120908060108061e0f1f150c02030708010902090426070507031b050904230f1b0105030603060103060e010b04020c030304021815130b0a15 70
    0xd85000d00d112585c4036991801d0b40083e0700e49810712900821400d038110340b52085642440c48a09445103a2036003030403c01d8004112a9001c1e109100b019201d410070b13076851510440e005a0941000e02146030030f06406080c43c00d00107141d8002e0071002640c03c4100c0001d0409011000d003141e9440800fa24005464009030700c24050840000340080c41800b690100b9540108607200c141d0303580c1c1d0703a003801c1c3c0f24880d80e01011010018003c03030001940d40061a03100d00420041c40c100e071440c94240344562025000341c1481000903800c118a442d000c80030358015500c607401d6640040038400c81d80040d0390980c0100d103e407082e182d04002c2d00f800403446a040400150b01c1250807070a0703400544032440700b0f40d40c1642641c4082c004102113121a400207820b440c46e40004604480103000003402e83c1c00100100260740c100009010131071401102a203481241c01d8060581440c008602d1400e030f0a8204109008100440358582e03070907810380c800c001c07202700140f4001456440b840501c2d0381020101540c80 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 265230413 1250 265229163 265229171
    0x1090510020c01080c040515040e070509060f070203151e13020303030601050a140a0f080702010507360e190209060405040b01020f0a0803190e0606100c0c060c06 71
    0x2140d04244564000c201015001040351000000c011100700c00000c040c04c075115414880812540d40342000d111404280c0c1400c0b9440314100400400c403184064140cad81400320412034000d440e29018190341103c8004442c10703841e1003e03400800c1c01e041a08421101c1c0d0760301c1c4010000520014201100d200c0c030b100d88210782c540c0e50590349001c41940e8103800b85d41603000340001030300c03503129000600518650313180416440510708244222500650540c2000c200034030340c03003201150301c00b080782d5100e44180300900080c1070001707000d00703d0034090004c082c0040b00403a8603111028a210003010740c0294401c0c0404042d42c54003082e12a46e000d40342146c082d00c2c00701d05034412032050b000380d682042000380698074107813074402000001c0140d00744c1e16040d40078a14201083c260140000c808460180da013480d640d241c60900301e0341e10407444000607403292404a03c0078050000140d0242d000d9826651840e0f51010880240c84480ca00314005002403150b00003c284540d01030981c01180340b20f20001c0c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 265231663 1250 265230413 265230419
    0x60f050c1e040305070e0916150f0810032607060c111b09040312180c0614070b09070b071101080f0402030a11040f020a08060a080625020106051e0109 66
    0x10aa1140303100252640d4880c5d0070a00200005004054002100800321240130448a00c40000740c070b80d03503112442c4a201c0e90800b034142c6d500700101c5818887d05141c0150b41785442401c0f181d04182c2d0380000b82060301504d0740d0440c000800b801c0302c00c002e030000700740548410141ca0110040c101140d2180300140041c0c19808404800183c1300d102c501d60210140c049002030414048111030090040d010050203212103c600020742c425922000d81c0c80c1c448048404283c00d080000d991154407207410000e504c51651074500034003080e11482d07076002c203101c002ca459842455207001c2d00fa0304810441c0720300144480030407108080c200c070145000c2e00d505c1c440d9a24400c007500c02800480700a900754010903411b01c000f0300400c5851a089900034130000f030251a035982c500032600403450070000b1865550900c003143ca40444500c008086030790013400a4506060b9615005000f44d1078040b10740c00c10385440001c5c0307000b0f400c041c019205c013070198200300055070101c80040c1d1590030901c0c0480c0581d8804 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 265232913 1250 265231663 265231717
    0x708181201241703030408070230010c0e06070f0f050613060f0603110d1704080a05100b03030a08090309040213090b030c1005070606050402040b0c10050112020904060f050c 76
    0x800f20151582010f5421540c4c3e94841c0e8920740c0c8007050480e03004035015130030612443e40401076684112180008010009050403007400c551804e00c04c0b074148002d0084d000390a030751320000c4a500a90004905459244a28020b00740038000c040c001c04074042c440400110b641d16064417841c0b50301070441448010750a100340801c44060340005032020318100c1c581442802c0003022040800e206000c50350302c03031001c4000641c094210740c02614443d00900d21140900c802081100d8851550f500c04103c0540e9030030000344d480c85540c5055086c860786200217119a0424410343d50350000c043d005543d07404001450941c17145041c000d0013101880d00b59050150f0800042c8200544406000c1c2c4000ca0903030f040503520b80d000030b881280c005485442c00300d010f856070300242c401400910b0985848a0118203031a0401080c649440b08161601c401002400c1c180e810050500e501035130250400d803580d052103806490800d00d9100158106402e006409168200400907410502031440c9001d0180c82d070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 265234163 1250 265232913 265232939
    0x40b130305030103030309110a0801020a230417030c060403030203010330030506041e090323090907030e0a2a030c0e06041b0806090c070818120124 65
    0x2016000a40500c01800064065444810b6081c05030340390b5087c1901da80000340e048109600401c0d010794010800c40c4040c1e801003007141c12144d81205400b59a28850704041c0c841c06076124200f0b6000c2ea583c09111400e2042c07040b1046007104105541c0c1503e001e0902070003030740c0300307210482e0300c4100300b07400b08078562000c100503042c1040e4811101e114450030200320007070017018001c258000c0da00d008854a030f0b5100352520340c5a00c101c4002050400690801801c11034907110300b0340202a550f56294030703202020b01202c88030841210000e40c244c442c0c041c102c00510003080040c04a202e80c1c1a0907045c04803040d80b100c20f0358440200e0142c020711072280343e441d41000d80b100410410400105101080c2440c0d14654010f002410005101c1d0307015400e400b407003203a1010b0802213090001030150300e0506030403160340240307059911031038040c159032034040910820144259000054121146c6a80d03501080b0b1109290344000b400b2030307100303d003010282050080d4003c00340070340f04000080c10107040e68 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 265235413 1250 265234163 265234201
    0x3150506060a2f0f060c03061011010b060d0b120c03150603120310060906031b050706112b06120b04030201061503060503010b090f0105010e0f0402070308040b 70
    0x1019081855540054460400f4031260204144001500c100c1c0c01090180404002e100703c4000c00300c10340c059108604244000c2c120075600c41e0200704100440e1141d00d0070352410540d038034050040840101c0e03254010100c0a15881c3c0c000d07000038011843c18955040100c4660301100c1c512a02007105614a5803000005013103605508200c0d003502090383ea11500940c803040140c15200320300c1844080c1500c0d83c0c0212a09030503815010003e03c0b4407580300c43d9100c040c01c0039040400a1810704040880141c0b20760781c81c0302c20400002502420080300d5000345000c4440402020b4694540100d142070031642002402041108000c1040000e50207004220495600c0d05480d002c0300d000d0384031441c40c1c4c90020410f805540d00c49500054032901e1601410ba500807507500001c241c0d041508250950b8000c1d10354500c1030405038103002c01005d080b10b030141110002d08140307401c8907495000c60f1402c03104005c00e5510910200d1a0401e040d04070054a00c6103101d6404070000781e84194050460482140d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 265236663 1250 265235413 265235419
    0x509040303140a0522080c0a06140718031e0c0602061902340503030718061d120111030108070603050f01120215040504090f0204060609050d02040f022203150506 71
    0x481701c5095840445c244100c840e006400e42850501c03c81c001c40d14200100310100d4165a60303010000b1116107031000150805d03194138240f032141d801039401c4c0c6002c90a078040a040040701117002e112155400300c0700410580c0c0505462541940c512010b5101d14040700c12154804000c10103489501740f80c82160704005240e0f0034550006040400c044440c02c5084160400c034246100d083c0108a0400103184110745e1a503412a0804a211500360410390903070001d01440030001080000d20300f500700c04040030006448004e444401c0208907405002103c01c8050182c00c0000041440c03a804a001c000b920440e4405110030340710308014002c505001d20607602542e0020a1420041c038052035680481c2a40d217a50a0030070b0b4540001508569401f08122070740307100c03500000d00310304090013044001c010074288040050b01d03000218211390040a80280305d41d80d81d0f00c8005c0c8401d1117905485003144c002481c03200b44100f5480041182081340025500303c4136024601541e00158020140314000107 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 265237913 1250 265236663 265236691
    0xb03070501120b1507050303060a051c030f09050a0303020102040503060106090e0c031e1503010f06080c06030405030415020a05010e0304060906030e0709020307020a150b0d0b100509040303140a05 86
    0x3420001c00105001070000d940410900089840d20f80000f024200e240d00507401f844c0c0e6410514200082c810055100354003501c0c1d102840d40d080f043c105901041940c06080180141540540c01c43e246c2c401074000981c00240c010010040c03542c15400b90096480c00da04460642c2d032a00b01c03e030b41001e800c0c8500d41c500d150040c0080c1100c8503400c040c2d41c115440e40b0f0001e00c2c1b0381c17051407030600c001c1084440c424040c00031103500f40300c0c1c6002d000d9212888200b4004201407400d1040c11625100400d0f01c19000b0b8030b00102003410020101b0484000b003c50200c6045001d0907080020345442003104141c07251360030036100c090284c030044100c80803906c142c2c5a90841501d481410f9000d4040c0400e020340c1e6005401c000500c0b000d0034002148182c081c2ea02400010b032070703481c001c0c440100e48000f0310405850f1102d4041291140f140d45682d0701e03000341c00320700a650b076150000c1103d0501c0d0401034101c40d00006010030190544c0100103401c0240940d0300d0f4903501c125031041103c40455180e03082c4051 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 265239163 1250 265237913 265237937
    0x6030b150a210c03020a0e040b3307060501050310050135060c04090608010b0612040507350606030a0809040609180b0906130605070908060f0103060b03070501 70
    0x29204080c818401e0b0410344006580c04500000b02c1d900d160740da002003900060075100300d50348841c01c60342144040340c080007465244c038041003401e901036514030002e0000c403a0013100c1000c000907805d80003440d0402d403a590784c1649410000303444207226060180c410750040401c05119405518180c54010b1071a000b960420b03000f0b02c103000a030142c4640240d00c1042c58484104040c40580d104441e8547c85654031481d044c0540e00326171056000b0035042e490200d442040c0c0d500c40049540c000043c00600429881c1c50a0207824030015078860351881681082c81c0b00d001d4275012614008103601ca24030380c1100181ca48950f29481e00f2a015a0b05800c04940e0030001b840132006454003102c003800c0047d0f02900c0b4050001110741c0440b204500c0342d10480b0680800c004034050640c000703031400103844a400d041460a03201c290003003005000649500008011501c1a818035000302004c85c201c504d01c2c244082c0c0c004101c0406e00040e29582e06004119001e4100025000100c55042e5a04520858 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 265240413 1250 265239163 265239167
    0x30f03030601030c0504170105090601060c0515060a0b0a030b01030513050c01180f0902030612011404080f0706020315040c090b1e0d06080f010506040915050603070302040f020406030b150a 83
    0x13002000981c240201400301040d00c0c000e0140d1903500c0b034030617000000c040c03c25a40311481c3c500141d010204106285007001c0000780041116039100c00d0f82a120074060f150040040c41d18001604502e40c003502c0811640c20459050304400d14820084c6c03030030420b0752203644019005452014010781154040d140002c40d0b9441044100f42039400a100000b0054807205031070b100d01c500d07500490204e6004000d00800780b501ca900e0315602c496210007001a1152440703207110003000148003800b010000304001000c00d500b04100d59003294454011542e910b0060b46000c84451240d018034055445e10203585411030158161074150b4295a010b54140340c40c00e0011031184281c14810003541c141413050302048855030064002820411016001c5040d00b02c41035821510001c010602c1a800c0110a8001c503101c03c010682140e080d80011603182c1d03903a804a40392202550000350428902000100554050b038080c000750340040d80c0c203019003240d80c410020302040c04660400001420890214000c1c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 265241663 1250 265240413 265240421
    0x203040f031d100c170a020d0809030d0203280b0105030613021303120206070504060507020d02010c12050c0d0206010518060a03150906110c0718021b01020403030e030f0303060103 79
    0x403109900d4040346030552004600440050b00304800450001084842003200703640014101d04940790446040c46d5a9a800039511019000394100780b1111002044444200b44221502c9030000c0900790360382e0a150207036000d00a94004440700081366040c00303501018890260a20707440c416510320303080d51030b038104111220341005010103000390708000ca00b4604440e03003074040082d40108550214115452806810700c0401071080d01041401c0005004041d00308096900403070301a165281c1c40c51007032006a580086102003e80342c070030b14074998850b00c2d500030014070710030020a0a6419400242a041c0da880c5400e01070b281d44400c0001c0e8292051a58009441e8001070003001499409c1d901d40f0388034450140d10984940964584184009000c1c940c098007070344410221503286031000c480c60321615000c690162111301070481405103c00b02507601074400400c42d880b014042d000d880d0019600030b500c107100440102c1c908c0b0305440f0440c80c0101e0701094051804000c0c502e15651180110010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 265242913 1250 265241663 265241687
    0xd0b1c03030b18040c09051021030507050610060f050405010207181d1015050906040e010f110702180606030406020a140315010e0f0a06050d110a080a0506040203040f03 74
    0x4800750b8601940c0d41920343c02d41c1d0141d07014800103222241010034100640d08001c02d095039000c0c40d170008004040d001d0030041100034150200e1900402240340450300c5d07108205001d081d520403401840398800c3c0e070301210000c507485030b10740607505218400e00351154041e61081d10301503000020104075600100d2440e1500500c880c0c00014401c2c44042640007201a249202c80150b0002100b005450168414035901e24858444d008c0f04a03d40000907580070310080c4814021910b5221a00c00740c070b0250070440041c102c540e02840300816031001c18500740c005150681c441c1203c44240e10006039105c1105008020181620746903030f0740c0d601c4580c041e40c0042d00c07107020031009801c001610b0300500051809030160b20725103202c1c490741200042110300b214503050b10502182c11010543d0303503281144011607515040403625410540a003200074041c1255101c1c0c00c2c0340c0014102c0c860740c0c0c0085058880c0380945010041034a403581400101c3c00103d078000c09401003014800c0219005500c80c40310 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 265244163 1250 265242913 265242919
    0x2103091210050c0301060908070b0318010902040c052a120a020705030105010314010f050105030318010c02060301090c080906100e060d0f050304140612071103040b0403080d0b1c03030b 81
    0x1401e04030001c20803508216a0440c510601000500502d944020340d800200860f1006001032420035001000b20f11019000e404081024a40689500400e410003a002c1b030300200100071102c84007002070141c2d441401c01c2c803420b07083c1581a98003054a403813a4000d0b2200315009141d42e806421440f0360b650300400740001035204a01000805580c01d000740c1d4082d42c0316150f910310202424030841c0c00e465070840c506591908010052005460000c182c44945540540309680000380000685180340d100382c029400540010003c0b801d00701030b4001020351481c60369981c8a6a5650100303d441d03203010b5403460384d0709c2d04019082008158a0600341c0d080700b00185500421102c99440d44000c1a07400802c94039500003040c04c100c044172410650184460580d0098903080401c0701d200d1882500520540504c041c0d40c0700c100d01214100300b5240a040c00240e0b5550f03560312401c00030000d40000c2d52843d03105003094550740180c00c04140b054400d9542c1d50146c0882d20265505074050400030015a030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 265245413 1250 265244163 265244173
    0x10c081608060112050112020f011110020f04170c090f160327030f0905040902060f0c0703140c0f0109030818030f1605180c0307050f07080309010b21030912 69
    0x41302c064103100e414020400d10b0303002e009901c0131344103010340515880380d03080c10700001d05454441c1c41404215103020850107074006a4a4030f0741500f641035030281e600680034486141e0940014040c0010361400b84103012a1811401d60702c40810a40d880c408544803030328414014540101540a5080110240a0962155021401108482e03e0440c815009a000030b00a5002d120955017069807480600300550b42400480d98640200350301d4410107021030801100000c0c000c0400700c0c00d0065001450344106441c680002805196030303a10720305403609100b50302c0c3c409440350540c0580d4804040300e40c08a2064184220070b0b6218422414001c0e50b9a0980a6520204100d05090100410141c80300845040c080e050005014013502c02a60068040c5481406d001300741000b201580da014049107840303513654145602511a900480200400080b0088148880303001d064003d01460507050718546445483c4000503400784d824041040c0c42034000300007101b82810012000c080381c13290341c01116 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 265246663 1250 265245413 265245437
    0x4150203040620030f0c160f060b0a0e0f090303150f12030d020a02070807060915020a080d0207060b030604151a09010602011b03150603020a1e11010c0816080601 71
    0x24810085070b043c0341000e8500004200c6403405001c00b958100b02d2040c907003400e0051600440070452024840a003401c540b09612200300030700c1d03070816001c40e800504403903020790b43c40e844d0003011401500c050b07202e0040315001454280000040c2d03031007131007070030402100b444c070b0281401030180601c0d440e56005200c10b000b41030140c100704000c00e881c0405400059859600c440001d0400c880364008a480e50884030082000c650300040407405d44819000d050300020351a1401c0e0321f0015200001400d400001c00c102e012180168042d24030507001c3c0304280240d02d565000c140d141d94044034000c1016210101c0701500c080641e11061344410a101c9034001d1003d0040011841c0409900580050f0346829010911401c040c1f100014064181000d000c2c80b20b00c2503141e140c8800c40e010b05410507a011030340743d054501c28501c21010500071b0313007596030394502000c0090806402a4002c402503003800f070640e029500ca03540252181d4190900400803c0a00d103044810701000740c01a0304000c0c55010030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 265247913 1250 265246663 265246691
    0x6070e0d300905120706051c061211010e01200708030c0a02030c010504120305030a062705130507050d02040e030406030c0f050301180b13090507090f0203041502030406 74
    0x3001621501d181e109416030070000808101c00d0f50480c50085400d964a100200c4d03001070004d050b942c6508141d92928012482d100201d4481048494032900b014800500341040c6441d140120b4000c145121a140140300195100b0074050003090008040840d801c000b02c03450b10840582c2014036099400080d03030391150030728580040b01001d2240c1c0006c2c20b0a001c501e01040503021011084c24901c0c1040d18001c0d00c174603210044500641405070000c00036134071581c13a92144010340042481100005040400c4807444180c9664080c4081c0c9003001068040311481100d0000b203902c84d0007810190308280901c040300c4a07203401260855103513030030180080018805800070340310300c0d41c000690076203052005200055000110091080030401440803042c418080c01552401e204003142000d550404100e803500b2000705214120301d014018010820041084000c07200c03405802c0c090a140070164100728441611b0083c085200710312034281e0300c14660091a4400d02894000445d40b01003008 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 265249163 1250 265247913 265247963
    0x1801090f090e0105062202030403020c09010b120709080304090f0b0904080703030606050a0e04091104050106030f050a0c050301050d060204030219030201202107150e0d0206070e0d 79
    0x4100c01d05615010007040341c100900c21140d000c4400c4454030441c2011800024000d4081c3c0c0881c107000340c0010000b410b05008025100083e400984141115030307448080d28010703000880454681c41d01240455000d074420314451041d64800005140351a240004240013424105000f0614a441d18504800e03592060140c40c8502d01455046a070740009140c018100c43e925007240e02441014040b1414280c2c1c40020b01d00410003d81d00050401c80500b481900e00740c480803240e41c090308000c0049000c1d81e140d08241860400700a09100d145c03106108101950f00035500540061801d000400c01c91038410004c4002c1d9004010051405440341c01050a0307080034244180080e012a2041085507030104166213246119150007503880c00c03c00002d40c445880c545880c990214004419150403039110031584050f42c80780a41c0c1a0304810b0142101030700d181d4000c59481d01a04004819030b0b80040744007440b03005195110342c2c0c44200b62007041542141c0503c243c417407115a190a07214000c6c1920 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 265250413 1250 265249163 265249169
    0xd23131203030608070f24030902100f020717100c210207030e0402090306040201050d14090f06010509040309120807080336120d020c06010f03020a09111801090f 71
    0x5400f0a11034105240075141c41040c0e032002c14040160350003000302207516962100b04504991030300030100101c1e0001c502404a01c400658081c40b040324800010b6000001000c510805401346c03140765503101480aa00141491040819041031403079408034041035108403031010060038003008009801c80c01716418210f2070060480c0c150300041c0d840915400211301014100102ca00b5882d10b1480000b10b80c80d4080500004d06200300810b8451b820321542e007144211a1004660245a2400c440701d0707a030740c80038200c581d0094000c54001040710304000544922407901611800e000516041820713801ca5a803401c10703106007100f4450382000640307660017540503031400c09200c904180800740f00c00c07124402003030085201504036095680c0c2000499074588900002a052b0b4035000e0015070a00a4468180145031900540f000407640194070b00b03000042d80d000b90f82840211f030310f0711540021a6280d00900f0075060381800545072103241c15200d40900702d810b2610340c42c2c1c16a52030040c0c030080c010760 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 265251663 1250 265250413 265250417
    0x120a060207050c09271e01050109050a021204110d0b0a0c0810051003180602310e04080a02070312020d03150608013b0403020d23131203 60
    0x580d01e0521508101c0c810290104480e400c0031810a03007000172205032841200860032034011800b018080091104160500baa03c4050318015400911580202005d014407000c251420022071100340e414406d89034503609118010450b070301c840c2c481002c20100e1154003544500c454000d440059000c11065025240d41040803a00f580004405045510700500951104104020410240c1d641c9510548110064203001581141c688008001140c442c1d10180004d80001000c001c184400c8411520861286800210207088103807000000d18a03441030518481005000c00d0210758407100601c0c08010500440b00303110b6503642c1d103030001c41d0480591009a0444007240120710b4240c0203c00701601c21007900420581040c00241070240306018012a040e070f80c00e403082c106200c52074030030324610300c01140c001d072090381d90004204560101c60840040c011155901c401900414541d0355040c4e0910350040d400310003041491045e044240200100b0001010000d4988006200c01422034000d03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 265252913 1250 265251663 265251667
    0xc0102160804152f010b03031b100e03030a0507020c04060603060f050603041a1e0a0504060b09100302060a0c0b0f09072102060f0d241d15120a0602 65
    0x4a2046544007100f0a5032109020440028103540b0310712000c1040100740143c0c44080c14030030584540d005042d440341e415090311000510942d400c82030004501d10540801c100c6410000d4442548292140c20340c07561095441480030888000f070980040381e0214803881104d4000a490001800f41d404070760100c0003180d56038100b4040d2801200316600540303425900145035081507070314400e2031701c1c030b0b01802e80b8011480300200c2d41c400c02d007400b180d240442088180c7c405041c0542620014003054804a48492a10324012040c1c209600191b10640c001140c011060303196800744545940241081401c119042201d10001141240c05601a884c00e89000c0120b20303001c0c13400ea1512201c0d4110000c410620075840907210007441840329280d905568298481000650803109800f80c0c07600c8060840c102503d0090581b000746031103800340b19401c40401c4580e5603190b20180c0560846903401d20071444d00000303000c0716001d08007140095000d05a41540c0000b815000d041100c0b10000303d42060700 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 265254163 1250 265252913 265252919
    0x80a0314040b07080a0b03060a1107020904110a170c0409060b12030309010c050702091b0409020c0c0a09020f18031212070e0102070b03010e041103100c02120f0403080c0102160804 79
    0x1009040e56407221205c9400c000403944000004e0751008010f1000781c0668580d4a12a00380b0b07092810340c0e07401036001c2d1809159051a1a10b807200180d000f082074045d089a0600140c4d4a0342c040e21800d540c2c2c68034024010300311459044c403014007000b02061b0b030301c29101d81300c943c19901c07822a44040011408051070b22403d00c01011420f582410b48804108081072000341d000d07aa840c3c0c101d54011040e5100b0f501c1e54145c5007105422401a6400040d8407440450300d44900103001c80c400703441c3c0c0012115100559200e004070340481c0a5040740308040c2800340948090030b8035258201820004c0141211a4550800e030b58041961001303110001d8018a0418404002c0d0480d004580c01ca100f4009405003c1c2004251855400144510a03110340c008020406002010124002802c1d001e0181c40403541040a07a50103003003030008203030040c4505002e1401d83c141d80402e5420004080c0c062901d080c1c955190000f640e006203c22080555003080341084500c0c42007440724003148542c1c18076442e146 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 265255413 1250 265254163 265254167
    0x110d09090b0603010f05120a0501090605070215070e12120406050403020a090b090a020d09050f062710021b071410050a120c0905150c060c16080a0314040b07 69
    0x140d62581c07a80240c1c01800140030b001401c11180060300d0099480b40b804002001c48a0300d04004610090065403038041c030302080c40310942145102c0c00303071902100c008003070030000c803140184222514400540305038401d0b840340c540074204090103103170320048032464003c08410030b41a03803144e4084400316000080803c1181400440c02c8000c0042c1c85003080403c7e03408000c590048002002042c0340c41c1d00280c1c2100190b4194001002c9603086801c0303400070070620207141c1d45d07500144d40180d04045850301c007802d00d40401801d21003d14501016281a0490341c002c0f01c00b03500482d036006030301019510400c0c1a1181089a08010400a05c4142e0590764a2003440204003100580c0030400c10108042812143c009031302c84201c8500b0310002410851003e070440b242d0001707800c255802410071600116000b1000064032038961403000b600c2d01500d582d110840d003407103207115081c68040a000c1031400b280716200900a41856070030041000c0f07560541100400c3e10446013107600e10240018025030759 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 265256663 1250 265255413 265255421
    0x20a141e0c010806010507080901081b0304060b04050c090a0e0702010905061003020f06030f0712110d0212060301180602031b0313050d02030315091506120a0e03070c15110d0909 78
    0x804c6c02d1491800c0c0382030302caa908502c103c0c1c01242c140000384003ca11521408000340d9403800070032040c1912400c0516000015102c8030717080c2444ac50070320011074201500181215030300107000b001070303409600c4e0079104594180010000c00c2955a507260090205070103124951243d43d50008107801070b42140304000c03507014120019806401c051040141d0b41007a401890780040141c2001400380a01000400240c0080c44c0310440440c4d01080307a50120445801500ba40281d40d995079519540f40d8007491b08a80d640d00707900052225113880321002c00c0d099401160450310440b000d000940e44251441e11650003907806200d41c1014441038000c1c00400d110250303810740d040c4060351460800c1d0000e082800305111075684105a510040342d54040014107400c210440900100d46520424680c41100300044a803c51a6414410030300310380176000c400c03544803507070100314440118107101c94010b402c10710461403c2488403240d20401d00600800c02440c007101d240e555450a2402c18143c44161 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 265257913 1250 265256663 265256671
    0x5061816020709050f060d0615080a0c05040902010c0206031003060515040e060c04061404030204050c070507140907080a1d010515150a03090804030b0c18060a020a141e0c0108 77
    0x2e140000317100450f0740507070646030480011200c2c81946005810114018541605400d40341d0b400b0480002d01401c002c10203d045601568a4520f81581e942c2031205441d01c80e5802400592001c40d580c0c0145003240c003440d0881740c0810080d94640d203984d1114120b0781c0c15100109402c6d0500038504003468540188107840b040301c80a0038150a003180740f0703e00c50041d4086c280078000e441008040700e140007001c0c2e400850f0024018003c0c2d003003102200e5600d80c4a01c034207a8940c00b5900d030104002404041e8800d1061001d40024510341c2c0c0c01008413598040580001011900c0720b594840003107450a244440d0300001000084034100701391040c01c00e94621140c05c0c000c24245440c6074070000540c0c00e44440704400e050214240d41d0524000c001449070390401001c0c440c801042c441e4611202014108202e5070322059900b8010350410000b0900400308203500503403080401000041000030250b0a0030310310b00403a0701c0400d002d98041810301039190b1240a80d44940d200781281c2da0310600795a00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 265259163 1250 265257913 265257929
    0x5130f030507170703090b1606150306060e0106020604061a0d05010e0105100506040b0c070f030804090f11032a070602090a0e0403020a0803060d0c060809070e0108070603050618160207 81
    0x5004c9245d03401611006480c8222050b040002c00c5c6820a6141c42482c903a82e80e40c003810810480f6410b10f1810201e620602056404615100c001328680720388042e510f060316442d40082002c3d5449988800c041c10030400401e254042c501c01e00c0c00d1545602041ca19103911940010130002d03154043e240c00c44400501408007072036180420045925231800315002e0351505070600e40d0f41c2c0381008400c0c0c80d14180d50300004641120f0032001081c0640c88003c0c00c1501d1002d40c0900002c5181d200c544159070345856091980d030070030008103000a600c269881703da610100c4003d40003c41ca00080e54250308030142c29650309400003000110303482c082071500080d01d00c0301d1400b003640c1020b45000b540c8241d401c0000b4400500080421030f03940c2d402021240d029400689140c0054490400801c0d5071000c3d10f251000d4480c2c1e07030700850040700c40c44c540ca05075461200241300591628400314003804001e003c09401680c10071910081030715081c0c41c0c5210780122804485290b0320108000d190001e564071000c2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 265260413 1250 265259163 265259167
    0x120b01020a08190e2b08160803040302010509010204050901120303090818040501050a06051204030e060a0908010c021c0e190e0f01060f0507060506030f0601090606020f150a05130f03050717 83
    0x7000703c540903002d40c02d02c40c5410b1501142410f03858503c1d0a0707ca00c40c0849104500c40d00804100705149004500c201e120303034001d0103951500802507090b0302a03801100c3c2c0c005081c40051003207a0f0444913054059001c0e28001c1030914594407041e85c90b91251850300d140e0072484020b602c440c10706025484c01401d09031788c0001e0045c50481e00070700c00d00444990021001c1000041070915200324800210384030001c1c10aaa213105d841000b03002d90015100c0d010700c0c3e50a10742030324041c0e400400c111301c8000115138005242080544225409414024043d52015009550802000c07043d81180d01600c4110391400c070b2420000e44643c0d040f45c0c1640f04608120104048550481d804002d8070f0002e82d100d04003180946a902c000b904025001300306150501c00e850000900c03a20503040042115001d4080d12003021001441949813803a105c413011030080c1d0030010841e100060350200d544005041030314908010241ea03450750f0581500c0c0700750001180400e11500f8041c180110780c0d03500c00d031030000c0340c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 265261663 1250 265260413 265260439
    0x105092404081515151b0d080108010b01080103030503100e090c0415140f0f131d0c011e05040510020607080609060d030c0615030501090b07030c120b01020a08190e 72
    0x10300403110262840717006003492100c2460854031441a21900050070f20000240c4000140d119500c95404201d840001c0c400400040d80310310610805910140603580e03400795a003107450a1314954005886150402200c1c0b400180e580322045495000b681513501030710100c401d950070001981d609043e0a2002510392008201800101a90720030307003081074500387c0c020428600000e18503c0c01303118080e00903a21481c031580d80302c03090384040c02902d100640c1d18008424014030781d5454031142401408102402e0074182080c400c0410900072a48501c0d01500d0551103801280812a0014410000d0390004050042c0c079604214055441074041c0c5541200d4034209000503003803d00e001e0045c0507c1021194030f81030291507048a400e820585440390102c5949291007402440039403000d0351100880c801040806110303005962004e141a91803c011210b0807207840c000b448118603041c19072141c558031100180111000c2c181c203942c1c500c500c010800e6041d402400c060103c1120b43d1055080110720 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 265262913 1250 265261663 265261681
    0x61401020a060b030a0f0b06030715200111040612060602031303061a040e030405090903070b3c0708060d02130b060c0604080403050f060708010501050924040815 71
    0x301e54000d8001e8004140342c080540840d05044142d03201500103065241e1040c107101da0203204a0181c00300740c0c203d82c206551000c403400c1e2a078400c40140002240c9408412210307480c0d0715240c0700800160000285030f4007244118071a6407283d44001c020424285003c8080034440c864400240920b00281d13103001800646280107003400d00000381415502e00321207140602481a20985580142003045502011010681d41740c00c180700c1c00d446201d01c034000a410740404015104020323841034000700b0070b0312601007040d40801d589800c6007101d03500c40942070f0310081642101c000700f000c0e0b0407070801c03c1c20200c000078040340b030083c2a40d0140c3c003214050030060700d91100a5503543c100400c00140d0200507800607005100d1081c91011510590007444140f00122b4000c1c000c59110b17201707d0704000c000f0518140c0742c3c601261408042404e07840104a2540203000802c50361780e0062800c1d04061100b0202c1342500680e5592441a100c0800c007400708201c104100b2501c2100c07181f1200e1146003041003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 265264163 1250 265262913 265262923
    0x10806090a060905100f06180b06070f0201021c0c031b2003010b0406171e150a0908070506060310090c1202010c12080a060509060117070e2206140102 66
    0x38002076460080c8004d0107003d10000601c0689210f040c0b181d10840718071070003d45107a00441959090103901c031011001d4138483c403c0e2190002c0c1807181044407940703456030001b20501d0203070305600482c4981003001040448010806829440b80301c3d000c6881c1c24000e05440e2090521044238540000ca9400f0425505079a03000504507544600d41031126001329015109980d61950071900304400070500409000700b00c03014000d040304950b100c44e50b120001c108242c030701404504a070014841402c4035000001c4280c0e1000f020040824110510307a02c2500941c000030013500c3c150424030600003035180911907070519600b800c00512004d5075075210b51340064411320030848800302000c0c4600071a4014602200020303000381e90004401d60609001c4c0c5480b0781100c102d2300181c901400481d0714a0000a07507801000103944521140c2d513a0601601300b90b80213410241402035200800d251a69240c1000c149504134820161841207860068019103500b40c0204a5030041070103c2c00702640d00184e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 265265413 1250 265264163 265264183
    0x4051507080406050703110423010507120f0c0b0c03060901060305060a061805060408210703120203060a08030f0a120501061718061512120a0302180d051501080609 72
    0x74001840d8172440d0313069005041c0101d5074140c1c00d4002c90009014041c0d054412143c801c4001c041501d44440d000459503482644002402c0070003084200222502c2166003401540d080e05216481041c1901c600f401e0901c01c4440b898189000020494030703060040e10a40100903d0a05100c0c600300000042c4422005000d90410000c2140c1e00c5840003440d020500010080039040556550300e41c0d20954440a02040409421000200f015464006034049070040c40d0583c0e5a0110240c801188101950024004943c0300c014603001140c811402d00041100c2104c03a8410390790f85135800d201424243c1c0400c02000100e207001c004009854011501c03c4009003010440055a40d40d500340310600f141003107404140c0d1058504110414036550310340c00b8440307001c43c2c0c1400b03080d5211a04558441d0216145222060f00384203100f0028001e030042c2c0b4501350201c80500f070740ba82d124042000326005040c2540c1c035030302100d18a05d034020000c00050140006401a01c05131416541071907a52800394 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 265266663 1250 265265413 265265423
    0x20c0109060518011e050702180403091a070606080d09050409110405040206071a04020109120c140109030b1311030a0503030114040f0c0c020907020c0f040c110303010e040515070804 80
    0x40f50780156885500f065800400b21282840a101441030007000c41c0c01440381240150b0221100b10041c0c0c0c0e00404c0144540d03803554440d80c95034107006541c00c9140310400c011096040c1441113030300140041c0200c001905e501c0009014440040c80d00402c0e071205540054083c1d4507000000c00800c0d0020b00c1c1c072201c020700f1364004c2040d031218800320b040b40c0304021003c2d1541100300c2024204050304800c55001360300176078440010039126440303402402d800407801091000e000400b0481c01151103002c0c2464030701414020745140d52601c80c0e90310403004980803080d80c162440d5880030480c1d000c03c6d415248000390024090b02c07085940d450760764841070081c1c1d00241e00e010112502c1d9620b582010314260000c80c0700780706480ca02200500400c0d040e00040b0700c100e83c22000203c0091000800e04050031008003d1fa6070340f08541c060200902d40c401101080010b00550035103081ca040000714004c3c05052900a0705d0b2070182012410024003012155651000d2000d010403541d0241840c0d40040d000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 265267913 1250 265266663 265266697
    0x30a02060310051c120503150f06040f060305090105162c04020c010506010806010e240c010e0318031222051c03110d090303110c0301050a060501020c01090605 70
    0x1542d01c03804228071503444140d00c455240001c00034030500b16003601c821441020400c049403990300b82560399020807210400000b80c00b00186480c7e140c0b48900224405024040d039142c103481d100e0001a02e00c140c0c00100100341c03203500303100408009100307a65000b45a14001e9580902a28005180d0300d240d400b08140d0300e008006c4c1040400c3c3c0e00501000e0003030000d10455813003c01c03440300f0707019000844066000c140c011001504c5540500703040600120010700c034425a4080904104100502d80c0754450043c005100c00811800244914941110100021500c134084210081e01c1d40300d40c014481d000340c0086180781c002084100c01d5440059030615884409950800004200b445503840190700401c201410102c11485203800700000b40070340c4c2c5007e032602a2500080d035a41c40c05c10790500156000c2c40400c0844d00c80c0e1502d0b11000c0707150b0b09940056601100003070a44000340c801402459554008204641c0c040210270400d210a0800008581c50301f18080c00e1405141c9280f40c80d201e007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 265269163 1250 265267913 265267921
    0x10e070306090921030603021c03030b03010203010326071a060402090a0f1a07051e160b0901030c0e01081f030c09020d2f0706061706070914030a020603 67
    0x41e80014014201c2650204a1407609007404018041060036072401c0d2a5000815600a44039008040c256a00a4031a00601511524001884500c840107504045da12180c080c1c581d40e081c00214001c50160450402c00c40c1c012076104e201c43d103041c0da964105a420400b0350700041444540d990011004040c501039a0b40e0800820080c1c0314080420780d0010311000c01092010b420101c1034296002d40858a44040c5000408a40751184c90740280c40c55010151121400384001c40c448620042c4609841401d42c14400003840400c15401400d214107000c100303d0010759251281d5400c403000d40c5840d8690442020020b080000098420010b070468090b0f4014034400d40c183e02c00c002c66100c8104c0080c1c40d65100010029000b0318210a409800e064000110f04103201d168901c002030f091400d900600f94040000543d80004402c50700c50b07131031720b000140a0390000211168103844d0005030025252001c0020700c0c0e1101604580300c0411008003102468400240344102c1da03034140e5845a898503 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 265270413 1250 265269163 265269167
    0x10f080613201c0c091104030c0b18060f070b0c0301060c030e2103090a0e04121107050a091b02011a19080a0309060201050901090f081309050c09030c0315010e07 71
    0x4103e801c2842c51501140380c00401c00f0000130b610403030b070b04403a0410a24220610015851081c2d10028100740d038442c4090000703422180050108003691004901c511680201050803500000c50131849294089011002d02104101d42c3da44001c550300c0c3c292943d0b041810182c01c03000c0110740a07080103441918595a03484589503860132541d081c0e0314014520580c0c44950392075200745c91403400341100c0d403c0094001c000c0c400d490300859100048042c10304040c001241c2600300c40c0e100c04214891100c00040755110800d1101c003501010001054008400360000e54031603440725040c04582c50551914024000c500308110204c0342101d650708007010b43c0d10340248048544e0003243e11030264440c400200340c0c00072030034001c5840703030340092086964010441e0700703c1e40c0503030015100c0400d1514a400181418000780541e0f0201500740218030b4440003840121901183c0b00c80391264005504038840c5010002c1003102c5400b01c0c0149010064903000030100b51041c1b282d0f41d1440310362000700f50024 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 265271663 1250 265270413 265270429
    0x3050c041b081803162303090108070201022203031b111002010f05010e090f030c06132604080f010501051011071707031101030203060d080a0207030803010f08061320 73
    0x84440004c5a855125100c0301d011514240c030012500007500408105444400302d644118628800c8040c5060042040042d51604001020a8110755007045074020600c50301034442542215400704030b01c624294a8040e107110300c15203100761807000302d8202c000060704200c100c1c3c503104010b503210312503803085a00c207a01500d0b00004000314a42440004030303d20340259078440c4104049011262a02c01d2103a00603100e104040e900005c9401100006203052010510080e009106407107400c1c1c0b001d609104149a6840f000c40e41c904001c00007000c001048041010040d82c0d21010300030062940340200050a9205e1400c50030103200080f5050020309038140300850043c444003c1b1021400300314a07890351201010700040f5204020341860400c03a510034829240318204c040d103c00d00e2112aa2980f00140e00810025005c511404c40044001540c0c00c000d10f00815900c20f1044600d0f062044060a00c00010088031801e40c1c1d94541e0b002154000300920404018032001032501003080c000318141c5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 265272913 1250 265271663 265271701
    0xd09020612040314070c060e060c0105100f05010f05070f1406011202040c0c02090604090503130308130617040821070c050c030d021b04060f030c03050c041b08 70
    0x4030100d0810300744903415058510892013543c0e00c0b594080c000300d001c03d0328010700501810001c3c2c4070009000150050f44030a0400000405d020304041c52200f0442c01c0d20801c4902c0002c000080e041044403400d00c6520001034070090800350018011858000d0460003a00c02c003a007454040360a0005110030704000c1100345036004107a0780d581d0713100c003004010b40384001d074100d000d10710f002039114101380706807030340c04006034028140c21a5840c2c5004100c081d20b0ba0500503a00781c041000252101c11641c0052002148121040da4803072403550004640301001d0b0780300b54184900039141c4141c00c202c140c0003550055011100c1c80e19850b2101c41319a840c0505c3e0b002c400381d80c00b2003080c001c0403500308090481c0300d4800c038201c600c3c503081003040c117440701c100803013060142e40250500c000a2502d00320302491407402800c0041d1469035600100310f0424940e0040d02d0410030310405000344501880b2800295030103450510805001c01c089d09041032540e0089030411120501041c00c400c003140c501041 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 265274163 1250 265272913 265272919
    0x30e10021b1603170307050a0503060310060f06020115061b03020708030304060203010e061f0c110904030807110705100c11041410060216050108060303041d0f060d0b0109020d0902 79
    0x10418141a480345840a81d0105841001319898901940c2d5880750440744035007aa655801d0074008041e80580d429000a85250f615001d2480d000140500501c00c0307200404551300c0e05402940340c214081e0866100c11030740306404000c842c041c450030341c01070940500505c3c1020310281020342401c00f28100040c40c1c001144078080003041c007050000c690041c41c10f0b1160306900d000d0f6600c4210400204960100207104022070b0f01c113000b44001d004810142c0818000d021150145480c08002180304504070760442c00308099200b070240076580a001d0b2082a00c042c401041e81c14202400220410500e011840401401e280340c0d1040055804140000a02c06401840000ea1401c20300d15280c5085400481d03c8840c07040c002591440055001108551401000c45130f03400d004c011560b59030003e103083d4151004000001da02010b010b811021040c0c0802c02414504044030800010080076001d0340c03183c1104405000411840885503046071302171080141d58811121600000c0e1014200c00b0b94 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 265275413 1250 265274163 265274173
    0x9010f2f0307050d060e15010503090607030e0a080c0d110d020a0807140a0f060b1c081303120302040e011a030a0e1e071809050a0602030702030f0a030b010807030e10021b 75
    0x150141c1e070f01b01c8090250f40b100f90885480501c1300011180c41c003013110318441560048c00402c2d5414001c1e400360b9181c4003404261203580c24142c071500300650054071018a80c0e481004240301c5140c1c80705880552014001c090110601c0c4144025620101c081000d055544001205005c002c270111005508845010940c3c080b45410304103040401d07903c02003074504600b01201c4514504d00100d0076210080c0741125403080341403e4a81d0003032600002280030603080c2d040d1010000c100801c1c25101522501c0c0d502603500c6040000b441c44845060f400061130401003e03c0d03200709252395007640e138403041d10744000402c4040e89186503d01080f100021403040942484909601400315580042d10118859803c0c80c403140c2564400712120450060450741021840c07400051494000390303000032081c4116403c00103059441650380d440000c0841c0825070300c5160000c2d41d40c0060400e64401d8043c102007201c1e03d02059010740395001c55814104003a400120840000000344019000040002c1202d07 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 265276663 1250 265275413 265275419
    0x31d0f0909210c0a06180215040f0b0a08040b0a14070c230304030f030e06040f030203010b220905030d0501030b190e0c0904031709010f2f0307050d06 66
    0x391541e000ca84190142e4a44403200340090004008985941216100620110515032146802020040c0a00d42a80b00703841042015030781d00390582012144180b0304680d6189441104044c400f11507100016040c3c0a1001d0000e080c4c001c0750765548103400100c1c19849580b140c4114004048150801510381b10783d005000c1c550354000d50070004980315511050211611002808203410300010881080d07008110600000782c1101c00c003014a84603061250140070708000180380b54001d03400c10b034401071804c402002540b07424064541e50020949402003810200300c0410301c1540b000141c10411520f80c003031142000420000c49400c08000d820400c1203584174a0079680201094801d5221454240c0c0043c10302c1c0600d04c01d03011141a032a005180700741088090080c01a0002d01c01da00b40078214840541134003400d9403c1e80f0802c039510000800d00c400c043e508045450f014080d00c2e5041e01c4200c80d50f030f80c850701c01c010f02040c0d1035040155141d03030300c003c1c04803080d200e12f8100c0c244040c00c3c60800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 265277913 1250 265276663 265276681
    0x3080307080c160302101d0d030c050423010e040510140109030503030a0b0108010b030c0406030b01031806050105030607230705010b0307090b13090809040f020903010c0203040e01080604031d0f09 86
    0xb000440784034401441f19101300d02d2003250100d80080c0d80c41d00d9810200120745614044c0d808404210b81c1810b140d400d040c1d03503a6021307640300b00401b038084c01303d420401e602c9069a8400405001c41404840400075030a022158610b007075518000c0394424020b141c1445203580c055400c1e2001194400101c9941e4038040008001510040d62003902003000d80c80042002c2985000780d0b4810118103642c207040c149005403ca000d4100307400143c1c103061b61076503040503c070003c50046003103602540300421507501d0403091501e03010f00184070b0000c000104590300104958040d0411601c401881d01c80d844101b2818224014550500000c1e4140706101c40041c45001540005455541c11a02d401c1c604121120410644580003801840f03182c0401c60300c0000d02c1d0591000c1d081c40c0c440d200c0141000c1011010074216413ba000e06400359202103010800654048090f034050481900605201c0c102650050500118890060142060116035010301e0b01c0c2c0425842e110000200360a425003007488207 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 265279163 1250 265277913 265277923
    0x807060314060904032c0a0b0c0d05030105011205221a060d030516030c0503030c040905010510080127021902160f051203070503030c0406090801050103080307080c160302 75
    0x54100501d44000052150326001c00100d00c9650180c48060040b1302e0840c0741801070700a100aa8030404814142e8151a00d890000d10040c2114070500c550f03c241480541d45400c001098600800c8000c000600c60350742e101b07244004c00c2148480209198552110640b540140c020345100f260480c20003c10034000d44059125504040d04031844140d11441c0510a1a502048014020a0040116040d0303c40d03500c204080d01406440e1425103c141c036542c0d20700315030042d502e02c0108880070400780200e802d64400c0701d0040c50101c070954507003d0882006418903105104400c960340c0030704501c4940340c24421f901d5903140409601195581014038060603842820309461005100c1c05404420202110110328103a81d1401d0500706828640ba0800010b0f41c140300c107520480c08140b0440f80050003c001a500800800c00456122400d0810007440c03411343e50301c806566030400c401080454601c2d002c0700d8000b0100d14203203c1607641e001f20b4030802d00c0780354122010308507482a400e00381079010407 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 265280413 1250 265279163 265279181
    0x3030b04230705071e051905030301060e010c0c030314071b0906170628020403060504211b060204050303070309030b060d0206040504020a022e1401080c010f0908070603 74
    0x102040e01d5480714501201c1c41c0c000e442009000d0381e00030404079a006030045000e05140d00c101c08440c140300035010032502403480b2850840e0300e5400803005111a5404c0042800d1003802031a05421248554441100c80061031002609200201190948080041c0c08550203030350000c2d0200105602c1e5035240b81a41c41c03610030640c0a900d0841c0c0031a164041c0003a0784404140e00f0018402030712541d5418000c2150b517400211000d120315580000115680041c0000758000c0c0000152898141440c0c0d6215446142d800c100f10081d66132540c425400c0075166171740c0c0f400c00c00f0442100c1d01c80d1820000910854004907850b2101207801d4003010352002c0c03480e050343c0c811480f61486841304020720400f00610400258040c1c8140401c0c00b03d41410ba0240039078440300e10490700404c0c103612441c1c100c003404c0c1411002c40e440302d00544072030403950b009140c414401d03604040d01542c036004200391144440810f40781003001314441490018130802100d005005042c00b42e44100382d1b1040081c0007043c0b240d0f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 265281663 1250 265280413 265280471
    0x306040b041707080d050601031d0715020105060303030114150d0f0e0c18060612072003070c171005070e01090f14011b0501020d14091f0903030b04 65
    0x2614441e42c41500c0d80686490541c0a80458105481c007a1030030b01a1500400140c1019624442420015200e603400b800201c1e003080a030905500b840c07100503910a0000002c0190780c1400d05000c51501c00008503070441c1e03400745410100e86185400901088940b484000311180041181e030b40300002ea03408180050f0b0130f203000b0841c1804030400b03d922044054000d83d40020490b1407a07406a091840f15984040010b20702858400004e01504090406850810016406c800d440c07a07051031039225040c10690300c078004c6080131425a29501503405a010300a01010741d500c0405500d8820455005a110122410300c01860070b0301000f80300c60340d1165080e00013940041c0024012603515480816241000ca180d000281100019a0040c06103000d0320580d07a500e00d074a001085081c8007074031900e0095107011076650200c00c64100410f8019007403030f01c29040b100c030000810101074200709070a100d80300081040d16040c24150018020480c0c00341d0840c0c2410124404580220b1550000480c11 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 265282913 1250 265281663 265281683
    0x602041d070315081b010306030206121605120c0f07050615030709020319020304030903080c030301090509010506030a0308090114010f090e28020f18090615010804020f040b0306040b04 81
    0x10010724110b5034002c0c810f50206802101c2da00c85c41c92813605803034640c0181810007252066695011482030703488005a1075040d40c01900344070119020b0400c01148954030f1400e0f03030618820a64445081202405032240070078002102c008001d4000b05960311580c200703068601c40e1910200700e40300c814091510910a006120020845640520a6902030b04002d0760b50486040941802d034002e500240c01035092140f044000030010310f00c50010402d4400401c051920303549842d403031105980e03016084041990400c3e082140b1928000b8034034080072303054500340c44a511519242401003203001220301244030210000b0402e01e40080d4070f04115000d001042190130302282c0495114042080c90446c1441c59800c0032a100c4d02806007050381034001842800b44280304d10000d154115400e0030645e82e03040c00c4003000700c2c0c4001440161340c0102134810342107491481c000000c0103080002c0000b4450074030041030501c1904e580e4400b0440400150451301e0b1790500b070800c072020100484c0c0031902c51800d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 265284163 1250 265282913 265282931
    0x2110030c08011e0b030307080c030a0e0a061e0504150206061903052e06060c12030204050d021921200d0204020a03110f040905010f0e04020603040602041d0703 70
    0x8144102c92031180381c0680f45203011246403801000d0103c040f8015418441485840081580300c80280101c1e100f180044d0358403c00540040e150b4a240c8011a20170148000304001c80b17a0072120214144140241420041c09220001c1e51540076a0300100ca0310074803002c040300060b030001f6080b07000b6113080740c50364081ca4020000426080d041c1c00000c0c15500040110395558000c0007046400041c4500743c56000141254503c046803c1030344410000346403041c2d08410700c0203080b078021000c1d18030714007036182904082c0400c07664419201300900030460003504100310140882d0607409010344404800e6004111515803040020310701d000e48650308404a141c10030807401a4014001c1d00150843c0d8901809070201700083d00107140b18014591604c4c01c0c0d507008136220000740820000380b40159256402c000442080f564142c0088290032031040382800601040e040e240c7e8001e504403140da0b601d0344ca9141040280c000d5602c1004002214001441f1703000505c05418031031030b100c1c1d03010800313001c0e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 265285413 1250 265284163 265284179
    0xc1401031b0c06200702011202070503072102070f12080d0c21050105011d010309020d1b06020313030224070c0914060f0906030f0f060717011401052110030c 69
    0x10300305400b0f504d50030050382005500502d800c0710004a580c01c01801e00d00c150310b80c5403d40d8001d000442c0d030001084a91050b00950001091504c0b102e07100a124031801c000182100c14164025000d54500742c4000600304108601101c06080c84480180f00c0c00007100005010400c030007814000010001c064401c40e60002d00c40d4504a89050391100b085006000407840140090102030b4101901c9859043c0561212a108915288101452150b260b00030111a903080c54a030401d6045420400c10404c4070101303298a802520380450780c503080f0705614440d40700700d00c500c0141290313003000100d60542400065445070341190501e007400d002540c0540020744000c0400c0724050380c001e201c40500c16850400d459803c1e48030304094100c40007500128502c03490204568600122980004104141107500c411203240512030f190300355855504096038080c1900c01494035074104000410340042103d0010403411000302102c0003000d1030308104060107003245813800305039003546601d600010f00b02 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 265286663 1250 265285413 265285451
    0x12010f05100e13020f030921090a03020613080d0201051504020c2505040207080705010609060810020304231e120706020904021e030a0e03070c1401031b0c06 69
    0xe80c0580d00d0b806841c500000700300400c00e2914183c5140d981c00d028840c83c09021000843c050b01007480244040d6480140c10b100e03801c81010034644d40381041c00360305566100ca00049040c1c83e811038001e9128104080c1c011803000d035550004401e403007600ca880000701e4040d84401e01513507101c40d41c001100324007000e100c1a44294035a032807991384481e0380f040740d40244000213000390b00700c86c481c0361510741d4500000301a41c024030019034041000040e44000c200007403041d1001403085501c1405018a4414110f031241c000001144210b50000002010455141024036120740b800030b54404441032100103d03500c0000a0032641c89080720320344a11300c0c0c4000900d000d01030748039203011450140c2c00c0d41c0c1c0101035040304c0403032500603409100310300000313000b40c0700c0385840c122003001e880c3c0302d10b843d06a00c0b0a403010001e000e60b141c5c008000100201d02044205016591002101d031260701210004800812010180028500c94820100103c0d58000b0702c1154660084070248030b00c280012030000e0003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 265287769 1106 265286663 265286689
    0x60d0606080709051b0313050708010908092e050901021009032f030d0504020d14010606030c09050303070308091504050304230d1b050612010f05 64
    0x1010b00384c8a42e42d84200c1c40d0101140e0541c0e0341030744c21624032002e009240403154000100b028400100f040000030401c41c0002c0103504000d007029150781e00301040291140c08041c3c1820000382481c00c445003c190f00300d013290076034220602c0030f4a440d03110100203415801140c4280c50510181c3c03141e01e6420703000b40c4882d07002e00d8441e046400044564403000b25030741120081b0041007440007058a4034181400790005580d1106c1c000a407505034003a400400308120b43d50800340844045d0002d400303c6a903a201400a8848410300b500d454040e405055010351040c0413190109100303000c43c3e034201110b2401d40d803c61801d0043c000e42c80c01d0450f000d803410f6200007030403c2101c480d0044c200128940d801c0f08400c08003004000340d00c921030060003501407a85000d13005101c2a21701c2405004110081131203640f00709140c2c0c1c2140311502440303401456680c003400010982400130788a850 = true := by decide +kernel

theorem cover : BRFrame.Cov 265107913 265287769 := by
  have h0 := BRFrame.cov_init 265107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 265107913 ≤ n) (h2 : n < 265287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
