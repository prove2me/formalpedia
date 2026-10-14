-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3256
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:07:33.681326+00:00
-- url     : https://prove2.me/submissions/565a5a4f-15a9-4aa0-8283-9808704f7000

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 585431654 ≤ n < 585611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 585432904 1250 585431654 585431663
    0x6050f0307290906030403260403051b0304052e08160507061407091a032a0d111c05040506040212030d15060201050702030a120b0d0803040b22 63
    0x400d0010075140c008040503402d54544011454000303031100180c07054000b03807010b4000070f0f4403d00140d0305c0c80303504404601b07144080500380c08500d0151380040c554883c041c41410349400908549045890401c1030f00c0c09800014000c03020740c3e202c141e0402078200c105c0301a2200d88150000d0840ca42d00481c022802030000fa41c001d030043c0781d41201980e841d0300c050300458603660343c1c0c0f0030905c00c03454001e1020300807801607071640041450030483c10f01207a04070702c654040400070000d018407501c03107650440324003698079100c803c10b401400320040c040c024591120031150501142007400c110020044c640d02d80ca040c1075002c9484805c4a2204607181124000c000b5840140802c003d031402100480d032030302101080700c1c0f0b0b0108403170200c0c060303c1790003803165844594201c003446982d03020b0040c254003c00610095040c03891307000004010b1a00424000340c500c0c1c0c1c07813400c10100d888181e03000e00e0440e0410344007580d80c2401d1500750541e03102218803804010058480c05040d4031034542c1940140c1c0c11 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 585434154 1250 585432904 585432929
    0xc0c0f1c26190c11040504050a2001320a02060f011a180f041103010302030c0906100e0d08040602030a02010f060f030201081e010b0c07050a0b0d1508010203010906050f0307 76
    0x50305802c1c0e40d00a19040f05540312030042450310138981d56070140a1180340300340c0140681c0c24807850800003031a40000d0700b1100000960041c0c90f540d9003d0880052410380f045c91a2040c2040040a208058100308801e95858001200c044041d00002d025000c0d402c0521010344683e82d41c2107010300084219104590641c040018840f8116848208091100300a08164185410f031000408884452003071401c0b1520210042041d850107000021b9100020b48600c0d506240501c001030400c94448511802c0c45030070707940241c440c0c6445100303590059000c0d1105649944500d00030b5525004041c0741380041d8205440403110b541507006580c11913a0303003005410000e0a50340190f420850060030b07110740c0c01d02c08509845801a1030743c0039000f00a0300b140103544103103d200c07003070a0124503003016008240107541002402d200f0310031183d69104102000501040c0e505404218644c20b82c0b10152560020001041542060b4000001c55500b240c0c000d0f8055004002c0c16150310a5100e00c07a1a4580c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 585435404 1250 585434154 585434197
    0x8070204020f0c0705060f030a2c0106090f0207050d0c08070204052e0807050f01020c030601090501050901080325060b1807031a0a0302040b0105042c0603030c0c0f1c26 74
    0x20542c010003003400c8002b1641198040703541482e580c210501304641b8403030391501001c022081e403d100f00001030340c20403410362402146843d8507503150410074044040140c1d41c2919020301901c4070a0305c00341940204240480d040c11a546101030804125110000711001481101c9078030356682c43c0120f4810501808020b4984001c00c18a481024607860641c058203820080554007400f0842c080c150040001030305504201c10b00152a8058001075260b038020403e0151031070304c042d03d44920701c924100f4000880e00e00e00d090b5000d081040d0706550048c07841005841e910f40c0000405c0e00c0b824aaa4040080010309008004100740d4851142d410a6081d0004d0016040c140c208210805042c144035182c981e413600c03074244075101110701d248926600c0090428204607640b040c1c1e00648100d00840c2003101d200c5c1d0250300d030040124128410132409401421545480c8060100140c0030384900d15845001d0411010002030843d040c40c1100c140c100141c010607960080c1d07441e0f030115079840e030880e80 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 585436654 1250 585435404 585435421
    0x191803060b010504080708100c0f080a1a0907090302090a02040518060607083004032007080d0206150405040f0b0408040b0711011409180408070204020f0c0705060f03 73
    0x7611480e18100901040007003941c0c10104030b0310005060f1940103050702c1070b49017605012154640b140b0010850102040d458003588400000e4101e15003600005200e04014249500c00c0c01203800107400c140712000b040405a004229201202e00964101202e6942c175502d00007284102c2c043d0a030321500c280781c0f00000148298400c2d80c000c01c0a00340d40c2c074001c22070301d8172004c90b0884403038001d80003040d0804a080080401d00d04520120f60308900030541441d68003c2c20202c0d54044c1a800d29500c1613084003484000c005000003031000e48240c079250001e07014020345074001141c01031a0204415200d1a903400c1034400d0307034400c5070090100f0f03071544c8441e52040d401640185c070070748003a0810321021400c40d0200000b404079034441c008402034805100c002408150b0600c8003080c036042c052003214096226400362858110880444541c50758a41c0703400681b5001d0150302075081440801c10384a400041c00050441198842c22500441d60711410407945201c0c0c454109809442030010030700b8103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 585437904 1250 585436654 585436661
    0x6051606050c070b01032d0b0a0504020f040c05070605090703030203030601050c0a1704180509030f0a03020403080f0403020a090e0a110d120f0f020601030c050609131119180306 78
    0x80b1a82005850880f05480318001101c00303801c00e43d4124031911660aa2250b0009112030014100340042403401035600c86401c4a0b50003080000c020b5203510000f821965940034100c45040300a0003004038020480c4000c1071900311401c00c90f00c084c58800800c00e04440050f4040841c2da0546c02145542d86040044600c2c1d00079490b1041c06104000345500011050071050b41442c40c034046007501c440c40c040c0041900b56103185d006140b01c0c503003402d005010202004464440417004021961621603141c114024411a4000fa02c4000080780b01c0c154045003800803c1102e00858468841c1c54450380d542c01201d515800d90a02c0740e200c04100000500180044408500010700e14142050140c0318400032944030308010002a000b0b41d0240c40b034540000d02d824401ca1188014911036055696003103989119000d020311400c1c01103140620340e40c40030885060415541e00c00e1090741c81c241c2540c116600042c01c00e0341c0303880c885841d2100351031245d00340c417203110311182c0c61007565855611110002c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 585439154 1250 585437904 585437911
    0x3040302041107060207240b0a170f0f06060a08030a08011a09030604150606020c01050d110405060712170f04020909011b020309090c1603080702160b0d060605160605 73
    0x91400f4030072103000c18039602c0030b40080350107044219100090500030f440ca1000e40442d1010396441c1c49903410030b43c1c86152110050710b80403405610400c040302125880c11000302c0c0020400d201c1c11024018040c80450402c0c01150709a442000030f03911115a00c2e16402003000600002d0686e0307004202811414524440b1301a03080341e540e15000000c00483c0c1095001c81d005e40b81490105641c0c030004120b803246c4801081b491029102e00004440000d02502c541c1040c0903116459907500b03071401c80320303078112401442e0007031041c1e966007041e00d420404c0000340c070030400100f4030001913000802c00109040d40311341703441075503690310355074581c00c00032052409080381d28150350380c920755500a85100c0e080b4212190a400440c0c6590501c000c00190a40082154004244c103001907551b60001c00d0381030900701d616003015501540d42d50012442c05240021500403450881c10014604022500070150168080018415a500d41500b078600380700e2008131021070890f031a8002c01156203a44010740 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 585440404 1250 585439154 585439181
    0xf100212130f17091305070504030f061803020703050106060e010806060705070317090a050a03030c02010f031104121101090b0a030b01120e03120f06010203092b0b07020705120304030204 82
    0x481d041e01d454210f910030030460008036803080028015040e00e40701080310103000800c58140954071380044020114010340c40014002111101c44204200041c0c21013200714400072440d08804109040080d81c0da02d01d031006940d907501e00711002c81c2c124404c0422001e5518180c4941b582038881d0000c1c0300c5154407164090350b85000e42403010001409108824201d14040320015465080000070810007403c2540700074030602c2c1c20441000042c0c1c000b0320510180d43c0900b850400c00f84400030a4002d068104600004103030001340101d050601c2c490b040610b40d000740c90900070104841c0041d2004c2685001e9100485810320040307a03094420340000a14180c103140a4580300c2100000c0b106441c4066030703001e603540020035128207910710300b14201d50103041000106124103101002030745912410100c03034018009030400b0020380d116100304ca10300d00050200c224007821542441e00c00320205440c9040107000d03450303001905141010484801d07501c240007451800c0d2540d42004010111208000c1c0b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 585441654 1250 585440404 585440423
    0x30c0705010c030f0605010c0f0308060a0e0a090614040314180a03050f060619140402070f060b1c0c14010306081501030b0f0f0612100204080f10021213 67
    0x140020000c0c0150481c00c0103e84010549100c076180000540d40c154001c1c40c100008a0403071004070342020915401c1e01d405040a8060b9280c4901040c00c100b0980c224080284045081c05007001c0c0c19030014241c280526410851883c10380d41c10209000e0642c0d000d00010088081c94041d215004020019801007000c402181c1d1409004640504455402613800341c00c4240c01e070790703254000d025041c0d0011048886103403007074800809400181c0c69028441c2e04c054080f810b080951a19070448158580004400682e81d0461900c68090101c188145000f0214610324051400103540d9510701c090303112803481fa01d81d040100302c00c80414501042810151651000600d030142401210030b02e840c841380700b40c4503604602300155201c8000d0158070425140b0410004810300040c45660084012074600d0210642c105503503251880800c005003110307100040c00108400000b90074a1480c0e01d00f0180c40400005400020490041c2d404030501507140c4400149424441d10310340c510544100c00c01c2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 585442904 1250 585441654 585441667
    0x40e0102091801030c091103010b07020d20040e0d120506030c060a0923010906180f0f0e0c07020a03030c03020f060406060e060a0317210f060108240105030c 69
    0x950145010b00600881944030300051081c8000078500c80c02070a907508061001c40f045000e02015440140f0502418040c0032519008554400712820f401d6504240c26010440420f140d02c0e520388071030f240c102e00c15440e2410301034800b04c0120b60745800611a4882e0118081550350700c01c090000145000e0341800b0f02c1280c0301d4150781c0c0e0303400b9200482903903442c690004c0c146008208444180e49581d83c3d0070002030701025842c0e0b0302a8903841038858030b1030a0503e12103100c41e00d40c0c941c0c0d115001144002c4803008081001c184140e44501184d40e038004544241d103d20001c03440350701c60158040c0d00115100401c2c80820700a00021843c10310078411070380c0c0359160082a900341802035a04882c80e9490f07450030000140c0750f81071203030058001c88007851103e26540c0c4001002405d03690b58113000c1e4010800700344c0f02700940f12540030100005060861844d0100d00d81c1d0080404490f0340c1d0100304d090001c1421800c008610001194040300d500c40c034040782000648013034000500c80000c0034000c000d072 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 585444154 1250 585442904 585442909
    0x18020603012601020a020d232b06060e031002040f09091a0f01090e03090306160509060f030a110f0702040207080d2d020a08060f0a030503040e01060305130f02040e010209 75
    0x9185d0320b0890383c0900001445203200622215810f0f0406080e2940076070f05201d10b452000c00c4800d1005203419000b940c030310302c00c50621702d0390541808500ca00d1508a001441ea50402c280c8810101d0450584804500b101080c10890189001d15403450308100d40500200030305600c0124524028040110900e14101c16105019004c075490b041b071000c2d00004100b4880d0b00d00070120048003d00145040c03544d10000303c0e0703582000414100d02451401c10041145000702d0868000090251143e5507950401500c44001d070700c152400490989803442c0a14081c03216400c0e5040e05908900507803030007c2c96020030000c0c0d040001c056445000c104440036400308548a940411201c1c43c84c0c00d0061070591105030000341d5840c0a0601c403078010040b80b4220f551144040c3e60000040700d00400a040308004201a07400030b8000515611000901003081030503c1c0f640e074102e0340650703010300060b541d100603009510039980b0300030100c0f0103240f205401840c1a0f0030000003800d00c0c000041c10142103c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 585445404 1250 585444154 585444157
    0xc0d14011701061a0306010e0103180804170f03180310141915060305040c150518010906090311120601170f010c090302011b080a121802060301260102 66
    0x10800c549140d000c55024100710030300450f001000743c00c1c24900d084250301c201519074071000700f0b600e041040b680046126070313000e544081200324102c102600344404138501050f45500c103001300707601d032941c1c0c2140d1403040e00300060701c243c214480340c007440c00e114900350a000701145d1911182c1c0e050080415202000b4032610031a90305070703900080880d10341000742d540e01c52084000c00540311542030942d1301012091040c1d0701000c0f02d2881ca4005450b030745d90308140c1c54171032441d0007a0580300500d440da150f1040d80b110140c01443c03541d40301c102c50159418010b4400020398850300012038283c110420120740a243c1035051b8000190400c042050a04081d0781012001d0700304211140300c1a00d2803070040c0c1e00300301e841301c1c0400c0da100800c04200d130808054425442c91100904014400e540944529100c200410300c5507030040d100e980315509144040d012a4003801c024100f207191a02540c020407012002035181030300509260318603420030140a054030703240c1d80c01e203884403005184240049000d10 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 585446654 1250 585445404 585445409
    0x3607050411210103020901260f030a020d020609150604091416050f03060a050601050f030702010b090603011401050405090f060a050601030b031b010c02042a110d02060c0d1401 77
    0x240390750326030b00c0c40c110101c0008410b950b403a035a5104001840140c03a001e0400e4103540380f40e140d030b18a146d0005807500644200a841820b10300918000e03600103400000544503220543e001c0e038165074009a002ca1f503030384040354065283e9115980c4920390209401c805900428060408200090652a82c1030041003403083c0c81d006503c4100c42100c1c000314200d0950240a0460b031002d58000c070385000a0340c440c0058000d03149951741314080741241e030003003003183c001011145c041c0d902c914007544082e00810342005002d000b100c403d00001d00d280707018480c055100c3c5041c00601616400c010501006001c01482084c503807181540d40c4508080803c00240700300354981740411240f0300000014203a808521140e0b00035400f281401d049400801d86144512400f1318001c01540c4840c0001405071001008140d502000f000d0302c0d500244c0080c400c2d600c0000280c0300d1288601c1400d815070744c0d0722007030300c0c21400580040f40070600080b030301f00050003070410030200412008030304400301c02030b05001ea = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 585447904 1250 585446654 585446681
    0x2d0306031b0e0c0c10020a02031e13090509061f1206050a181e03030b040f0203070e01082217030c03041205030f0f060a030b0108010209010836070504 66
    0x300410465030303080b000401d40c862100d070b84240c106078108180f690748040071113414802e80d4000c200318a440d44200255610a00e5540c0301d148a403014980c0d107059540700c907500103400c560010000c5030490440c0943e03801100c03900c00074401d136592103450300780c212a010a1032004800507100010f00802c21002107000714094180007400d818400031403c2107a0044482403001845911184041140303518042104106074200b84503008007171500710003c01e4007000380c0741d02c9494000b410759440e070181e001d580701301d40729143d40e40da900c04280159640c0504a0b01d084c80040d6400d00d178030400000240a00b50544203600554404402d00000300c800c6c1c100305c41f0341101503000b004100c14400c00025200c5a2065070400d24034508203120070b40b102010043c40129601280404942e0320b4480751b058100858104070140542e58503030502e14048e40c4004035850000d0600b40c0801d148071420258609544c0041e00a0640084100f140c4184410001405659802650000642d07511240207203141900748 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 585449154 1250 585447904 585447953
    0x60306060302031314101d010b0a03020d080307020f0109060e0105060f10050d0902060705012a05030604020c10050a0501050f0a050f010305063d030e060c0c030f0f03010509072d030603 81
    0x40d0035402c5401300c0c07210512612b62600c0800142c2c889550701505180c104200c1a07490b55442c3d02a0b15018000b01549110b6103441000320074400c95030700001c258803024000b030149441d89020404e00d49620110584c1c00400140c2000400b030040000f003250440b48200401d1045158001500c1600130b0042a5841c0e5100e500d4903040e540b490900e4200868285070000182180c11002000b0b03000013054140141d50000d408541f0302d004112203080d15003840810300142c034150003414054102071245901901440088070280d181401e030120035070344003030f1880c1000b0a250004601034440a00801e402c6029450b600300e241c20740e03d0540c101500d0a0211421101140045040001314841c2d01d6003014034104071a40440008a0701c16005211040b180341c81d404021051411842841213405172000005101e0b112101e0b41c40c00345040310011121886540e6550400f81e891900c0e005040086041c40202d61700e03885211800d05112414034074000034115200e0390f03400c2c202030b10007a10742c106070403 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 585450404 1250 585449154 585449201
    0x100216030503070209090f0c011d06131a160609020607080706090201080a060302030a0b09030f13090c180306020309070302060d0b030f0c030c040519050c0406030606030203131410 79
    0x400b29061781c1c06c280f0202c01080000e044582090302e804c0d0710301000c2d04000f8000c0084802c0480181d003401c5e00a002080d15544d48128030340000e41d03981d20b00c9112031598a800c1c0e009140c2c19403030140c50304803034400825242c1c220b103661890b009150f00c0c582240c3c0018144035400c0400c210101078101d82d03120710800105403117240005805100024100c000c282d09104083c40140c4021032034038052584041c40302c00b19211b442c01c00341580100540b2584030344004c80e0503011400081c020000b00e421403801086404e141c21000c882c00c207110042d00c021541c5001040000800e15801140e0140500095a030556220390000310340b58441c2546d20007092325400602d40340e142c01c1c0032060440541000a202e000400400b0070b803203d5800480612580d61400003840301d0751040100818402e161500f0842c0385400740f10005d41e074004e0301074000020b03d0540007203401c1d8002d2086a0045c105024034072103d008a990b266101642d44080c020396010340341e50b075144e0640a0042c2d8070742c0c0c40c21401c0041c0500 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 585451654 1250 585450404 585450409
    0xd0e010c2316080c150a1d04151404090506062803062304030f050a030905120316030b031c0318060b100521040507080d08070f0c02010e1002160305030702 68
    0x34507407801c24802c5c1005411032055904040885d0148000d0341040c0380c2490096091760003c2c22040300840d0498104501c4005685418460720150717061030b00186081480c0304144812202d03804002411a0f0021010610501c0e006488a01342c0c0c00e03400e001c641002186440660440382c50f88120b0350b841d1201055012035400707103085101c1ca2071181c400d00241c64103807401081604042101424003000180d016942d9100381c00c80030056070400200c0f0901d04c0c1c514145c0000c3d500171605141c03c5100f03102800d804d603200e4000d0a03203200300200280205a100007038190041c0f603860001003850398400304580350803032003039800c0c403460f014407000a5991105424003494420300e01d06082000000c01c080f03419810240600040011400e40c1d048080d5110325140d880c100c8503030484001c4d4400c80122141150344406c080b4801d0b03650f0340d9100070f0b01e451200c0503182e114031000c2c02030210b08060210ba100341031042d00e4020403080c0348116000d90411800281079102190020ba445810003c0c4000960 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 585452904 1250 585451654 585451663
    0x60d0503120f0a1a01120b04050412030b010f0822150b0112110301032d05030304110907050d0c051303050717030304150207060906020a110d0e010c231608 68
    0x412030a10082c425101407903151882d202c1c5135030520208600340c0421285940c403458001c50050400c1080341840e091008816482c1444900000c1c00c0022805c1554030030441d0107240300f00d5442d5100c1c00d0700d402400740c01245400c50108031411003088400f01203611070468005002c064207000480c000743c940010044414000000d00d480d00300384080c1815001407040701e04607038000c4040148241c1900c00b411154140711020343d030300c00308455a2024060003000441c0100e20403680c01110000400c2841140e035412140c0c407020800500c0030030035910302c907002a8203a455a1030442e1800809681005014525070420784442d03209880901c80130145031518002150b05900a604605d02540c0362110250040861101281c002c102401080b00e580c002e0b01c0c6644d4400420364441c00c0491005040b42e408120100c4640700d00d8007041da0583c01016103c40d0704006940320181c140290b25400d113411040b01d10110b200460406222401200380078100c1180c040b4159039000360714140da0769140 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 585454154 1250 585452904 585452911
    0xd03170108030c1005090f16061d010906030c020f0607050a020f1516030f020d0209240a03090c0302060a03090c09021629090105100603050408040e060d0503120f 71
    0x190300c00c03c000c0822500010340092100c0750240c010900340c0d5685205820140482000010303407090f80d4007042000d5012200000b40c9105aa070440a0384204918522007017105078481e0100d01c0350403050042ca4401d800c40c1f8503446032030040b0f880c007510004001d403814504641102c00581d007c90501c8140b0350500c111b25441c001000100031040c0c660000c070031220030180000030400d1003c10011b480394000e800030005813001046c21900c450400071100302960000460900c5280711142d11807502064001c20a100c49460078110b081c13a80c0207000740c0092449440136104000f50800c00030050751078600400c5419620354011480c88403e24001e0410b148c250802d44900d030061028510007560b10320510b20306a041580c01c010050034115001035010070010b00c0d40b5607407010082020b180415000300b8006c507170300c21241d507281d9540c4a085040f1542078034000c000100401041007800c0600c040290005402402d4034002e81e00b95503034070f00e141c0c00051502c0441948030304120680d80156401c903031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 585455404 1250 585454154 585454169
    0x50f25080319141609090c0206060f0102010c21090f08090414010303081308090915120706080606130e0a0902030105070c03080f07050d0608010603021e0901060507110d031701 77
    0x922019690668101e5000420071510644d01d0440c10903118402c003e60001056109030810005007c454001d403540022609640034480502070700040d0b500c14444d44201003081d9407550668800401400f1900c1c543c1a0f80114858881e4001c2011407140c0780c0e100c003458840c0031490b40e1801d01d45e00340b1007a81c4128000a03c803400c010010404070750040c010650180d030034181c100c001c1c109840c02c0c451038090640995000550003040142c100e0300d520301c2a508981c11240c14170958614500e145c1c3e505001d004d0302000600040c0071030b03242e0a0030320107020409a0a0001185c040d250303461140c4000341200e084a646440b0092007056003001c0c82055049000c03480e00034005282500c0160200401504100c4503406140006401c0c0384148243d40c80039141100510031984e840c04110b0203004103010981c4107944070860740e90100b20460f801c100301c00016092041c540e00c0c1c0302040d03415810980f025039140b040112800307020b03070741e030460003e0b01842500c4400407071201c1641c0c001605c8058000d5035 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 585456654 1250 585455404 585455411
    0x1506060a0203070b0915010b0d060b030c072d0305030f070e010c0308061503090a17040f120c050a091d010504050c100903021806030d0f050f25080319 66
    0x855040c0d0100c11900d02c83e0f000019550b02d611140c0341580307803100c46c0b20503000790070703c440000c200c03004104004d0a811000020a02240c1e864401c41c01c6903210554617802c0b40c0c0020058100060b0f20581741e0310455a07444444110090181806800000711301800c0340010340010401107a00b40c01080703d40c0191652805810740d516003c000b0f808280307124809000c0c44040300005078160b4442a4000242c03041c28440303520f0782860038507a50344213040c6400311030051180118040c6400100b0a80d4102c03042c4006003981c0501d00a070382d60b04007000b000c081d07a140100510202c0d140e01d4035040381d0028080355000040c400a4500302c070030504040110110b0316410042031001282d030008400c212440b085034089801c440c140400e6a010782c40c0d50009401400030360203040b00310780340c00b8940e116a01c1902a030b4102040318404071030b1140341c05824030100320309228103c0c0000d02d98015100004000450b10b90100140d07503240040d65401c44111034ae141c2c00820449a95000c2924400c181c0000030240b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 585457904 1250 585456654 585456667
    0x504050109060203030f01050111010e0a05160501031b0804030909110a09050d260d050901020a0306050306091c210506030111041d1b0304051b010503190f060f08150606 74
    0x203031050398048c400c0c1c80c1007041c0002c0d20407544000303504c0203a41c2e9054004035400d1400910780703d91a03100d507150300c0703a181c1d030b01000c00a002d5010780200050481c22265410070210584410741e280d640140059041284050f0080b40103107540c4195196181c01144664445c900d1004c014058038035500220b000c0d0f0b008510940000d104041c100711000e81d00f02903e2840107403100c04c440e1500a026140c48028109024044441010350040984400c01c0d078091046540b110281a5524425103098055070b104032081d5003540c0e644a040076000c807443c581030f0184416903030303c003044101c600354584842c4d50b64bc060081c42e140074803078045040707600e190341030405260116804117031300644451003c0f0340c01000080c58110720740f451000307042c480c40032094036400c1a0030403580d14041d0880d100041600c1c2d5011401c07a40c002c00581c2d04c107640ca1204183c1210551003480040c04003103001d61001e9484040c0070404040168810740540700074401400d100c20b040e42082060880500440d00610040281 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 585459154 1250 585457904 585457921
    0x8100b0f01120209061c05070e1005030703060b030108150108010b0609060c01062d050409080a0e01020a06050a0b010206160207260307030c05010e0d0918020f030106050405010906020303 82
    0x152008002d09080301d40d200c50b01060310192003803401807980709900285002e84101007a108002210715100c0400c4103a0b0361034400d980300310b114140150b2201d8200740400503030b032080c0011544002c56150102c0d15039500d0710280071030303003003038024443c9034109400904c1e00c04013135904d040c01040d40717000920034a808000070070980d10030401164024040042c021407a04800d4220000038407669061060310400034100ea03052004891120071a82c00c1c09000184529250261a110b01e800001c01ca00c1c2c4460740342c042e1805852005414154000c000d401808180b040c4680c03813103000b0103000481c42c0400d18000904200d0b0044c00e245d042c290394070205040a600203110b006075401c5150340c02810496482214a5000d84140c040c1913200004400d000c05500c140384203070b000d215030024418444486002c948079102d03080e444000601c540420060142c0a0451000c444600280140f9200d102451500d895100740c2042001c2400042d08021659000e030050004100510155080d82000881c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 585460404 1250 585459154 585459169
    0xb13080d0509031b1c031e030c021c12020913050f100b03010b0403060507050c011e0507050304051b010509030106090c090b28090803120105090907080604200901030c08100b 76
    0x14982c56072844100500805004140620205a403c106147c9854200b14020b000c0c1052015000c01400b4a41030220785000c020442803d102141d210780741c040b80b11849000094115500c9140d004075907924400e03040b0f52920405006420240e08020640f8020340d421141520740c1c0c1c007944c8032080c2000104900c16451090300c0030f59502110204240e120120700312103074020180700c1900c0b0b52800f200305000b02001d210f510079202c240003081c0301d90b60b184501564140000c403000340c400e40006070000304000d21480e82c0d04e5590814102141085c24420201c0c0c04c645007170300208002c3e652403100013000e40d0403e048100801040400c540f928075402c2e10b41c1504411005104118288010000350f018082c01c0d20320064180c0b5011680c881c0300b01c6812030603403c0e0a10a4a0044400361701151b480702000c24104140d0700408000c22b802d445035642d82c00610103891000700003140e082c424404d981e8622410500a42c010140e0424640c201140203003484508000344591901e06a080212600c5014 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 585461654 1250 585460404 585460429
    0x4080c0402070c0305100203161d04050a110705070e060303074d0f0111033702070603231512030a0306061106060a0b13080d0509031b 59
    0x3100541c89100514100030700c500581c0000303001d4000c9009150b50300e14580d01441c41043c60100b020030729405554203455100e440f11901950302c44c40080f2540f2400e10360481508607200c3e0300001900540d040451340c16411003402203440c0e8029580401180d4280042c054200800310061860100d42d541c2e1203680c2c000700c440c1e46138142c00c115004005030303805100c1c6021703840450400882001201c1c0c42d100c2c040040043c4a8810b49510242079a25482039030306003c1e88441e20001d5141003404626500c1c00800d1110007103500c0c40100b00c0420001500c1548000551a600104000380c02c0481c0a820f070703140c4a403490400100600c403940c80101e00507800d0342042d10501500c8200482001084488408801d8003c044c0720000e80c2640503503055002200300c80c000e0b070310200d980c0f10441245480b0682070301d046610141045c0f05011220004006011462450b0009005141d540c4042c600b03140260b4280e81c00304d40c001c504a2441d00701070242c04482d22610402c0c0c0350601024000918010310b10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 585462904 1250 585461654 585461659
    0x103140c0405091801091202010c020708060106141c0e0d05090a050909011b080129040b0342040c021f0209150d111608210403030b03010b0604080c 65
    0xe10100310300b51300c120051a0301402e2040244000c5042e42004c07810500303041c80ba0801986000394a285080c030100b00038050b02d1440d009441c090340b0700481160070401c460641c498091040040b808031400d020f1007079402c0e841425004c140003070f21494060038101c182226106000d810460403416655980420027030369021900011261101d250840c0140112104070803a1506201c0d41c0300203a421402490484080d040640d5180000f040d03540030009808007824003c2e9070510090028070a8007003d55484401181d1038006d802c90b0b0007004001e2415802d0040d01111411540501d885280d4405c0f295202d00750780c14400002c071400d009660300f660f4800c95041c554400d00381185020301c1d03012546440d03801010141b010001d54442d4076140c2c0b245444181907480e100382116044c40000c1552a0444c1072100924a4061a02c40c1d6460754014030826102c6064040004213148801039081d014a0003545c0005100d0000ea0500d421204120400c0d0303c1040280010403800c0d100043d401d0030710005 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 585464154 1250 585462904 585462919
    0x60114120304031707061d061501091502120d0b0306070e1305061c0b160c050d18090507032405030a030e0414011512050c03061009081207020103140c0405 68
    0x40c2c075070000c003034001d420000301514207000e40030301e0207071914800d0095149103000355050b507222240c51449c1d52088070f074114046101c4a2042012802110000000b640c2c5401515501e01d6600d29000701607101303a81d900c3d0340c46d42e908602c8a0b01e007400c1224991002d001c4c2071015141440c4000036184080340008101ca880c3c40304000b41c09070306d844840c10307013210414003d4005500285842109050110394005114181100c07501659200781c01000d041070708900504412196220110f9400842140401441c0c21400d400078000307150f841000e205000d2a03400280076601851b51580900305445402c40c03605c03020360240510b55000c101c05007840d074141003540c806140302020070040d0003168504011010640c0000500303a01400e613090502d04280c2d110000001440c0940045420982c0c0c4000903e40a00010741d850400810f03201807065141080340c0c1d09030b0380d10701980c9002407900c2c0c00340215101250034011541c00d4010030b4810303512500d40041d02d14114280303526034001d6110303583c071681e43d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 585465404 1250 585464154 585464183
    0x30711010614092202040c020318060f0f0313081602030f06010321090e01030302060601110a0308160309060905210c121e030709031110200c03030c06011412030403 72
    0x241300f80300b2101e46501410038040c1c80c0389841c019484e60052028411040f403038a0f01480d80380707815400c139400800b516421074103111700e945003001250002024441c2e204c0f000d85200e00400c1c1c84002a250242203460078942840c4184141070821404241411447d0b104034018070000b200400e4403220b6101c3c810300c0c07081e0505402c030200d0321000a9488040c101d0344100011040c1540400c40b01c0c441d100a80302c00d076041031065280340d03440048e004080c0000d0851408565214031210210020741c40c24074001c40c40403a01e4803541d04803010943c08a440c0c2d8072026203200d000003045030391099031011035046418520b00984250312a41703200c3c6014103500e40000d6040c001103004020140008460008541f41d10b042c101c083d2a4440c280810749e411007000400700c5031441e004d45404000f01f5165a2602d01015603000290301030f4807040180c186003c0c0c0039022610f42c50030000f81100f801050000d01c02d65141a00c01810940d2043c14903008082c002d1320315407400d1000040324210b03907000c0c440ca8807002 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 585466654 1250 585465404 585465451
    0x130504021206040b0307091d0705060a050304031b05011803020d02010204060c140102070b160905040c0f0818010c03230603060103080c010209090c0705010c0318060b060408010203071101061409 85
    0x1010747c102c804070b1352402886594641c6a080550440d813800d41c11039000d42d0700d43d801c00255014403946140084d07010400200041e2244801800b0341c040100036421401c269030b507c50a4465502c60440c82c041140118824140c0c10030404043e503109000861800b03080032030007041221b104001a0509007944842c0c94548003d604540c3d582d500900c0c40e017900c0c104101910440c55040881c1030010361340c4240411245050b200310001c1144585400d180401080c90070794854000401018600085601140c0808401c2c001c403040c0c0c54207564000b424940360f11140200c50840c0f201400641d182e82e080000c40d450000d900b50540ba00301e5006a111201c06801501921a08503281d410619540038400c4c8801c508016100b071034842c000a2040c0c0000003403c8007101c1c20344007607554454142014501095540e8004400413002524003407a15803920161802c0e07a20940d1500e0000d0301482041c2c082071002e01c24031000d0402c83c07102802d50040380c1c000030001c8101416003d84030710410460807110 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 585467904 1250 585466654 585466663
    0x50a1202120d08072c10030e030f0d1b0503071407050a0f0201030f0b010e010c11181006080c0706020a1107290301050a090902190b130504021206040b03 67
    0x2030042100c41149164400510140c1e09131030120100300075401150520185007500c000303213004141c00000f04aa19010020400100c055010030b0664035001100b84160600c010b00b40802240052035840c5c040e0034104d4200c0f10317403040c0c010b030107404400c800c80499400012030343c1180486c50614107007480182c088082c0d10540b00014258032421740d00c03d042003a244041e09a05000b600d04004998042d80014140d070a200002d500040030400300103100d40c09500001d01182c040c01c00003e03401d8660011400c4102c4548404009401c00340420850141861051000d8032551400000c9800d0031369003d0401d0190314001448a500490302401e61407241c042c406c642d50380c240031240821340d9558040510010000f003607a444541150140518a149049904aa2014100886003480d160200d4020300d801241240d11221038110707100302e446901d0032080a01080a6400e07503030301040340c3d00c2e4400d0015611550289005012810b48810520251581304200340c6010a03c03c990000082c1070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 585469154 1250 585467904 585467929
    0x6130b1b01020310170604020d0b1009020309060a290607060906050a0c020d18050d05010b0307080d030f0b0f09070e0315060a12050a0303200f030412050301050a1202 73
    0x207600c00300c10000a21000303401c0c6001c6401e441c2c00c1100208111803180e40758042110701035000070100c110900050005410558131115620100e078081da02d40c16050140c1e803007640c1c504215408007090102d503c01300e10440001c1d000c0100c1206000c05034181c0e032040140d5102019200c0c200114014090000d01d8104858159001408100c140741145914009004109903400188200c0900a41c41e0740103805001103020743d40180240303145014100104e030511007400300c0b01c95403100726003a40c03614104400c4014052035000740805100c1808000c1c12642c0c26181c405980e810110384100c2502d450781542d0842c0000d640c0c0d00003c0e0f85141d0103451200c40041c91030f07014410014103038842d0383c24860580c01480c1c202c1e90324095030354030980e154081c03030b0032200a080da41083e68114006030280d032000301c10030a50002a204000c03000d40110060300911001043d1000000c04c00040105202c00d1064090080c100142103506000c04140c03545a00d004000341d07210420011803d550f43d00b8014502c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 585470404 1250 585469154 585469207
    0x301030308070302090321130812040306020702060910050c160e06010e28090b0307300b1015140d0b01030609052d0919150e060603070506130b 63
    0x1450980d09403071884c1f50340a68603102d80385080308004568010082140a0f42c03100401010f405d007411515994003e5000c0c44040340c0c4114108104803681d11723502105803100256844107500c40f131340d103c42c690030304074580000901c40d20880030074041c50740044a00744c0c03c60f50030700c0c0007008049203001013042103810040500c81d010390340c071300481c0300d03a0300c9012030341580e54071074040c0900c0e440c0a043c541d4507001400360038812200b45c46086410040e203041803924100c00a9004c41c10340c05a15810006001601c0103ea000c3c40c0703103000e00c8800c0c80c0543c030091b5691145030a0a86142c0e814441480b4010b902841710607545440c1d50f1001c44c0c1c441e800c070320068040c00100304600d05200c1d05200340300e0700c0340b4001200c0d10551040d1058181c1c4d40c40406116400c240003600c081d88482c4002e50b4a9401030748102c510440c0070805495030b880d2031062a018420440c000e00705410158101450011554072261040e40c08020080c40348a11042c07405c11204401c0740161213400310700c1c0c21004203c07c504500c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 585471654 1250 585470404 585470443
    0xd11060d061707080601030506011e0e0c0a17040b010302060a02030408010e030d060b1201150302040b030a050a0501120302030708370e060408032a1014060603010303080703020903 79
    0x1144511a100120420010b81c1203514080d075980e801c0d07031a05000d2002501507048000100142c200303a00c000c2d10f0804070025401505501c1d4481010389403030030758480c5903415000c90441d0140b82c014200d24007840c00d00030f840c1094509075907080d5810741d050000074040c04d030121303070307140c04500800680707001d44007880003400b0558102500030723902d03006804501c0c80707a03003411000650000001d0440750075140390200654036030f080c0a08420758103c0304100c90101503007004002901146400a18028081c4000105090030891840403e40b40180c101c0b505140405624500084e0000f003125130032070713002200b43e44524810811007510810300310340c0c040709880c4104e50f6001e10740d0140e078200d10061a0712041b001d060110140013003401980102c0c400d42c1d0040008540b030014410030000c0510220fa00c407021800301203012800d182102c40084e40254641c808203108600c20702c1420f5111000751030850a5603d141c4006190070405000d02040c154001000444c0d83c505000c41c100100300c076800305 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 585472904 1250 585471654 585471659
    0x40b0301020c0f2103010602070b091302040b2d07140703050303011e091505041e0e07060207140337030807080907060e041a030a05150c0301050d11060d06 68
    0x44d407240c141d64000020081c0084c1010301c0b0402c0a4140c80c180c460070790060007004c0c03d01c030080085d58404000140e0120414042900c0e400c1540010405000d0b100b050a0300e5031a00c0170b281142c550b0300681ea9106500341c03164400b00842000c01c0d00d000580240300b02c40003d001070035090411102d500041c049000000021551001c007503080a80c1501180c850710513955510080c0c41211041e001000154014100c1000186859042002116100480410500e00240443c01102d4030100140c50383d0b003000c007027001000d4040c40301d2801089440c0055a1261981002039280c2c0d00410300d4010b190115052440070450034201c40c0030314801e107003103003401c040c46041c06410600c045403200001840038000038005403000c200030341110700fa0740b100440f18480808100240011589001c40518604001d04060b90100308c01c58000d0300650180c044a81003949005094a000300358002c45039080004000d00d46030010043d06840d0084200789a080400d80042d18901c10683d00503081410030402 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 585474154 1250 585472904 585472933
    0x402070206190e091303080a112704060f03020906040203091e0703062a0305060607060f060e07141c2c0d0207030b06060c070f030501090c0e011202040b0301020c 71
    0x1602d0588801301c6190742a035440e8080741c02555414440100082c900c0008580e8006868101c1d01c144404082004e0600c81101c002e00c41c01f51081c00c00c1ca0b02d40480601c0520241001d00c507038009815201e1030640c1c040d0641c0c0116143d02d1000c0c1815000315400400a5000704040c85044900c020422464a01c01441140981d4840460006645007841e110340880b02e1202e00d00004000d08803c0d025800048400300283c2c010700c002442180c11107802c200d4400002c00303034460784120660302c00001030b10a04018840c410301400030b020000f030110020b4641c0301584c010b81651034144104459600381a01e400c0400003600f0300000c0319030552f003500e54a80d0340c1140d10b808441081c6000085541c0c0a01464080383e03581402d22014000c85407420110720241803c2008211b220010011500e45c540d40b048004640d180301d0780103841696450000c0c0b010004942041c1004140141841105504104004003180c02c00240203108546d0360103d01d405403001e40603100c2c400785c11340a81700b001450108 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 585475404 1250 585474154 585474167
    0x203060c0319020901200c12060108010c03020c070e040c030812040209070503100303080c04030f080d05071403010603091b17010f1503080a03090506011211041a040207020619 77
    0x2010b44a020825140380381c040c58501c29286038040507914100304511182e01d81d840400c04101c1c0340d4860286009406054603081120400c44050000901c02036161540703441c2110144110301003007500401c41c00411010003d050350035224050781c41d49060321503260001088546a0004000c10000316943e100050b00039041841903000355101119555104000c582ca440110f0308400c448402c150280040307071145110550004a514001e1314040d141e489030b4074405980c800c21038100b80009440307411504140201900100300d42010011ba002003a41051680014011001015690300c2c0c4401442141c42075591400a40000d40411a80b03800c4c0000d420b2881800190f015800e11881445841c6a4401d420300c0d07030039699500c0146415556507155a50202480d2410161151420381c041081400350034020030400c0c1001244250380d00c1c2a071209540c0d130700c115201d94030702000c1184640d01041c000c548540c044800603520a0244002000f501500700304848051041d1040400e884e006407 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 585476654 1250 585475404 585475411
    0x61b0d050a0e0906090c071a0907030c1e03110d0215030105010f0809070e0603100203280c02100203070c061a1810091e051e0a0e03180307030203060c03 67
    0x2d0b5601031000301c1d042032191660050740e04640043c00380c0000b03010f044081018088081c401c42034a1110180034a0400802a05894102158002c54000c1007040824600b0740b0041c4145500c07848034943c220038406c0c052003948000362214029415446803a82c802c000c0b03c0e09282c3c01000c3c80c0225003a084011195002402498081500200b03040c0301c0a011f41507251040a24400806045040030190803070300030080c14158141c0303d07103141c50362040311b18000f03907108d00101d1420a24140d4440c00c0e8044204074000104c400d82c1c42d20200201e500e0380032500c6140c01d140c0c200702594a03101c003042182c07001140302e0080c00d072714501484030780e22200c2d410055251103002c17203184c0021561030868800b00c081c20341c0c00000741d00e48010308201c030310005c0d000100a1440c90301c515444180240c168016900112500c8280200e10174240b41c203886031506c0c554002000440410000c2d10031080203540340318a666070000b485051180c81381d10360f42004940c1c00380d40d01605403045c50800d0b84040409402c10b8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 585477904 1250 585476654 585476657
    0xc0f120e0609060702040c030204120b0702120711010e01200304180c05030f0a020405041e050a020c0d08310611030709030201080a0609020a0c02090a0b0609061b0d050a 74
    0xd100d102040e24050050320011100100410325014140d0708200040c0896101d16040c16000e10001400300348503410100464001e90380c4240310300e05070b80c1c0203003465200c05c51b180c103440040c41b0702c5001c0f41b0101d155000f640c0c020b00f424040c96140c9001038400c0341180f004103040070710448401c00c40f444044054411260005022000130400e0400314007039400e2200d4900018500f8000a58110f28403030b030590300510720741c00042c6440d8a800c003003803e4500d14141d8181800707820610402d40c81c03091094503801703c40c6050843c00e00718542c14440d121401000840c082009420103e480a901c1240f0284258840c415101003030050f514003c031040c03038980e030581d0001e292100a16811041c00e0440b8800c1d5465511040c22030b00319401590a001c003d4a041641ca5a130304c40455509000d100800c89114991540c0d00d8005d0302d8030400181c4140140100f007441e06141c034181290700c9803425285002422103829440d100da01c451460410f05030400c0f03424521030a48800b1030250444010a43e10304203 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 585479154 1250 585477904 585477917
    0x507051903021806010f20100204060807030911041a03030309011e0c050d1802040e100b0a14060705160b1e09030601060e04021204060e06011d0402010806010c0f12 72
    0xc0c3c00b070558001c50441d00f45010884850070710031011301c0b442010114028529590b84c124156580403460420020b24002d48150300240030300581c4d8000e6912640714030390340b400f400000c44a654aa8001d03480080241c040e0b40c50340ca20306850204074400800000b40981100d850303251620b04640a480c100b1040401d1860801480345000b4141c0120611260b00e80c8540d460000d4150152000b000c1e150300b2005000c41e03c50b00940117a42d54051602a007022200420641c005203041508481c0301941582c8900c5403600c0420842d682507084c2c2c141c0c000212400ea84a03009410701c41e042046034014858201d100c0361020482071000006065400c070f0450506200821080718584540b09240c1d030541e055006400410a40b4402c0040204000d0060300144c10600303c2c03000844945e809a400b203aa9030b0300c2d80060130728160b01f0420742d401030806040503032007040c032080321480c1100b02a0001e410000d680c3e000440d20390007010000d0a141c1e002c02140c41c0306069003041d144c0d078a400d00b0303544001480d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 585480404 1250 585479154 585479179
    0x4050d11030c0c09060109090e150a0608060c090607050d0507062313020a090f0f110a0f0e03070f03032c280506030c040801060503010c05030112050705190302 70
    0x400000340c070452142c50303008050315208201007001000300103007100c2c10030a1241c0d0109545030207000701c8660a2280b0000e0169a10000504003800001050190000d20b041010407070100e0018000e908842d0040c842c69460708444046200e03031042c61000740c000c1c49880c0d03080d030171641d1010007891003c1c0941810003083c000042c2110b4814a868282641c40c800800811841b0214500c4010140e1005200c4070886030b0710a408000d4030350304d190b50744a00c0e5850600c0b8240000138001d480c0b0880600e02d640d40360052080c0b000c0c1040c103205942c0340401000d624103a680703440412061016020941c001340c1d03040e40c1c03807400a02030680e8089804400d000307202c440b100b00d02d05088030300d100036000b407c1524108580ba825210f200525032031000d03210450000180c0b03500d5440045028010302c03061665501d0070b28210744e0035140998000350090785410070b140720a075401401d9a040d22a240210301c6007030080d062591401084e030b00040c0d170041c0b010f500141105040007680088a10075a110fa14402 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 585481654 1250 585480404 585480437
    0x1303031d041b050309100615171e040602120c03011d040c18020d0e0705190b19050712110c01020601081504140a05010218310603060504050d 62
    0x2151080b0b200907599200c1c0072030002c14010006540c4c0410108100c44c030008482e84070509946a82d8894100c600e0440d14044013142e1201f200809500341034074084607030425002c90004080541c00c1070740f02c1c14000001ca01000303600c2c0c0403545007c0500c3c0501c1c2c2107040444200040d5407080c402e041d05c04107100b101d009402c6100d048180b00396040750030441024075103120a0194846030a03441c5826500300300310b8852031488d119070304000741000c004012050405c418020a224010781c41007564481c0c3c00c0c1080003103042801c4450003002050603500300c03104450160b81c6801000ea0042040c90850300c04540c4135880b50809040f03200d00301c1250740070f244800040e0f8540c002805440f00c50f802a0040c01e10f00f07036400c1c90352070700180728100c49180366410450752802d000500703800311896500055014081a05c0c12001c1807001070480c1e0681d1a04444040e2010305965001c10042600d40303117000703000300016588458011904420144031624017071800c1500c0303d01020341c2030081071202c0d14030407401 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 585482904 1250 585481654 585481661
    0x80d02060601030c0309020315040b1014011407143405041d0f06090c011719020d0f02040306050f04020d0b09031b0a020109050913080f1303031d04 65
    0x140540140c241901c8000045002d040c10a1801d020305031108040300040c2c501300310254600410468485290401c1c0ca003107003210304050082d591020299405001600c105605042983c0003428441c4211100788603103c094080c01801400440e10750780041d80c85440864007030000801c114510b004203032804140c220000e81c3c06054404080205c1c000e01150038183d0003108204042e004451050306400c02c036914084071151540c2031a000310042c01a4180d0801107010340c0042406e0000201c0c2400c1180d00000000502d41a15440054184044600240e04544149030f400b0400c1c4102e0030004441d41c040e6020b840101c1f0200e01e02800a9070200309865918041d540c0141300e0707114504140c0310f400c02e549010b0001d01d042c0c0010050340c1c5200c01020615a0100d04a101900700d084a600000d04108803941c070050140b4990001c01810710402c000380289180d0088005403609441c841c05800350254117051400c07c10704200100516400c02d05181c1e00d550300b074203000100e07002038040c003042c1c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 585484154 1250 585482904 585482923
    0x15042103020c030904020310090501150e0d030c08090a03050106080f060f010f050d031101020a0903050d0905060f070f020d0615150e130b0405040605060f0607020607060b0118090b040608 82
    0x843d0024440764210f40b41039001142c20000424110035850340701d250400444500307a2065400003900350303003000580e4100c1ba034641d107480101c40c074181d86141920064801524444010082c007800598003a0907662481203001542c0c101d4002c104440e02c0d1204540c7c1d44a065404e1082e40c40b8440000d0ba1403d02d001c6014161810107080d04503503407400d0103000c40b5a06480d41201880110b44284a81a00034400340007070070115035480412924508059081802c81d41e5044204146942d040c02641c50303860031101c180d0191204980d0322070711400d110348240d200c208020341c4500044031001c18488190801da0f02c2e8422a0a0703031030043e95510350300000304102c440301c03408130f00c60f0707810b10000c1c0c030b440d14035503108100704500422a103e1101c000703011500c0c00c41e0215160b0b5070b90014001c8a050815282000803000d4456515061075600011000c1c001e078030b0010300d0503445802c100002d9200300e40102031325130041028180d107600c4603003140180c8944205240140d2138608001500c80700041c0e403101 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 585485404 1250 585484154 585484177
    0x21120b0f031b0d120206100509090d0503060a23040e0d1e110d020a210e0f1809030703080606040509071101230109060501080910020a021504210302 65
    0x90014054801010b003084805440d800b00c4200894004034420003041410718440340d015015514180005616040c82078105502a00e4400e0030000c004070000313107040500440b8248103031280e54000c0080c5004100360082c105903200038802c4010300301142001c0d0100c10342103405111103400c1000071580d803c1d00310170140000d0015070740b072810b000b400400780d501c6210a18151546401e03c0302c4e4240340981d010342d49401a44108030000038010400c4050512803650446c61050604030713440240320703c503104000ea10424800c4491140c036034034400080040d401c0b0715840181c91500281c030940f40e40104106030042410f000c0058420301d0408211401c3d40c0e00200145d1080c2c40300c0304121401c108124508804c2d643c2d9006d46040c000041000c00b0b0307031803c00b0414002a60500000c0340c1910503690200c0d040c080c0410034041e5219012410300d04800a100c0d0068441241c940120324003285840440400d030250014001031294460300d1012100a0f05003043d106100001d04408a04c210703003040c01c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 585486654 1250 585485404 585485413
    0xc080102090a090f061a03040309081b060f1e03011503060501050a030b0a0302031c0306050f010c020d05011416080711062a0a0305060102060a09020a0e0421120b0f03 73
    0x10110403d50301c0300c150203514240015243d0f032110500c0c81049400648602c280c0b501004010070541e001408402408804010b44103282ca0061096040341c4403a0100e03114640114503c03071041084401d0340c2d00c440d00f541c0420340c0210007444e0604140d000f0301500a1071507014050369034041c064020b510031101e06075101e43ca007034801d0310300304c0040401d99240f5a002e0407550002001da582003200821088803044400011000751001600715885644264018813600e2400c0300203a8010840070105901900c1160a01000e80762150060001e0b800c48414440d222052018442c940d5000d0020500503071030b245c036203498034001600c0043e00c03011160420b51018002500c2c051040880500100c0040c0400d0b86280c0c01c102c440b4406e400c43d00340031000035070310340800c0f10703640c0d04001c6560031103075030b040810640980350085640c4070024010058840940c41c007050030031000010340c3d9141401c07041840f0020219100c010a02401c1d0725401c241c06061100c45c0040c4d141055040c40c80140080040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 585487904 1250 585486654 585486659
    0x21507080127140a0f090c030b19110d060b070b0103110a0e0405010203071e0206012603070b0405010b18011a120702060105090c03040816060e12070c080102090a 71
    0x14090060b000004058149412080c0c6021894050104000828003807012a0310f0804841c0080701d0580210100090611742040041203525006805581c3c001c03468150941d2884003206d2210520030940030b07c80d00e4020381c1030074124543d001d00b891a0900c0c01c24484980d07100c8017181103000d102e00c007403d807034115001080054482c030411110040d01800c02c910103070356402d100c1c0703515100311400d841d43e9400004215041e9448a05a12aa080d12450100c141143c0800950700d0505000b0035250700c1100c00781c40d900c0d6040b030788a42c80301c1c44030a044a948040c40d1901c0d00607540281e600b210703d9820030010642520b061160486030407244415800c01e680f9054460b80000701c0102d2072140c0c02070811908c44602648808039100d00c100b90002c0440e945007009100a00a00070300c0201513820078400e1100080e904030448441c1c1321880861007003213100e410070000030051030031528041c0c811a1140580c9100d0f50018204080c06140c00440d0380c2c0e9501d004500740d114070200d0982c0310300d000909 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 585489154 1250 585487904 585487919
    0x607080f070e030708030a0c0203070b03090a0605070311070303090302010e0c060a1b0f0f050d0f170915010807050109050315070516050307060605031b0f0f010c12050a0215070801 79
    0x400c1c07031800c2e00400322203500c0d03a5012041d0444e8441c1c1441c0000440380d04001c03080d42004c002c3c1e40000c142103040140b540c50700410654a03500080030007000b545c0c4aa010401307943c407a8109040345951118815524049850003500405403044114095401c4c0080c180070988082141d08000402502c21441d15440c40380450b00080000600e8100b01703d4004490081080c101c26420518030805400c0840c0300740c4d0070304030b292643d4401c4500070890207454148406601212900310340d07010b485c06040c581c0b5549146030903c80000e4208038081c509900008603124001440000c032042a00d910740101d80b0b070824162200e00c4002e110a8045820002c1028527101d10000d014400301c0c2070a0046003000755076200c1c00c44c0d00c8078806a400e00d40715141400146014425400290191341c0000f00b0700b40ca580215600070381500c0c4e135902c41d15030700e105005140d00640f11080f42c00c0d401074455041440c00100901541c010310340d88801841402c0301000750400c4040f50030b00641c1191501ca2140e840d002c4c9 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 585490404 1250 585489154 585489167
    0xc030501270f0e0a03120b0d240905030d060b0c0312090a050a03050405090f0412030c03020c030c01051006180b0d021209010623060d0908190503090607080f07 70
    0x4101a0503030b44000d0703000441c6552080c82d006445a1018100e1134200707042c020400c203072a100180e02a49062200c02040e035a4072610030245a0103036190008045001018100740e903090f4624403901c0c01e11a0060400c040840140005440342d001001142d4650000e00058000c10032a400b242e442040030031184e603a04d9481560002980b01211005805966458180184800304801240001ca401d010038503100c1002a80b00c4004500101ca40c80e16444107d0b40141c400304010516035110f0f03071041428804e8048924164400c0c04403640d2b01410000c00380200700481d81c0800c0b0000c01000400ea070341c407c0c1d00660740720a00340c55110b942d5040c41940c201d10303407080c005c420f01039900300201418000300c00d20b0b03144502e1001c40000b5581e442e10989500d020500c1100c40485050321104404940d03c82d016140b1003a421710b80006c81891629111805206184011040700110840e40d0880c2d5449030080d44a0b1451209488231a19058800c2e1280c072029100b80c40006846000110900d02c13402 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 585491654 1250 585490404 585490469
    0x11e230307080d05030a0506010f02100923030409180b0a0b1305070e01110c03101806020301032316030318030b0a0b0f0a030209060d080c0601060f030c030501 70
    0x1030039690310560300c610051502e04a0a021400b2810120401003060300502c42e5507070062080c01c100500200061000351100d0108408041e100d80d0740d0152010302805c0701600e20038012850b001094030701e98054856a9070458420300a80c00d050015138081c00c0300e01658040c078260320240d00141c176144c1d441c10501030300301d604501e6002042003200780300075030a038000c150041105444255050b6080f500042c9080024001503070b0341c0c1e109402030310107138078009024640c100c0030010008852910b9480c001c2240d5160030068441d500200000c0248060420300720040a40c00010540c840f1052080a4451003005020742d5911202c041c10000b0a008001e29101c0351082c1c4d1420b4400707501d82d41c03800031824094511075500359940300a00194241000c066803c00c034101d80e50340e00c65245500040c1400002000075004120700113030803007040320410a070b90080c404c030341c2a18030780d68642c01c00804210300c0744501c0b0002410190382c0304540303000b0710030030741a10900c009198603c502220701c0b1010300d1034034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 585492904 1250 585491654 585491659
    0x513050601081b4506010206060321040306020406050c07140303040608060402070b0108060612060f0c09030a0f03050703090e06010905040b131404050d170a1a18011e23 74
    0x4030141e0b0707000e10120300c61040e40d0a6040d1307400d0310110421005200d01002000c2d0707419503200c00240700d225600000c07404804144849130f01c104441200d10900309010741c0d070000300003500214000c1a07250700b10025019002d5010100c6040c1b542d0740c0c40c2040307100000005c494058104200c24001d544c440c081e40d5500a03805000035103482030307680d03a60404100076401003500360454014090f85160011400500221540c000e24072410103040065800a001d010009000c00000c2c1d4844079403014070045144a401000e184544001800e0240c520750180c8130860025a02d0440800d00c085400070050189006941e201e4030103050105200041801042d170310791118612103690a511840e005540d0300e030b100c00310340c20041d0825103019464112000400820301040c021100859072034009a56802101c01c0e81c04102c00c006070062104500c01302d40240d422071501a20a81d00d03002490303a140c101c84201030f0480038481000310f4804411f901e8007c800312700f038106c1101c0c0030200000410001c1040c00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 585494154 1250 585492904 585492949
    0x2f0c0a1202090a18050f010e0c0901050f0d0203030f09011404030b0a09060204051003063318150f110705011b0203122b110412030306090513050601081b 67
    0x1840d06041c250200304d60101d034980d05c0501e4901e0810707000e005140075107c40c0802010f90008100c001aa4418140111400740c0340040320f43c1c0081c0d4408503d03a10068014050f01d9030f0301203ca202d108541e120b850740c2804200948079074044070446030111001c9a401140ca00110744500c0c00c4c000152000311700645103140c0a21000c1050b03641c00061480e40c51560300e0014030140380c40c1001403001440003181c011940d407090011002d0308010080c0320b043d40b4624207195281c07510425518a02c079242c01c0002001d114110b222300b050b802c04006190803006413100305903076055001d481e6448a0500905001035940b0001e140400055130800d5003440c4004c080d42c2e9a40c000301c0d0100641c9e00102203d140f081714189400e04030329040300a21f05001458001400101090460b003500f622039807044070f02600c4226600f2040c18440c0c1e01550150621041c00d100b00d0900216500b000c62250b403095600d8010400009010744d07002903400900003a6a50000310b4179415420804038a1401d413044144012 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 585495404 1250 585494154 585494171
    0x20a0611120406020309040b090f070f020f010c0806011b051009030e04090302070509090609071a070b010e09010e070f050103020c030d0c05070b1e0a0b012f0c0a1202090a 75
    0x1640c0c0c0504043d1989600460f1034070b41000c01c020a4a4031180701c140a003070b00350117019104000216040d403000050500c00100d18109104030710741010103d5100f440d5281007603011002da84144003c0c052403090303075000750ba00000c003c6400410700010005010b507102c41c641954a0341650000c4840c14000d04007000114942c1010600743d0b0701c9180308600507000b4010510940c504a071406030442c646070020b042c0e80ca001544d607583c55400c0d000b1201c010701070740350203c8070442a6088403405540078a0015040d652010380102e912010744e15410b103542446400038540500041690484e40324410804020381b40c0f4005400940c441d506024480c08104264004034100340202c6a10840d5982d071a0b5541000b800c01041d1203102030b001080c070440721034810708510300e494651a08003044038800100f0b41d00b1701d00141d50180b5409070b14011000c05213515524514044071604a14192200f914521030100c000c02800c4403450240c80703144008241d106001d41060071141d503125203c01000103034a071 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 585496654 1250 585495404 585495433
    0xa140f0306090304080d050708090103050c0403050f0706030c0e09010b0d090506100f050103230606210405061501020601030b0a020f040b180901210602280206090307020a0611 77
    0x740490710900b15034400503082200b01410041140c180c95907142c50340c1000c030b45a841000034424008003604040d2500c01040114440700101c40043d54007404481401038081c1c0c009860307004520881d00420310b08402e1011b86401002c01d100891002040101700781e00385403a00b461034008051000b40c041e61005101b0020b03508105041c000c400320074407840e010340751032580403500c2c1d400d4001c1810542480c4001d4412003c030030a01080710b01e6080320704199a80c80c0c01141550007200c81000d507041e1030048110b426228010054002c038051713800c0e60b034242d5900d90214880210306425900682c0b22800410124003c0d85496800c03800d848005403030700c84d001c9c0704514030303030415084107000b8000001e29017480c5108940601302410151034000c81c1d503241c03a039121500348241840041183e8000042010400a541158109a60100c1040700c000e0110b0902c1d500740f42d5002c411025200303003004540401c4001080e04e040c2c0368000e00c40f48a450401c5c03012145128112200481c43c815008504002c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 585497904 1250 585496654 585496663
    0x90d060e0109031d100915180f0f0906030c03020d06091a0a0f140a09080d0903050405030706050309030306120c0306010305060a0612170f0d02181e0a140f03 69
    0x1e4000c0c4d44842e00c1d1450710b8481560b21400e03e40c1d0510410780c0070480340e140e642094218040f100303001104c04200280750400d0700d14403028aa00c98000140f81c501003180e50100c2403080070798600007038040300c8035101d451172401c94080d03010240603c000244100010314286420031000346c4688004156411507664261250344013280b20006c0071002010412400482e219006071084010f400340305003c1c2d6a403481e4290f80002c2c1c800c1200701c0d150341022081c030003094211008120004820441d00005007401403c541041c06000c1c441d000f01c0b51700003005842001581e0043c08607201452031915050204401001c403480440c81602600ca85403560b6030742800305034020f50080002c0d00d56468040105812503070390350491050745111311803000c00700300c1082c820484030801d8510f5540d6800000c07940c8816000388021202100d00008100e110501d121640d1550314100741c550404182c40c5800442036000d01d5010141c1080040200300300c40b042e09007480710b0542016011041680603000400e051 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 585499154 1250 585497904 585497921
    0x403080f12090a031b1208180303010e01060908070605040b16021806040501090c050316021504030f17041a190f020405031b06030f0a110a020c030607090b090d060e01 73
    0x3582000811074241074010303907450303001c5c0103154400010074500d5440340e0150448141c1e4200700070380d00c800a4259482001080301c0c1044490460307440350383d255454900004240104070001e800721100042c201400034800c016280c464880c00e0900c0d0502c0038040f41500406d0110b403804203100c5004001da1110304003610aa0a49000a0030500e855018402966010307444500380910b04003400c80480d0b402400d413604016001d00c0d8068032802000c00320701c0c00700101051868a054641070004040e040b40040e54206402c0e100d01645014000358400703940412200075040c1100d25000c8941d030391001c8801c40d4440064a191610f0b0b0407018002c80c12682e01d000c900c3c3e1450740c005402d0000d8a81001002c50036010000451190b42c0c41102080706400301034003500ca422102e00c0804c917032940c0b5421110031008003002c040d4540310300e820005d580c3e41d4802d2030035009000307003030200e000c0902c9400013805403000301c2505450725a0741e2003405072001c2811000c1c2c400d55a110b000ca40f0b903200078068801c9 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 585500404 1250 585499154 585499171
    0x507150207020f10020a1506091401030b0106051804150305160503011109061902010b0303072306250522080d0f08070e180406062105030403080f12 65
    0x8079101c040c03041c0051150b5051000d845409400d080c500100c0d40040c1c800841d950203226040349000030403a000c007900320368001707009150910702d1074110000a42072030760481c0c0c0210000c16440c0d80e01d11003540d030382c80b07014068194130043c800749003603508040d04100303d038254074a8003001c450380d2603d56505140010040c114018050141040103107402d00402c1d480c1c10f084d02c28940b034100d031580061500c1c401c10b201c07a14404400000c0c8001c0300d00039032009803505000380650307580384458a00020072404094020030501c00c0040b51010751000040c284e4410b0414400701c1011015484814404403c040310b10400c0200c10000c1802e08100103820341c0780713034041c00c4103044101c1c00d0060b69400d020008101104010601c03000d101c1d1150f202d96841e4018031513040000030b028941022814550951000d0012510703600180400c120581d03210b030088801c030451b01917081d200100c054041c2c40b11803402400d0ba038020b10062000c41d1040300102510540394802500d00340550000c0d0f9000e60080b5001c44 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 585501654 1250 585500404 585500407
    0x161227050102100612020f12010606030516030c0c031103040b0c0f0f030a090b0306040902100c140706050f0d2d0c2a1403161202030c0d0f05071502 65
    0x310758040100161019a84505000d10381c00c01c0c001d40d0710080d030706201070b203e003c445680c0d0700940c50b401071810000c034008000703010706600c038240035010b4503003a1040d406441d501d21112040320b200e40704c0c86e107200f10159500c404031050790b1010cd80300c000c40340d08070405000402000900c040308200500000704040c0c050220006400403860400f052a992803031590010840130b41180e85c0f00074441c06584020040759140d4039401c020500810000200035009030250036500303426a041749030385140314421400700d02002c0681c02460b8072110140704901c0450f8090040c007003035284400140c007485000d514005091203900c0003250344d2500c0300040600c000c000621910804105000307221560005051550220004c40039115450b042c4003060b030040322030003000c1010031a0484178940c50b00d640d24122038a50f4071345000800301e40b020230b00840d0f0383c55000024111150021080c0ca280c440d4050140c441c10103000016569040051101c4080000c200070807000203102c01d200c0e8802d451442e0740107 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 585502904 1250 585501654 585501659
    0x30e01032a0c05010f0c12021806040e0906010f2304090b0103080c060a1503030e0d060e0d1704080a110a0507030602090108060339181b161227 63
    0x12405c5a04220f035540c075690400c01e510409681000c0300f4402e00d10084801680da4019416a401e9800d05030b40300341e400480042c3c005008040c4050b01c038000c00408090342c4a41e41e840c40c0750304d080000c904c680749202c800c5843c3d24a160841c0700b0b001d18401c801070404104881141e885500e031002c2604100c46d1f10707030085060009000101b0030623920444003441049040384891103880036020512008080115400f19030809488101c6820000c95014500b4041c040d44090351603100d45c8882c07200d100180e48080014148806030350300c14041c9410031280762030700380c40e808112101c840030b420300c44241c230605070500005101000048015401048016102d00d034450004010700740182c03001e8483e0b0b10074000c031846c400d00900780c2c4028803000040c0300f2120301580304041c0301c08c41035403241c0d03404081000e285000c0390201d11018400d85c40e40c840c0d100e50399501004040789020705200340700c45000d110341f07020000c0c000303203241c40d00c1d94940d0800c10840710040069007160031929007003015160601c1401c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 585504154 1250 585502904 585502913
    0xc0d091403070b0f06060702040e1006140f0108190e070315050a0501121a0603010b0d1514040803010306050c090405090d0909061a220f03031b030e01032a0c 69
    0x2c0c00d40003100707800303000c0050401760000351240c01400b001900c1a5030b40c4c4820f0501207000c1102c6450210465010b00c4050303900c0c0c118001c1082c12107000d334055940c0d152004880d40c410b1101d41d21612541c0101c0f03440c400d4558802000b01a00b9210030290f218280e0003001003580310101181c5035400d8840402d540c542034409205841043c0d0102561440c0c3c01d01041c00030302e007030300078462031039805400f072056039100f100082c05854000140d94100d01d21081e07240c244242030440940c0c41016050901600800c5e960110401c0b00c12038004d0620a003e00042c00004e1481c2c003d0341d04002d441c0d00e044c1c1400d40650000b002c40d0416918004c0381d50010155017000784d0041c141c80700600c0c456400b000841c0c17030650030140ea0910451a180030000014900e20704186440311448681044880c1080c000d80b52100daa402400c00e01081c0c000c20000d60f1070006204200d00d6003000380b64542d8809000302500c00054002d04100403038034901d101403082c900c0c6c0004a42030314400323299441d9074030384980685040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 585505404 1250 585504154 585504173
    0x20c1203190b0d080a0e04180c03050f120f0a1206080604200307061412090d02012f0a0e1003020d050c0c0a020d031107060e0414010e0c0d09140307 65
    0x40501079030501c0440b00200d4001c0003694117404240c18120141480d00000500400e00405096807c102078500703141440a1011508141d9110b0401c40c0e09800c4841402951001103d000225800080001c400c10740d011b40048d00e021107003030412002d03083c1e40d600b01c00180c4610381c000000e1980500100424044805680c1e610104425140d82a00da521000310391280c440b801824140144034244078019410348044600004096044412900f003150f0030644401e00320843d4001903007044074007101500d00c40b03251250903426101d241814600308031201166000105400244102c800c00c80e41d00303403240700303d001041c240e079640160355001254000741150405400400340c00d00c140300411903a4030000b405140137070110f600c03854600c00b81c5002c40349c02180c10100a400d0090010019415400c40d034444a01c420884081c02420181000108a440240b080b02442034504000c0342c488403684004040d50340d0461004541c5003641d0f01c444a18820003a080d08895200040d240c062180484 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 585506654 1250 585505404 585505421
    0x12060e07180c1d040b010512070c1403030106120b040b0d0305040f210b06060705011a09090a0b01060f050c0703050c0114031009020a051908060111010b03070306020c120319 76
    0x3410348500004025404103d159004464001ca0740d0711044c8141d40e0041041c0c0704400e8144001d400d161074005001803500c084d40714101c80d0650110514180b024001c010b980c180c0d8040d0b1390303001c2c5000c80c9007140c402400e032400c507098106584d01e20102240e150003440c0a1400c1c025218203a40b20f26182c80203240300c0c00ba40c0b0015a0b00820b014032655007511502400b10300d9042030303004002d40c5426001030074038407620303074018400d6180c4820030030700c0c1ba00381020500c4400203c0d440d207826612044040d456000c00f6100502182c0000018445140034001c44410310b880351500c5030510b544501d004d0728004a5800035106548541c24040c469030380b18005121502568880320f0450078030f05000000e0040d14010000e150360007240e68030031648510300f40c03400e400e00001a1002d0f6031483c24054210741e41501d20034001001c0c1c01c00c000038075030305018080003940702a00038101c01d441e58498a009410000202030203000c0c0e0320010b086680040003850180c2001c245a00d80105055201c0c0221220b01c1c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 585507904 1250 585506654 585506657
    0x2181509040c0e07210b0f06070314070c0810051302040e03040b0f0d0e011103070309020d020a540e0f0d0f020a1505100e190f1512060e07180c 63
    0x5106101030b10f0b01f0002c14040081a5159a16a00140340a940e145042e00c5000c600e088045180c200f40446554a00121140c00041d2000010100f01a100760340c2d00302c43c28081d064841018400605140d4081040001c1c540c0c2070f2400c041c2c49041700340c01359200700706c410a0980041111801c90b50144240541110444020480701e1034245258640c1d00000f0280d600f40355032207426600355205c00c00c2e041c100950003056040ca00c1e80b0b456650b2807981c04e854654080c0b54061405076a042200c11035441e030740d8055591504100c2d0001b5000c48809506140700080540721004e0003d500010400c02d0581d00c0744001038654a45107100091800000800c003800719409140d810022030801d500034921000c080c000803400d69201c42103000841c2c020b500c0400d010f8a10010044402131814801c0d03d1140910302c14049a40400401070a407107034601d100075440300300d407030030010007540f0007440000521807400420700c1210340c80500e003041c1c100d910005002ca40180c44c440310804500c52031001d0040d6 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 585509154 1250 585507904 585507911
    0x6052d011e090303082a0c03071a150a03050c13020d060e040506130809100215010f0f05091006081f031101030606020303130201050a0c0503031302181509040c0e0721 73
    0xc030359003c1d01505029001c0c15070941c00108000c2900c1c048c800c035103010707801140208035032000c1d034403039120110201c640b5032001070064207040725440c2c030340741d030307408a0742c100740100846000e0504010200c194000d03000007055007008200348503c0d2038001d90005081c500c1440b8803900c0c0c10304002d42403031401045408440b4504440324005061030080c0e0b6083d2600f076624041d6500f09881c143e20382120b40d07440002030800d90000195408a0440145c01d0303c1090f42440805583c8a090004c281030680e001a6070101101c002e001451003100e059502201c0d030f40103a1820714a8125075030303c2004940040c0d40740309509440c0032065803d8040c3c5c600800d40c0d80b00461075490b00d01d48000743c43c94440030090421400045800d41d403842100100d0b0481e4001080c0d82c1c1d20305000300203c18441e034036103040f4081c1c0c01044100034640300b80c0000a210710034803811341122203085010000702403801401201c00c10182a40820110b5030000f8641c1314034050340b5828404c441020300000f501d9006140c0b40300d517900303 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 585510404 1250 585509154 585509191
    0x1203090608131b0b0304050616030b01020c130b060a030b01020d0f1b02121222050108012d060309030e03282109060306052d011e09030308 61
    0x30a0402104243c3c00c401211150703620310070303100e0020549901ca4462070001100348001d2040c00f05410b8040c01c01c010103194036541c00c082c19425504a110154003680009490942c18144030304a40128105408002003007150b880004423140c20605c051000260398008030703811035804100001c40c146160901000000e500e1400030001958001b4503d000420f4034072800454880040c16180c00d07090a0650392100ca450000e00c26a4000703e2000d5846010714002c14844480360506c03100740d03101a924500b01381e081018035003880c0742c0a0f09079503592503072815814030f14012880709000b41201d554040f40d0501c1c1418002d000070041401c0780d03c02d401c04060108840480700d944901c0810860048803200800e003048200006c00701d000700c201e11005484820303529405060a020b0700e55989080003e1074460051158016440322114908483c8500c0415200558801c0c4228a141450b0503008050350303032058200c8038480311241021407502c0724148201a0807411090340038a101e06000d64050 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 585511654 1250 585510404 585510421
    0x506040e0910240608010f1211100309051509070b07050304030b190b04050c09280e0f090f0c06090409060609020318190f170708190201090c060302221203090608 71
    0x1328148140040d48d41400110010000218405c04400800401e1003481c2c9184590140160140b500121a140124880c58400f0000010344501803442c150003001c40ca130401a40c4070302e82e403101505942d40d100030b01c0000000b40c91138640500c56241d4808090314840c8004115082e541c8581006104506010800403208a1801500c1501b101200c00307050380410a408a44840b09480141c80c1c103888028000c984071341c494004c00e000340000c110410307880d510145056101c2c50401c0020040317400030541e030313601460301002600b00c0307203001400003803803018603a5003a049904d0f070f41c0a030380520340100c10862004c0c402c000607a20a008840a810f0b10000030840700d0380d044003d00000e240302c1606001000f0700c400210203480281100c2e203805ea407086c1608100520b9040b8000d11083c0c20660300000001c1403060181442150340f0100d0710400c00e0034440180c000e90040c1c1d98501c040000c1c0030880e58456641c59180e80142681c410041c031000313442c10014403000c200c3c2c1103a024080384400380401d01 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 585512904 1250 585511654 585511679
    0x121e03020c10030c120c0905030609010e0d080405060402400c020c0109050411070f0813090e03090d060e03070f02040b0405060a090e0307170c070f0506040e091024060801 75
    0x60445d40010421758024003990400b002c0e42219405100344130070080169015030010700000b0054040300c0d0b1500541d601150700e07060403580101960040400700d070040c1407000c0c10000d0308207640c0200500512240908050036134904400000d000880c45060306010584142e0660000504c003510270b0040500010b82008002e204040c000c6649020000c10261200709642c105075100d4201c84440d0021300b451021508031043d0300f10500a018800110b006c0a03100303001021699102a50501d081001005589100c824040c1c503002c1e00c81c160155000e0052006102052090b9251030002c180c6d801800100c0d142003141074041c81c17520092200c5039039041da42d041210442840407600c0e00d9145c0001b400d40c0940d8000a0440160340040608a483d160207022034409000440f20340c103649008020303904800c3c2c401d4980014040000380b16001403a0302d01da81c0181d05a04032400703480340c070700d05204031042182e01050301881c1c580980304225400301404000c20031490184a00c0d4104940010070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 585514154 1250 585512904 585512927
    0x2030907170a02150403031d01080406090f0c0f09050c2503110a1a0601020606100c0c1805071d03150702010b0a080c030111070c121e03020c10030c 65
    0x9401514811003a0030010060300c1000b40c0d000d8228010390101d1104503d0031380281c001100807a007601d0104c0070307011110b40300100e00e04d4140d54080454941351140340081c80c6480c82998889100141720303000c98401e000000c0100350680100b00c15500e420880f0084640151500d5140c0d03030b081041e480c00100307103060083c0d4403600801e00102207400b0306e025203000659001112160280201c848140030450b43c490b425514140d18040407591400012600c0b140b0407500290700c1260004c0881c0c54a11460703820b502140b2a070048020703240c0f9020283c203000c40a8100e509840e480c2c0040103a065800550340d40c00d032404550401800d510760300080d07158040706240c0780c6100d178100c0004604a10075003262026010140040c10202d0308c9900300c5444a0700396880c81c0c0a58207080000c6600c60040040b1044503411440020289091424100401e903d842007514418961052084c0001003001c0701901e00340710340c0043c003900c000f20b028031001041c114170a0042c50300e007021400065403c07d441d00704 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 585515404 1250 585514154 585514169
    0x40e060108071401170f0709270f0609061203031d10050712090c030615051305060a0302031204060906050702131d0d021006240e0102010b0d1b060302030907 69
    0x443c4492100100e6034079068400030130004030720400b071103944108246124003508039941d80500031500c0da428844a110030642030441886000102d0305070040c4e5611190389d02819400200740260350704030740c80641e8102d80100c0900c0035108155410035070180309041498180b20040b50005800c10400b646a0b920012442107040d229400207000314810f0704044684020b5607070400c0010366605010f202d400c0c682c00101c44013807074000312400142242c1000000c0700c01c01010303200241e01d0845030501501000e80940d030400c0d203080001c1b0050f601031001c42c03082100302c5641c13a2224074042004128421641c010030912004001c10300c00350715081c810004600b91408080740c0c5030507020904004a09030015100f103400f03041c0c80140603c1c1d0120b14000c0254855805100c010344500c801c030072852018071040340d490300498000c12000e009c3c42c503c0c8900c000c14000043d20b809044041a805101c1800407200b01c5945014041903002407082d42015000c5840c045045280240d149a0f036240140103511 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 585516654 1250 585515404 585515429
    0x30506042a1119030c141b0402090a0905010e1501030b010507140705091305120c031903060f260c0901120203030405030a060501261002030a0f06060806040e06010807 73
    0x280030320100456004044200b0400b5050300b2603013402403400c01c5604007250002030440d58001100000070382d50004c2c860080411140c190807000300300c021740c0503240507500804845400a002d0400d489440e00a211076040b0001510348140a51602000d201070f1354141403602c0c00000f026641310303041d00c90007603000510340030303068600380300d40c1c07401c0000d50200b80d10a0b42c800800600741c1240000c502e855118008480141140da540c04540703004000e104102070f4000e00088019106051030b5005c1020503041c0015010f488a6003000d040c0001d07000704c03503800031908a141b4403800c10b50080c140d88942102401c005803840c00002c10f071303440603c280b59419001c080f107482951303001c0c4103d600a03c0004e0886804440794138082c40136040901c41c120b00c403000203030700b4140107208001400482060401411540542d2040c0d14020740028142406460740c8424200031456103204aa0252009441c0d10945190000420003560342d4010f007030300300b50413150040160210004420094491001403a07 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 585517904 1250 585516654 585516677
    0xe0703050606070f0809040c030908030703021e03090106050f01030b0a1503021c0609051b030708192406030621061509050405060105060705100f0b10030506042a 71
    0x780b124040d0980c007400041c4541c416404000b6030304c0080038500f5082c2c5052000100060301a4100c50110384058034400c01000007030101413081d40140446d640303c54500c203501c0100003483c1090f8000f11010034aa0f0f54641040c0700c0d81c903102c101805400c00c2441c06004034002800484d410034003500c1604e42480440c0d403080204c034029010b0710b48060a014001106840d20241d0780e019001030b00c00c1c229640e01c0c3c00045510b4040a03081c051500214003281417460f06e0301182101d591000400854135407220080d001401e103c2405200d0340079084030140010030120b015143e01c00611680508103062034613904000c050320700c2c00202c5042c0d2aa080e2456400c6d11070604001034079441c0c60383d020090100c0e02c0441c41d400b1641c402d500403070155084901c103a03210b80c00e110691055940c06081540301310100b0501151640201081c41c0450b4000f282c0c0c0001c500214001b2034103103050802082e250410054142002c0c4540400000e100388048400c0d0145204030400c4140c0c1102041001000040b0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 585519154 1250 585517904 585517909
    0x50303090d14010c0e0a150c1b0302150c060702160e0c0708040b2d09090411030106060509120312040308040c0509010b040e06030607080c071b0b220e07030506 70
    0x21034030001c2e041030091180d1510b4034001003205510a10841c80340040c00b0380440c0048030005c1c0707500c141b4169101e9040b61161500c500c1c1041d00141d940c103000d051422400f10042e1514107101105101910102346c8dd07400000c521410075100070002c004560021078004101c001a01280086030885840d001c0c07592501c88001c1043e114003040580300c00e81c0050300180a8001c0c9000b44402440c01c0411065801e11100d4000084140049442d50700d20500030300f9158980600c0d1160040d00c070b00181d0721500e5460001c43e007500d080707500c0200070906c003240349001403d02174480303030315802c3c2240603500e003528045010942120181014042100c2d0500040030450041b030340b440500801800d802d4590381d034000780047c40d41300d4011810b0a410311404200c0d28100010721500460807525440140d40d18402241070681000030706580c00002150b140340c586001d11942c4000c1c00e0912130071541e980035010388808048040f505060800c00d200c10070403880c0000e0403144d03080800b80c54042240c2d100c6000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 585520404 1250 585519154 585519173
    0x5120f090301050702030406021203060604150309050114070207050603040c1a0705160312030e0a060f110d0606020705010c0b07030b0103110d0501030c050d02091303200f06010b04050303090d 84
    0x1a0305406610389401d0001981c0c000015004450ba65401c486801040d03800a03506400145c90458004c40c0c14002800003001002d908a03202c000761030300260410203500d410307007591503240840000d0364017403061142e06581402614040e103815581d0f2855810b00e5564052240541d11446080340c800003219400c0765840c10880d02032603001030480708028900c0024555542103072104551607482c0062000d82036010303014252404000e00054000d4000a8032514054040c0100041c2c80d030f560703400c61216818008020703203054002e850000907044d00b0000040d02d0501030340c000303d040c403000e00944800141030303544c240d45c056051310700403038507120b104010f901420b0410902e026001020402098409459203c181224060542c00c8075095840d4140000c00603c0a0065001003259001070460501d2540402e501c600c0703803810300c2034021681c030b807104101c1d40c4808100346600602d03010346132000d0822219015116408980d40740514100009503030f0711808400711300410701c012010b4144042c000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 585521654 1250 585520404 585520417
    0x702010e1e06040e1501140d050c0f0f09030c010c05030a0f0c06050405010b030d030c1d0a030503030712050f060a0509090a06021902010f0204060207052803080304061805120f 77
    0x1490542c40741c4d103501e07084810010407207420048883c41e5030041d065620a041d904e0702c00e4195481949007094880003100035140080c0fa0318800882045509000041d4a0040281a201d01c204079140c114001c10503040404140400b810003558451420110300044121002c0302007508102100100d24281625001a084005040c05283c03a040000f0f01c54190801c031f0b0200803c4081c7d4806520b00c080a4048502c46400a00041d4071403800390050000004600c0001400600c1050000c0d5a039441c10b1466000300d45c2100090405080780d224003070107001d0f40d6040800c004210f8410306d0804041071408895219180c03103114850041454000c0501c190303192a030300998159a030b070f8212410030403802c000b591910b00661170491020508100c81c4207880660380a44c1c003406105242c0303c1000820300e004810040458a1480c01004e1980c0b0400d0841c01988120f40441c1c403842e040c00c00c402160860408041051a00c40b18200000c0d00491030500c4100c840c2045610f038a203980401c100e500502 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 585522904 1250 585521654 585521659
    0x1080d0806091008030a0905100804030914190f060207060311030606160506070f020c0405190209012001050415020c0c010302030a14130b01060927020c0a0b0a110702010e1e 76
    0x10704906c14540c010740943c15035005607401c0300351080e4128100c0d09420100c40c00f50000d800715a040c001200c0241c800d961407000100148000160f8041200811100d984020403103003558a0400c02c03d90140111001080302e41010841440c00d06800070240c400242281e1180000146503099032902c40d0440360b800d50010308403a1540341c00803020709040e08a403110009446002d0403242d0a18007400755a01c2128201c5940200402c02148040a9001001854188840d120000c49141caa8020302e03000c944010001241c681801c0c180031900d20100c0060b1031a0390300401070800791100000701000c203001d00f07103401640e90b6210b0510030010702e502e10303040c032002d01d40805024203001000c1050394814081c86901c43c450b40c1c0c602080d2980b030110700c0f9252080b0340b9075542220300c0b0030f10100c14038041c0074031001504c2c1c100c1c07511141d814a07040c0c4104480704000041403151f624a50310840103030703000911b41149889415000071b010001d0056006200e00c4d200c0c14900c840c4072600d11200d483c803002 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 585524154 1250 585522904 585522907
    0xc090c0921121205090c03070519051507050a200f0d0b0a06090c0806100203030906150a03061b0f02030306131505100c060b0406050d12200c030601080d080609100803 73
    0x980007a8031590b03106c0446103e48940480800d5a24200030303460701444050f115220590324180921011081c6c00e4403c06c4041307014441000481c03420321a8141441c407030312000c0083d0081b84180243c02c000350402d28040c130841503c00160340c80c0d11404d502607540101c2418800ea413007242e034102601194101c05680c0e41172804540100342c01c1020140144012900e10341140c556510499036408103c86071003047e4400340c0800d22121000c80d500f00086d0002d0100802c0a46a40710380068030380544c00c60300c84400220704403920541c02000c0d81242029840503620b036050420019844400d0848542211a41c03252802080c2d500c1e4038040006160191281c0c0c4001001ca402a1528040300070035500ca504000f50007184d85400d220303010580d18000d020201040301500c0c0c4001c5010841000000d02c44243c1840502080495044124400c100c00034912045c954045c141001e0f4180c0c4000390680c02000901034071a00710801e00d500c00000d4403180710aa8582c030001d10409180e41c0030000e503010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 585525404 1250 585524154 585524161
    0x4060f080f0a021c0608011a090402060a050a02010b04020a11100501030c140429121218040f1506020f0303010f060f020304031a152e03090c090c0921121205 69
    0x11b040d0816200f0304045042181c424461206001503610102c8009501c20f0080040580c81400b800280030342001da44000284104101c0128003260b00400554011070202284140001c80810500c412101200070502c0503501d1030351101207047c80d5000d505801c4080d03070f5110490303441d182d00810144e9048025034800751000c81c0c0c400200603403100c0c0c2c1c0340074012141c900b03103c4000000d1401e4581d48001350980c5043c8140130098182c00d030800760103622a460b80b0410041f844140240340400d202c10044000141c40d1500217494000c01d074600002c50b800500c01000401d040000c4502292854140029000c45010040b82140704a410040c104000198841c1c0000c140104003445540d410469420b1641c1550401030000c00d007200c880c1a510b0850001508141040382c41d04110b40386040108401d15159500c10f440000c907040403184a03981c1c0310060039150302c454040f000f0907a8040c4145040f410440700d00c107410035400d010781072142001c0b07003140131481043c0300f814600381000200480d06 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 585526654 1250 585525404 585525419
    0x3230d0c08010512030a0302030c09030604210f090e0702210a120216032001060902090306070e130903051204050a0c060305060a050d05030702060f04060f080f0a021c06 74
    0xd121010103001441d100000b2429090440d01200203400c858002c50504100c814101c01a600040040b04a43c030b050203080394685040280724003551142000b4000203c1801610092403103443e1100104825000c100602c1500000740100b038402d03110000129540b00c034800c0e0b143c84500303440c1c5108010307030002071804c04a039240500318020081c0d981c200f48401d8440d040080e0b005411070703d6140e180c482c1101b03002034001c0c481ca0440c850740c0d0009005440269030b0280c00c446c400d502c417120b02500003484804a00e0b0512090b51701601c1820000080740991001c42c003040b51600c4000e80f9145c0d0b030303120481814001c80656000040080d0012500d1429181041e200d0072460001c541600e05640080b88450103030061a01c20000a0a0f0800d131038070302410440c80b04440c000665071404108103540141c3c54600041590007400c040e80d9666514181000317003160030a0154600f0405d9803000c0c005059240c0d14040d0704020042c01c00350721004044800842018003160b00404036160403400a000b9 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 585527904 1250 585526654 585526661
    0x1014100e061c0f260906030a110d2403231504030f0809010b011d0105090d0c0e0a2007030e220b0906030a020904080f04080721050a03230d 61
    0x40c0310b4402842c1c801d8801c2480e0009140070800074804c024280304407012800e00d1005140d000140e80000301e201f101c0c1200380840740e40625103008101d40c0790008160381000d01c1c2c2072180301186200d8051181d6207140c540055170340100341c02403820100f80c0d02c0f03040c2d80e0300104007d40c0c4644803000f44004030f080070f25020304940711303003c0070340c02094100d0005075243c0e2040c4541845004181c456000c0030f8000c001d0320a6003000801280e05014042c030520509071074a00d41c0102144c401c10305403214500781078800c80c410000902601550782000810717080f001c4c800c8031500000780c241e6071080d00c0742141e140903a1100300d8040007030b07000a020088030030301d0882c134a05413580c003600c054100008100c500510000b000100c980c0d540542c03017001144018102070b8141c50f4000c1c001c00c203441c20000700c45403400c51688a68010301655114041c01c2c008000045000548074001c4164400b00040c0c6a0300e0b2601c070005000c0203011311060708803042000c20440c59101c804460380390340c00ea45280010b03c1d14004c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 585529154 1250 585527904 585527933
    0x3060d0309030606060c0b09030a0c030f03060e150a050603090307020105090f04140a0f14060910080d1107230409031b03051902031303060c03060b0703021014100e061c 74
    0x22603d00c7c3d001c00e021034000700440e0241502c0e81d03111180c140c51502c1c10b40703112120750340c44020980d0f10500040d00311404135589019201501c60001d40059200421800b88101e4004a01c1400c08105009950a00100715440642c2c2801c15a4a81008200041d0410030000400d83c01905000340004807881d446015440b420444208019905111140d070b0101c840c18581207950402c500f01141c19464454480b9500281082c2d0700f8101a4036020030701d003409006c0d100c002c0803d000c0d122a07a041c0c20305010000c05889482180e000030b0f000300300c59200d60300d251503000e4000e44e941d0076418241441084241da2190b90780981403105621860010b08907840b00058003031240d4603e41c2c03042d6861021007200c00c0c05000e5000882d0f0141552110f100410005902e2028181c0c0c0c0c800014404000c1d60141480300d010340c01604000c802c00d490041134035100c1d2500d4886074814403c00002081c2c1c12096400c1d15901440c019265071900c000c6680d10b003081e5104d40d0500e18a025200c100400760030b40c1d0b004d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 585530404 1250 585529154 585529163
    0x50d03210b060708130f030b1014090103020103020c0f0303150f041b0f2601092a11070b0d0504140f0a0b150907090602071a03060d0309030606060c 65
    0x40224244282504444816840a6000380100203c03404030380f044001d09a81c0901c0c06142100c80d6413010f130000942041d5000710b07080a1400c04124a904040c172110000b000c0e454031040c076010041d03000030028041404002e060560101c1d0710003000c8020070483c10b000f0111801c4a569050051700c80c8622280c810516204050362203076943c030313030500740213440407205404045402e42074104420340744c10712034038485002c0007000c3c00441d0046030b600407808507007500008a010694145142c50303083d0b51001350030300125551441000382c910066040d0002840061401254040301342c20b41d5410040385900031940380d84080b6510182201d90b51116005901c241150a045c080c0540000d8941400105100b01e58100640c3c45010407000001140c0c0071404c40007103588a46003400040c5904001e0f1a40000140312403000c5c0a500d404100d0360001d0f0201c8500a603142c20030300224005072100800b450b0007900201281c008160143d0900c1c4040c1d03078004018442c0644544004042940d030351030070780d03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 585531654 1250 585530404 585530447
    0x100b0a020a0c1e0b120106111011030604050702060907030b100b070c170d0e0409111207090b0d02090a020f090a03240203090307020d080c1605030625120204050d03 72
    0x420b08010412105c01c845d441c8050040c0340e01e00003003500d200036000c1004585000390706901e1204805885154506841d10380d903d40c40341012000c1c00102c0e04010546019503000c8030601118800000b951001c0760707480159111240d82d1400701c5400e4040b1548004000b19000c241c9004101c2c80b8400841600c0c11601015298121403ea0907030340c04260500001003030111412041031306060300483c4000b070003a4420840309501c00702203602800d203402d10b8510394000c01305c144441d85050080800c114412202074141010940020b80384c206c0c0500501025503000030007046d03038000ca0094404001c4024019200303103503a0b04040310060400c2c03106d0b41d40940300c842c1240c8404540d2080c0c0c0d018042c220011818240707180e003030282901d15000107846d54402130060f150f8040c401c1015855100d125080205a94075220030b241c503000b00a84158500d46c0d070f0421001c0180324010800d00b40300c0041c034014038090454108140248101c0c0c0003607030070000780025002030540048844510030700c01c20000c2c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 585532904 1250 585531654 585531659
    0xb150a0323010618180803010e06030c12280503040b030f1006050901030b0406030615031502180108130203010207120206150901050105070827010f08100b0a020a0c1e 73
    0x2500303c6040d405414a150220200300e608480107502084c0c050000c0c0c02c4d5901507010640342c032002e03034009a01c4440841c02c0d4004001203403c007130201c240e40c50780942d9250002c94040d49081d895681c41441e400b01d90009050411078109040104070b909600101620386d140e445031950300c0250b0048450320805514100400c508044e401719036400c8482540c0c84508005500c0011400303440e5801c240b0ba84540c4030000440810780611803141545400804441414030b1450450032000c401003880185c1d070320600035045036508604a00c8940302c400d103001519a5182c2100d694400b248c040065095032000c81c40710300b0010280c0000d060403c0940807100d2680d180803140d1211035902c81c0840e0007141d0708004014650144000e0007980303200e59a014101841c42d4600010311078000d00c01d442c2c48800940003481c135608000070081007030309441c01221713914108003085800c80452184a4036110002291740703845100b071120011142e403040c0300c0b501950750362000700ca0454880b413003084866142d0400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 585534154 1250 585532904 585532973
    0x20d0b040212070605030a020d15080c0406080a2003030f070b010302120604030f05030c160f1106120103240507030606120c020c060c010b0d15050a0501030f0b150a03 73
    0x140c00441c3c0d2181c5e9141e1440c0d40c4c41640703501a401c00d03030132034240c1074a80640060428400745c2e84000381c8441300080c50518041003c200a8501d01c0d0310459040d0030402055010600f41450f0307080001661000b003088141d00c90201c3e02e1032003590b00e85c0801c0000812020708205022041a049034004c40350780d80040880c4808644032030050300c0c000c01050b0114072220103240180b01031540020441400360070031103000070404140ca0301440868082441c0c4520a080040e070781415001110140d80c0103043c003c0010715945100c40601000c0d0100f120b445c9204940404c810080b60300d03d460110501842c20302c0807003e0040c203914013905001c075024550344080740070700d4402d01c01c0005450b401449013401c0c0308203101c110340c804900220f4654849204040944420341d52401c894450403058001c18011000c81c01103070f0000c0c00d040380160410300100086241300420700910fa4000c941d614683e22000041003114420a5007290005082c060000c140003030110044440800c608590407518502c10f60b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 585535404 1250 585534154 585534163
    0x30c0705011d06041b08030a0c050105130f080715090b0604060605090303091e04020703050c070816271107062a050a020f100b100311040b090607020d0b040212 70
    0x1c81c0d244a42c48040020b0200d20142c00b11755406440c0000112010744841c150707802d56004c070b011a804961844414420400244201136010828140000b45503c140d42d49140d0701c500d400003d0300554001c954001400346245080010203140e000402240b1a10320702807580384800c49500c1d129510700314000070074030700805c211114550018003961600380400300700174089800d0364131011884c00021062500d0b860300e00c003d1040d82e01a899468840c1480b052583c6080d11681012a40f07402c99230200036090081c031090000c0d40d03c0441c1800c0e6080c1410807420b80e084031509004070950400c4a200c0c195601c4100030815140124018400d4449401c4400c0780101040300e41c03030351800440c0c0c0803040710f4416005070010096a105641a9400e0080e0041c90803904101000300030f5601e00c0301c65100c2c030b44803040001140279030505110030605940301c0c003014022803091440c00600090510800d42d22031088076034141d8000c258188600003401d003040158401c071422030081d5a01da0701078400000004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 585536654 1250 585535404 585535451
    0xa0f1d1506060301210f05061f030201050f0d0906140a1a03030d0b130504051b0108100b0f04030501052a0f04121e0b0907271a06030c070501 62
    0x300b00e10300d1a445c05c04029604414005040648003544800c10005030440d05128100d0703000b00000c00031b6051020f0303080c141b024950605040c103181c4403400c05c0180d070800b041d1503007800d004000d26154040081000058484030b140108a140b4012261122191102016008001c3c00c1c07002c02104180d5242c030308940c00106034055150f0b1050141304449061504140b58504d0050440c0d4240c0310182e000505440c801d0f20119082d8025007480c0c0040d0071008070310440036000b460101d20714141221140c10050013405055181d1000207014009401c02d103088034000e5900400800c101d141c0b46000c3d0941070728014914142c04500c444286480040c1d40070781d25104c24405040b8541880c000740c1d8108512a0202202c0003140781c182c0d2501419076030700407411240a252030224919014840034206125504040c0c10305d510180b240441c4140b2004050b034031f5902901c005011580101d42003041d030345030038400d41e01203800003c0010003c5030f04040d02d15103104000034420000030385004160f4070142d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 585537904 1250 585536654 585536659
    0x70603060b0717160c1401050304033f0209030c0a03080a05090a03080a0201020910020607020a14010207170c010c03050f070c140d02160e011d0a0f1d1506 68
    0x103105401c0403c940031610034401595080b40303860700e41194401100f415900070240d40300301e1200e0741088550100800001150002d181c281e10b5443c0582e009000c460483d40e500214840700c40c000b40394011a2030188518603050411180c030380003030946e8480a0350001410351300070b00403501c0b40d8106041030b84004040c0ca40c008600c074208403507580111859080503640641c424a0814000b0100380c1d0300004041c27500c1c0e580d00141c3d0314a040b209000018840e140c0c40703000c65000d0001c000010b0b40c0802d13034554040e4403841c1d001d0b5589245c403005029019000f8080e03e00d000040c0b18020011122001f400e403020010000d20100c0441c800c2602101c2d400c40300c2011b00640800000c44081c822810240301e58402c081c1140c0c84140009281c0c900110f40070390a015900048841d484181a0500b0b20020320090a10401a604041a1103094225076000e000302402d0000400e00308403541c2c10248030700f03680a4080220980c440c1c481280802d80d51041c3c1914080c1c405219450404d0f81c02c41407140c1c001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 585539154 1250 585537904 585537907
    0x8040f0c030b131b0e0103032d050a1716030b060f0a02010912140d050606280311040b040512030415020a0b01081504080901020109020a0e040209010e0106080402041d03130305070603060b 82
    0xb96201a505101c00888144c9c0d40400c03140224030840081c0c260506199240da0703019252144104060301001c14044080321603840c00c820402500c0b03050f41c10701010000c0b860f001c80c040c2d4840000c140103010b81084010008400f18402c00407590550050500c540144804907411208000a40700c0408014200001040800001c1c2603100c541d0050f9030000c00103031285190041a4104900c41034419680f005210040488030042e5a4140541400c0c080c02210701480c25141044240c0c40780b0451107054001e1203201d10b581a80f982c00e0055800400d01006030600e80c00c06250025100d2045d11412140d40b0510800494a800009408085442802c0350740d9059112a22000d10343d40080181c141190b4850048c1801a2120310039600107040040c000c114508143c030400250300d47c140c0040c9104c201a2004100485d4080c9140744c1151b0152130004a8000c000080d50244090800c09043e5200c005112503040280300c0c0380000700ca005a0985000d29120b00d01201078490a119081e000c500 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 585540404 1250 585539154 585539159
    0x703050c160308040c030609050c010e03070b0909060406030f150c030501031a041415060a0801020a02120d0f06031a0108010c020c130b1c0b0c0a08040f0c030b131b0e01 74
    0x9201000d030058060040e440307442d1b540343d54080c20780700102c80c101e0b10780c0c005010101c05540c2001120003901c1003200949035050030590044030707902602003d07610525041d00481c3c4503803180d52040740555005442c00380070300c0b400c2c10400b02c00380020350070940007460702c60304189039840ba206550690350700c84842c2c0141c02d03070180c0140003a80080c1042d50003440d40601c080004108004801100342201c01c5030a840c500350080240d408035660200101d40d00400000c0300e079940c0031600980c0b011a41e8015920b40c2a02c0010800500310041c200034640c0c604400032050040840322018000b40c0005401d00f1a0f0325288510300380d0305552080310259000111501c0c40e8a05200c195003014451240002c000c5075070300000e0103141c6160003083c030010540c4e4906c81032000c2004c2c41c5601076a500e0071507291096001c8024089030300108003400403407200840100b00001518050002c41d082000d0380003d05014008950507015160102c071080c0c07500c00d211072450032142081080b03c1c0c0722203852205a1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 585541654 1250 585540404 585540407
    0x40222050603041e140304061808070e010b450312030a0902240c060106021b010f0210050a05090d0305090c10090e010609031205090a031209050402030a050703050c1603 74
    0x31443c04c41110055010302e0071202d800e03020405070000f09000d64030f601c0030120142056000d224660000301d00303904825018060b8094506081d811142d801d4600c941d91a090514070a0b08800300b04070144244050319034180b070490a400c0c00e07a43c1c0154408042c8501c00b02010940e0f164122407080191060510004842d411103903c0780a006001401c0790140b949502e200c0c1c05880c9104c1d004d0341c5111030100d80c82c05070b03100c10401ca901501581c001004a0030305180000281d00b48038020314100039501081c4802a8428000c2200200d40b8003c18072031030401c0e800301c0e000b5020840b007a27907907071203050408400e09100b030003440c0c0510820001742008a101606000c40f02140b22100000e101900f00001096842241e0369030007410301d5552610801c1c00c6251140c070b004489007200042100621421000d940c94035030503400c1704d1340217406a410780c240e2602170b520144954486ca50091000c010040d00c4440d40e00400c0c85980c465400b0441e81c3e8400c11500580e004200314044143d82403aa00c41c00030307 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 585542904 1250 585541654 585541703
    0x806010e13050907060314010f0510051b0f211c06050d0b07031a090601180504020a09050307080111040306020315060a0e0301060e07021b06070204022205060304 71
    0x242806006114455241c8506600341c81e0151840b41c0c45600001040000baa8144184c1070a61418120040c2651500c107112080480d180174a603c0780342d8100c040500742c0d006004403121004140f001c40200000e1140f296224a0b5605189409000e140b4030b010b15041c02005900e03625028080c0c1d141050810182c0e401800d528480740c1012690b00c1c4408141c3c0d03515040c07481c504920407080c40c00d0502c1c0c203400080039103001d0005c031041214540700e01003403651003000b101d13480300080c60303d20200440756107290708181e00c5a01143e04030f807000451103110755100e000d174001c0d51015021600070740e5840740c40d103080b5001d5003250001154140418000078209800440e04502d6110003411940c90000010303100341e01080228000c01c09401c03080f0700e00d06084c020754008010b00b0013007865900d008000030f52a20111075410400134828036000c2c007940e61b148207035007010740c01900031500c540002241d005450480780b0f4810900c001d40360002078070310701a0102c0e4800c42c4c0c880450300c156003400d0704e0842c4a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 585544154 1250 585542904 585542927
    0x406050705070803070b011806030305030708040219170708030a0212070f050706080105040e060f070f1407080310090905030a0c080d2d0905060402010c0212010f1b030b01080601 78
    0x1070103200d9000900c0703034040003e0421980103440040743c5c1d500d841e0310b10222381040e840401d8110300344002040440c0e00310050b40c0c0c1c05049420684c1c0266510320000d000c03a110413100f11038203006e441e00868192401c1c00c031000c1b01503640c012601c0194071410b2059590083c1c4030740600582c054154038030001e07040b5000e80007d500c505944052000d003a50740301c0c281a41030700300c0d0780007600b85801000303e842c06000d680345010b40100640600e04000d805116103c03001080b12045c4003880030b10010580c8100c030345503110000590a9034564103203151800c00c903402603a0440050540000c0030912001500c40c1401c21607000d0000c5140407542035050700e20840c25501500c41c0d00b81130000000c8052030b402845078904480d1369500907100ca441c40010140c0105050106031464042d0f4100041c800203070054020b41c09003488649400c481c80040c0024084100c0242c15500300b040d00040007d883e0400100031212401c05c10992131f098108804035000301400d9400542118040385840d405194004d10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 585545404 1250 585544154 585544163
    0x10b0a051521071d040506101107030204090b04060b0a120201211a100903150f06031a06010f1b170c0d020303102405030703021b010509070f0b04060507 67
    0x1d0b014000c200c400d10140c4119040c0021038080101d10702d0440202121100c2c07610100d0301040103040c8500070440402c00d107245c00051245210b14903000c208200a00c0e030065134014020310810241b0720301170f00301403800d950442d4041d0908a00603641e2070321044600a49141600f9034022070034903001100d00a40f101c50005808000b40e0340100d00410f41d01611032000c48451451805200d000305014002c0c02d104d140c04100500c000092000902103065010a4029800082800310030700070032200409060703000401410134407540184282404610318460403090700c034401407507003007841620701d041900c00360656012900036274000241c0982c0307035180180116400c641060880000140380c120903907030500141c0d0010081080044e42841d015001c1c0c14008003011148a140d0f00340d00302c0828000400043c00404000910035a01c2a41034811603140d5200419051140e0344000303009200c155229006030040c45404140003820316150030480704620100303481d041c50b00d0320071034454011000484 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 585546654 1250 585545404 585545437
    0x12110402070c0e04260412081603080a0c020a150207050106050909250b251e0b070c0c120f05070b030f01060f0e0105071b0314010b0a0515 61
    0x420745241504014000030141d001484c24242019415216803021816810003900382c2c1c402502000b0043d14212441428052002103142c9043ca166019001140e0b0b01018036035582404d06601006490007040b00d200b003080f90080c806c800300d0301d074440000c01400001d003000320486215070640c01011094004c100004145489100080402c0d07002c0e121020503034895076004d042c4d0104020403410001c0b1154403007103428a00441d604150041a07000034448000010f410000000e03210040c0c5c01320351041c410b21200c4041e03c0c9400c4403062035002a11200f80c92000070708036a010307d100c0c4a0f80342d0014082040c042c580081c80c06da0009030141111180b60741e1441000080c800c2091002501c0322072401030322031500480e61a01050143d0182080000380c01d8000d16030707a001002d80640403c00c0ca0281d40c2d03a482800d08050035000031071404c8581c20398500000c140b0028000038044800d04a00900c100b480751010018150018092145d020514100c21000c1c5641c81000f0003000c6940080700 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 585547904 1250 585546654 585546667
    0x8030103110402070c03210309050c0918070914011e030803090a08070b040302010c020a0c091a1002010905160e161107060f0e0103110d0b04020c010204120c08060112110402 76
    0x3207110585c81e5004907481800c1080d0090316407100c442c1c03d00a80780c540b80c108040d01c0240c46265890004154442c02000c50708007042070b0810b48100309080c5100441240c04203030750b900d494802000380581000780ea100240010540110b81d590410f2460540301c6003000c05401e46d181d03218198400340c4049801c0c82401c0c50340000807076100103000800d0284030a07040c5842c0c01c0c00d010f820b440d510fa50b043c00b1904034034460b20004100040380d005413070188000155104022001d2014001d040406035030226a134440f0001280d0b054212443e041e2003103054409102004d41c500049200c03a000c3c04000050103800a030000345036440802402e0428a85041440c0d65000d01c2800d100041d000a00024001000d103094942c0064581c1c8040c2e40c20720702004440c020302554403031400790301d000304a21501c07030340341d10b003d0b03921901507441040c5400c1c02150740d035035550001c1c1d00380c040c5010100c94040310701000103060600402c00f14125105011300e05c1c3d171b130091966801c0710f500030030034541c0c1e2045d030a2005 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 585549154 1250 585547904 585547913
    0x10b0d0303020909180a2009040b09070e07050a0509060906190305061504030b1e09070801050606070f02010c15050406060501020c0a050a050609040e030a09030219030803010311040207 81
    0x1040010302036140180d40c2c0100c2c0c001d0140d444002850748404081d81280807101180c002030801080da0014a044205101319810300308011340d050307440b03034000404801d200a000e4400e500e07901909103441102c040964400c0703a020701a404944000109005102070401e0310f0103031307005005101000388044d10f48001c0000161054101c500c0711503138903401075841d051954261040d250045c10840d00d4007421446500801c2c401e104501005203001401800310b10b507065503140041104d48160004001454811851952424144140840707582450040f8009041807811608000d40021030840d007098250010b480f410b004400468070100510103031a41d2101602c617250245101c2c4c600070950f246403200091034103440c01e034003c0c402c40300044104000d941d6030300402d080311000d0312110340701c8030700100080c0140110042c0b100140400941002c88a901450074011303244200c41e074070781e0301910500619014180c1c1c00000d128071020001403005c100b100310100302c0428010005460102507684 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 585550404 1250 585549154 585549169
    0x92406120809120328030e010c0807020705150d0e0a0f05070504050a380910030b010b030912030411030a030905090603010926190504030210030605030c12010b 70
    0xd0507101c00d5008601900549030280403100711002d544000c0d4100040d4600401c40454155902e050801c018104514428044e030851400c1200c030300020010b000b0807690260004c14202c501e00c0c018010503c0219491510003100050380030000c41017410a0f011540d81001031916540d80d20f054810400d4090008402d40d078022140342c444c0010f416454a0a8140001d85001600d541800f60802184e4040002c4075000440c803c2c0f41015440c3e40c0280c800c2c118075401070750b005041c3d0480014010003001c8461114002c3c00c407845030183c5841d42c0ea8031140c24115000680b40c03d0b00c0c5401c8084009240c400d07a40145820900841ca801c0c40030092400003860142d80b80c1c812800300c0d08440e0704002074541103034615070006040d030083c482083c2d280e44515135009580e510070050041002c45082800b000e40c01e8500011f5a000055442407040d00040c1c01074201d840100e11400115080c005c0300c0740301c0c0c0140300460b1000760003022030098410411410300b0800c2d204992540d0b840d120030382c00d5074a180c0d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 585551654 1250 585550404 585550439
    0x18041803051213030f0309020105040515041401050304080d0507020309090f0703050a0b01020d1d0a12050105070318080703030e01060f06110a0c0e100518090c010201092406 76
    0x3201e01e981c031490b008610300754401c010480020045812021004203030817040003e5a03914030304e4005102c22040c40140da20b4022900850b4009054022201d0302498100060040c0c030101080c100021a650004440b5032004980040582d0401d0010400c903403415008141c0141e0342e401503a0400c0407110200b032610404689540b0325008203424011740c150107205090b0801038040c1c050084104c0c04001075038500c03069551804201080070242600111004a0312187d4001810400071035031310242050081c0c03d40f5003d5505501c1d142c003160040d406881001d07050203080401c3e9500b9419a00c41e14040c0d0852300b025014075848403242100c2c1d44c800e11410016010903120fa11409040070801803a01b081680760302c46550206940c0307004240707001e07801d00440300460924441039943d000c15410030301031a8011500002076044021342030f100b4098240c0b040040004a591221400004909803480e600c00a418585003140c03004291a1601c4035541c1c4009050703011a1482d40c56000885e0341e01c084 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 585552904 1250 585551654 585551657
    0xc1c09060212061f1e0905030304090902030d1107031104020c06010807140d0b1302150403060b0f04020a0c0633090c05030702030d0f09082b1118041803 67
    0x340b003044041d152650f5546005442c06040f000c881e884002e004e0a42e10340f9000d69002c540121512000691117445100080e10002d0280e03620b865079140100083c20707a15001321700c2806044103249a5a100b00d0308d9901010000c1c1c000c0881c640b460729581c803070108891165801940801241c00c4500c1c0c2003103c0c5000301240002000798514041400b00002403440e0350910070061640f000703011130403e034589a040b401c001c0315010360005030300c0050520b101601c5a0b41c01c20178085400001c1c8a0a40d000540345102030340c00f00346145000b070402080b0711070784580380c002c00e80c0c06c0303540c001140050740074130780e52004046a01c00300715072b04028402c01d2403882d510507117070340f4a01005c3c440074560f401070044201080c18454218203100d5030107500d90141006480c5647c0c1d95645105a240f003a0f0003102c01c0c15004240f9907075070501c12031200100041c0e5200305819441000a0325002820382c400c11410304901000c0c2d606151034100c1010411100c6c855595115450310400c1c0359010090400c080c00910a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 585554154 1250 585552904 585552937
    0xc030209180108070803072d02090408091e3007090501090c17011203050f03130204060b040b0a0e0315180705150d0903021c0f080a02030c1c090602 65
    0x40c151050725242c4e81d5081128107030404e214140c005209000c490b102030300d00e182c0d0203e004e5448120744e0303e40ca20180c0041e51004158042c04140500700009150300142a219080102c2c80500310000ea07400e40fa59054004c04492031070751080702c1034082401c0f1103640c0101c000b9149240c1c0c21031840e04085404c40055241c0d154010890125a485030b054646030034280459411014004400c450905201e884031620f050008402018072503070841c1d4880c0e099511207901c0c2d04007440c07a1004000301c100100e028905d0850042007002d5600c00752021500c0c0400c80e5868003602c144225110072041507600e8040c404c0030003094401c0583d20b81d0350b02ca010041c0b07042020880b0f100706940740c02c030580e0000f03000e1181c002c1da00940850b000c04035200c12880420120b801981031030202d281c034064200c1c106180c100075011764042d41e400b08151003460b0f410742d00c00d90142c0340c4881c05c40881c48290b4030b40903044410081620101d00008280802d49081400000c1e05500c40e00ca142c20381e230013040c44014003602d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 585555404 1250 585554154 585554159
    0x10020a050d0f0e06042405010306140901050108060703020f040f091517030301030818040c050406031a0306150a031a190903020c040b0a0521010c0518040c0302091801 73
    0x280b0701c50300b24a854a203006001803111119401e868050180018104480d0011642e02400201940085454480c03000b0465503a59080510041c140750400b41c03c031340c0c000c20100728a800140106e81c142c0c0c5960f805407440341c55418040c0c000b03600040d002c10120318144800200d00011011010040076017210100d10b2168001003c1c4480046070403002004400d840d04d00240c0b1400400e9a0541e58050050390383c40440c1c0b100c0f40c0d40c4000c03040540794083d080084445c0065480006841100e0b0151402e001c0c000101c0850400c450b0450324803501a0b10460026000c091018110303181d40070013508188249449858520071801c3c0380711030081e080428400c1c001503141e04101c0b807121044d803407000c01c1503160300d0381e0007511440e580c0303180340c13090b529410310300081d66903d080007004000040081810326540e040c035000340101010300f2483ca505e0100039000d5a0701076822504140e044981e103042e1075a40d401004001c04e560304250040645c00c0c4443c00b055240e680c0d071440c5060000d03c0414a40d807 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 585556654 1250 585555404 585555427
    0x17180a0b090d170403030b120a0c06110309010c02060a1707020304230d02040b040f140f0f010b03010b0c120708071407292208060c03011505090310020a05 68
    0x281400040000c00c000502e030782100c5403c0441c02c41d00316501d85800701e070b0320031140b0008000d01c400304080910350080c1e156400c204000440d254003121aa81c172512121458214015180d000d81c222080c0402ca4481e190001071424800030150418241005030404540b03840030f0904c05000c5400f01d02513440001e05201c81740c180e04640040b03602480010803c18100008902c2180303142c038000303018580781c04081005640e40c4c2c12400b82e040c1d0750036040081d0304d9525000c2c00765000c1501c101090b4150040402d4414040c01105816654506920f91640c1d103411134440c400c1d405038110401d580209591a034001c24190020104140107a90031916004581803910050106800c2c0c041c00340c4c000b40d030822402d00200340c211413180b2048800c880c113000008148565104e0380403107000760444c0000001610240d080c070b01c2c081d00e401004a510554880301301401d10700c8280600d51030000d40c51800c01e00c07544507400903d50b0342c2d009010745410300502d10b140e509036040b0301280c00110b0b03408589481c180 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 585557904 1250 585556654 585556663
    0xd0c03140c0d0809010c03030e030c0a06180308060d0f02090c030a050a050f070e010c05030406031e050f0412020c090a0f0b04051506030915010f03150203060117180a0b09 75
    0x12000c9840da807018146503140f840e1442440c81e00e90602118881203c10305000340c0c00300068440798801d4a03920382111107c0c070b8580785030f00411101e0500d03000b040100000402c140d080f400381d160300d0381d08075521410b0801c408402c3c5080200c815407040025000140c0f51fa0744d25134060020302e11040d031070b4203008002070140c4000070450300707006203402c1c20040e0f8114600002a000465820195107601c845c0d00125004c00200d080a8458480010002000d82d4168070120b80749418910b07282d000a00da90403082621025207900041041e030300c0115002c04d10040394200c6000701c0780100c5284950503c0441d1030f400d41140ca641c0030320399502c2e00461984103400f60003104582201d00300705500e88004000305444103084540c1c041c1c03e01000003000d2a00c00c00404804a2b540d110400b003940e5241c03140103c03032040d030108495010803100100b120070600d0003900d002e0b0405071078a144405030201c100444130b1000700210950882010300f03050a02d8180050b245c2140a40141e28141c07030102c00f820700e030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 585559154 1250 585557904 585557923
    0x18060e0a0c05190e0f10081506130612140607020c06040b130e040c21020105030f070302041505031006170f09011b0c110109140f0d0c0314 61
    0x4640180c03211600040c4000c4111007610000c640400780d540016510b0007005580360030a0a00e03404403028064203e0480b01c280d440356082d05e00c0c0500e80d503110458191615880b250030040000c020300030400916201e000f8002d507032105c200014110b5520600d40c42c0035201203c064486013515101603030302c0320b010b102403940070b5a6030004000130491400030413954800d5120707940040001080c403004001e03804041c20020403140e00510b84904045c00d2a00c81c0e50f00d14818628a91070000e415003d18a00900290765913805845680c15940d038038200c018a010020b1a60041683c20040481e2400d6008608503d000c0542c0d90b054607481d148640d0034081c03e44e134124105000856640304152485020681d03440200d401500c01c0a486105a00e4007405040d0301d144a12204003c501c0b0b01607070300c09080c481180c000c000803002006000019207146055024994005203120151422410301e40107240341e460018001e0149002d103525441d10700e0720950000c5030b0406414010b18420403003080443d80 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 585560404 1250 585559154 585559181
    0x60d021b030c0a110d02030a0c0f14011b170d0b0a050a080a1211073302070b0703120e010212090102091e0105090d12110106181e1806 59
    0x1a0600381d440d180d5a54210b01d900030a0750280d1134408007a42c40380c2c001c14079004e6000e0b080f140841041e151a120362040c500070700520780422100020501807008928040c40010b8503079544104c0041c0d021122441c103840c1c150365100b2211108a203040c0702c2c4004211200304400009142d03103000080000181603640101d101d201d0450060081003c0402c480d05175650020650070941d4036210240c0e800180515210454010036000083c0040800c0d41d40d50803540c0d4a00012011601c003c0521190740c1020072640140d00051081c031011030104011700c034071406410b041150311a0b001d030410135a04a401c11201c3c907500410f244510614000701c0a8120459000a42c2000c110801050a45510402c1d0455540d1900c0c0b0b41c0b00d00780d000d50111800d1a202400c3d11181c00034600b040350680b1a02c0c41a5000101074000c5904002010f11402081c0c6086114a00381003000c03145180140c40c40c00f404000d480f16040c800c1ca84020981300b003050000c030001900d03c08046030b040100854810100104 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 585561654 1250 585560404 585560407
    0x90b07020105222d150f0f050907052812030e22021c0f050609060307030c15110706080a05060a050303071401110703031e1119030209060d021b03 64
    0x34002901d840e0071404000c00c4482d180700107500302c000d4030081c0401340005481c0800704000c0050750803a40c0c1010440c410704000611402c6074a42c1d6940446a0807926401c0c02d401070300c001e00c0146005a1203040080c0010202070700401034504a11180865a01507403150324045240420550060741f40300317a440707003140c030181c1c15041c8460070180005a11400d4941c01c0d0300280901542d059001610b498001c00c1004100381003460342d12000034401580d50743c0c424424000010524a4005550410b07258016540d10340540703098510812104000f22100902098040420201d44d003000210f008180c2541c43d2545401d040c2e08001c00c40310080c080704e00400441006000a84002080300d816590000003011240d84203000e82e0300410300e44074050301d100c0300000c504c400e0680c190444404454947e903c40100a00740c000a4100c03903207024440000a400d01050b2007281c0302142ca0074181090b418050b14040341d40000982c103510032240c0b0f003007866010450214130305090307000840d4440c0040096 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 585562904 1250 585561654 585561721
    0xb0306150c06040f0f0c030f05060a18260f0703120207033f09020f0306160f050408030a03020414041109210d030e2a09040501090b07020105 62
    0x4580340c00c401800070304484401c0950b03004010b60b40301301d42e01d03131a0002c0c003450205860b89000241906408e005503002e20610300410401e034010310440c3c60f90000d600c001c2c0081c18640e03a502c456500318a803d04416200c5010300b8050340528402403e08800540b2080eaa0f03840914018011100c00804004e90307900c14896100060742210041158050b0a81c2d41100c0a42805000c2c001141d000b00000500542c4849440715003025004401c1c0b56108440312441880c0c800280366554000312000f21904c0080c2681c01540c50007002c4c002c0c0305105038a0000d00d015113404a091855001c2000400000e41c00102000300d00d26601c0103a440410448042c80b00340044180c0607014001e02400600c561aa1460030015900b402466550b80c9468020b0301c101095155028005104240c4000e000707002e4901c0c003c081010321444212001188882c143d0101540c90900c4075440004008940c81c2d9a80c01c17071403000c85c1640d02da4506c02c880e81d90010400e803810410124a611114141464001d40131019 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 585564154 1250 585562904 585562927
    0x7020307090e03030601050c25060e15030408091203030f0106030c0e0a090b010e04111317120904020f1306140703021b01021603080918060d030c020a0f0b030615 71
    0x4c403504100e091070b000303813035000c00e07841e1505003090010540030780c0035138062140382c01c4e220b00b409204644075500c828171203100310801d00c150002c2200d072422a400042000500181d4104090b01c445070000c0d11600c008002000700624560054699042c0407464100411900d5818060040c00700b4030f6103003980e00c401c80c580c04a01080c20030b0154005980d00c510800310750364498016040043d8000703000f844507005200040f40c0940c8540c403803112890409002203040910b9260401c407481c0303e80020081010703140c2c0c001c003c0303404c90000544c0c030035020032280d064551850050103881010103002224507140103070140844c030b9107414010700d119081c407901c004a600410094043c554842c4000070720207072080101c0c1040404181ba80140100450110a110b000c0c0003400d04090140c0300048294600c03061308114074811500140e10542c40340d10a000070340310b240814811803000e0162134602e078a03450440c0040c0745d03e410116043c500071040281c01c0c42c010080441c501d0140c4e0760145048942d080 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 585565404 1250 585564154 585564157
    0x4141014060d02030f071212030c050d090f060608010b01020c0301050919080906040e09010e07050f1011100c0315030209162601090b030615010e1203030a0207020307090e03 76
    0x20a40b00b81940240700066480901c00e4071450b404201c107560541d92034615003a4050540c1909882101c604508503601600a1151800400050b21414141217101c1007030b05c043c191500c8101d034021091ba01300000280d5070f004080c00303807422a001244c0400d524000925001c40c03a5040c0344a0783c10101801185a004a180e1141d181000c0700000d4200090905480ca40301d507610b081c1d0480740c005000205400243e20150003059224000d1040d503000810a5507217035842d009150f031208044031107100902e403018040001d140b8034117140d407c18a08000c01410484c0050081c048161a034651841c86035052244a05140ca0740c000025241e003140c01058422a00405a0620324072071441c101e246070060200c20b00071f0901c103050600b0405000398440c0054020300c580006e15040c000040b07020701d404641a07200b00940d10100203c1c0d8246001155a415401800c0750041c0c8181c04081d01c1080034401584144014640545d5503605841810300d040201c1e0b200325070b180d107000425400c0140100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 585566654 1250 585565404 585565411
    0x1b030f0e060c030613061e05011103040e0a0203090f0703031d060f070b190606020a0201110a0b06060f160c060806100206061e03011425021c0c050604141014 69
    0xc17161201d10b90182400341c01040e03a50064400b8600d2100d004840a075180c0c0340e0400d540c4213a94540ca503030413141d00e440d602d01881c05000e00c2c4100100008600d29140d60240d644a02e07074400312a904030002c0d0260341400744641065002413140c108030000c0250580032610340c83c0b03055940350301d4103030b08981c64040345c000d841300280742e80200d90108055215014001038070410a03c02009925503c40003c0c0d130b51076a5074412804280089808035030708034003103903501d542c0e60400813039600380e17403040200700081c1c0c404040810070f0402030050451658250400b541c000c0c1c0316203034032505a4101003000c0c1c00a0030041c192441014200c2900f2003555011034010f8000c2c9080d98050000d146140c0d041c2100c136015614a0f41542ca804001030b0900004c80416014111903c10f0b108280310000c8031203280000d001c070035005a400b00046124544000c6540b4244030464900766000200b10f036a164108801a00c00340c44034410a06c040458140920000c01c044104030020400a034252800b40c4240780003d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 585567904 1250 585566654 585566659
    0x30c060e030705090402011403090606030717030306040903020f01060b120603030a020a030c0f2009072f030d15030c0906050a090f2c06010806060d0b07031b030f0e060c0306 76
    0x282c0454110390003240085464801042112745a05c3c1c5007030302990362030046501c10301c03900c5180000104890300c42e86101c2000420805145140c0d14102032001419010f0300460451081400b41d030001e403000e2049601829055118030754840c1d4044a00944440240502d0b20a0b0402c0142011058000401440aa515007001180344840f414086240058014064607485903100b0351030701701c005207144480725201120380e800c0700d4992000c11100ca03001c01d10400d40e0512105a206c24054408103404104104001240d2402d0220b015000030b444c910034007011a08428542401004480c0c800103018200300e41081007680c0c80c120001e40703074080c6403140702d012030340d00c0c14055000c0c0900d400c406410500020320410300030f01e02410410048501011140c2ca0055900104003042c01040d418003543d0028020020b5241d9a00c13407403003400014090409066440000003094600c0d5440d00380d00480a0314005030b58512031911030240c07030400726040c109410480800850200690a0b2500b03c08213 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 585569154 1250 585567904 585567919
    0x5030c1503041209031a2a0412020f030d020a0b09031813020d090c062003030f0c0d1506030c1106070e0d0204140a060503030a020a08091513030c060e030705 69
    0x28000b003030fa0810001d40000e0031b40845c1188440f0030606000c0000e00907800700b03a00301d6190302e9a5004003060034422003403581d0749034104010000d00b550818000b051b01d00042900c960200e6200002e45007155140c6c8400242c2c002c0c0821405110012444071f03480f00c000005546031115442d9080400070300c1941b81403007410305214840405031558107480d005c03a068003082056a03400e0030328080021642c030884001803481541c54200000300c04c03032203200f001000004d6003035840e0403010140c00b40f00180000242e200502950030901e8890141010b00f840520348e01c4034860509400034250f411001141c4244070390380c045240d9005000440544c4047c0741d2600c144980e9201780002e02c070710005d04004c1d40c85400d003015607010b0880102c0c524040c0200302c408100c09170350b13042855160301616001c280543c1201c40c00d0000b1800c028010080c403800246900402648100310503415003248245180824181c8418003c02c01010038540103442e19062a201050303400c00000d58880e85ca01072507026082 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 585570404 1250 585569154 585569183
    0x70804110301140901050a020703170c1611090609040b130203030d06260109050a0605060303070807080304020a3507080d0521010308030f130209070905030c150304 72
    0x1204032032004a100e0003002401020805078451540d90026a0280c070035528103004144401034034800c440c0c01d250f01d0344400341d000c0fa6507000744a041c00010580c20344044108a1851010305c00b640906009118100500b0b1003c0c1c3c4005014604500414160140c1d8808003840080382c400c405140d4015072000c2030002da0052440800d0950180b8001550054240000070039001244070b00210400d90700078030201909480030b0f03075500341c1d038110401814940081c000a40444c00a030007255000e0400f40444e45045103665a81d02140d1050f00265500e040210900c0f0071803400e100d520004201c20403006407c25007030b045004060900040c220b1404082080e0081d5804003031045400030652441582c01100c00c41c040074003a9072151020f6540800e00075002581c603010f000a95050b00d030415082420340d9a444601028400060411071000000d0342c4503400584c0e6070f05da003611450725075036929001807405090501d0100c445241502c11120020204921000c540c2a05c0d845030f04150071080d1202d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 585571654 1250 585570404 585570413
    0x3150c0c050708150a05040c06110a050d05070b0a05061f09091506021e06150627040e01051b03060109030c0306020307090806060d021504050612040209070215070804 73
    0x11200e0000420500810800142c0c4a40118005000e4140d58281c20010303501c0c40d0600c0308950f800c84000700700101c80c08090102c0c174407523929084500d650300d0450364490030503210285880c052030035450000720005288010016452061070b08000504803e00c56418524000341c0100c16480c512007814034050a00e1403030301c0c0b10716800c40050403a80c40030840e22103030101030320b01044240150405840346014510242c1402c040d004d0000d920350000d8050f40d19911416204d420104a8060740118240004011500001414401e00140c601041c3c460b4500c581880f0a80369441c0391000180d26000400c021001d008007540013590903028660390300c0d5216401620b04049513003001d03086003d911170100421079264000c40c00f5025544580c850a40d503440c160b030740d41c8012140c6a800c0302c0e10041c42c1006040c07606691075042480d0600c6800c06d500c0d000860999045040300c211404035440078001903042c40c024842d00112584081d103030b00c0d8203080c803400d09410003500072810001c100000401b4030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 585572904 1250 585571654 585571667
    0x40b0a060506040305071a0406090e1b0a030e010e0106030c050603061233010303020a021e04020c0a0c0503030906030115020109080304080306030c010801051302031003080c060406050a020403150c 86
    0x800340100425226604c0b8180381e5501d50650258450080a8140d1030681c1303075500060f034044480399070707441c2080341c00c211182d40d074038101800071180000c40e0182c603034101e5100e901506040e001c80e60000342c24000a501a401d40788071840b02c0c0d80d036034075140301440810b003044201000c1e25420b86005070340f88c40d1403010411403421004200d00321b0140c19007041e40e400260b4894000c000000780305040c0450b20055210644c4428807004000d6805441500d005040c680b140440d4144202c0c501a81c1c035511601048c180c0e407000c02c082109810a81c420340812006c0070301d1798040c0602707030015810301504130082070303040c03006001d03104d112000c6030000c0201307602c00d400c45803a05520007000c40d01d07810107152800c80c0e90410742d0100d120b401444800c600f503511503045c445c102d41c8000c2420340001d02e9803071080000e51000d0302001d0000001d9002201140c0028010700205078210000d0aaa00c0c1c181402c00403070b0000340500b0705450040000308046440000506a044680d650000399412202d41c1038465 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 585574154 1250 585572904 585572909
    0x14011e050103090510050718140a090921020304080f0d0503240a0f03060b01030c05090d1109070504031e050c010e06070b01080610060e060d180b04201008040b0a06 72
    0xc1e54180010011f100d0f90101c03110940c5802c001c001c10099441d088840210b1050a04007508011000001c04c848a0b00343c000200c250300035074444042024140b400b402090340d800c900d4015034000541002105820032411003035680800203066020a2028000c042d4071003c0e040401e0104001c5404d000c4580780d010280b08004c00400d04c818140c0d985050420583d840d12054404501c0d040c2e0381c0311a54041e000788040c0c2452651120324005540301080300800800c0c105451400c82d05004007015114001e020740100000e031162511a49981381c070048035140c1c111074400b40200740c50001c00042e0000780420f01207200742042c08003600702c0804074803580140f080103410031074030800000e5407040c0072885030b01685050000030b00b2903407101810381d518001030031182e401100412051145140a92010384c2121800308902c003414110b032101c0d4840342c2d042d00c0c180d54100075288000350a41c915480c40b6440c2c134003505d40d100c5460400c00c0103018480020b0000d0401e145910006414254a9106001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 585575404 1250 585574154 585574183
    0x301050f0646030b0112020f0c01050c180a0b16080d0c03060305060606070c0506090f28060807021c0311070606050405010909050d1116060314011e0501030905 70
    0x1201c0900c140c5100100c901c51000c5002c480c03809451000510a02400641c4481030b1030b00004c2c200355802290083d0b00045000c218640b0900404024010a0203518012050000c41c80c1d2207000048200620211f50a48c0600c104100241000804d210340300b0395880103861591101254a5401e00c80078510410300c84170311407450088280310302a0164080e400307983c0140221406680c480042c02180d01c0f940c01d01511080710784000304401e2070010300600b900d00002c1d0548110351070100101d003481e50340603171560003206c14064014201014010b0701004020610f481c8041c1c3c1003900d4040c2d114520500c0c401c600010010400c4003103030181c0c101001c4840007200d4295503580d5810700c4c5005100c40d0283c288924109000010f03101e00b5805440002a00719014280149000400f501e140d501001c0c006020301481500340000245902c41e08010b220648001c50008a080503135185c081d01600440d209407030080308220b80303018101c080d0741915028240052009503500f0030394a44002400284c2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 585576654 1250 585575404 585575467
    0x30c051207080718062c03031204060b06070201141b060a021317071503060306180209130b0a0b1503010602070f14030c040c0e030d02030a140301050f06 67
    0x5210b903104a102d44619410740c0c0f0708550750724802200710482c94910038600018a64440030b510800309088042c82480801200100c4600c02d0011900b1034200c015910101c1060314100006d110072805252540c01c01212070620300596540044c110020280d0390381c0400c600440c0d080340300345c5a000381d000c010400360300312109450801c261101030740c48200d69610000c0c403201c00045084201d0f04105010b007104014003079080c1480c10201d4030a041c09040702c1055121900007001ca500b505c20725500024507161900e28070228011304c04a507501500c2d0a5951100c030070401c000c1380e00040280c0c2c00c030080c0407001c1282000f20340000c190b40700c1000700c01089500000005112500060082c2c2101c07945812601140da0342c0804803040210242c2850f01034015405e03400403440c140c1c0c00070f4481c0c05030742032071004118078002080c984102040c2078405644001201400340c1d810611441c03030b007002c0481da2441c6605200100d28030b080c61400c45070003550041000085841d5080705041c0b000824031023031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 585577904 1250 585576654 585576661
    0x30f18040615030c020f1005190203010f030210050909010506031503100203010801050906010e04110d081c20072010020a03120203072c15040314010615030c0512 71
    0x640310140410102000703e45800c0f4400403880c0082100310007580b860b00034020035032400d441140030b0308004000555600d000103200880c90300d2803014501a0915075410302c020340c10b40c41070103241e50a050303506060080a02c00c9105903a140e05a25040d11010348001d6140e4549910125052800c1d40c04194180207141c600d14442c005980034504032005031000b40096114905403a03103a12081c001c07002e2920b0003d0005d004510380400010404170040c000014140c4030392551101a0403000480c101605007039030406a0025502405c42c00ea410340e8240081030000704150501445401c078003d01c4e0b8001449640410003c000307441a141102814200380b12108000c0251034800c036100031804901c81e20000710100d0f13028400e0f20311610791030b00d4980081492120340395940b58580e09980101e04403003c504040d4175500303000314000c58000b2030140c4450035450412101a424165156a030b0b1405a04202c48518410301e0355182801d4280051440120141201e15214580030710016170b9000050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 585579154 1250 585577904 585577919
    0x60e13080f0a0c050c090c0f07410105100315110c0304081902010507031d060c0c0406080c09070503070504090501060f02060a1517070e0a090312020a02030f180406 72
    0x4200703c0b81c403603010360344ca4100d003004008180d8015101c0d01c80e000c42c02c0c852007082100090082c0400b074011548044104449075501505c04032a050325006008040703008000d6081c041c003501c0508040e04000d0102d49445010f0300440031641c88003034002d0220107482c2c0d00440b0706500c2002c2040c1104400d82d40e0f800140d80450b0303686c3c42881010850b00c60082e1100d044034111801c0300003e541659024500b0956440807603921100c440c01c82540780920030903205c40d0f40ca9200902240040030054000e0003d0041004110764140c0d11111403a000150b49840ca42e54201d9402e910040380d01381962a0341314034500301c5032030045421155110345000008200f040d04007101444151503682250560794591308648291049044e000101d01c440490601c05861007420b29801066075104036401d03d40c8d250440d08200d43c042e41c680182c1c40d40c640040092541c04000300840d450b0030030341540f030f007240d06200a40c0d0744a400341902c4400303404202000c1e46020203013039500030789005009000e407036100e824 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 585580404 1250 585579154 585579167
    0xb13060305060a020f09060f0a1b0c0302040b01021912020d1b1e05010c05030f010603090f0206091503150312130b0d0e0109030f0801080712120e10180603060e13080f0a 74
    0xf01c80f40403030200d044100c8611070740b114112204e2f038031041c82d415007403440d400c1c0005413060140160650044401013052510303194564170300640641d5254808000d2030300080d0800d07000c2d000120030010001000700c0404188012010101d602620208201d100a10b03401d0000941d00001000c9508080e01800c591780c1c000041d40c000c0c2440c2c00640001e0340da07404280c0071a00c2c01040208048541006d141c0503250030000b910002a02400c60482d503400c400c10800c1f82c1d80115401411103001c9406400907040400c1044d20908410180d585403482c3c1c0303030014400da4103a04c00c01181d448000313180c4c129103001d0307005a82c0303c000140080c4031039000e42c07501918610f5124840b4001a110310000035a080e00091030004a4601c140112402400c944030a4040c04000a0080c18000c95100050703040d1100540d0703040c4d69010340c2ea65089894403144150901c03c0301d0740114200350403c20309100d402200940a60041d80b401c1114100c900c540c03810003041c6c0152020658002c1d004942d00200300e4010b50b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 585581654 1250 585580404 585580417
    0x3080103060b0409050c12070f030b04061a0d1410050901020a0e010f0e040f09021903050606061e07051e0f010f09050a0b09070e0403030b13060305060a020f09060f 72
    0x207014041c40740b004050100711012514040e01551210015100d80c1c00c208000010960b200380070390340e00f95241c40c0e003610705a04035441260580302d15001c02042c06002e10a0780780c803d555450340103804803140002845413a0708640035041c1600000450b845000400c040c40b0115001b030000c0c0328034502240780318000e410603a0a10003007100c4580c2c02c40f05610610b02c420034a4481d4540c48081140d21051000030202c03400420822a900c0503100c0145c0c0d0351030240c01d000d43d00b070a500720281d4214034046003084409411180640340a12803c041505010201401c480e9800400c0b915000c0500741f0905d80308407030300b83d0032050003a20850801c5c00c00c00300e0780b07a0b44205084000d110f0140066051811a00d40e48800350140d04070700350400015518806440d04000024212082d0715141c40104201040c00d40341100420b5845a04100a06040c0c24940861411040c1003080c9442d40d11565100d03440188021580c55000801a0f001c0300300406031400c07a807014110f25107075501ca06204e441540540c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 585582904 1250 585581654 585581663
    0x70806121c03020d0608120415031a010509040f0f0606110a0804061110050109050f130c03060f06080609030c0f0f0d03090c05030303130b0c0a0503131103060403080103 74
    0x8810305020400001c01c403809001c004500a22a4050388084000b034002d402111029a00e070000003498071010840311860140000340e040e0b0b030382d1030706480340c418452500d662002e050070905240e0801d2030030740080343c440314282041079407603954034001001021943d07a458561403801001c5402402660b00010550380316403151800c070407407034064550307a14000500902c101810001400010f20400420003449080300845800a0001e1420030998509130024101300307595070100146000f0a40712550090b41c12000503402d02e45c29221540041c0d15400054a00e0352070b0515221001481e80c41307500200300301410b64419040c40d40c4c4607130f125031041111001d94403d0004c8252894000f04000d6002140500100341d160750358a41500500b03001c001c26160f07030b10009000203a50318140000d520801c583300c101401e4a01c0d9103010400b010024100c42c84d841710910111300e00c2d40e0441c0c05c40f60003070103204902142c1c2d00540707017481007294401c0241f5018000d5100b44000c05170042d05450599204 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 585584154 1250 585582904 585582919
    0xc06090c051011030304110a0e090303091c02100b0604080102272713080a080603100605030a0605040c03050a0308090f1207030507141906050f06010905130f05070806 73
    0x1030b00040b1000302c000310b0515440d400030800304000900c2c4000a40003a8806090301103142c0d03031420000156a0200d400d005140c000204105418000380805240384590f0602c00c44000604c0000940e50136420b140d039000c1c65554041040d050b9122020740380184080b030025523a804004000d00d00c00012000c0607150b039130342d4503e611301c6464403c41111035841c841342e45400c540034980c2c0700849070308084d1550000c030144501190200d0b0382c00c00102040c05d101d0700c800c0b0403424008281032a02c1003018101880b80d1410200740038a0781c000c244142a0f50304403e000c209500d4504202000800c503a00003800d80c07240c00b40c000d0806400c4442a48900c10034070660780d50601c003685958035584000f03484080d00c0720401072580000d0295004d0300f0303503074040c508115640502c00a45407505008141440d480d06ca800b10341020042709020345603005800e0a04011503040c40700018100c100f40740103051107082c1694980c0c1c6160b80a03400700403090b600a17010301c807504100401070f082c003800707540c003034040ca40 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 585585404 1250 585584154 585584179
    0x22505010311030912030a0e030d0903120c120905160e01051c030e06030c0d0527300c03070f020f03060601080705090316090204080708060c09100c06090c05 69
    0x31801d040c3d070310075040d40001d0120003540d44401401944020302c50a8915500e1865400c48041000a801d904611036400200b04107507090140140c40c2045181e1303600c500344250600025489005200c24036546840840c0d034003110b01d04a41445188501d02041ba090707404000303030201e0520a01412544140e45c0703042080c1140002d880400b502c10000340100d8000e601e40446c2d8240080115407140d0110b200ea0b09104209540409851081e206c00442c4c0300d84c0583c000040661442100c210444a00100340d945001c805021100101070b00d04484200000940b8400110000c2110b404801384016a40e503000946085041d2602880040c0d000c0c1540b03002500550a0004090340a110140c4078203d150b940c5ca0000c84007a4400340764160140104840c1007150318103007880303401a1001c1e00c00561030b5424402c03030b01d1074840c440d030166907142d00201c00e105000d5804001c96500080a8038040c4600045110a440541340301800030186440c29515400313004000c2c64100503902e04540c418105103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 585586654 1250 585585404 585585431
    0x80901080c04031106030a090203011d100902030705100c0b01060807020d1b0f11030a050a1a100b130b0316090e151e03160e09030403210225050103 65
    0x22800002c10381c0780c4c010b40d001c0326850014003440d80310300c01c1c10703000ca00c1c0541a8082400c0d075260100301440c0c003c1c17840c08000d4036501070041ea81c1c84030200c2d4080000c4421500000e41d1388c1a0341c0f15082c0104161201c0428981c860210100481c0d000300d003840340c80d6900c1400405060040300d0200040c0541c0c00486441841400384c0302c1b000407034407030050b94841c1c69181e40c841082d0b0404100c1d042054506006010380b800c0c80082101805107002d130420005c94200107508031030307882d0304044928042c0100490080c3ca05021415100380940003603e868075842140f280282e15002040d9040e004010048003104070b14504070140070a0f50361110036a0b94030b040214a110a540d440040c44000c00c840c2090304000e448000f540440f0116840000c01410119040a460109028000000345000e1080d260301c43d4600350402a1403004520b00b138610f442d0301006442c40311464001d82c181c02c07050145180f0801986600000c510143c15609410034200d06a1001500c2160301103820801d0b0f01c16141d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 585587904 1250 585586654 585586657
    0x41101090308040e090a1e031701050d1e02040908091002010b010f0f02100908070b15060a030c021e0f1603080a21061d0108010207021f1407080901080c 67
    0x102e80c0080c40c142007504104d01880003c200030711040c03c601c40c1c4402a00030600780142d00d038002145ea1f071010410041401c00a102c41d410505600e2503013407950041110b07403691001b045d40076410107401e80d00701340c1642119024031801ca00203075002d0f0526641805024944005007240b000880d032410b516001d50383d040e4240d441540301607000c12140744580c1c215038081c03042c0c010aa8440d1054612901468802d1011111900d009440240c400320b048010030210480042d004a2140c1d0f180300311140981c0000c0c090b04c10201003000b05a00d03440c5015100b4000c00c03410001244007121030600b8014010361039910f01091707034489543d101e400f080541c1d194007124400d084e00e4100100e686841481135054030081329101600c100a41c440c00c106403090b40510a07500a003c030ba01704188202121300d9074516007001a00440b0340340e407040260400683d82c003001c41d2405c0e0300300000c4c40408100850181d91641030b0528624079420001101c408000c2c9040c01465411001d0f02e80e1282620f8840906406 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 585589154 1250 585587904 585587909
    0xc0405181c030c1d2709010b031510060c0206040302090f06090624210a0c03050a0614130e0a0501050103060c1b0809041d030a0e3a02100804110109 65
    0x2201444050401507080c0207203070a21180d00c03940c0c010400305c480d00c41291541c0f0125981902a59211851006450140881c3c19101140d01c100c0ca010f080c05070301c460800580e40711788814402d100a1b0301c0215154601540c00071600200102400d1503c0e4017489018142141e11074445c21910000500c40d280460401d020b030f8940c0d2450380d030b1b001e15000342000158001c40100006150b84207020045800140c2c1d85403164505260200f001c2644400140030340b00d0250464414905204060085802025508114980460307900024018035500c2c040200092506c0e594030380144814001071040541100307049038815039080080d03110581c003c88105091480390306036000f0085c19072020859007005031104000081002500a00c031810105050325101c00c0503045030000b15603052107179000058240c804509486010000c06400c04034603e00303038032000c00d4412070300d44401d0b00307102d10468071780300111a4003904c141481040900c001c0c103581d038200c40440f002a8500551502544220000f608 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 585590404 1250 585589154 585589187
    0x130203061207260708071203170721060801050a200f0f07110616031704231504061506030903050d0c1106070305100602030405030c0405181c030c 64
    0x20440300c808038010f2080030400d440560b482140d0f00801c03505801d00c1240014546001509803080c600d24024088040364956540d811410f60100059290084201514132030507030320304410b0b0a07040d401318000b0281500450182e6280030700b00405003480c1d601c07844024a03036003d0a03010718034000651449101d0010030000901c000d02c1120060415480949071052040145001012441d000b0034400d4104030207c5a04900c40c0041d0424942c002007010890402c03641c810f160791407d0b844048440c0b144a140700d00102d548201859404014060f0180c00607659682a50504060520f07030054903007104060780c0c0c075507540f90001d40c050080c82081112503041d125907080521418580c00100000c900e54802e00880180300310311214144040740c030803800d6490000301d90030302e60040a2000b4164101c0d00955000300814040c80e03400080540d01c1600454010625681d15010f0490043c241d1000b0002c1d449010900700d202804414001200381c516a420440c910345c1e180b044030038150441c1c0d4041c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 585591654 1250 585590404 585590429
    0xe060c090d050307050d02010c090e130b07090806181618090804051216050a0302012001061203020703050d030506060a03051f17071205030301180902130203061207 72
    0x1000c5082801c81500d000b8001e0043c1ca08016680e21058200300c803682e0000300603550f40042d20b40b419000855007003d440351445c01107140c500b10742039a4014644800c00742c81c0010301000030301d06600c00d1a00304041c2c02c101c02580c65606001000140100e1002d000040701c0c018800d001280710b90041889040f6254405071514808604800d20005c000340356003520705803000c000200305c540b69641c0000d12404c511000f015449001017003200ca19050381c000c14408c620444041015030f03071207550588030100c06440140039000380e5114078010040d40c0c0c451b4210740600d01000081c1600401c2c81c10407a40941c003610005603441004404a8a08644003a8855030038413985d100d41c0e100380c3c059580030070310003120403007200314100c040b00d03824003680042042040400c81185090050058400600c006651031080b42e4440d51025142e00050007121000601300d044040d141ea00c94020740c10031600030709200d18100780d07944c0c44030207984200c90140c004c4800a00c82c4c0d200040014812085616100416 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 585592904 1250 585591654 585591667
    0x61a030411061603201b0f04060312020d03050a0b01050703110c1201060614070c0501140904060603050a0e070803040501180b030906010501021204030b01060c150515040e060c 77
    0x40c10418003055038140c0002e000e00c07a020b078640c0c2c10b410510000703020b0380722002c00020407a00f21a640d000300304c424181b03030440c01d840c0c80004614500207001c80720407250200c040000c2c0000c64020416640058040010480c01da0803250b00883c000ca0102055602801103980e5205403206850309a00541d0009404211040100e8850070015085420f10410740b04c0103a14000041c4242c0200001d03180541d554200801130035400000e09000156442d41c2c103402e02c400e83d01e030500c2890091007060b0603c0113400d00030040410a0b0b04550070f988000700200400ea89410000740100b004458400d07803a440c00204c40d204540020700041100c05000043d032401e4205001190100d103903040c1901603108102010880c503440300b01451144403110020300681d850800020b00c1e040350909481d4403500d00b08030600105070003603a0141941d81c81d042400034900c41e0701d0071040382c00428818600491030502488002461181d0010705914122001e0011007030003058981c8034142503480e000d5848040040c07 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 585594154 1250 585592904 585592913
    0x40f151409040b2a0405010210090c140d050303090a03090602030324060f0f0d0b090405060a090305071a010e0109020c0309101112280c060b03032101030501061a0304 73
    0x1c05901c282e0300140c406500c0c191014100e141d501c1244c0940700c15001180c14000ba5a040202014140140909010000e02915000a03103103583c0030300f050410240025145503103035024034448640e031000c00c4a68a14000940d1622118200c1084002801101c2c00141d00c43c800020340740142d85c01000340c0000d0041031181c5104580803e48507420641c1845908001c0c6ca036500070f0b141ca2141e0252702543c07042c1c0304400c142115540400a4411100f82050002060780060040c1c0d01482613513001519407081d090903a02c80c00307a40c800521040840d10220701d40c400c80317a507190403185480d0b60242c039a620380f07045005a0042c0c60004240f5030050210807001c5c6000511107401e809107060540c7c3c0545220001c1c2e050821505001c0d0080038002840d840f5804a0201e08540820b80b80d0b005008081c1146c005202c40c1300c18034050300694468513158500c3c0d405008031a81741c0c240240c2c52020010142da40c80003c182444140d91551801c0d10025186142d020008420280810036915503500c5982c0c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 585595404 1250 585594154 585594173
    0xb0405060a0e070f0320040311090103120302030702101d010501170a020d140f060f060102120928081f090c0b0d0f0f0506030d0c030807050706020702040f15140904 72
    0x8851301055240e0505140c150804c500340000001502000c0340d0361425414006440381c98031403564010300c480c41c010000700e030701140c00b4500483c541c9009a50b94035046ca0482c0f0b8911240904032a65103408404128901014a000a019100b800078401e43c1ea2301c4440a8070040e030b0519491141d00199540001840c01044404100e0311030138010385030044010f00310b85440c41091075104150300c04001d0010003401c01328210f41c00300702480100260708112078020315500641007003d002b003141d290034102e440c0b080d071021030420001042c6400201c4ea6184100e032780d0182c40249503442042c0f0b01c02005009628080c505085410442c0f01e60200e140038100200c5034411100786c05255680c0c0c9401d4440c81d002d00071101a03001c104804189402d25104250030444908004400d0043c41580e010000b60800151a8484c1841c01d1403511040d07030341051000b034810400700035401340c80c000d138480111280b43d00803107118181100c0d0303000d0962104002e002407540c0c5101e03a984014101c002400040035080e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 585596654 1250 585595404 585595427
    0x6140906090705040b0a030908032a0408030a0305150d0503040f061b0b040203030d020301031b05120d05130e09070303030b060708030606090109080604030e03010c030612020d0212030d0b0405060a0e07 88
    0x80d0004203112039482d41e000f260000e84a28820381e00c0152141141c10341c102f00c01c0c0300110b0304043c0038513061800d4607650741d9103e200c02c032005140d1104002400c115030180202030300750001d460522850100e24000d61030764407502846240d1200c1120220f030a5200341240c02141c05084a84c0c080d407d05906c80060880c4003d004a078503110800c0b4800403030f042c0d80090350003580b18a65408024428041001e0100d4803a00300d58000c101e0001380030016000065078040d001118104260383e420b06904010303520905400011130801d01c1c0050201c1c0100004030303501228000d5a04100030440306040092901c80c03500041e000410600c042001e41c039102d00108641e40050401d1103900d6594202c8505102c011a0f09a0100301c031202c1103000e5007070a004441e0103d01030320b810001c1c00e0402d49465902e446991029024903c0324105504540328600643c400b400d5041c11a5120802804c040d4060284400c2d940e00850416001c1245402d009060000760f4020500d481419512200e04548504101 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 585597904 1250 585596654 585596657
    0xb0d0b07090f082d0a2004050601030e030a030b120708031314090c030a090b010303020a030201050c04080a11120624030a11060c1005130615060806060c010b0406140906090705040b0a 80
    0x182c0245000904100c0c0d803151b204241001403461840060800c01265070080c6280d0606080039140c0040c0440401110f00b03070394403414006214011346012482c20704030040104003a2080701404205680e000001c0d150780740c001c9100a494039210802c42d03014020300c030a6242c0088240b40810114086903018650004254000080d91301c4940c4420385058800e030b000b41c000d604404c82080605a080c02a142d01046c0030a03801c2c541807501034aa5503d007107102d005401011644403076003480da5500345600014520b8421036403941490540c14a500004007504000c0c21020802c0e00034500300410307100c61030b03a04030079603220381990300c020f0081d190322000681200d802024a6000381c00f6183c41136502604408022134450515843c05408640d440c000701400500c0e903120400c4616031228030035900c07000a954043e1648a40800c9901500c641d04c00d03507910501305400881c0114115204200041040310600d4450b10b0f00018400c0040c8165038242c00100108424007801d8040c90007402c004c01c59 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 585599154 1250 585597904 585597913
    0x3140a1103040b090103051003120507030e060304120206090d0503060913050a0320060f0103140703050105010e0a1a0a0504020f070204060905100f0b09040b0d0b07090f082d 76
    0xa0340300e5504503401904039030100c0c8004520f280c605c0d603041c0301f455030240d44101c10100070b030700355140c0c00e0650031140d04800801500240a404140c07241580001030311010b00007039280e003404e141411150300c1c0c204961006100e004001500c101000a8075010112191074451441d1100d200380000340701d00900d084403582007401040001601004401c650034040d40d524503542c15031400c07480c10500402e201c044070b0b82c0010244050742848602160450790300c4071890800d29070201619003000741591002d02107500c0c00000023428204160f4031391060101e500304000c126400c0080f80000c81c3c0c0840c166030070001d9a0401c0c81582400c1c0d00519019480d11491400e00300c4540c001005e03110311741c121070481ca44880074490001d000c80740700c1024002c0900c00890640c00c00d5049100c9019103c030540c03003152038030020403890300c074510b400c010150004a0030310340745071a00c406005850300e407144080a01d402d02d0300080b03060001c106080440080c800071110140200d40800d00f10503001d8006525009 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 585600404 1250 585599154 585599177
    0xb031e0103050c1c0305180d02121c0f0207051c140f0d08070c020d15240f030503120a090c061805040b01050d0f0b030a051b040b01080a0507030605090a02042103140a 73
    0x64145806c02e40c0b52b0003100500040146146a0001c1c10326440d90300240714951504d0700c0910b4010498506540054070040c0c5950021030f210711103d04140c40c064060301c840c0807003024080001c0b9145860450007070440b000702454080c100e070514030803908200001d1341540c1c12001494505220000c0314000e01541c1425543e8005403002c8a001c0c0704c8202c01410900d80c68a0100200ca07600c60013400540139a2a05e41d01d1501c5154403407040788140d00001030620001a0304010030b51010742816048030f40b6502c40f546514014100400015604040c4402c0c0c0d800011a8a05405449100d042c181e590b02d05100001070f03a800540112041041d0f181d4503050f560b00746031420845a170103a8043c078024500d40300e903402d4040c01103a140305443d01490601c49408690f9800494081d040300448400082a82d903030441240281a203820032580304001d60103104040e58640c000e001907800c05010801c9602001d145115104901c410007008a01c040007061040300440c8085c141359580390420080c41e10 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 585601654 1250 585600404 585600409
    0x6040306180803091608060c0a12060e0c031e0103080a0e060405040c0206010f1508070e031c030b0a0603090f0206160b0a0204090e0a020a0b031e0103050c1c0305180d02 74
    0x42007150900000d905c00150038543c0001c2c0300880000780412130103400701c0e043c252200c805611500303040c02c05100d4803085001220100d50f1004000707101d40448140a03040000c411a02d51380107580c01c180e403e1a1811003100c2080b04c25806040341d500c081c50364a45614410300790717007612229280d0795000d0014040050355450f42d018a103500c0f113980e4040e154560400c041d16074a241960004076881d8003c81c2c10580490300040e401c2c0e00721007942400c8404a480c580081d00c0d000719590200c4083c444058032800f100c1d05034105240500f01140c0385200a40c072280308808445400340041d0954540210f1315000d41425401490914028841c00c04455042d0711a8490000150784a680c034039400901000050300d14410340c02d4000f114006820406450b4002442c603a44034050031a00440001c0032905a1030107001e006035500e001c00c4625815a583c3c1829604c1d1284040c64074003c00c0e0071060f4004589141040300055941b544400c8d04000425141c1c203006165030401a801150207100580560f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 585602904 1250 585601654 585601657
    0x503030a0c12140301090615020a0f02241c0c170f04230a0c14130e07170a02030c061213240509151b0c03040504110a0815060403061808 60
    0xb01046d2038045403517454a84c901c2000c1c900010454110b400c40c04828000407141d40000b0707403807601251001010b4074120f2000107450140c13103076550701c034100040206081c013800e400f000040c1248501041080c00f5400143d40364412541d1091568401400080c3c0ea90200c2e008160002d000782d001c0c8580720803c0b6600c000c002c0a00d0002d118581c040300d1400d0406c07850035024000f400b10b070000d01a480043c580411800c00d40e42c400154596121034403054040c00c100444030007003a40030081517240c1e00000c55540c943d084048141d01a01a15004415900f08541142c5c004c1c80d01ca00c0703120700d541d100c60040101182000085030031040084821014800e802541900c40c0303018a00050242000840ea62626410280d40d0030003544513020400f902851062003046114000308039580c400c10444050309510954100540c810f1804000d9549042024060600d0080903141c00406440e03203180d01c80b007030b1120002c16070311480c100000e00000c1e00a4004000040ea10300c00725200a1556170f500803035 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 585604154 1250 585602904 585602909
    0x9060603080c0a110a0e06060702030c15070b0f1005060a0302130b1801140313030306053102090a09020c01020d241e03112e090503030a0c12140301 65
    0xd0351100341040d0a000e1107940c02c1524070000c8038000d0700c16181415250140c440100f04e08c1c46030790082440c9d0b05544060050520344423008119070801e80074140c0320340d900d0700060020380b80d00c80f8550006071251801c0b1001406001c02088142d1941d140c54100f00c0140c3c480d146141c1016000e2003070302c0c00c1d90200c0424801811a0450080e01c61100904003015200002c24060400c00050030104265155004503070300070302522510001c42401d41001d40140c040c95025035000801030900400781e030113040c030501e184c0e0001107010110740c2e079903030085051f0f000d09101e00d030b880a403103181000001840d46c010440f11920b00005414584117440540454001b011101c0c0d02c4043c402101c80c1d4444042c0c0c0300d00240c00c041005102070304088049114882c0395000080540702807002c0d042c12070b81c41500d1a80c5400c07900b42005500d45215100400003909201400c1c0030456064001c20540340100582c0c18404156407000007094854484150040c120189078007405600e481049580080300e005602 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 585605404 1250 585604154 585604177
    0x50a120207060f020a0b0a020306060408030c011b080118021c0507090801060501090f0b0307030905030c07080105010f03020d03180b0a0c0b060604120609030e04020d1a030706020c040906060308 85
    0xc80c0c41c103500a05105001141034045401c16417020b00007038800448150000442000140c0b01ea45100c04a1424072450f00710b094288070110f160b61600d8015004501c1000e01d410210100c080d481d182540d440d94280a0f4110030904014508289103183d400381540b411002c2c48424100080e00c2a80100c0c4c800740ca2002c00250000018841101c003405098014107080c41c00018007413400d420300090024034040c81c4108600000801c0015209400ca547c1c0785070814283d0341d0712010813604558030682c0307100c0c0c40840e50a1600005113410346801210031a9005049800c81c414165011640820b90410b00c80c100c0d10050000310713202e15000054079021507a070300d60718070400c180c0c00d00d42c901c05001850140b02c0c1c103042000b0310035048800c0c200c001c0140e0258001c16001071074542600c0005410300d449400c188040389103001070902e600030300c0701000c1c0240e900081481c820145600e448582c010000036a000341c180403250708055100000b4039010b02c0d400100c5507141e5846062aa204000011307 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 585606654 1250 585605404 585605413
    0x81308060a271502070209010b04030506010501031b0e0316081006050604061b05010f050c070b060301090224070609050d110f060402040504140d051917040b04050a1202 74
    0x40d82800d244501e02d11016500c50b12803050102e00501d820105054200410411003082001220320b001c0d01960017841e8020909080340da11641c00149035001031200b502c192154900000381c80d4080c4c8110400d02030030041551801000c210305680c0c2d02030340c0d40c540d40c040c81070051241040a11051a202601070303500a0050b4007601c04640058983d20f400c82442000104401c11500350444000380e088120085241900b502c203042030703401442c0c15040f01820740c1c144820041503c0a441c000c1c082140300b41400d1f202920790b00181800c80e501300e28000d41210030200e04c800003c2c01c100f4503110b01604003001614140b419540e0000f40c8071030b02011103995001c048005855600004800201e581132001050b0043c00480a03950755900508040d00943c2e441c40461f0034014901c5491100040d000201d178000303407800e240240326a0280601c43e510090021407a007000784240d00852880c3d00ca103002c0203468840b40c48802c00070300084e01c100c038a803040406031000508440d0b02601c4040080c3c0181 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 585607904 1250 585606654 585606661
    0x20d141b0102010c14160510060602070302100815090a060302030a110438010c080a08010303300b0f450a0e030f0c0307060605030c0907050708130806 66
    0x3a0039140e46110304c078113120144d00c0410890741c0c60002e40760090704401d4000700244541c14528100710810182c41c50a038101640070520b140c000403c2c200f200e2007503c00c1072884c00404070403200080192039005190941c46448221841d1001002d82c20480310340002500c01d90b0307580003915209808108491000072190312070000c0c9001d110305441d030f0014030007050110b101880c442a00e0508070180101106010880c00310340c0c0d100d030707910748002036010b0000303541e40300020b002600c0440d0920040b0006000b808a2584043d0ba241c91940d0741400603144810000241f000c14015201e401d0407140c1142c01400080625550700340c0c444019006901c0724000e01441d00194048a80020702c9141c10203908802c03400b1841803052410b03800488404009081e00c0500816030561168500d041114280410000c21710700700400144502807050380e0400403140d0740c805040e00c461400d0041c5620018120005031024000c400901ca000d1088050525003c0143c101d4503028142c0d4000210a40c00070f800c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 585609154 1250 585607904 585607907
    0x603060b0a0c02030c0316081504030507031b02060a0210060510020d080603010908070c14190509090a0b090106081621030903060204031208101521060902072d020d141b01 75
    0x810884a00c03272000c5091841c0075100541148036514005041000c110048011038a6003400001400d500814282d51401e01c5d10000b03698840f000c20800155183c0440080c052074004902904468141c0261000b0300e41214107894842000303040755055501c440304000060454401441c07894816200d0b91003c1f41080f201d02551103817204d5a902a01c612031368562540c44071200d0f501200d404440c43d01d6140d5900c4445c5c2d081c1021000002c041041c20004d000a00780c0c10741113031099400100c101c40242000315000c940c0442c1a00ca51207903001500c403c000c0324810390300500e00c954001e0501c0c00354965250f0f10b4004a1340310b5841500c80504000988000c5030b803000090b504035a010002c0704040703041840c0880102c2c080c1250100740310000f040c90003010102083c0e04c14440c00007204000080d600c040384c5010350303c181c3c0300b100d800011030001556009a881c0540c1c58584000711000c02034680e60901c4a881c18075001034544164a003041c01403150100054410201218a08886c28045400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 585610404 1250 585609154 585609163
    0xc010f06090629040b180306070305090c09060604150516081801030203041502180a14010801050307030b0a1d0303070e0406080a031710080f160603060b0a0c02030c031608 75
    0x7007500d03e14510b0082500090300721070a48054540c680300e038036600c15200350040d6a64600361000c0d0b42601031101004000c58241c1c1c0414400d208441c19103c1c946181020030055100403110320380e01c048144401d01003071b111011095141034103070412602c0d00d0010020450403003002e240841c1c20403000120100221100004d00c40000c00a0030254114180780e0f550034407442d4032004c2c10548581c04500f108001c80c0031094409281c03005050110003540b540d112520aa010440d070fa8045120400000780b9410b0001d01c00c03088a070810004645070301d615090b0710181a12440902a00d251120036042c9590180019030081525456000e031650404080c001990856030141a6030b40180c0840800300e40c0114045080d40c0320f50300c49440507aa0300100d51006107083d00303d144284614290081c0b03d400004401c0d840c1005d00301034440c0155550707400c40c1541c0160160001a032000e010309038010f405807052503044c504c01002d0311105044034000c01d150180c026000403400040c2c10040220032020311 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 585611510 1106 585610404 585610439
    0xe04050a060906080303090c0907120c0203071709030f0304061704020a080f0a031404060903140f030c010207150c0c03120e01050a0203070f0804170c010f060906 71
    0xb13110980d281c0040303491502601c68110300f42d07030340d142024100d4821301c51907aa8451110040425070068521a6281d00a40c8401c0c441703040040d1015540030300d00d596001c0301d50785560481d020586058249040b244954000f00700511416500c640320701d8412060071410001e507100c07407001c0f078010b1038182e200d0600c0e4040d010210074080400300b562481c00d0f001e03a640c101c40300c1114a040500e03100d14400c08020035940f0008000180600c0c00d45207141c01c820096400d0144e107490010b04580c02881006216540000c03110704011103801031003400890444201300f11011206d001e0101a04146c000e814442030329050024200d90790401d01d00d0502100081c0850b082c096249000383d0000d44810700800c001420300711505203c2c81d21180b1680d0451000d200c0301c0b0750490703001565480412001400d549030780942d6103194040c0a1400100183c0c80001400c9280c6071f03a9152103800740 = true := by decide +kernel

theorem cover : BRFrame.Cov 585431654 585611510 := by
  have h0 := BRFrame.cov_init 585431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 585431654 ≤ n) (h2 : n < 585611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
