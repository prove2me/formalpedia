-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2946
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:12:48.723191+00:00
-- url     : https://prove2.me/submissions/e5e45640-5ca8-4756-b888-3650d151a53c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 529676258 ≤ n < 529856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 529677508 1250 529676258 529676263
    0x170f0a0905340e16111b04060f030312050921042408180109020d1103010506040b030a11040905060106080405010f06050f01230c0d031a0609120a081201051002 70
    0x112070f600301010b042c2c1d6448021032203116244c8000e02c0240240204881c501140c244240e00103800314500da10640c2d0030003030030700040341d4841d0024680081c402c60280082600a80d542000c814100008a8642e079064469418040307006a545407800113100000703000c01080d0050829689c20701d14000006180c03031104809812086298804100c1140c0880c3e1401c410590b0442013018203c00410b1340801540405d111718940d000903650301c404501000f15034a0213000d0143c124008880c2072020046a10000e41c5540421030300401c50b0000c1c455000985d180e903000418603a40000558000c0c0d030f5283d201601041c4101c904507881d500c0c180c030283c050040f074460401504d0024103803031116002070f0015940d4144041c408001e80340442e00b62008040c600d001054110a84006081c10207640c030310140a071160102410b90314880b510703445120382c0381c040640c0d80b034043c229a8506454440242c00781032090010000d801140e000580180490f60781b80b4080c100c070030596680c14820303240031080340c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 529678758 1250 529677508 529677613
    0x603050c070f0b0414160302011e0906031e06080a050601150503060d080d0e1b06071716120207030b09060403090e0c0f2701170f0a0905 60
    0x14002481c8142d400c0c0424690604140d015110300c180402400e405401189009a60358440d103a48031075841c24003c40d6400311100c41200000a00c5520503455500c0282172028203010300410541d403941c81030400c2e41c00601000005121110800003142c071402d1168440f01c0c002401c3d9110312400c000041c03a1140c41c0910f410702e10041c4e460300e00b17540700c4000300500302d0051202a24006018008004003083d584555510001c10300d00400e94030488080503910404d0010f00c261054109026810104101e9000c01c5a0201c0c8504450b68036031110174000b078965038442000c1c1c049120031410030519900042d4000590340580c40d0000b43da6680d080c4c00360703104030445000700055140282007020b00e1540e104c041c0c011100d0a800c1e414041d8170715110405402140421403241199000d055180e260104c950710041d00a2911015411410842d0300008030040c1078581d05441d1000081ca044050760300440c500b0b640701d4261038106008080b000301c003034030741904400344940d066880700341c0794420b80802 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 529680008 1250 529678758 529678763
    0x40c21050d0c02060d0e061f080a11042414040504030f08042612070504050d0803040302100906200a022a09101406070201080114040f0f02040603050c07 67
    0x1000841e24504003181c54035442d140c2240c10610500415101c0802401100000c100200061280b4613004880b5100441c28500d250100382c9000c800b406070b1040481c010540c140c01c808601e04c0c20b01c01b1381c00308000b8000021a40d80c2042e40380484c16007400740440304411203c010001003a080141810082100d10503613000b00800da010044480490044404580c040d008540c00d95140c4401c02a52a8203099010303114400c0c0300000b40e90400d0326403202c000360081601c2c50603a090a040002040a005042101409100e404400142050300c20072000800c00711400f07040c0700c882220f1600c2c1010b0049600701c3c2072820a082e4980071010303441d400361250b200840c0d008281820030320b581d46440ea05090496950784405080b5100c4540715550500e028004210122200e9403401c203120302c0e4443e00e4907000340314020410203030340581c2e48408000d0558031040728070070500e00c0a02c001001084814821000d42d814070348403854080e8039030f001d03004440d42c51702c0510a564419464918510401900 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 529681258 1250 529680008 529680013
    0xe0d0c03030506150d0b0306100308040501080a060b04031406060405100b0903070506071a0705040e070e21010f0b09010509151504030507050a06021b1c0209040c2105 73
    0x4000210340310b50485604070344003410076440c09200044022a9500010701d02078400d40752442054642403c1003050b9100524075800c521a0b4110740d00d0103103600c51740c8103880c1004038050100d032100742180d00400042c0520408255265624a008124028142c1d881003e500502c40080da880c10b160244600c140c0d004001041c8460030441e280702940c1100070415054840c1e8103000c901521400300a01e004c501031654450f44000c400c0a01c40c210500070400d10400006020400011650040b85500041030307041141c0500400b6010031006048244850002c10001d011f2450084040d8030203030032a080d2481c10711145a0300c005000030b0600030b03c40c0700d42104041700080c520118001c1c4201920000903c01750f0441445145441127800540040d20640c0003544100494505464424002c1010340013500300d451001c0c0c204024503864803030b8107020b000c4801b212a00055030384a0f0641d0301e680101686040e0030a410100020503041c010448900c20b81c106001100700101c48001c4402d900200 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 529682508 1250 529681258 529681277
    0xc2307030c1e0512030c060f060301111e0d382b02040915060f0e07080a0504140106060512060a1505130f060f030b0f1005090d080c100e0d 61
    0x900c00300102130100141140024482022002c4003402454061113850281080e1802c2420800d800c44404103c450400f80c81040100c0e014117800401100013240305030859290940b0807010030107050b0960004507140c40034500c00e13161103890090b54001c0c02444001662082c1e6480500580f002a820720b420318004c500501055042c0c3d030305800140c00d10140c000b00d1030301d509560340d06192841200c0480c1d266122001407220000300304000006010382e8020002e02d05042c5005044914050580703441d8503118000103090081440c001c401c0c403818503008014091390f90b50000c02a800c11400715001d080c03910041500342c6031400114050301c50700c4038034804408500c00700780c40f44d600c02d141e240100c80c0300b24800618805521420002045907480b00085aa154503008088454401a127446210072056040d02030f116201c110510b02c02c5818665503520744c550015020091404004140b0b49001035285003541d0081124460300440d00703c140302c581c55260306661123110314001000020280311 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 529683758 1250 529682508 529682519
    0xe0103150e0a0204150518030307031d030f030d090b060d030503160c05010c0503072706030e010209060a0207181a0f0103020702030616110f0a030c2307030c1e 70
    0x1c520300e810102c201401440c003681c0305000c031304442c06034085002140c0c01152240c0559105940844406ca044024510b052802e55010300b1000a4130511028405481e60a02150328100220003041c4c4200003200d841d420b400341c1000141418203003c03518540c003030340480d646040124111031a01e5141e01c5007411950303003040075642001c05007691410049080f4000000c030300223100e0707000184056994507650b450034a03405803401c090503210070ba00159006202c00c4000c5034103d0001035503041c0c500402c10516242925029008080c142039024000141084a040d00010000e044400c1202421010a041104001101c10f09814080200c90f41001201d1503d4031001c10403100d80141001400d001940d00800c1c540074086980040300d40e0b41d909aa00c645420484201103036401e07100070180b270345c4a08016502c030480c400c4006c03340804011800108451810803115000c250b0214000c049407050500366140344503c01a07070520030518001c01e40450340001482c0001c007001c1b025402e6442c10 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 529685008 1250 529683758 529683779
    0x1080a0b0907030b0a0227030a06051003140106060f140702041107050d09140d020f0f060912060a0c050c060601211409301c050108030a0e010315 64
    0x8040390326602030300b0b5001c00002c1c02098542e0181102800c0162160444a061281d022503d9040f80072400c043c8100e0129640000303003c00040d078012030110701601d91503510202d44025400080c8821142400740c403415405501600446045585020030420600015a08110492030400706940f00304014009424207411000107940b030340c9829850101ea40d156582090101481c2c04001411107104003c0308001c40e0404009100448000f80001c280c5d50018511503145005039016044130500c1c2c50840c0c0da03100030b0300e8600d9000340040c1c0301e500b1203c400d1038841c0001c80350709007540d1030065000c61040c0700304203581035041c1000003031032241ca9240040d45c129055000c132108083c110308001010348514065035402c1c1540c01a049001d0420f42d00c40c604000700d017201886a410fa10300c400f40d002088008038a6201c0c0b4a40c241c4d42d8650710824801000400301206048070b90800c400043d0315a0000000c2c8200c8400c2d603a074100002c411401141507500603040100c25241d6808240411002c6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 529686258 1250 529685008 529685011
    0x90f010918080304030c03080106050901050d0f09020616060c0311070b061f170c0a140304060212100617040b060111030c0d0806130e0a061e050f0603010e0601080a0b 73
    0x80c0c141001200710580d541c008941c0f0440c0c0440024400c043c01d08201038100b41b00c10f0140806040c503908101208000034a00e01505030440314031601ca000c1c1d074000d128190b0110001e15000b900c00c4d42d540d400311400e4010072040c00d0341100c0441c03a05100c4e04501344a88522100560340050703262a00700c164665401c0302ca0080c0401d0780c0008201c000c0d42e9007000780000642d10f0130b02a11190f044100c10300340031044580041103040500000c02007805840c1c3e010318118810304143c40015280c0c0c41e2410804005d01403034010300c0c044841d000038040d042441211400481d0340c41c0e641d0203000079060050800d080c3c0c00f510010002e81007480410050360041d17401e80035440015040701e0418010804907403a110300e64584d040400c1070034003804400c0c10b02e100c0c100e80c000034500b400d00131a429140384a6035410751a00103440c1c190b58005456070300c49002141e6000d050440c10502060a00c800040955a07090760503d110750700e800c150030614400400e00c98122880c00c0f000d44080e014a0321500e056010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 529687508 1250 529686258 529686281
    0x304092408100f14040b060321031609080703050303060a08012d0b04090c030209060d0f11040204081606120e061504060803031608060a05060306010c050f070b0d050105090f0109 78
    0x1100c00c44070b900c4c0e801c400103452156010f20480d004508103182410b0820400b000301c003c1000410030040c0840081c071040381d41040c00040134250050b0130070412074200007603400c400514090b016000042c0000080a94022201241d058201c1da43d1034841c0d600329117400310b02665809515140a1007421245405405074102380004034004030640f0015049440c1d403182101c903a02c0c6c0000500c1541407581038254825010364003281080410b4403008000c00c5001340042074044182c1c2035221035120b42d01510014460501203400540542c0812030000324140101030000345c4120101002030404e01407040320019050203490a600da8503112800103054000403500213071101d00004018100704000c500c180d100c40340da54499201018018401e005c013901c81841480744103800d22150b82c03510100d0b0f41208007420f00a0021400d40f90035802c041104500400da0f0284030030018030788140c40000c110f0104106d90400c441da0301d03003040002e070305419501018400015401409220b41503806820040c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 529688758 1250 529687508 529687511
    0xd020103021b0c101e080c131d10050a030b06150a02010903020d0f050d110c030c03040f05100509130f0c020307051005130f0302071505090301050f01061e0c050304092408100f 77
    0xf0441180c6070280b8040d4000000d070340c2142c82c401180d0440292907500100c100c030110121500e05000600340362814003023b008500040d001c5555a130b05c242c0803141c01e44210415940702c5d514018042e00900e0214001c0c5c0c058000d51108000c46407180c451030001910680385c0364200152801b042c0e00600c0740554091450400b0005404039500800141141c160000c3c011652282000418102c84000340e020724040e0070307e00400701016130028241d80c1441d07810b840540180c116280a074001e4015a80128181b51600072102103440d4044001c00361103006804644c0c0720300440005208a43d800c94600c5c07940095946200300064280d4010350381180684100c450683d260380f01207081d0b810f0740800c180030900c00a03400f9541d0500f03020b59540004403400233043c96240a0000d00b504c21502da1084410715200c5060701c10b5030150040031038081d00f080841e0b1b11562104042d030010b142d01603040b00702088104c140611180400031850a07a143d0340041c00d621281d008402c0068540f9208040407107 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 529690008 1250 529688758 529688767
    0x90507120f0f05030c07060509010203030112031b03020d030e150c030403090e0123040b0a031515140f0907020c04050a18050a021201090804050d020103021b0c101e080c 74
    0x30300c120b0803462600c1d018002660740c07060386404051501039594841c03814400144261702e440e070707008000c4c1c80c11908544014801d0304902c1c64100c3c0c103034041c442071102400c00035409500740340e03000481030500001c0d91000c00080e090518190f40d244003000000000b14090400160f140301401c01868000e8031a040040545807507140484258009811030200c0440c030702c800000c0703505032900000c040c000c01e40302003000125a80101ea1001d01500018203041d206440d60120400164055200e0001039080f44400546404091015202c1180301e40d1044d60368504040080c5011104075000c1e49040d0020204003c021703007031002409000f0801000c00340d80300c40c01d42205d0360a40c24403000c2c0d44500064050011144100601c20070300846042c65a032401c00300000042a40c801c9500385c41003100c0100c41d002ea940700480c081e210b00d000600b0344c98500d01c1c1130620004005501d24600c03000f2500140001400fa40c21100e5660701010520980d15070b182c040b042d940140503054100e0a0100b006190 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 529691258 1250 529690008 529690013
    0xb1e070f05030a080f01090c120c050d0e0105100801050603061308160f02040f02090d020402070203070308040e011404110a11010b0909031309150302120a0b0f061003090507120f 78
    0x11070f00050700b2400442d5282e02003200149460a1803805840056003c1110a4900c44001d0459031899029900303a80c1e105400300c1002c4c00350741030722082018ac42c0300b4003143c2d2410482d00d02a200a80f01c101c4034008403440400c808106000f2244280d20190061a080e541c19051000c1e08400704400d461000c020004800d4485880600760f07000380c02902050b048016520510080b03440000090020318410300104106548a070310360810a41c046501507101c40b0540002030410041e544020030109001400040050b5614485070486e12041402d040380501c50045c40161002e859000070071110412a03000038070f003e66911100c0100c1c4d1000051200214030229640c10404d44e2060010f1380040303003140074011004011000307050300480500072558560b00680d9550540d0100030b2040c001410110542c4504002020328590000010b4143d4140f22003031018205d0142d0f103290007820310b09400d00125000340900320190307a128000b031007911b24201600d200c8030000d100894001041c81c210401 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 529692508 1250 529691258 529691263
    0x51614071401060303200f34060804051e0703150914030903010f1407110f010c202e1d0304090c0906021506130c0306050103060b1e070f05 61
    0x107184284c0781c9401da8119a03d0000441003402c042c10303581d070f002c00780f2140300800c00300d1102c02032238141d1900c4918440687c00c00861003400c031640b44140d4405180000c0183d44180054062402501541d643c400449144980000304a420344143d0340710074020000a4240b400c40c00580450001c00114541140e07210402014455a81510b0764808604151689030a12074201c1844901c0c1040199401000982005040060903c41400359040503110341c05001c2c030503c20071400300030080144462080000d4100104103c1070940301d101048a0045208006610050b550031118054107031944506e82c881c1b580076034540301c120141c81d4100498181f090350345106500023030501441e00c460801c05000c0464a0038240c050800445100030810640c011850031803202c2c0100380a07401c3d58605000c20304820f48a91005400c902d0a0301e040e5a55905600c6102920000d1b038007442203641d10100ca4441d402039032415600ca030010f961580c1210445001055100d1091000d14010900b82e1121030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 529693758 1250 529692508 529692521
    0x20010e01090309050307120204020c0304080a0c08010c03020c031e300609070503070e040603020907050703022104120c050603011806060206040c05090912040f09051614071401 77
    0x140580d16040e00c10101030708111114044c00d401e90013402d009103000300c40350003165030304806401130798001000112140b0900443d005010b01104880014129141507081d803540740c400d406941d442e040b041e220306071290003169038003e45400114209424011040e9241c0140c03601c05901e0314003002010031b40880c80d000d90070607074640312041e1581401841d11031a00d2070b0061081d032088000d002040071841d003000170380342c10581510307144007404164000300e07004242a8102030760021100040044035130340b20f802000224425400d070b0b0515041200c038500c00d801011041001c203101400305014000030041410b031014060759001105036503400200705103a0080e040004040710903082d81d1280b694501403003004000a10041a20345000c1e101c00000220302d008040c4940109030214117400d07c20000e0742507244210701001c0d526560380781043e041c82203610440046508042c00210144100707800b101c1d2010f02d5403503a40d13200e41d41b000440c182d076002d00c4080701c01c2d024240c40c03070340b006030244180d1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 529695008 1250 529693758 529693781
    0xf020715030b120a020901061d06030109050403030f0507050409020d02160606063e100e031b03030c030a0b03030c0f070518040c090b060f031e010f0f062001 69
    0x41e0b8035541000d10405145003e01110300c0c0e4415130700304005845034031a0030304441442c0751107100e003100c0c0003c5116030794234140704540c806d001000210b0305992691005014a02c640c60800000d4100d24550b07094920840f40e480104400344020040c0c040107400402e20b800300c0820040c60606840c40d03070709a1050398134056030b2240d9a56824445141c0004602140140170b00e00115201000d1900f50f803442400b4245808188028540400003802041032510703101c1c1e69034045c08544400a6040c0e901d8122544120403914a450010341141c00030088034000c1c40960315842c6160b407105c400902919030104002d030148402c02426244007401c0c41001050344090300640301c3c2a1902c010850b903206507008a02d040324088080c04006070302c48000c0e000f142d0b01d00001080d405622000100d0034050395040e85d40a400010410003106001d400c0f8000030104001d15400c02d90b2154045c0130b0703807080b034003800700b982d080c80c031040c890b090040c021142e13408100145c1601b4012003010301400e40d140e02181 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 529696258 1250 529695008 529695011
    0x151c090f0c0803041a0901030605180f010f0b03041101020a050d1d300c041a09090102090a03060e1c0503070f0e01090608130203060f0415020310060f02071503 70
    0x30301040115100c904001000004002d40c01c1c28245041c0031080c07800c500030318606400c002440d08032640250015402418002c0ca080010386445204128200c000c542d0146c1080c8410008201c0340703551056801658500444682540d46030f0340ca000b00b261401110074194452a0000c3d000a0f508000b01c461144181e0388110411000858981c4890b102c410614410907010700410100400c80c031450300c0180505007074140010a00281c2820451445621500705080c039000c64000804301100e22004041540c0004943e6500c0000380d00700c3c05058000780c0d002070040700c108003003045600705c280c0f2a036440d404d54850645180703c1e46810130140d0b242c1d001140000c010045002d80186000009903001e040100d100340300307640005c12000c261b014803002d01a011020484591015210140c0e05038060219002d1341842002c2c10b64581088604459600c800e00000340746003554001d0b84e000d9842084805c0c42d150034040103035204101c00800b10308501c200c0d1400588800e0b000d083e40110701d082d890 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 529697508 1250 529696258 529696283
    0x201030e1501180f05040b060d11120c010e040501050d15020904020711010f1e200a05070305071403101d060103030e010f020f0c1203040f0305010f0515151c09 70
    0x202c030002c2c2e4244084c60440b403441c140402010a000d561150740c000c60494082c00500c0c5c5618100d103e5a100718100390704101030f0031706560502400601c415103400262145005e0426410820068a009004484c0c01052811303251000500c03000d00080031000d00c81d000340c103040e00500802c049800001040d02c650070401e130345071032558000046150f0b4043d140360a40700d645000c20002520700701711001c4010004c1144081d140080280c0a15009600702e500341e030340c820302078184556655402c1c042a685401400d000140e060517005010a80401c040c3c0501031038086003c0400040110b03503030240b03001c1d40c1201d04072100340c0e080c0941406036100c0e0711507031041c40d41e2500040c0000060720503034045d036101c40113945015800103954120968101c400d0b50b00c60808280c958110300499021044071080743e0404401c01006400240d2004c8a400007040183c3d2655800e031080d007012000941c100200e044110400c0e008203005000b40307d007150040542c0040044160106c0c1d074030b00000e4075010344110 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 529698758 1250 529697508 529697549
    0x51c050a061401020c280315060f210618050d110c01050706050403110307030203030603160311130b15070b070c02011b051e0c010905010207060c0201030e1501 70
    0x4642400b9101d141046100c26400384000f07940e4002c404a080d02c510383c0141102c5c0d03142c4405514400340858071100c0003840c1e5403840d0240c043e480030000c1024040c20f20f600070600308280d100220449026603181e500d140b005d001c400c0520041d214080d04c43c69140d40305075100304101c0440141c164440c0004000d20700002c840104124510038000310240c00c906242c02d0144e0340102910082a009240018642c9551805441000410303800c512540000f04610703080c90340220245100e018160107859010045600b40019170034140402006099080c02070340103810194241a140c0d03581601c00030f24141e101c1d000035080c852440746143c2d0110001342080030041d400c11482d0704040179042541c0c6d50b5103564006446500c82f40148188070016030181002d001e4200b2000030401d0119103a10921000c442959494a41c03019119000c1001e4840005440d4070010f000001c03294680e580c0c414240c0c180e401107024182d4000044850710a0ba40410380c5810f000c0c40480c020700301800701551304000e21 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 529700008 1250 529698758 529698761
    0x1060506030c0c280602030604021905040905010e010e0c030901110f1309061401050c03190905010e01080106021e120406030902120a11011101020d050c3610051c050a 73
    0x401c0c4002c0412000380b055022a610300008103003c2e540309030091f8403075883e00c1c041402070003018914552721520090302c606141e045001070058880d0700c1820302107681c0750b00003001c86450a1061508518040000138140030240b0301550304800302d90008125200491491480ca4104401c5803914010005d0b2614451035a603010314010071160303038140a42442c0550038071a0a00440c82e07030341072000000724404980300500031200d200c2034444a120719000c481c10010a0800305024450201d044d0040e0860a503009040385412243c032a401021000d10312044109030820280140d20544170b94114221004084e20140000d05080e540010b010402e5004000d040700c56500c0d0410030b900708900f190089255600c40b440803c6003800c000d80a0001200b12600a10038401d1944e15940b80205101c0199074090007440300e4144040c406500224402a20381814240000002a02c5101841d00c686040010140c00785070854141141000801050301d02d2440d100d9000c1413120781c1c0d820420980004c0e5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 529701258 1250 529700008 529700023
    0x902030136020f04090f0204090b0405040b070e01020a1415060105040803090114070b180f2b051306080709061e11070b0a030e0c0111070b0c01060506030c0c 69
    0x1a2190030700710038080000c00c518004440454100c140c0010f003042e41c1c40c0d00c2100701c4004000362030301007207100e0114103020300a401c180586503406003821203440c01c500e09800b990b4000c03a08a2505450f07a20350803800d544d50b29070006800e0643c061340e40303890046400054140d4448640d080034200c44440d005903c080b8050082100381031010034481801100c5001098891019003030800030700c6201c400005c1603540c06a2900203101d002341404000116120902076030210b4140411110b129401c880c0d0242c4444120502c0114503d002e40040d403880c28840c2d89419454541c03c01924003441c40004004a000c00e03005080841c85110501202c02c1d4002a02e00041c101072402c450bd0211601644601c4c0140c5070700b803010415000300744e24002d60700344001c4004000700d40fa00d603075032927112502502400c14094004194003691101a03115402000441c4441d00c030b40000d0440c5506100640300140c1014840c130140d59621140800c043d10740d0401140200004401d1540303e2540698261030b02d00c8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 529702508 1250 529701258 529701299
    0x7080c01020f120a09030f03050903010b01230d0e0604121b11090636060d0206030103170705010507270819060e030f03091b210a020a09020301 63
    0x400042c55071900700200d441c03070102c41d18501ca6581c1c3c0c074264a0840e80e484440d04083d0a285894140b0420960018003e00c150a003e5009000c060350043c0156429058600311480b8066100074840614440310b00078100c4003c010800154560002c95441c40c0175001c480484101d000f42d000e03490540d400c0b1821004c43e1070380f045a11800044ea5036400032141c036089403203000e5607030030020494950f208030041c901e111000040c001014151300c000d81c100800800070724041e00d500d201041030742c140605008003007034016114516507443c0d60f6421421003804020007110002c203101100001781c2c2805083e000d10201d56401e101080d580341d89241408182d00a0350039032039190001c12040c0b90100b44032100030a40310382000036812906042e0054414040346050302d000018000c458562810080d50140c0c40d00320403520790401e84035649803030b0000203100036480202d02d1580e44941e43d400704106081581441a1043c206240e400300302650541d80058991640200050100c15100180d0104440 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 529703758 1250 529702508 529702513
    0xf020403291e061225120209010b0f0d021207170403090e091f050709120c03021504150f030e0a02150f16061b030c170613090507080c0102 61
    0x2c0c5518080c20961981c2001550292480000b465503500e902001120444180684200646440094074042c10804041455880c2a080070035240100c1d13101c0e03820315601502035421a420405050115005109100800c0100300403820329020b25001900240c8591a00d01380181070907203000d009144485500d82141c0c2c010b030100004a944071114101300d490b03c14580841d40c6031924201c0c20f0400b6a003079005030880c140e943c0515038500e40d2010b48074034203607600c40105585804182500640380341d8007a02c012010b0750180007610708403c45951098440a03020301d80b079a11000c000300c0304040c84041c2d0224800d00580d00c0180e80501074421603242650160401568a80c00203040c09070b4094000d00001000c5410900c062409089585100644c04416983c108915001d00640285101c491111090000f80c0d80c001c0c0c001c0c01442600703a4203840720180c90440d013a00c185d8020004104a078068005803481b042c0080510906944034001d0003d0480d4a0401501131b00d401ca8020b039090455 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 529705008 1250 529703758 529703761
    0xc0c0803270d084005070b0f0a12021630140c01090c0801051f0807090b040905060c03010303031410140f0901180b03030309030a0804030e10080a050a0903091401030f02040329 77
    0x602542100c0c680501c0780ad102510948600c1d001009005e00c8214070511a0601001c4003841240004000c8030350014500282c84070700700c00240350100d0122150350104214103500d05400c00c03248041e00303180d06000000240c500c42520f0318180725619a0102c0c4017a5555030510403040410b11040c00040d11005100302001e103440007c0b07035900050301c81c01c9011a5030b44ca404d402c641c0c80d50046142180c202d41150070710b04050020712101d40c0288022000700389440344e4001c44500c0c40241328402c0c07140404080f2094038113040b180929000c05603050b8040707005c0d14409081c2d6a110117150181c400103200480b088003010045049980300308402d0710a5206108019140c080042110403514140c600031200380c0702d80ca8280d80382003280c00ba07560b0000700c0d540350b05016a485624103219078500c040600236031b1100035a03170f41140d642802c068002800f2000c10310103641007003d81102d070007042c5000140b000203030300d401d400c81e00641c02c11940a0300c0500d121401040c1021105091f030302050248106 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 529706258 1250 529705008 529705027
    0x40506040911060f130b0405011206050f1201020c10021309050105030607110f0a06151502150907050603040f02010e03070f0302040c0c0803270d084005070b 69
    0x481d2001941c051003840e00003404c14500b40548181c500440c010056000c02da600c0d10140d800701e0b04540541c50014a503034004200000950190710b0840e900a0068544130240e001403101c6080642000207656400b00a80b10380d00702d040056041c0d14107002c5006807540a5102c181d00e01c005194010b21802d8104030040c4007c0e500424840d410281030700381142c80e55a0341c4802420584203001444481c00383c40310041c148081034020310101001c400d00c4002c02a1984820100c83c018400c4a0780164421030450408042c0901d034070350072084c0e4204071441c0035075950000d10381e40e01c111411907054034022028011940c0040d044c4407607336070444c0507051090901c05071610b82c29a03440040c0c03045440342e84c0000268012440341c83c086170055202c56070791801c15028110101d1550f00c6040c001d6450a01c01c410307610204000300780c2149642c1d0548580c0b01c1e6003034104024800b6410741c940041824100c00c030542036172a800c4020001e010303462100521810110305204455001201e44541006404030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 529707508 1250 529706258 529706273
    0x105061f023307030501030213020c1b030c0307060c0501060e0610140f120f010b0f09010305040c120302100f05040305040501031505130608010506100f0c0813140405060409 76
    0x82d071281070304450001151100011010420310ba404031091440100b0b00c0744103075058005038140e038000c0e01c0345500e2003240b82c00c1c030040b441030008505035500080052980d042c21082c07840d5600800408860203c2c0b540c1d00000c0c200381d41a442103001c200d00360707560030401c482130103113800400c51541c10f2286407070007001040164540b04a01001c000750140810740e1141c00505031001090508191502c1c2c0b001d00c5640e0164200665a40030b0104102d0000200c1701040f004035040d64401c84110360603e1901340040d00640350141c4220f50000c0401c8000c0b608505d00141c62904038040e5004006440d40340440d42c0481d08160780000041e800d0504010101e5000402c079011070b2130078a070020b966900c01c0c0038000415401c0e0015a4041039040300060185100e405c80b106991041000b00b1071910cd05082103854201900120049400424851011806203404201940c01441e2091520320488072030f0206194a42015150080b6400e0b0350b4078904081c81490350141c0241c81c00c100c0941203844848 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 529708758 1250 529707508 529707523
    0x1113090b09250201090b0f0619180f0b0402070b0403080906131202012a1103090d141002070503040e01140d061d010908070b0f19020703030207050d020105061f02 71
    0x10524400d20030038850b90300c03d50140028580051b558151747c10403100c016007044064841c988101400c81c0c84078480640f404601c01100c81a003a104001842e01104501510020030b8011519a8070003100000e0749840c001060041e11940c10314440c0c1c50310f4a4007401c4860050100001e0398000410005c3d58114010b9a418650301325283e11600741040201328058400c2102040070707501d6020704860103480610140c0781b0900300761134540012503001c0126a07680200308004ea4040281d40b0210302280014044410103402c44007682c1c00d0f90791075072001e0166070040b041200e0341c1c0e100040070007485a84d94400ba000d004a1030300311040075070140010341c4141501201512440c3e0307601800c3d141844045120092401540080c40005003c0c100081d0942201a042d01c41ca0301e000001940c50301e40d404043e03c9884809540140e02c01c9280c420f00094200078412024181d08000c0c140118108114640c107241031603001149619200050000b03442034181107000352181b07400440620394021038a01d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 529710008 1250 529708758 529708801
    0xf0907080a03050331060e0114060f0117070503100905090a030305150a030b0103050c040b0d1e0b09010203090106080c0105121506070819050403080702131113090b09 73
    0xb6890303403900c080807142174010750504c888048414900122803560b405020400f0b03401018100040c1c0003c6041034280c03480712581ca01110303920300002ea084d1810301030886130380d40e040c035000f00321134001d200f15148000f0981c0e8000c0800c0d0044104600c01c94040a41005803034032200a0006040c061003803951807480300d800500307040d100c1000603809030044078101c00241e0700074581d01540e40ea90800740443d60080c002641d2601401800c440c2c182024021811144e1000d00b00d4003844000c0c0c3c6446c2c110900f4000034512070401f180d198404070726604061030045002000060352428407044076030840c0d00340e81c401d003100e1300660700300700050713800a040d82c0d4501d42c00d0548d40315541e19042503203a14060102d20359030181020030010305220181c400340c00c40c0b8040300c0c928005000e0b151401e85603070080c1e1000070041c4c40304100400050416901840d414402c2c0d03240820b601c01421341d0080705d070300084190103003a111003100b0000c01d0070600a0031100902a212a0080d081c022084082070030703041c248 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 529711258 1250 529710008 529710017
    0x302160f11030601120309080606060a18081204060f0807050f090111032206080f0411011808100b0f0603012d03061b0302031e151203030f0907080a03 66
    0x341090022040c200ea4848030000c0549640d9030b140e812241c1402c2c0700040a4000403028500401c0308880003583d071380100001040f840c2400000d907821550035080300004d52211241550000d0014420000301d0700700d688d20034140780c4403420210010411030040d205802000003c3c4103004901d500002240c0c0203a4081d036055503290303001d40041e190f0340a611210181c0e031100080b50044943c0701c840012038030b00003004400e1255038581d0112202441544d00203c0d40c1c00c0315020a00154559806644520381030420841440c08500c0e10242d94815620010840d00542e102c000e4014040c03042c410654001c031040001ea0350010041866030005000f0b007a0302a000850048405950800140300e03402c4262001d030a032505c1c1c1c074050024040c0348407480c2007410155904c0302103a0080c002d6900c5441c0780554485a004980c0300d00141c01c030003030298404128030142e8428162518510600d01981c414000c0d0b58a0406c12840c500c061001803d17808142c000381014810b03220b021603214101c3d03425182 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 529712508 1250 529711258 529711283
    0xb040f060c030b0108060f010c0215041d07080a02030a060312020f070621020c0114090718020a0e210d08090d031806090c05120607030b04050114130608060106091401030216 76
    0x513500201601300c043c1d4000c1410bc5845242e800140042c825124440f284440c0c80b1025019042c0031081900c01c200403802880000700d03103001c554040d6a0110540b10080b0b03040d40d9036240c80c905403801182c1100140c105041642425001300311480c0245030520b807940451802840e00c2801d02c68140c24211426000610304402d0842500911902c002404590f0f419081c12000c0d1584c0e105544035440e296401100340700f8810040f4800c0c3c445803c52511010144020901041108601038a03482042c83e01c08041c1845c1300c504010001e0014040e0b11340303100ba030412890b81c502d4203003074400010801d07007080494240841c003803040e100141d0f8440400300314a0f4041c9040c2403404031a401c2144c2000b41c507001c1401d00c07503001031070b10f0140304242c50802c41c0207040018403056032000d0003414600c03007080c1040000c600304070104120089558034000740d00c2c0c3d00c592a8904000003030748240700045109906100c0c040c1e051600243d40a0b003400c04600d4000085140d0401704500140a80000711810 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 529713758 1250 529712508 529712539
    0x50703080f010b1b0f0d0215060a0506040315141311061303080a090b0a0305070e09010e0c180d05060f1f0626070503180109200d0b040f060c030b010806 67
    0x5d1300030950380307140540b11021284107009544171420000906030301d00d854007040c518103040300c1e091305450002d060149028119161001c026103480c42ca4100c4594070215400c02124250085000d10344240c0400260603ca081030905034048c64206e03446218204507161651508000a40489034002e10f002c0d2503c0500e401540c043c200350344070030880000000c5101596915600003403054003a030316000f4910900b4000d110040000740a9404411480408100c6110f4240007038040c0c00c41c07501801c0c0041c250500811402080014116415807005040c4400124095400c0b64044424015010058802400000e100519202c0d0406204e20040600c030f040200010b004152101c0b41e03d42c00301800d10000040040d401295100c19044000b1000022454103028032000da075004070070803000303460a5207200c1d00b07a01c5440c401580700044000780c00002d461030900510590003908964490000c5003008000d560400700d0b0b9404144c505106041d10f41e070000c603196040310050700e01e2030b140e19511 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 529715008 1250 529713758 529713763
    0x7030f0207120f1505090a080d110d0b0111150708130501091505101a09060405030a031d0f0108040b06130e0102180a060c030c170406050703080f010b1b 67
    0x2900000044503032803120200340803440383d504604a210f112803080a598030048001103520039500025943c1100100c0d03004949400041d0a51403440e210009440c0f002c03410700742080d4000c1d42c0000c1d20b030352a410355041e90340e0844005045407403904080c2c0304000b86900e80c05110840200000c0c2409000404204124955140c049000303501400030000765200703040030400038100c40c034000c2c211428176000480d0700750320b43c07140400c9401c0e110319014410741602106000e0303001143c0864020106201c00510340d6001c01294070440d00075102c0c0008602440001c042d407010020780140a50060b400040c201d99024110561207508001e0201c0140c50300c500058420687c442c0c03c001c59070800032100c4100750194003c1080401010001b11024101c00500c052030416106002c0440c0300c0c0384d5600c0102e070241c012900d41e144501d2072401c02d04541e4008500b240c206820120000b0070125806082503000001c55820070a42e2420158035850302c20039681c0c62081006040e8619940340e041035111404 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 529716258 1250 529715008 529715023
    0x1a04050a080c01092d1e12050406120b060909041416050307050406030816030306091b0e0f09130c030210080702070e07050d1a040906060f08030f07030f02 68
    0x414400341c0e0b50a400790301940a0101c0c00001e0320100d0b0b10038030100100c03c01c1c0d14a04a070364034415860001d62556243c0410702c2d07001c07581802c840c3d07124400000c000307500138480c0d0300e82d00b2103511a60f072075605141005120706560320036012070750310f0601c40d0080c039035948054681c100c0302220711207055550707031030302d00c1c0d48203064000400310703100e04600004910688803940c01990400d41c00c455600756140100004e590752440054178504013049402c040c00c01860946001a00074280800d42550f02d8103210116003580b00c021018103206483c0504c0c4540c440809520684101d80044041c01c1074000074003202c10103081e03403c04103002403205040214000c169002140c0040001030000c260303406c043c00800301100c042d0014001c150002c0f40303500300b50301c0d1a0f000e0f0007140d0f100b030b041a050249600c0109042c0c0315516044c068420301c071600d81d50301d000b007020080c45071001003a21854042d0415510141da082060290010701109103594000000c0d00e04094151428074000d042c0385000343e003071000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 529717508 1250 529716258 529716263
    0x105090907031e0501050310051003021203040f0f090c0e0f04021e030901050a0e030403200d06020a090510020a0203030904020d1b020124030201020307060f060807030c080114041a04050a 82
    0xd506404610020241d4413050486078247d0a07130f0074031619084a20102e400c1150340c652243c090b25814000b41c01e14440402d8114420011280360a48403400581c01350383c2036002141034904841c0034050703519180202484c0030704909200c3c2d54881500300050031219801442400350303a01092a100a140007840107000503411006103589062001216010b00b2085980c440c082e0308050740c403203807210004201d030110b940011120440461032805039151032038500700c50380c3c003880c440c1d030800101e0004e01c01042c80305050780700d04031007914240620828072410026842550050f00c40800580c8000c0100c51007000d045400607519004803008030700400031142222611750a65244c40c10442d01507101b036030981c902c0c4519240502100c8900710b04030019000003401030b0400d001043c0010840c0d08549580883c5100101d0f11315162072840c0d1030b00c51039600c192030702800780d0741c10402000c0138810784145c20845100c0039424600341d210303003044004c18000c000c000b25015002030b051120502068009a6 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 529718758 1250 529717508 529717541
    0x50409090303020903010c0c0b0c090339030d02070b0912070806040c05090c04030206030712051006090905090322050901061d010e030d03090f020a06050a080f010302010509090703 79
    0x14241e080c000c000f5000050018081d6180c40c01002c051802054814000f550120404441c1d5403914421320701900586810b230f40512682c054110380f22000108030008440c000100303030644040c07418680c15040b81e40c1086002c0e0300513100c2c1005041d804595041510808401c49640b00c02e004003042031062101c0340074113540038040000c1110080820110702950040c5451070010380c8602c108007031120309649840d404442080100010700f006009994412803d06284000719a00c001c18029138030212005103c801c41004140300440c2c010b0a030310003400c0803203801c02c0381e0b147c07030500c165a91203400100c0907084006501303142068410038042e00a8000500507004a5955082c0a04588421484905600080b07d00102c42e940b00780700d900d48500d4020001c0420b81d040315002d41c01032164000c10b442034448a2200000340c1c4540d418035005150075594980e958004020040c01c031540681a03c075802e964100400140c0c0c0e000e002d50b00809403c44a0014a8075800e0080d4001c000c0d4503510702e8641c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 529720008 1250 529718758 529718771
    0x6030a0c02071d060907031104141306180c02010501210c0801020a03050601030c05030601140d0e031c1805030304171606061406090d11150c030a02011109091501050409 74
    0x1903090320f80440c000d07241501c003062142c845440a070291941d4460358078034080144000c00201c0c0c480000308840f0072000d85000500f42c0160f89041c10f980581c1c00200d050a40b00c03042050381e82043c401c4c14500f09151000304100e50401d10641c1364900014044d5510b1031085084009100302c2e65020001085e112000315901e10300c001015000d04000ca0b445030219251024100340c15004000300c030b115150580d10320344019501d2080c8180e640003409032030207140d940c41e040d00c01b01c003040004203c0e40311203d21040c1c81d0f8284001100c1581c1c00d08003a50b44a09180c4801c00010b200001541d402c0366000d0202e05442c41c1d142021412070040c0c080340104c5132441c00403401071004a510080584102c0500d45804018480031f01100d403150003d1345411120401240000c1402180c2d003840d50030700100400f13074501e091203201c0780135040035003007030000d820006101b42d0158091060312030107051510340d6420000c080c00050012003004288010400014000381c3c46c2d60300c60411140a04041c50080090 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 529721258 1250 529720008 529720049
    0xa090303021b0a111012092301050604150605040b0a0c0c1403010c030b030c0402301501030c0e040f060b0301060203072303090d0302120417100b06030a0c0207 70
    0x44621507101a0342c114042d0280040c1801e0100b170454240c00b0503104c0d03144030b40c98402039070018652210255008460410021004944402d00d02d2900d01d00f50000301d1581013120030001203c0d0b000c1801015480490b07005c000c280d8000c010f41b8221012030483d01e444a1800e10207071501502454020421801108003203241c07000c501c8003c091100c1a8006c01914640e80c0041e4200c800b40c1500e55850f9001130103102c2c00d8500750700104419080030100d44200b040c10850348000b0010100400d80e03101c0d656040016040d60314100609e108400d280601c0917500700c8502800c0307900c103038900764010703912a498400d10304681d8101d031000304030b5805d8469480d0394031a0000d4581d0443c00c0308a40c41101c00c09029003040b6031501c400041c0351400040c51500f0101420080240795800d0110194001c204203003a00550000c060300007042001c203882c501e01c0340d4040c04c034101203188442c0d003125460116084a0354071200282d90344540c100340c0005e1020310701c5400340c0c9014440d60012050b4060000410031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 529722508 1250 529721258 529721263
    0x10906030506102d0905090a051011040b030606071416050a4203090210020303040b0609130209041203060b0f0703120605130b0906010908060a090303021b 68
    0x1241e004006840c0b403522503240760034001665124803106618044032a544010805640186030308000c4400c40c0d2103030b40c901292041d640100d0381d142c4981c006185803400d00009002891118050050800c0a1844d20000e0341290082c0e018510807080701100050aa4445c54219090716820951421401050701c2c0e003940c0c1c807400303441c51802d03d08070764100103003604044031024280e45c00e030010046400000c144501c41004540100d00040e000c40040707204e401c201c07107038017044000c00c1d0b40c1c00f140b003204a00601800141c2c8603040d0301154010800c100104100c10585500301c20111800d840c1038035440780b1040807a01c0001e001c0e5220340044280000c00208150740121a04a80ca06010407540c139003c101880c080d181d62001003001c1000141e0000b80306007200004000d0004001408c0c945940114107050300125500d544155200c40e0303181103140180361140d018000346040e660705e905124005482d2640603200c00f461680358000e80c400c040c003035016211fa410950040000581400140e00d5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 529723758 1250 529722508 529722521
    0x1c03090624091a09040501090c0609050915101101060515030a11040501020a1101090b0301030b09010605030c01052205121501080606010c0b1305060a14100e0103021005120109 77
    0x441841c00d5038001821101d90003410200d0364030703580960840c0012000e0004100d401002226295a035960300800104465009406402d41d56a1100b81a0800382070003810707036028000900c800515101d080790703591032078004000d601c11031a103500d10440e4160140e01418154004582c0134250f43c01609401e51041c02451148520b040c00740106400d05025207803078444c0e0301950340140c20410011000c181540300e0b4a2817580c040c900318002560701d0050002030340082c1c00031102c0500307100038070469103024081c01d000707410700b20302070199155550f001070a90310406025642030800550306030071940c1e44040d00001000d02804200e0201c210003121a15100000440303120030052000200e1078030000200c1d07500c50441078403030040500a03134440d803115040c02082005160310220f000340c001038042c030060b03024000c80100410070400402940d514004020000c1704e030450003040c00c001c032010f458569411a034040e9070400903280c1104c01150703582710741c80c01d00d0300718445030780001030445c02076001c807 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 529725008 1250 529723758 529723811
    0x82203121b0f090e070e090c07050a030804200619200a02030607030903170405100c0801090b09040f03030228020714060909070f03090f0c06021903021c030906 70
    0x34003c00e40311410750074440d20984505001450440098202d42400090a500704c128900090304080e4141d444500c0e01c1000b01c022400244c0754014001009140303070044080f20444000ca21408500e003021900500422003d9038403e0094000c0c02806401081080e80c1031b01000e04030900c128402c810f05071b81320304a9908a00a20481000400042c800d03c5200c2c000d60b030541d81e0300c0943d00b19010b03214980d107020b0030a643c0d60041071003030300310300c072042c807507815072030040d403210801507250208001c11036070101262402115000c0410000030350000348458036540c5800d00617211084000e140e880304030001c216a243c1c0c0203169900242640014421040300c810070088030090300d0740340030f2003114000c190340d0310f030000c80c0300010500c800e01507201440c9010b014a0f0001e4036814648510401c4c0c1040e80e0261140c0c644141d090182035810702460111038034241038030481002c0ca6900956074890388a4281c500310049658169592003078001b100c440c2c1e080601402404000d902c008050031003164603 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 529726258 1250 529725008 529725017
    0x3070308070210140304060207080c100e0d03110702120111070503040e28050402060d02070f2105041514040306050f06120a0201080a020708031006082203121b0f 71
    0x100007042c4e200d0402c0b0801d1840e60074006081da252559000003942068800b1a00e800c0c0034421096204010000214284004407021400d440491a601e0030681c0160700d480c1018100380341403040c00f00e15030888080550540e5000f0f520f40003e240c0e1401042101040144140000780070018008000080e0060306c0440141d81c806031036901c071289002035282e0380c908008405205104030b02010b6440745038401e001030099480d00b21458010000c03a070001d4022103000e080d000408040c0b01c00c00484569540140400b80d000e030036001030142c080d000d03503c035049040d001c02c80440b035514865a00c10a100c2c0340850143d442c0d54480c0f5050025040403070310400c00602580019501e880e04000c9600440c0b80c88014000311002a0011100c003c8010520510f054080082e14001000c0c4002540300b24225008030b0b090f079045c814000c000e1400940155982406a00900c05900d8605005414558581401380203031480c0d81409020340420001c1929450701148029a40c0d80c000c00c0410824956598 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 529727508 1250 529726258 529726279
    0x30a08100509010e0a091a280501030209040807050c040f0b180103080a300905150f010b0703030b0406030c1701050108070e04030909020c0a020f1002060c0315030703080702 76
    0x3403101c142401d104041c604002d403404104c4a0030b20780d12424046c0d010750916640841c04400a06040700140c42e6215488402c0b0a0225900310024402c0503412001805200951442d00000d03400c42e8040c0010708084c03000a0b030641044010002d840035030030040c0007409020740351a2920010f0803101c603a580100b0000100813503c800d507900e0103059039070090f80242003504a6a023182c40310005d007000f030001c10210705d00c954074151620119099007050307040880e000e02c0e01d1602c1810f00c514050700700c071500030980034840b00c1041b10143c0342c10b4500c1d1003651343e29a00e66080c00c402410b00031203819009450120080148580c0c0155502655039000301a025600340c074007424200d4030244101c150903005040244500e8920101c9150090f020749000311000f80c131030003a4030880c0d0103c0308800c0b072948424030302802c50518441000000306d04407140b0740354074048000a522604024a840f17505000080012001091218125903000c0043d085038400c94503131801e00d645e94071030101644a01040d50 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 529728758 1250 529727508 529727519
    0x501060203190f030e060a0f0b06030103120c03050f0313140c090a050408070213021c0c120507090812070203120a021b060f030708040318290c030a0810 67
    0x708950310702d050314200c01d00c050200e0314100c070820b1404119008142c1c544c5801c1c41c01020400c040c0b802081008000903060307000d0081c03034089515202c24140a00c0c07080c001000422921020003d00c2c080900b0032046a1280d450b0445041c811400c480840000100c00d010104c02d1040d00350724103c0c8903880500e504071240c85101c2c0e58442e074210b002d40c0011181d0010303400100701d4014a41140c0b01742c031a182056001c0c0d00040140c10401640c0a5440e07001c00d030410120040031140c4050540d4880070001d031084104d0051040c050224a40400781e21040802d1240d44109585001232440100b40e5514603caa03590b43c4c4541d020001c00d0344a8800d02070f405029078102e400b2900301305144c1d0002e0142c4c510b00d03145051742c0700d220000e0741c3e403285d814490040b801c050a40150f10540307142c1c2e0b640c0400c0c501481c015100c07850820500d8030851980e00240105a468048042c1501c6403100302211030145030081d40c0c203445000100c0b201c13800003055102419811103001d502541c4202c00a01c04662a0b1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 529730008 1250 529728758 529728763
    0x302060c0414061303020d2910171e01200906030f070c050a1a0907030803070c050309030313170f0d120209180115050c030403080a1206060306030605010602 69
    0x3400707242268220b002d507051503468400c000b0814440c2c584404540740c0e40d60340000b120150035000541d030000e02c0c3c402030003040d21072200c40602d035600a10306280f50b040c2802d110160b40e8641c080c0900300340c01100b038101014402c11a00441c440c0c1901003560544070b240c1c109018107611707200301c0a5095501250241c00c02c01c882561980a000f4145230b09541e2020161441e0400240403501230003908040400411341c244510321159020b44a02d40100c0008400c2a9981200905850302c1c0e4010700c03014000602071a0031a90800070030b2034407a1491001d41082b9003103200306642c01e40d061100007540803603010202c024000710b44035000c40c100c088810140c99515a031400c10b40202c01e0700400e0000c032045000d801407000c0041c02c00001070412000f5404140c50700e03014584900d541202c01c004203e110007000c0f12550614661511508150042500c540d482c051804014001840813982e50b400d680b15506074440d44241c0c0d10140705040c1d5480d00034004240501065444078203240000c21983d000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 529731258 1250 529730008 529730017
    0x20102040b0f031009050f040b090d020c1005090901030501050a0516050906161b0503010c02030703021b010c05060f090d0309020913060b040c08160201090b011a16030c0302060c 78
    0x681c1030689004a82c503000710a9a0004280c41d103110740015000c200b0900e2886160b2203180f04640031941400d00c0d04050001200003040388956034014007500114030f40c08100b850010006542e05400c0e100c124609030740a02030716003480e82005010000000384101508914055061068200081d480d08418903800950704014070380414020000201c1c2420101d0041c13403104d250b5070a115031050300d9a1b03904500b2007d4200d41d60040e4540406011300e00d828852220056150300043d0b10b0400315a5004e910742d5176000a4040310019400e8200700369000b5071502c01200d912409030dc6c11841d040b0314442c04850300740e61a038440c5c071442d0540a16a8003074442c44605a070001d00850490341c41c001003001801d07104500302c0e00030380c1320307007980c2c61588403800703800c04032400c44d120360203c0d10f4008024041148120a60760842e8141021040440e0242c607049041d501e80c1110400d550440e545001c11520410349001e02034107000018004ac194400c0c0c1d180e0b51548294280c0b081a00c0c1c10496021a004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 529732508 1250 529731258 529731269
    0x1020f03030103030806030102041505180108010f1413050f0411010f140a020f011803030f0506010804030c05010e07030f020315091902030c100305090f0d02060a2301030602040f0602010204 83
    0x2003000140f004c680603200040d844040100003518054031032044c41081202842c91501154001c1031201113040e480d000d211103070300203180c103901a62400b800001203a00a2150303414141c5080c8506410b0b48441c11108550001802c0138011800d00444105043c5012102034610441601d820084c943c440ca08000e0714980c81e641d800200601c4000341e080542c81a04004250710a94800440c07405080c014210320410041c1031410508a41c00c018081d5621500902c4017075140c1020010700f80e800c03900140e0819018076040c2030801d02450f1842c014500c0e4070050f06148100c203000001c00c4594020b8540140c800c1d02507400b441c40084281103003902c01d651f45821a004030302c00c0407c0d1520404814400760005048844c8401148042600c2c041100c20880019444204100c003c0c2c004110625004103001d00030500706003251402521400701610340401e003600c0c1c0003a204c80c0e0101d50000d20481c0041c0f2522409035940b4a800002948a80304078800f80444401c0003d00d1703401803094900b100c8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 529733758 1250 529732508 529732513
    0x110a080d0503070305090c04050106200a150203070c14010c030b0f101206030804080a031b030206040b0a061508090705030a08070b040501060b040b040321230910170601020f 76
    0x1110920f040e0007400c0000c00c050020710039401c21418507642c0c1d006a90080000d07032500e43c40104008804000803c15044808041e401480d440c000110f1400c10100401e0001c2c0d030068517a2180ea01c11602101000b00c082d002d642400030703008000406503c41c0d4403160154904100d038503404ca00f400114505040055480032103800d4840300b56004580c14503089010b5100083ca003610b030303611300c4026040703900314940c1d80d40304404410415420460b40d00140d03070060480d81c403c4c03809607802580c2d80c00040c1300504500190011800c00041d9402c910094102ca6100d940000e1070b1050007041c03a0300899004426224903000010745050100d0550051038014018030301e002c2c400d487d0142a244c1c0034201700c0300e80d0342e01c0307500142c90300c03c850240026203403549000d55642d29604100408520b110041280034010303d14030004150030582c01e2101008958030540c40702003c00d001c410f17500800400c0c0c0c0d00660300c0c1140891182d8401c000000080c0002c078291004d803100f0b001241e40700d1407415062102c2c0d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 529735008 1250 529733758 529733761
    0xb09040506131b0e01050a060c20040f05130224070b04020a030221010501140618010201090b072c01081f03050a081b010c05161a04110a080d0503 64
    0x1402058805900300e0060f48072512584010741c503040f41c0d0710b2561200d4401c846032401030000b41341c20720744800102094034001c0300b060025251149041258410782c0d00c01e08858003280703900e89079a082030309002c40c00b0904010520340b100010b400740721160801c0b846082104074114030060680c40d45600005014040c0d4202840c5030780307004d0a0b600180c0140d80c032450110340000142c0d1407400164155000d00d80c61420408032050300c500f91813040c0c000a20aa0300e600441d4140d85415090301c002c05a03005181400070304140050780100301c071480c003070700031040b840070000d60607040580c0d81c40d20404040501810300503821000000c00c0329180840c0000d03482070106140300d6501d0001c01100300e52040200f40659240d0702d062800c007040000310f807605001314000c10b030810641034000c00ca0344103500034401e0604131107008286100d1380541000b8983e10006000601044640c041e1300000085030000003030070315080c0383d10300300401040e09101d50b506200201d070088d804101d41c62103c1d03072078443c1ca055 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 529736258 1250 529735008 529735021
    0xc020d050a050f0f041401020d03051302010f030906050c09010e0108040c120c080a0516080604032001181b0f1d0403030e030a080a050702030a0203040b0c031903020406030b09040506 80
    0x80e0f021140c0441110030070301c0540313a42c0030440020030040810910340343c501050007002904002c4103402d80402d1610389420007800084240e40403100f0f83c3d0910b4a2451266410f005a00a002407900901220314180800600090341c10040140b01008d880394400c00452500440e8070400071140108a60590743c03041200750160810b01c0a05486a41c0c14041c91b6100e100c003602d0b10684003c20303927055015002443c0b00c3c1509503251000b504118029107098603254070040c00000040c503610000f10761203003681440d15001e40c400300c560803994041508004060405031501300500e12903030215402200c000800d13844500036102100c28982100c2c1500340f0b0010900b81c282e00c01401078060588806040c40c06940c10310003818685029202c600050070322810708412900c1c0141034a0a41d441001040c00007a00041075900321402414016a594246c404c51401c40c090359260501c1801000401401c89425801800945005a40403c142c403441c400f04042e01c81c041c3e402600c02d40000300402c48 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 529737508 1250 529736258 529736267
    0xc0c3c030e011e020c1e030d12060506210a151206050a0509100c030618140a200706090b19050708190c1710030303050a0902030d0c030e1003020c010c020d050a 70
    0x711011003070151103102900c0c1007c681000e4088109100042121945019100b43e6100d0314010b003400307071130080c1001c8286606422a14a211880e04a0b250090020f006c44c4066003000440307002107444490010340d500d80052200c828003070111102400c0200140000111784a0710b841006e006000300500d000c0a41c50f9070080a48100c0350341010b44882d804100c45c501e0108040700da048a005c001044852030719074000c1e941000d00341e00d8003182007603004030020300d1040d0780a004078015000541e0b10140c0d850050020000d011006060421000800003d600c2044207a98240a06181032001d07940f000b04c201e58250085071518514ad40550156100f003500d607100e0045d070b450300d003041001a5481d801640045800b2500c0c00c40c0c04858034007c0c402c1642c98001c061701700c000c0c1441400f0b080e403ea80040d072a003404079440003c01c08141c0014050603c110b036a804070030000f4003444880f0141100041c040c0d408a1500f80c103544c03d10000300f010510000b20710742a0030b140d03a1444d0400c480100c00b1070717 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 529738758 1250 529737508 529737529
    0xa020705090c0d06060e03011b210216050303060901090b03030415020f060a0b0f0910050d0512181f0c1401020409020c07090c0c3c030e011e020c 64
    0x551550043c00b2803020a403103845408040e11854894004d4500b0300420503003540d0390f56038610305e055201785001404035000f8101030180044800b00e0391041d600882c01c3c030000c1c040c1d111143c480ca03c10502207400d01801000450040c03005554072441a83c8481440095907284402141c055204000c2000040d445050151030800300c1c0c81540c40c5928030203070191074540264ec1075a005640d0307032960445450801c1a08081c81415a044030961800c201c50009160b414800c2900480500d07002008201003030201810041c030500e100d589a40a00c4642c01d43c0381c00340c803070301e5010b4074081c1c0c0003d044006810380c2849041c0207540d403403107440b4a5903c4401e000c200e441070502e40c1d9000d220214403280d560000e804801d41203402804500c2c900094141039038400c0c1501010300054498141c0031445005d080401d00c242405a2640d072203070001c100d88015000c501411300101d100104900b00745e0b001c0e020807090b490903661034211400c582c00072083c0708a20801303071b07015038040502d58103213040c98030101 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 529740008 1250 529738758 529738771
    0x1b1c0c020a030b1623030a0207030306030b04151d10151203230310060e0a050904120e0108061e060f0705211206061b0f070303080603030a02070509 65
    0x1c03040c0d42d0341e03549009038941c09a44281407052419405911990302c90781d200c00000210904e0241103040f450455500d20001d09103480a640025480b030505000c5e4221900656001508100d2450a820602031060851001e0010b01342000140c050000f510040e9050600c011b401800025030140001c50040240206456001040388000942000c07694440d100c014029164405007803a1000400c075070134800b0342000b174411030500038086d4000880c0d00c4a001d40c0c8403414441d203003155903030004c6c241c2c1c51268055613101c1c0764442003000b08a940807914001c1146a283c10600c0509440151000e030421211302d07810404103400c4540001405541140c626009040c0c11b1401044c407c1c606030643c4031140a882d583c3c0034000c0c8e841030040c070340e0842072038089950b144ea041000d440148000300c82c014000300e10455010807082d0b102318007500350700710860700c1c0412a01000400c4a0b0144c03614000d02c81034001c90629400030301141408000c4a404140a40c00b03010704900f000d04000000e280030300320 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 529741258 1250 529740008 529740019
    0xa1103040c050607241e0603030c0f0c0b0307030b04140c090d030e04050f0f0f0108120307020f070f140f100302221d0136021e1b1c0c02 60
    0x318200041d40391101401c24007040b0210b006d1036003c250202c101c410076020a02c60b4503081007000825800910307000e0003540101d601704a0520b42c1080b401003c2d40e5045008501d4001040c8018507400d42d00001c51040d0540781806000f00510001e8161103003154103c5401004200d0404d4914080b2840007040e442410011a00010500071908942c001c1324980d8810741d50b9010b0188107050040c45942c080c09002c412440c03503050140107601c48041090303002c98a90301001141c1d14500034401400300b840c2c103e0844514654407110000c904100384580b040192082c1d85000c0681041e481c0c1d00030900020707111440300b11011800700c000b5881200122600d100011600c52014542d0800e0390040500c1034850926404a5400303030300550041e0700454015000ca44182c0c401c00c2c0b420000c42c140d03aa42104511040c0130444980e02070b05c5545001d04009040d9800c405100c809540078240c031000005002810004116100c0d549002c1e0140280701c880509401d0b4501c280728414003102140302400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 529742508 1250 529741258 529741283
    0x305030409050103050118151503020913060c030204060e06030c0f07080301030b0711060f090709151403071d04031b0b0a050c03060a0303111c080a1103040c050607 72
    0x540504541041d000903a000780c5400040003485024001c2007102d8880b40d51081003801c40d03942c0c0703a50605001c030304403070490380f40c507a40c0d10f4484900e80c0003c01103030080c0c4084807500d0050b01088504075604011142c80d40b42c08800040d03207220f03100b0388041d5603103600d0720a400135004040005a8100801413420302c0410400e00603d16a040d01505503141306101d4642c9a505600c0d001e980c05000600420030404504041c000314003000454640000c2c03c01203000c0e107134076250440c90a154841c0c00c0f8a080504001c0030398120380c149840c0d0000c6641e100041088841e52108042e00e45902c0d00c150010094031052520154402021180d00075100342041e84652101c0c952011807840421005d0341ca0b01c0e0002e0800904070300e44d00425901821840e4403500d1403909200140001d44107000150412091041c482441c0208014a0760180800c180302003001c42040b07801002d0f41021140b1750b0450342050004240c000c2da10050364010b039072080340c07600c100d4241000e10005070003c0205582c900400303030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 529743758 1250 529742508 529742513
    0x1205090d082e0e07031a09060a05060a09090e0601270207020310090b060d051b1201090b070908060c0d020904020d0911011409100e01050c0105150a0e0708060103021303 74
    0xc0022880b040e4000c0e001c2001480c1c8030200c0c814100040601c0103050401014203500802580c60042c8850f04581002c02c50b102c16000c140304407455007100da00001e000071000392481e040b03107280e011200603010502c0301e4100001c006442d20404c0c8180ca110481031080c5e2418143c3d01455041442000b0320b00508003492900081e00e062100841901760968882e148400e01003280d00d400e034071003001e861a080040141d0f5031207603901c40b89150210000210142da02d80b40c1c2e070304114080343c07000e560002c0c000b8600704c0c20200361440302514050046031411000144400c004126984a4036819010710308000508a0702c030041d51003484400da005600b0080c2c0307031300e0f82c141e0310802d036106028521036801682c401c800074242601d4040100700811050080d45403642e124401040203a8142c503010364a424034400581d80d60081026410903035007000d0800a007004900340c440481c20045528201003030b80c1d0019600a107401340c0c2c6960004650f070740096003950017500100b8100400076141c4501c5540da8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 529745008 1250 529743758 529743811
    0x10525060507030606020109050d08090a06020f0c06012111060405040e0c0f010203121f081203040506060a121b0801020f090f0603010b0703030f060504020f0a1205090d08 75
    0x11000c5038099640c00038003a0495151060300003424090000300070f40900360302c5580c0e5900b04030010000704200040014892501404040d41d150303888071043d034842d07840c040ca0300300c1500019980240e91081c0d01c00054100d48000320364100440041c0e50b070300c04002e15240c00c148690700500107908040104000140b5848600c40c152002e2450000780084401384420800d103e522846681d04550091001c5260260040092038001081a031a1400580c0c580103074545482301d0b034000e480d94041c00b1f0041512040c44001144100d21400075144290740791420400720000c0c600030415040d20300c403910b90010b03010b0100d2800400c03c000c0c3e0000220768030f042c07442c260317031040d040410000070108841649040c552040340c80704404540c554115030405040301c8040c0100040501054bc984440c0f0b41501c01680c085005000c0c00340c0150355500035201d4600c000d500403004240000e01207010300c041c20104d4441d00d801080400e01a1211072020032040b1554240039100745200c01242e00030081280c0d80 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 529746258 1250 529745008 529745077
    0x30c1309260702041a0a0b0306040b1203030f060a0b030c0315040509010c0e030a08031308070803040308011404110409020c070816030b0907270f050f060f010e030c0105 74
    0x90203a80307070b941d040502c1400282c07440b41c628a0190740c19454001610f56680d8403031000c0d648980c4405803a41d44032000200036100034045640c0084410032180034a090210045124146624071400c440e100c050600c407400d98144140b02c00b0403000d00100346550f80c4e170302c01150010095464600079080d007034001002c40b041515202042c1e9541c1358804071040c1c010030038010b2800304402804a00200b0384404505120041251107007804088000c010072500509a400c0d10b60030110180c2c42e4901440d02800d03194080c0a01c0c0d01000d00340280070f00e585414010003500503074122100e810240741c05003407006900300ea6040c40c054010b07030074086500241000611100c00074585010300d038901d58209a0a965800780c000c603c103070807022082c4520411800c2132108507840f10080c401c25110849407000525035207016840a90411051140146d55821441e003c1d000407569890340c00910b07401503c20105520400c0e070940c000c40c0140040d50700500c043c0900e0710010501521544000100b854030286 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 529747508 1250 529746258 529746323
    0x41e0e0303150402070507090b0607080d06090b06160803060f030604080a0e0612010b130803030a060302030c040911040908040513020c07090b0d0609050c030708070302030c030c1309 80
    0x408001c0011201141c0b0955000b200152001c40c03030003c0503280c4031748903140d034058100300a4039030074003042c15180d080441c0c4000b504444200c1d15240c811021401600b038038807824030707214104100c0074081e21b08034003210082074060290f50310b030207900c1e52080415000107000940c08080186000348076102400002c0c40741c2c1c8070b0342003159101500d000c09804403407a030302c110307005040c144400310036010b480d072000e41550100b04d0710923116604400d031501a8a1280c000c12102d02001c003d108010b4100e80040c1c050300d00c201d080c0e40d08102c3c00e50a0004403640c8100c013810912006002100d10300701a03000c41141d83c010400a441c1a4443c001b150140c80c90f42081c41b04560300082c18000e0b10f1043c007405018010303020040c0300310596040052a41c1906200c00340c000c0740e4510605081000400480010942c06001d50b45090b03a5120441d840f00c6c10b9110581c0240165021290f1600d0301240b41400c8560040100c1a181142054000180180401258800c40804c0c5154202100304807031402c00380c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 529748758 1250 529747508 529747513
    0x10306170703050607030209032107082803020a0212090a080d18050306010b0904020d1d0a050f03040503070611071e051c080f090a12121706010c02041e0e 68
    0x1403030b40c60030700e180483c020311344020144140442c496a0b5804121030000c824091182014042402d41da079a1a01c52030400130814500015000020320b10812842410f9550400303050030070038624800c0e0164840c4106560051300032005c0d00110365600c0d009800858400781140351a1929103103000d1170803d580c0300d9140031800217455014050b00042115000d40000c0d4040e103015403420280080c05c1c01010500d13441150046008451440c440d4007244400f040701d03120249480f0100c90f40c0e034a40740e01d02e5041ea0319000d03043c601451038100004640403030304046c0051100c2880c00038201d4107040b50085194a5001e4104001010034900c00307204143d8440c0100316100c18546000c0061448044040c0640034030402c1341c880202d060401076030310b018141c10209030781e42c00a40000d40355800301e40002d0541410300d40c1100501186510102c21b1100544401142d1040b54141c28048201161680e002902840101c4011300b0150803013100150301a441c401c9108441038103a094468140c421140da5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 529750008 1250 529748758 529748773
    0x504020408010b0909070f0e0a090b01030602090112060f030201080705070c0f0f08060912180a09091b0311060d0f0f0b01090501141b12030c0c06160804030e01030617 73
    0x615116244641005e1150001c01c9001d00d8500d842902074154410b00c8442810f440000e50140d0803508901303591a40304116500c00d6131a8a4000c00075040007c0603400a42601034038841402ea622404064031003050210000c0d51466004640d5540014058000c01000340211800580184440d40207041c2c0e07641000c5507076041180441241940f07a2217039070b45a00c04010b0044601d008034040f0b6201c002d90424131b940b0004000e11000702c1a446142c1500281c401d840082c408015074064451940300c0c0811500540f525001da4480180d140030180c81403d0b28283c00721103160207001030851400000001c10582400141c1030304544155070815203403038543d003070102907607804841080907210034200446000d10369540c03d510742c082c04588500083c2840e8410110f00d00c2009801c240100c502030040e5030789400220039a82d030f000480e1040141c031a540c00b140d00ca5815012010b1500741a945171101c40c2d4850b24126611014903c0b49810305585650200d800f0b44001d0384c2da080c17955241c0c02072040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 529751258 1250 529750008 529750031
    0x13050a141204140f041407030908040b0c0343030215041a0c0c0307080d0f1d010e01020306060a08040f0b160909020c031b15132127050402040801 64
    0x10b00c80100b0740103120700d151408091446c0042c8034038903040001e078030f00065100c40c2c1d803401d0003030b51081d03400141c016000403920460700c500c000003c1c40e01460750050083c84010612003140120207124a120103031b000005074628005804421440150091048483d10700c50301c0f09046d80220166010f5444a18185007824960041c2c10515005101c500f2200d05d003d01c2c01a05a49902440800514000c00098032030580401c51700301221404407000104040c0040d80c440d1440d016103002da4144550800803640040b80040c0700b6241325010280445140619051080f00c0c03036040100f003100c0d00040100307081c020481344090f0510900d5080d95514095454a0024081c00310300d41c0002101401001002c10400c0b000c029107450740d40344ca49107070f070001c4070030f0080d41824101869102c2c54103040d0708000080501e0303049030007000c1c05083c0381a5507912040391000301512840100c2c01180c4488014803c51b000c4170050614103031154104c501c2180c4410010302a83c1c41a84908480da4581610080 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 529752508 1250 529751258 529751269
    0xb03070507061a180709120201020114010b07120804030f1b05010c021e010608030435100b090f010519090908040f050910290a020d020613050a14120414 67
    0x2044c105800801d40340c500300c04020f2606405000f0b122079540302c5404107085900035080380221482d41e440c1c200c000e40c3c60340003400f034a400c40842601d000c110410600005809558414000d6400d13569850350504078460a903401100703d008a540101200803901c081a0203120345404562190b015000300000480c4036041c034020710781c3c1d1454507450494200412280001110101c4507640300000c035841e042540210500700c61064020121a104034800d900300c40800c0e4a60400061601005000100c41c00c1c4040503500311204130521001c1d000510241c80e10900580c001c1c00c0668100300155201c0710584143c0c2c80d554001c9408410100e010b00c003c400115100c00a0722091b07888422610380001541d10112882c0301340555000e80c0041c20200c0070011141249208035140c1a030365540000000031360704c0406c00c1034100140101d60104045079050401d1000d0650044001c200040c81c0346c50f01e0310050280100c40c15a4030074019000c00280c1954003800084c00304056840071034408206204 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 529753758 1250 529752508 529752529
    0x90209010b04050303120403020f0601060f140405010c02011d0a0b070507240f20061509011508061306080f060603060709060e0a030b09030912070b040b03070507061a 73
    0x440c50090100344081c0e1400001e59180e807031b02103000085034449040236403c2040f5021010b00c980128000440c4103900400d0521403000c03155904000d50210251200b000d0185000d0540090340d03801200c1d01543c447c010602c5292000034506020042000000d00441941d50241c1802c02d000f0581da0f0504c00244203150003440da1403060390b5040071004040c09040c401d07003900001c3c0907140185868051190760b80c0203a8550070100039102800840c20a503641c20219080001941010002c18450a2490440e412200380c0080c08101740c01d603802c150f40e4601c00500e03182d00410320700c4411500760004d000300c00007426901d014040ca10a00c1480c1c9040c418001c0c4424040d512460034000c042c1c4c0c0c00340030901103505600d020441d01d100c3c10000350240c00540d00c064030a28010041c8821110080010240d1700c10403220550200750700c07126a80c4400e99481070b520512018001041400020001182d1140c0d25141c641c0c40c1880f80c1c0e451908890440281e10040d00c81c0c2441544981040c07001013 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 529755008 1250 529753758 529753769
    0x14010c1805030c01020606060d020c07120204050a090201020304090903050f0301060306030512070b04120c02041b0221030a050601020a0f031d01081015030908030112053f0405060d09020901 83
    0x3403c480421a0000c2d5840f9405410749002d0680050704450301001c950585002c44914029121196542d01901106da00c00841c160302c100d1030003002c2004001c05101c1e0440c0168181c02a40c1854a00505c540080290302d2060b0140f14042050340c0c070180d4420000e5010b018240c0b0001011811400e0080c40c0038030052240e107204000304117080204106809050740158000200b80b11301a00100840f540c80e40b032038000350003a01703200d0003a41c1181c2c1036155800e0034110340d00f01c0d0036140b8540c842d01e00080030b01e19010070100d42040842c50134034075900402e500107010300440314100110743c0c1c1c1c0b1900418904058000401d254490360107007108601410b100031003445c1112042c02c0407220032945044522032085001d02c01160030b0001402a0403180c0ac680c1c001c20351588070740c0d550071081241004440203c0e280d0180c84003a0500300740d0189040000c214442402000c41c040031600d81d2040104041404001c0b02800001903d6036440010200d4402c0120301013508116841400858501078100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 529756258 1250 529755008 529755013
    0x3040b0108030a0504050609010302120f2a1c090807030c0b061e010e0102012012070c0b0117100207080a020606040b15030c2206021903090b0714010c180503 69
    0x203030543ca40e80711095609952049403e0340d529074580c0c005030001c0c0310341ea40840910341d80030100441000d60f602600c2c41545521103c018002c980306414006644010202c1c480082c144554505101403140c165048880040e00003401d404036100d07040e45400a030812000100b00c00c550707004000c030014241d5003044043da918041080c90b40316040326600d0310700350380e41000110905520568400d420140440030705804400703e03800d05415009890b441030103000403000403c00461001849480501403080d040840221940d080c403800740c0e1800f80030001c0003050321401c440d01d410302d2120301c010905544070350f141c9a505c2c0080c200207824650000c1005201c0d0740350524505581d110f0951405292140465132a50b0b6030b20b00000325141d000395400c071408212603190380d01d82c50031401c0021060f00c040ba002c49094060203003040341d02086841c1c00600040144c042008005085405800d440e13200e1446542408440d54000c1e0031100c46c1503150b000181e001030350118150000c1200e00c043c00e800c0e0301 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 529757508 1250 529756258 529756267
    0xb032b020c010f081f06030603021503010f0e100e070504030210090e15060f0403081c02160b041118100611030f0f04030c0311152703030d05010b03040b010803 70
    0x103402c03050401070903c1405800d00001c0c1c03040c40d0010b00f210041c020810744501064903210000c006010b41d0100b00c1c0901c640c191041010005c2e0010b40781209d550f03091402095041014508020070041c22030b62103c00c400102103103e4030003420591050459542d02901d07149140100549400f03a420182c1c00c0c04030f01442030002d00000701030b242d400000111003490000984010030241c0c4a0007021039034000c4041400310420a14000802024a40c2c0d000c0382400707251240300714103c0c0700b0b4480e02074000e900170168100084400c0c202540c0140a03004000e0034007185000f01d0290800e041c0501c0d101d101c0441005010100804404040c00c02c52030001d90040d80f68284903681c0c41039203041c41107104041100003c080200007220040c60b8810700146849640e86489a00240c0c0b24085a100722031007104071480c3c0c50014141e90812054400d0142584041007403202c8030a0042881601808100b00b0000960501d0103802c0c028511440800d80e6440c00d8108a03500d20010b0f006060b07190010417 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 529758758 1250 529757508 529757533
    0x150d020d11070203060a1a09041a010e0910050a181b06140d0b0a030212030d0614100c0309050d030801080c0103020301080a140304090e03070c09050603030d0504060b032b02 76
    0x20201d60190086c440000d6552074007005000004106002640c405440400c20041004081d1401181119070452002907600c4207541c80114004481c8503409900081081d9000c0c2d065070480b0b82c000d0074800000621064108010a42080c2004145d818880b110710300e00c05808280311090082c201454a07040c0105082000381c03141c0b150122080311540c0720702d600520b40d626400360400a60307000b0b04080740e403003020062585a8003c8104056500c0c54003400103100410404d210f51248002000b0b05204440440152641d640e8500142c1c02c001d0350080102d4592120404c204209000c1e441e00c526961500c445540f418000c604d001d0b0405005100400129000068002d103c0d5400490200000d0700000d01504d1400303568424100f072410726158170082c24000c0010240c040c0135a10702c0d514a9150a288400d8810542d40396805910030806050156045e90016400c540301c1d540218055102d13400180c07502000394841100014200d035003001017511905517280c1c09c1d1060010704174450104 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 529760008 1250 529758758 529758763
    0x904052d1005091902121f05010807030e0709060f0f090b060f0f070c060e0f04051006050a1202070809120703120c030c021005031b040b031302150d020d11070203 71
    0x1807140c540207035400b03c04516118040d4801c108444804001152035000d625584554502c043e17031a280c2241c00c070060840f420856500d02016104c040e110310307420b5101c0d190228024035414417103c0707035805803190200e0107004a01a101c010888001c402c80e040e800e080e005105003445601204490740b1b070284040072a1240001d8403900724a6010140e16030043d0030095859100d2207a005114a0180001142d50354001380214800354041d100010f80c048180280411103c05071100720b0309140255041200c680b1034070050600320b0380d52401c8018107442c0540501a42c100440464000c0008200480b250030302100c00c1000b030004030300410348680355032a580100e0011b25480010003507a0b200102c141800351450208455000c2c1040c00020484400182940c005941d0780e2401c40099110030f110303581c04000e076800d071094075540a01d0754548908200c54a4000041260031030a8003414041c05403800c80540303911003c00b040940c1e41d2a01498420448a4448603031032541d009011000268030b00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 529761258 1250 529760008 529760041
    0x3011b0309050304030c1203030e011a09100306060f0e0709030c030f0618050a1704080c061b0607020d02010f05010605031b04082b0c031b080904052d 66
    0xe09000030801c201c0c1c2440740c10352181d6000981040c0f50540001520141c0f5108031120900941c0c04220308a40801142d0a89000328541d419040741c3d906248000d191624125030840416004614150707600e542e88810381e040c5901c9007d20031800107003085590030000700d4a83c005d40354600384405904555440d222040203001c050900c02100c140c0d0400c01440742c2c0720304000503041e080d21081c1322480c5403841d990f01c2c0360300003100ca0030243d103800c2070b007403400c40d0548003583c16090103017010510070030902040307801c00d85884407031900b042d07065415000117003c100d003d6070007540607141e007817800305000c4e007510a5500050040e92501d001000560f601a0a4035000b9401c0d0707501e0b404a1500007101c60f005e010b80d8103d10801c0c02640750711190100003080300d441e09802448402030a014102082d5462211080301070b022601090841d99550680c03d00c0488441c030403061710381410a800042012070340116070302c0b102d100f1802d103000107000040000500b0903c0040410700a40b50426100006201 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 529762508 1250 529761258 529761311
    0x1206060a140103090f060b040f1109010804050c120d080c04210c180605130603030e060f1e0d050f071b0512070c0e0c040302150c010e0601030602180301 67
    0x640d0100c1c0c0095070303ca50031010000381c00a49042c00b019842c1490001044180041da00c1a4174126182c11040039500410306041e410040c0181088955030054480d2080240101c405000c2d80000d522640d441c109501e5186449000400550565920190411130081d0400d030200c007090200300030034501001582c03c8203001e40040940c1c2c1009203840228180240c02848003462b0242003c80469400e90111003102c4d81121100225580da0783c030142214024000503000a00c6600080c0107410110001c143c0c0c0204042e800b45440705c854601e07040f0041d824084440c00c0c00005008414100798001d90f40c100006620310134207800e0040c0c1c094090707402019400c1113070368420107240501006002c0c4110700608082da15960783c0300351070002140f104600424a400316504003055004001c40180c5007501e0f4084d042c400c1020b803a1070b03070030169000000c1103071983d921040002200981408494002d600c40c03000540c95440c2d2a18000c805003c146107507000340e14001d484810029521100d200090 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 529763758 1250 529762508 529762529
    0x71d04050703030c02061303051c030905150402150c010605040e03160201081b19180e0705032203030506030613020307180e0f15150d20030a030e1206060a 68
    0x1212171002c203000b40a440d04510714a05010000001d1240c04a12144a80406040f00441c4522181c0503401c03a900140043c05030303841250301000c807003105422280c0040c001000303100c0400310890300403400c1e0300482125500b41d4488408014900f01400303946054078210000d1403c12075840075480c161005030b40c019040210040200e201401d040403110002c007150702c4034a072380b40720704400c02c0c2c084100c2c03850040010304024a00c0a20b90b200081140603114280641e003620b40350140c08803126003000c0c21022210203a00c51000500c40200701c0790300300520070b8502052502e0918100341c10550003c004081c428540040e040060303030f0101d401000e46214038001079507040320f07002000003040300b00c42c224001d206000d41081007040000d40f040440c400543c00304405e5a40000440d21900d00b0946a0b07040010380c6c5e002c80000e0a681525a16910b44503049400d14515400003840d083c000c10055000c1603001e00008543d003000c00000d0707c100288802410a8100940440d50044a5118204050 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 529765008 1250 529763758 529763777
    0x120405030d092412021809090d14090303090a180501090513030516020405010f090f02040b181807181421011b030e0c03011109040e010617071d0405070303 68
    0x18002c84e0318603040c0c6a1301c80e0440d25445080d1100d810101c291248070310600c0814000b44021000203004411051596140303000d03a110120440d1041c1c110700360b0103070305000a12100750300f038071085840c0740104500c0784064840b010300c0c4100000c561040e0000350034982070404201c40e0140c0c00d012780c45000da00d072400e5036554408400102840c4400035009601030305010001801000307200003801601c0300303072070100f0850b40240304407400c9104521a41c3c51000c0180940c00701200d9600039041c20b000c000e86207040d181a49442900051000c440d9007000c00d00c101c014541d8071540d024071070041d104100303007000107060b00d4000030801000c07020301510445044e00a42c1040c00c0c00e40040d0000644100f01415084150b0b40c0500030b400c0301540c154071840f41e105840707043d20f81402140194200307914050320700701c00038050101810b03009040d80c0e09503403154000600300034450f0030114501942c401410705641425043c0a0182c421102c4901c0415000140004a4070120f00c40301100d5050820550303c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 529766258 1250 529765008 529765079
    0xd0e1903020a0b21041109070c050f0706090602060108190c0e0112020432271c09030b0606070309080d03050a180b011403010608120405030d09 63
    0x21120150802504581c0300c1400041d101034990181007401069009421160010351212024510481d000381c40103100110030100c5003406503a094000d5110301d4980c07400c0b001512141d1070244645409000b40e0300c44c2100b0404164402c4001001c0c01d501d101601003540340a003042c3c0e07984140b01ea00134940900b01c0940c810000340c1000304000b0000aa200c0c143c41da03450030380c2c10380a0304c14101a40a02d0800c054411140161b000090b9000303c1800c8240c200b1500d56001d04110703a00070324604814610014540307030308103404d516075858006800281125607001102c00034442041c000001404038400003800014082c2900070340c03200c01900c02603100c0c1c42604003100e41741140d501c9012140240641500d480e0740c56000240310781c4800343c0500a9260801100d0b44000a000020303019104440042c40040c0d005198244031600045c00401c089032601c030000d080240650707562008040003e420010350509014420140b13589041003e0424540340d80206800c001c204144022509030030282e44 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 529767508 1250 529766258 529766299
    0x80903121603060f0b03010e0c0c0613020a0503070f0302030d020c030d03150302090c0706110a0230161119090f0f0e0a0b0c03150d030203040503150a0e0d0e 69
    0x611842913940704540e92445d0349030840e80280110300c00610124005210f0622440840344103c0500d0001d00031030781d60b2680b00c040000c01c0b074012a0700101030600060f5a940c04c111450144c01240c203600011403071403042500c0c2590200c495001d640114101d12125070740442c2c6003400400ca41001f140021981e1005405040c4540000b58800e0002090012000030b15026004047c8901820480580103403440e03100d0380208126900142e110303d040035201d41300d50311142d03180646c0c0040040000d1108100c4139240d0407010300003080046141080081c41508086c82485c0901520350340840c440c864603140180d800f901480101503214840030714100c62030340c0103c480b801115401c0141e103160f28249034031240c482c2400d403002c1d00d20310b01183c1d03030507840c0c02200d001e0481250076500ca4106507043c081c1007510f81e80242c2c203500080c040080c1c076860501107011000c08003c07450b00c0c140740800001007201c2241e00c100040350300c901c01401e00550088180c40d40030104940e01d1204030b034455191384 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 529768758 1250 529767508 529767521
    0x6101d0705040323010b0901050f130f060311031c020604290a0606030c0e0a0509040302031c2a02070303030f1d060a060519261507080903121603 64
    0x203103024100c0c018000901c01c0b4441c0354520400320002070100c80071b00d504103c1034032028000c0715480708a60b102d2800d18a4803905021088500550100b900da00114451044494990007034138102484503200c10a46002e00a54a900304d072900c81d07081400100c14025503d5000400040a5104100d60f00311500058080780000d007000a46014243c5000351103600581202e00c03030700c40480d0410031008800e0740182d00354100c800024004483c0e140c0f07440c0802c007810070050029025800100a40080802e110744085029802600041131107014622000d0740c9030b00d4065450708030441d0444800c9101e40c0440c422048039054a0045030f00404030b00e00c10024000700d400d07590b001d906038030810490507001c180c051164007000410030507a5035071014848a245050b150b13011014000c0000d2000c007414541002d0003040190990051180502c4624074103690b200c1515030242074041000030450740120032603404030400303001c1c60030725800c1c0c15800c548001c05030000ca0081051005140490300c650f101c603 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 529770008 1250 529768758 529768763
    0x1c0b06150c06071107080309030a020d1e11030607030203010b09130b1306180608070e09070f080312071d010c02030c061207090f03120302130504060b040806101d07050403 75
    0x220018180301030058441399034800441d089028a14000030307071000100507203d0358540500909910410b5034200070701c003130051130101c3e204c201c204d0000034612002103003019801c1c0701e403528000754810740c41011318211000300040c0405004200601241111205480c1c240c1e0095030b910f03000c8990b504100002d000c074604044c0e0008014040c425209070030307804c06001c40e02d10004c0203445102054503001511554000e00c1c280703900c02d08041100403112454640d22075070550603201c0d00c9454001014402c0c03000d030721005c0740d5400468200c01c00350800c2e1a03260080d0103400c000f21091039028092038542100c004450600c41c4181c0d174036065481c18040541e100100511051b5550001545560454000d9403800300142c100c04001c0f51100c001140401565004500580d5030256514100c1c042d43c0702001001504415190004194585004040103000700500c0f294407203042000061400c08018400740b1901c0380500c0401400e10b1f55101d00801e11740c1260116100e5892941c01d0381c0600c9a035100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 529771258 1250 529770008 529770013
    0x60b1305060705011e0b1c0f2301021303051c091205030910030c140c070b030604020912102a08180a110901170619060f141c0b06150c 59
    0x102c0482490a0b070188200721320445880070025410003020990303600a901c02080b400381503000348c01161780700e590b038034841c441f6141c2442c000342c019111a0036604141d144043d040c050400074000c0100500024a42c04048a40e819203400c00101c01483c0003214850790b111011020110f4080c01000d0045601415014001620300b00442200400920842201c200016201044012456903081c1180d040002c60401041082d04004001c0c0b150792000e0300596200303900f005010b00380d850f2405021001d140328005421010030082010059503000d22003111802c010090b00140380c0d070302d407203010101900707031800008540d601090600d40301d5400032102643e20640c0340e620100140071040070308166044d079126660f40d984140001703d40103c0d011000054102a00040f81d4034803c0718102001c0004280202c2c1c51039941c1c2c0e031601c100c601138215000c40208e12241c200d20b400c001e0018108060003060045c1c48003510f4403040c0d65500003505440c03250b80280541010a5920015155001d968100303 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 529772508 1250 529771258 529771301
    0x203370212090c01020708030d0b0f12161a040905070201090b01090902010207062a170d050108010c0c0b16030906141b0405030c0904260a03060b130506070501 70
    0x12400424101155807040b80d2081c1d110385040ca51000c10000111000c5000541c20510451100405003034109102038001052050b2a00103550360002401d00c400d080c0003400c00c0e028030b5076103002ca502d201e8100108a04000000d0b0090074840030403582215921140020980c0301c24030202c0c090124250040d2402440c100082059071307040e0700811140340b003602100c5282d50b680d2020f0342c04031104042240c440300080202480d0042c0c519005c11014481c2c2140800042503680000049d007010f103104140301e98400051001e90b80902c076a641c8a0800d0a04a2010207a51781300b0400041c000c06400491f0800c0c0c4d86001518000c5e0402480d0a6200c1750500c41b00c03403d4001c001d40f94070220b54800148100c1f42e40003186c40552800c44050f50301c007401400d0015841404e00c503440c00c018208550000d107801507044960407248803072290500b020b030081c0d40d03100c180c08014142c4901e6002040502010048405404003400c0d00ca41124825500d15071102c060717007003083c01007080303d0707e00d50003414241 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 529773758 1250 529772508 529772527
    0x909100905100e0f0402010503061e0603090d090e0c03041202070b1927140f090f1e010608160e0d0503030a06120b0f09071707030c080102033702 64
    0x104020195070b041c90380c5142c61394848451440c441e400b900c002e80031030380410200d40b0604158001e801011114090315598541040119400751320803950145150841c103075030b49559912001d40001489162790114a600307040034844610710010300300404118241d540d001d1250f000b0b000d2140208040421143c542019400f468407000710100c0e00b500240308004030711643e03450000400364940d1000ea417141d1550401d4000002c10846000d40c0d5400b02d8191100314483d40c50005040c8141c10101c270b4034002c0c0c1400740f803070020f00304031300d034010a0420362400600c0b215510505d42c0d5844008065008400d05021405a40344400701c071072150042c0000340c4c44428010b00100071401040d110a00b004a19038418200c0138000700020020101080da0000c120f11944225881d90480d0505040e1071b480e690310b1442d000d0401501c005002207800c0014108284146103070742c00c0080000e24003e40c5140741c180703000c1246102d02e103982c4103540686480d01c0308404030540720824404040c24115512600708 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 529775008 1250 529773758 529773781
    0x180307021302130830031b0a1b060603020f100e090c220512030406050301090203040309051f031d19060f06080109060b0a05150d20071103060c0909100905 68
    0x40c684507160410b681101a50360035080171a44280403409200700704040c2c42d103050005900c01e01c10303141001070009c0021044203480340444100d520800000580628602c144811080800e00c3d091107555842012002982c101c94071022100d8201c0b0400b01c1a60383d070200c4c900c1c0b409411001d40a42012034420304400305403d60410554030101c40320315101200c0307003140750b42c0d1140307004140024806200401860078240c008c0d60300701d4801d060410301242c44502103901149080104030507040c095220400c204d80501c58403000f10010071007460030801d42000959078600301807500724103503810b8042c0001e018250b40001384191603000180191a580c560540c040c10003040182d68891178910a10710600c0e0101d03500003181c43c060306028013100c1b5004280b500d608603640c04036090791100f2195a446054101c190132180c3c6800300c031741c1c4031016400c25802c1a5a248000d40c001c1d8014001e00c441d181500c0c0558509134004c8400609596901c040b03d61115025404000024101814040f090041 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 529776258 1250 529775008 529775053
    0x1807032d05010503030a02030403030e04090203190c060305010b1b0a0206031515070c061202131503140105130e0c1905120606010801090902040e151803070213021308 73
    0x40030400c0c0590b03600d03501019180d2040001c0c1c07074050303032082004100290040103240e00480300240005035a001c02c0d0086402d10441540203080c00b031034240c6600812480035405406043c4600d0100640e45c10b281144280b8424003148180b0010f2107070007421984001c114601d903599001d0070380f580383e0a2000500c164144c1c070170350451180b4800c04100040072110410b803002250003001c84003516281c842d00741c0e13040030741807540180d442d02002400703081c040d010080070003420301c07031007130780d201d030451080181111428848184480303480380040142e03948907903a02c031103107100070320018a0340154185585014941041c06030000b401074060109511200b150104a403416120400360403101c200c0151100e004075171070b5001c180d001c401030000d01c520343d00000c0028070142000500d20303181d151483c5440030520084821100381c40800c01c8010440006e0955a0940300c02142404010347c00140a0031841d804e2038900c03a80814052144445900c50030007c186c03074019202e200c0a22241c10984114 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 529777508 1250 529776258 529776341
    0xd08060d141e1b01080405120a0504090f150b030c0705060f070216080619091e0204060b070b040803040f1709030d08042402092706090105180703 64
    0x801d03101d49203882c101085116a001c00000245034410401005503a5100007810540300c2d03110340f00e02444208007400040a0079034094865603100c2d07140010310810f50704650031a0b02070508003941c051001180981c140140c2d805900d4080e20b90781d8540ca6280340d801029805089441603100f0301c40d0038000011014041c40d0300d6400d8490303243c120384580450070381d18070807154903502001c000354010460140550f841c542c03840d4041805242525000401c0320f03981417413109282c29a00302000c500d0309200308002404610001c9040c440903440789031001d000240043c0001d00004005070400540e007118110030b03603000070641d10201d07080990304100c0d000050018040c0c400d900d900744440703003c1c940f620701c1107030320040503101c1c01c81300411100b42148140000300096028071506800340c0c0c9041001002a84c0305d16442c0e40542c0a001034202000040d00c42c40c000c0011500500ca903803030b806142c820115490340c1c0e002c040d894602c0c04070f0092004030721000d40000091720080322209c1d000c051415886 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 529778758 1250 529777508 529777543
    0xd0e03060a0207020d11041e0b03060106090f09050603011503050304031e020f060c0a021e010210110301030201050c1006060507020f0102060c0901111e0a051606020d08060d14 77
    0xaa0304140708003207200b2450080d6216541d0340243c00001e071a502985401200540003181c6c0d103100036411088849000c01400804d03071251040107140c10f0800119004011a00d04001001c0c5054040707011a1620b00501d80c0981d1210000340b900d8900750840300e5003015a000703001072560742c0d007016910f0380c10500040312a45500c10b081207107048010070305555507400400d49101c41104408101c3e90780c0c09406a0440c500840984202603580c1c40980f400901d0b01c070390801092414000020b0506440c440381c0131303503689004000c08049030407a09880c1543c0c0d087c04c20b60740d101c051041d441d1030000f011024003806800d0031340110300c1c02c0d805005000910b100b620818045d50000d0300680e292002260031b40003558060040320301c0c2d584640440c1507510b54440903034412041003c500f0100381c640c04011000c0340d002d605040100038041041c460202c0c54007106a07415410180025103601c40b10307001d03070104000c401c0070440c2990b41d040581715196000742c52800845440c40710303d807220310b08585d81d005c05 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 529780008 1250 529778758 529778761
    0x1203050c0f0d0906030b01080f15040e030315120601150c0506071812020d02041107050109080a0818060703051e040f02040c051c181406041709090a0b120d0e0306 71
    0x282c046d00981c1c0b5030b840c0c1615400c0c0b0f41d54440807802c180c958001e202c2100c00400d20480400da40302c0d8490441003c80400185644e80b41658030034010405004038a8080c1000040c540141d5002042203410b440c1c4910280503922400041290030183e01c1c0d40207030842c003410007402a80c5420404480204000401448161380d0796480c244010302101c0c0e010350088138031854080189000c2d071140c13000321821100349060030b8403070316040d00b11a01c00c01c040340c00720300005698001c0e60300322545560140c2041c0510352010030050741d8a44403030015100c1d806241d05d41d00426460f00700b20404804280458101901504c0c180c2003404000921080c142e004501d0103850400451280085031815072226060541e65190aa0300303100134200d0480c02d403013510824882100103011450340c40008000fa10007046c4504007800d0000812100d204900300c03522041101c1d03542a122141d209034045246400083c007049281c011a04510300e50160b800c090181e200c0c01c401c196000030004400c1c03282a0100c80d0356 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 529781258 1250 529780008 529780019
    0x181e030d05210a020408010f05010e0919060e150f1e0106091a070c0303080109060e0114010509030a2306090a1110030b0d0605160f091203050c0f0d09 66
    0x442c440d620001c901d02d4810721080e0b2601d407099001c0c43d0401c0302c0b140d0051601d5610b00b002c500312030441c002e070090f05031640e0041081c403030110803182d0030104000c05007040741c0313101c3c1c004100b40c40c2010004051170f85540c0b0b050f80034001400307042a400c1030300a6010041c94803541c0300000b420101c411010a462403d1a01801030f00b6420450580d8015207455400a04040082487c07920600205403000010800d400014000144c440000c61107034442e030446506220085044d52800d4000480715040d8100410a98452640300c610a55003802c0031644c6020020202e403c0200e2400003612600e032000000c860441c0910001200c05942c100340d8040361a0b1510442c0c5541c501140501a1841c004403400240b030440d1134044090301a003800144031803c40003042c0658010b140030307a8400d50380d10400c50300c001018400702c0c0400c1030b442c0290211002810107083c1520501990500c03034420080941058011070480d011b9240d58003c40f00a0726800405a90341c1c54007024960025011400c0083c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 529782508 1250 529781258 529781267
    0x40e010509071a040b0f1b011a060304140a050c040b0306010315020a050c010c090513050f010311030a0609050304150206010b03070f0c061401061d0f06181e030d 71
    0xd400c2031000b0345059450b240788150400c2e50004040d030007403c20003000078024884002043c10701c803840303036994880d0203582104600e4103401100c2c1480364108548114a4000c00c0d0040c01803181c00c40d9615142e4031241095102d00c03c44e072082c5000c62140f401321200f0b11600043c0a1603641c1c080701c060001c05948810301d0744a603420704c8000c0040490500345141c0c8450354020705403138000d40c03a10030306103842c0001c80c60944005cce8079800042010194103000300d0030031480080d80d0460848040c0311605225084805200e414440a88081d54010032040282c4d810b000d2043c0b201e810200070300c07503040e060030301d03076200c0d0300522414140c2c206605941d07a0350741c0007040711812500e44071074460461b034034031000b9150718110303035400f804001d24030020340002401d5100e68001d04204100ca12910341c1010000340c4200003141106030b80f4800c0d00c40b009840e60f20804074601042c4181d82640e16103202890f56418988605845030380301c511210103035030403a608440108000401c800726407421120101c240c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 529783758 1250 529782508 529782511
    0x12050a11160204110702060d05071e080907140108040609021c08180904030206160903020a0b070b010503010605030307030c050c04050c0a09050603191d010c030c08010506120712060f0303030b040e0105 88
    0xe4000a023130100c44081c0d40660312107a804681030605403030141c00211090368171940d810a450101d0314440038012003a1301007181c403004c3e0030008042c0300d42817400e02c0084d10104000b000140007030b4a511001003152500c842407441900c601140905c0c0003100c2c40c05802980108249080c2030507040c60b1412645040038149000d60342540140440e030312002112140440b600100909001c035080340000140c40b4202e890b00140b10354504d00e900e89409251a500642c01a4440b030310907810903400b40b00541e008421030b903034250f06041c10b04d4580c0081ca41075042000700421540d019140a003001000e00a41000b040c1c603121030368441c002552210100891400280c400c944031440d004088c90200082d6880030384a10b0305216840d803005d00d05021742e0b0942da61078404500183d21032001c991080c0e004500b9601510f8100c41325030800d50520800140500014044420400400d080e51003003840f0392b1000c0c024051031b2079401652512818040e01034040c1c040c205000301c0c0f8240000c1c410f41c0b010b03c2050f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 529785008 1250 529783758 529783763
    0x602010e2418120301141903080319140c0712020d05120c0c0a050729030a11040306060306060f0b1204030f030f020d150f0612050a111602041107 64
    0x1089071140001444951000070307402c0c55900c03c40040724403050001c406903000301a034038500e941c10511320b0107100c5074a00303148401540701110042400011020710a80307600c01c00380050b607246070b2001641800a01004007890300d9000010042c40006c03141c420082000c80d0113846101c030100031940040b40c1c1c444e003a2400c2c8000a40911030074122070705200b001d42d0040f010414035428205600c04d1309081403070b141401c554170340c0510400c200301492140034103810120032014544030b0010164106003070ac0010010030005555600292400143c00d00740d4020715004101082110b44914042e8004c20660040b14241010b0321000207000001c5002c64904049400f0300c2100c54a071950241c1d04511066465000d1548400154641032802d1000c0d1442900c4214003050a080c0724005030025545900b0403810221100c4082c055180c1080d05503181d0746201a0018040e6103802d0316100800040036060713081400004c1d519081810100304510107402117408200050801c14a901c0621540031b00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 529786258 1250 529785008 529785073
    0x4180c06140f0703090503060f0f01060c08070807020307080a0b09101a0f061c02041409160e011b0302030310091b05071b0e0702063318010602010e 65
    0x10342d0700342d460003001d02009413103410701c0103009071520300007420110b0495025000c034500e8010480700a040a04140c010105c6e4100140103c0c12902ca6003401d00c41c80c00c0207410580c1c0044d404045480c100300000041c00c408081c3d81e140e00180c90012200c0c60140c5200c5001d126040c00ca0411105901c078500d04d84100d0410035100c0211001403140444525041581c448020f000720b6020075401880d030076006114100040c1d070340e814010f03003101c40d400380d107410350254002c0c0702045400002c2d0141028182c440342418a04d06895400413140d070105802c402c40c00101c100120000c254000018600504200c101d000c6c1558680b031212040780c0703078160001d849084120322428824040d80041c203030140141070741415541d403a10882d1f005042984211080320702c0c0400c11030303000e0741400352300d400404010b158440c0c5c10000f10040724860592469450300c040060b0003a4860391007040892050140380c800709942c0d030391185c000e40204244c0d0000403641c001c15140441909013081c0905440741c0c0c2d82507 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 529787508 1250 529786258 529786267
    0x6010f12150e0111220f050d050106050303070c08011a150a090902040e100f0308090f040f060608090d03110a030908040305030304050a1709031e0102040504180c0614 73
    0x80c0c48940c1c103600c240d448000c6503601c480c950004000c1c060303106142541d244060380e4800000c00701c294a01c0c800007049801d040700300c060080c1c2003130401c1c45003110021110054000400d08007a401400c441e0f02c036a603d44400180e0340300704914001c0c80c0d822102001e008210542c0399091a03022040c284080c04e5100c1e440000180340000304c0360140518421901c1c240341c88940b1001c021040b0781c4690005885007021208000032209240306140c05840421030381c0400b64915910417050380254141d10b80700d000005005251501c60b94000b00707882c074103040d040c084c2e6030340c9100c0502044003c0c0c0f041441e0b4050044c4d101442ea0081c0118807803041c01902403813070104040c401301d0040240000441e213008003080b00101040017080914051401303140a8a9101054900300c140100d500c040d0580f240000d01a840c550313580401c02c103c41d84020182a404000b403803502600a210740d400080c1d01901d00b8588101d0760307044055081ca00f912581121084545408096940d41101652489664020071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 529788758 1250 529787508 529787513
    0x302100201020c06221a2505040902030c09040213060206070e03030414030a051501081c0503131506080601180e1207021f021c030605032e02030f0906010f12 69
    0x248030642c01d00f00c4149165030010140c0d60441d0786d4041c00308099491030007805009202d609407500c400701d021400448218a258001c01610354000c900c50b0380022a8040700140e080f180300781c12504000e0000b070085540f820600c960001c01c01c41405581c0040c403c603800a80c0d800c0c054200041c4a020080c000c604052034804100c0784401010b40d4240c140c05281091400110308100c10403501041040074001581010291894061a50000c980025034019105070450b00201165000846e1483c0241d41c011642820b080081034440862041c6140401c0054150000710360035061b103040300603a07020034505402c0b00c0d0a907000030744001c2d095007001264080d0818500010000c0303a101901002e0034160401c80f03500e842900c0002000035801820342075007034601c822032511000045080c10800e090802d80425511441e0450200d0401c0e0f0f5040d02043d505903542c2c200301020680e00c1d007903550b4580900c0350b812144041c0c40d082c1c0319119590010801c20703030001c0c0d8142901d920300300c107644121654 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 529790008 1250 529788758 529788781
    0x503120f0304020d050307030915182310020f06010b1207111906050f070305090316030201020c030a020c120304032105272b0609020102030d150302100201020c06 71
    0x82c00407a40702005a0220380054814806820300c2e50094940302411445c001c07240035084c010070310520801c81c0f054102c40c40400500e0341e003001e460600240d13401070030300d22465488035440700a4842d400030540b030660007555070001d0072032109d5150038181c51003a60b0302e002411041c010b04c1151185609503400007801c151160404022102c2c941088500a182039401603108202c181c0060368401d807101d04200369110031a14294200381e15180030072841c5007041c030054581c0030340003078036848088201c000700901d4400d4054555144501081e03950b581920b25019543d0303140c0c0e62400380100024581000c03c580017009442c2103d80251600003584014400c4403040c081d82004241440000d1010808101c113050301506034000d0414804c84500d20b45042008038a074203841500c1d4403840080104e50200702030080418681d02040101d202d4000d440103074110b014042d81410400d00d02422144036000501c1014101c83c003d032030102d06040511000ca00781d2140943c1c4034a103034421808140f524188 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 529791258 1250 529790008 529790011
    0x18220c06031d0a080903190b071b05100c090e0a0605012003090103091a0403020d030b060703021b06040e100501121404030c0503040f12060c030e1e010f110c0105010503120f03 77
    0x6e0940d1064504c0c144400007421001c86d00781d584610f4501001a05a0032040c50203200e88100d170602100026075842c0340d170300c9074110880e011503034030703a03404094083c06842103002400e924583c40d205460603500040040c2854401e050004a04518610084d603c21441241440421004d5440c0003c0c802c0154007511041104035510041d004c918500d51a01d400394074080c038840e41c0a88001074400d94000d0513941c9210300c1905c07a079000c06c10b240000f600080c4000c4031746013610b0502d950f111401c00249950080d84c0c0007a410503e60420404e406c007035440e00e1020350300c00b62280103c001c103035540c1808559641c1d11800407007a0710800700307020900034505901070502c2007040300c2c07900361134040d041c01010f220b0f0310105000120100314001c00040b0b0007100c10701011460100640045440c8155864150280038107010f0406504901d28a000390420402680c1e139003400d000070074644010b0304e0035500400121106520b418004590b514000c03486451456480a0312800c01a03510007a09c403c0d40b0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 529792508 1250 529791258 529791277
    0x1206030703060c0206040605071103070b061c050604170f0909131401060501030b2709010f0507050307121506050a020304030b0103080309070b03040218220c06031d0a08 74
    0x5816000000982e95008200c00d8101a5019100300d0602d4581241995400b8004500707100a04070b25070340d411000003e031411540c00802440083e122040881c0700700000105c080c40a814100b00803091010006050340114481e080c4519049041900305000c0d000b04851029140c03800c06c03c2600074a01140c40c2c0b0741000c4030400c040749075400c3d50f407020700d1103c000700b0b00f0344141d440c0d0004000e00d40e0944142d240c00c0000b0381d03d503124a200034a03911303040c2c1c0030381c01041d5000c0103620200320b058800b5403010199075650300040205080411014119410484600e00004d403a40710781c0c14144e400e40a5240820100200301e0010750a003481500c0c2c0c2d07040402c6079011440144000008144500075090080d0300586141d55a42002402282852060f0b040042c5a0703408005000c0141c460600c0903002100e12100c103800d84d1205140440640309000310f102c46e00a644070030303a060000099001d421101507803000c01460900c50700110b000e80051320f10400e0743d0402c0d84d00801054001008052a56 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 529793758 1250 529792508 529792513
    0x5070e04020f010809032a010e1501030303090f060f0f050915040803130b0a0f1410031709090703140702070b090d051216020a0f0e040f02011b06020c0613020105120603 74
    0x6501c1030309103202c091a1f4200c032441203602074a4803d4100a10590903180c218034041c0c49107800a40181c0844007040c40000c0c101030703641034040180040601017005080c0e004200340714042d412000c13000033705022101c1914040c03500000c9801c440300051030004002305045024040e03515a112000030743c000401c0c3c904400c00d050310707207000074a541c482d40384900300e041360008030683c84441103030489039110300d031640070003045003070000200010005408507680040c0d0910a86081e962050f16070099a1000390000fa00500307112015030160010b8041c03403510852081d842d980c651049958405c0c40c45086a1083d00700001d0446080803d1454071701d1780245c0c104c1d44840d80f051b80c2440700b0b030300c40544107071034026030100d034400c40c600112985c005004409018502034102011001500d1000d4070040c00030501d0421a4210b901a00240ca0b4983c800c100410b81900c00c1d0030304901940c8555945032590207090001100300c0850220600b4041d0180d5071141411080042084581c0000d040d240d41072 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 529795008 1250 529793758 529793767
    0x90a0507020c030d170a05010605042c010902031509060a0b03040f050a0503040f0801020a0f051b030f04030204060503010608061f080703060911010f05250602030f0405070e04020f01080903 83
    0x162400c010240300c001c2c495840c2c0c1e02800d105e02580c860040e01402400100d401c0100400421340d010090360709807014001d61403910174001400d49214289544003c0280840c1000001e8590f620360146205860303d50101c03056107116000c0201140007114180da01070000c1c00148048440c4102856000b48910300c0d4458a00d407541301d2924100500f00b00711982d900001c0c09004002c005a444001400840300035418000c0300c00e0301503e61403041c0691020000c01046004100c40c54042d082314040d0f4075001e6980e201542078022103558094042a401b443c18044002064141442010212989440602519158901c1e01c640c64803d00c03001d0301041c00740b80004510070b401441143c1c019841014006100105850110b902e00072002074581480b050801c007500058003c4221034800b8200e10340e23300020342c40e070b00300c0d04140301c5102c0c0501030500c08010050398513122501c980c00750b4040d00449062aa4440d1030180054040354000d4100080211211103035005803030181d048880d6400380c03400c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 529796258 1250 529795008 529795033
    0x6050f120408250b0403081f08010b0a08061330021b1f030e03130b07050f2a0105040b1305100207060c1101020a02060d0b090c09090a050702 62
    0x104402500e050364400307800250004030021850480d2082c0c0650361010a1001c401d8603010392a13a802403010f01408021400903120044041e84403080d07613451440c0c83c26640d242d41c0524002c20455003181e000349440000460980f800082c641d00c07401d1001092403601c203a070356416008019800404213520700400a50080c0310320141c105600860b5030380207241c00c00c0310800032915503141c0711a0078001c0780c401f2611484200058400001d10304030782000304618100035201444c51040c000060b90f01c0402c518040707191002c00c1d0081200b140a43d01b241d00e041d00640995444000c4001940030f10200e070007031044242000000420401e4050602d1400c01d075440c02980d02c140c0c0301e580101040c00740005c003440030f4030b0510780c0c8500c9954180b000b0100b0a041040140201d4a40400504941c8851241030300c1a0310030844045610b80c0640b9441d00c500780d40c1c840801078200d81c101d0920a042c6000011036400e10002600e0952600400c50b003500d842d5244c1043c02800c018240408601038111803011 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 529797508 1250 529796258 529796287
    0xd06020f031e0609070f0311041203050c071a1e0f0301091d010501060512060a0b0406020f15130b091627050402010e091e042d020a06050f 61
    0x480c0c07107418294294891241c9003000030881c02041c40d0b02ca0800082808600c0d83c6c13050994407400540c0c2000140350040d02c0d84401c82d4012035009006102030f103501c81d000c256021002d4100940041e00703d510701a100e24000c04a441950400300c000745090040a4101c0075011048900d00940e95401d4130301070080c80e0a4040d0b42c401d812505405894045420300d0041e210414528500c40318001c10082d410001d0003065071003512608030303c61564201041c10380c0d880071201c00062240400c1c041d901c590b0b402d030107921040200200d10050040c40304003204045400d208030f10401242c428100c5000740c0e556102e00d5448064540c1d100c51096401000316045409404005400b200b6181c8110341e600e416030840342040700403080c0c0294108010f000043c1d80280450242240480d044420b0380e41c2d071001d0b192004401c1c074490000d0740301541031100340304407214010000c274038150101881c0c405040b240e51540103004002500242c1d920400c00c0203620400140091b2250410311a1a040d080e0702d0110 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 529798758 1250 529797508 529797511
    0x190801020a0504080c010c02151e1902210415030e0a051e07140418062c060609190b0d12090e15060d0b0301050405071404090b060d06020f03 62
    0x5000c00da00243c148030a0800300708400c15404246881d0541d0725003940450b4080305920380071041200082072171100351140b040c0101c003003102c441c100c1c0e481d803404100e41700c40c0d111064460000b5024109210203a22800c081c0c50460100d01d58440e86040c0c50841080c00302d107990b9850501309541c0d040d8003c502007003404204001400b580c014010403c00c05110003490380c807a51680181d5212401c1080344248510310b1025182d421600010694800c140c4041c0c882041c1200500b0145003025880611750951500c0b2410160300070818107500045203036075660300d0309403031040d4003021800c0000c96000300d8071b4214a4403840b844020800c4103403040490000d07070f258101100e21200a100d00c42000340e10101c00001400c40100c0503200e82007060341100b204040341c44140c05040e00250821217905075030440c5103682c9018000b0811460142085602c0f42d070700e805620554440420030b5140d500c0c290154000041c0c0100b03083c2d0050302d640040118001421404a4040382c0a00c08107840100305000345 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 529800008 1250 529798758 529798777
    0x20f2b0201020106081506040c0215040605010f0e010302130b0a150512090721030224070e03010b0310150b0a0807080606040e1614040b0714010b030c19080102 70
    0x100062194400a400d6a4440d00005165404044401607055002c6003c0b500041e064900003460b40080800300c0c01c01c2d071195081c441001c0207806000c1042107076401241260b50040394400203031744600301c101c451036007032001a610030400e860489801c10b840d440601240f200401c0f50070130650320250300c03603603081c14848000465408141c4140080840b5803c0d5800001d035400b41c07034098140110748000f11444500000608071102c000c1080500800003100403036503401d006104070f208044031000c210001c0344c00b8000501ca44e50800803a0805000c1c02443d010002c0103050382e01c440c140384c02e0007040042d42e035480a8000c80000641101004010081000c2c0340ea18480d03d03140c8050050000200584164002c0d1010071003002400e641005d06074024402006404594040441c1128907180081d200410351200160001380340355250014103080d48100290f86039081c1c070004a500700d0310411240c41e00340e00045c1044003140341c45620605480b945c800c2c3c014aa90721602403908a80242204 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 529801258 1250 529800008 529800079
    0x30c16020a0b12090a021f0201022a010b0a03110d0c0e0c030601091e0b09040e010614100509100822030804020117100e09010605030604060c030b03030c0307020f 71
    0x80c3c03018078404018940d129401c4402000100304903804180c5e00803078a409200791940740d2001421443c400e4049841800c243c611300c030514499160b48020715003081c0400702c00f640c80c2c14000380c4c080c2445500e040850307030800a0248066490400c0c0501c207801581c0442e005150f40d600450600d0030003114a0282050758001c9840c2c1c500303c4000342103500c594000408080703044800e842030820072081c12090f03032000204191115245000300c0c4c098206541e901c4c0041d4200359000c601d502c4000394540d6101000c64500711070000c20242500d040c031038001c001d074215551814180c50140200e1819400c644040c2002d08480840d80000302c1000d40b5043c1103002646000c00e000641d1b03031061640311a403c07403014070051420524a0002000f406104000880300c1c80400580030b200d0a42c8640010035000e0305840b0035140c640381040003011986110070109141284000c0107080000590314944440d1340207610b055100d0f000c002038134404048260b40300c80e807010328886da0002c44103240c0743d002c1c5080a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 529802508 1250 529801258 529801267
    0xb060f0301030f02030f0601030f0204020a03180b0406150b0405040e03130b032a0909070909060801050f1005010c080904020403082a0d1b050109080412060c02030708030c16020a0b 79
    0x105403d1006e24070b02c1540c650310000c010701c00304540407a400011541150010b80e18a040d2005070080c058100c817100001c1c107003115003800e00c42560034203403141e13204003010414014501d1741e00e80c403202e8500945a00c000240800c0c400d0781415841038000496540480e03050004850782141508519000541510b1021003480b45016025481a4071290412034901c03540030b1000a60400e800349500c454400c4401c800032420441c0102c021401030203444005000c81e6444800389406490306880e038072000c249000000c0c44034414418003105642c0142e44070000d4509a8a41c1318058001c840920392042d800c10000000950080041a40c1502842c480803c5615152030f46d810b40c1c40b020b10901641c000f9500341e6841035000c94a03007020314142000000c0d4548a0070240d0041458050041001701d0001d40440d240c10400c0d00e4851561150301c060003c5051161300b00e03142c1c02501030080c117030f00050002c00d11890017100605201002140c00b611460700c903400051604015038041414140c0004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 529803758 1250 529802508 529802513
    0x50c191203060f1a070201110105070504030302060f0103170c0c040c0f02010f1b050d02070f0303060f0b07030f0c0302030c011a0f1507020d0c0f3b0a0b060f0301030f 73
    0x502c80c020045a004a4011490b0100c0000c448444002c55114240002070041c210382c00380790803c074980791900007041180b802c081d01421a9000d8001079025124010002d18402080607115050365840000301020b41c0c0c83e05085504d82d0411103003007140740114001c0c0340e5035450b00d100703840344440359680d20340311059104400f0f82110b10b898880e02e0018205421584410186a486094010709103410b940d00c008089004c402806a840001e11014000d805101807592540068055035100181390303840302e58802d0190501d2182640041c00b081c45a02654007950040d51500d6605000307005484c500102e209010382103d58040c640100e134034210070301110608007801004500681991b00990207039a42c40d14070254010203000074030490f101e0141360b04000010007924000c1000c04440d08010f5113921f51301d10400016890320444403040c4071280c0180403204030756411200c0e28105454a521100311500c00340c8021081140c01074070070041f016096014030007c500035806800544a8203d292 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 529805008 1250 529803758 529803761
    0x1a07080114121209060d050108010c030b1c110a050612090c100203071b0b0a0201060e1e04031808031b0c0108010807061215090506010e120706050c191203 68
    0x4010300e805208941a0758800b480e000440c078020b02580d010303240c1c85000701c0f40043e98038800d00010081c9541000c000041429054026005c0c8080d44d0320180300c44085102400f40b0716002e01900072250b030007110701601007061016041d0003600040d144c22040d1380c880002c00c0e42c0f40e006844203031405000000f00711301c2d00d80500a507255584200d80c58482c0103070488000b9500d00403154050310440da07886044403200c1c25154020000c289010400f1f0b100c002c61000a4000c1c030051184180c0c0000200008600079588500c01148041d10000b0035203980f61074400300d403001003100281d00780820070b03800425050800c201600741040c0d03001c480d1b86002d036034241072410700d800741c2d0610b411b000740c0000602084c0310200b080340680c4c0d00c03854507883c3c06001081e56806481e00201e0408041300741903003c154a0800c1d001136100e600c00ba00d0714220f1030209414006600242c404c0c0c0320b4940c0100c9014004144180002d2216030841022113504510f041007900000d40c04480880d0912441e80c031342009030360503 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 529806258 1250 529805008 529805039
    0x507091d0705061912020d0606021b0a0b0304060e0a151e02030115050f0706060603240e0114030f010501060203120702010b091303110a030306090b0a0518041a070801 73
    0x90f140b4905011864400011003090f0341c41503c244605c041e240e103405540c50741a215495040c40090041556400020b502d0b0581b5134450744240c03e03c118485110b08021003800112520030130132510759500c4d61184002000400c50a0a4034001d076402500072801880c0148451103d07030000040c02005c0401850326240d90b0140358005074010b000401c2242004192238034804164109241e8440105022100c94418000020705580c43c0c10004603c2c01e505500c5080c0b06016441003200c3d6801c10a204102c8424520400c203009103d40300500000d0781340342e10481002006011207400100c901071036825100700340c2040d001640042103000a20741c0505080f908402640000c01020170464081031100400030a2518070103140c1c02580201031280065032415810041a0b41481c0502c0c81d000700035205500c01d21038202d04000c90a08030b8600600c401007102c000900c0d20b010b00a03c00083d03d09030000800a441ca1342800703003855000080079514922503409952021a00d42c14428000d0b503d006 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 529807508 1250 529806258 529806269
    0x112205040606020a0c0509091c05040e15030c0103020a0e0a0306020a080c13060f050f120a0e01060608011205031303060212070804050a0201140c120910050703080a090507091d07 78
    0x1002c484c1c0401e100300e01c5081552410b5441c999640d0b24403500c00d15004100241841d80e2450111044da01c0c2e47c000094800d0304c0146a00c4444c548495009213400000051840ea05811400d0000c2556000b9401013041c0d00603803d00d6540d456090001581c01c2c7c0715940700f524450303000100079142641c0b00140750380c00203c005066051100e40d410144900b24940105d074148800c17803150320b854a0040080d00c480b500c08490f0b0551310701024170920204242920300c0000607040510300d000d050f5060180a042c1c8025646603055a0300e010704803050272441c0781059960780401c011171449602072896900145005200161740c95078050b100c00190b00d03004081400700310b800414840064804541c4544490b0240707405040e00c03859100c1c0503071074400c0c00b82c20b43c00b91003007801424541c6000c1000e40601c40040399980c00740320a41406407a14421000d000f000900d40c080040c0e101e054a60140020350b0158080396042625000000d045a0040c10301c00300380111740c001e034295000108011800303881c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 529808758 1250 529807508 529807513
    0xe12010e1011120c1317070b0c0c22050f0f0a02030f04080a0207081906051b0412050c040f020c1b03030f18090c120f0106021011220504060602 63
    0x1000070304a10000e02078403000c8400304112801180134400c0c01420346001c51400800c085207165240030200c0c0341110030303101741c165008100c800507004c41c1000546840c041e950024020010220080082c102100d10409c0700d0700b00401801c81545500d441807520030341c080c2905e610305040c041e5075455030b26030040071503c00030700400410001032011070809401c80d6115850a4a070b0303100090a070b04080d03031034001c60700b207129440c02d107440c4103499500c0301d401c1c4e030242000304103544940b040c05a21854401020748607400410040002c03c44040026581074014015a152040d280d00010309542628800c81038171900400c010000510510541402c04580f00025289107020760209449000c1c003050022110808100d461f95003840555050039008014018600c078542458201515042807901d13450312103510000810204d40014001c0c1603031059002044542002400c3c00c004d400c9a1548414925043c015042c400d1130440c05641c11082080744000741500300f10a002c12510123910400071503 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 529810008 1250 529808758 529808771
    0x20f010c0e13090c060302071e12110c09062215060e0409031d1507050610050d0302030702040c0302040e1801050a2c12030705070515090318010e12010e10 68
    0x40d01c05094101210b1581c02c0258554159080c40a181c00c2036a027000110400c40e01d01108011700c01100d03446151040e01d0f0142051102034465954039409101950480c0e04540800ca07145000014805030102000040d24800e4015039400d09440c5044007488006400e91414424550856100744000000303035820010400035440040540e1140c000d6014010400c3d0003860240d11034540f16043d10b1002c85000c0c0e507481c920300d0042c0d5a00c60489001d40c814802e01d40201e001e24040141405940c0c0681c01103042880325020007001b00305009a44013030543c20440000c0320030407a04054892210b5900c00d030704068902c2c100380d00f034680003003092510915003442013201d81c000310200b0442c80c0390b048501d094034405ca040c2e14074100719003844454040c0c012003003051050f4460010402c1600c11000e039000c2d028070a001c0c07240c5c803005803040c9519401c02d01921070b030b20b07414030094a14100140b44c03d020394a0010017280e409080b4001c1030b54140d444070031402e150481004010101403c940c0204081c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 529811258 1250 529810008 529810013
    0x60f1b12031e0703020f070c0f090b0a091a04050705070201020f03091014040b0f07050d0e010813210909050c0a05040506030a110d05070f1d10020f010c0e1309 70
    0x300030405204610104802c0c000c502031901c00ea05a8032214254852140d4561440c1000000b00689100b0303040600e141e41d4000c03440110314050515a002e001e007098030400e081c5035550001d01015284104100c00c071507011650f580d45c50003501c0c001d85441e25481c0d5502820b0000904159040f41c21a541c0d0340204002c10320340c0c0f600003e0f011201e0302d6107400c1e10440c00505404880780300c0e0380e101c2100f824022460085401d005030040561900c5142224003002503c1415500d544403503a1050101c1c03280e10024412454a09000b151144504401554041000d500542c80942858000c0c00035900c1380e01404115120322940350003010410b203070b40c105201000c000300070344114092240161800b0010072030703a003400d07040700411080c50111161a08030745c0e070403800141421200307807000407800784814000ca0b004598003540040541600034019400005010340000030070700c5141148030348928044400390038401c00c205441c4503a2140381c408004800c000540404210f0b41149030300c0c01000400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 529812508 1250 529811258 529811281
    0xf02042c06071d060f0307020c1908030f180907020607020d0c0b0a090c08030304080a090504051b0a0207050306640c0903030201050109020412020f060f1b1203 70
    0x1200300e070000f403100c2c07101c800102140150144400606030448044248100160081805400c52800740e03000c00d03005070716007819403041509d44170b6038905400c05c100c28100c103005440102030b40c42c08038040207444c41e510340200768402400c86d629170060300a0410301040316814010230301003c0043c40c20305450032842d01d91070101c02020342241d01c0340c0d41e149101c00800003040b8140f0000c12044068035164034050610004650040c501c1100041c000007000c02d5600c0c3c1032151034006d003681a0001c0e4290404044003501d984280142010352140d10301c00a0030340c2e81081914810102c6680c000e00400d6400c00080d08404a81e00d0140c605074521280540c44624000c0c41086100c0b03046d00100308054000a4917504041c40a40c100041c00d00c000740c80c1c03d40d00200e5980440c0e20a03030013048140e9039030429400b2401107019005032000e006452001600c1d245c144920701d0f40000700315502d06003860358500300540c408403010061990030030407035482000174001d15801c03440400c020b0b45149000001c621 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 529813758 1250 529812508 529812527
    0xb0706060e09210306030c10021f0c0c03032007030c020f04061503020d1e0c020606032109060f03130b1506030703150905090f0f0706020304120f02042c0607 69
    0x2600c0c001310005115a80c100101c901c0414040d050b2400640240c20003511240c4519000d045500050400403510030907104040032855665105821030700035507012400381c01c0004200c0e010711641c28ae41c110795420f00c0c0061545600c0303a22145002809441405803494501c4000e44c41949402420070001c1c0e01850400b803040354900c1c1c0140d803000c1d0040c84c58020920004000001141d102040c1c1c0349803c26840014600e600d80c0032070b0250b5846000b007680c0c0d001d070705928803401200c0982c101100000303034004c0e03d54400000c1c066814851440b891400e40d030001c17500440800030840c50282803141006d6025000604400c00b00c4e1100600d2011400510010302000d0400d0b41c0d0b85004228640c404051802801c00c00c01c080c41242030150301c803951420202140c40d4140540254035292000004402085655030f4000c2d6040c90b1500d841512014410502a80c11501d1008503e00690307940c400d45038152000c0c40c024505940c1c40c40c40e091001c91914014130281d01450920031101d0b01b00c0203a1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 529815008 1250 529813758 529813813
    0x909092307030b04061e0606050a05071403031005010f0c08041412120405030f0601080a0602030702070909050303010e010b0c0601150c05010905011a0a06120507090b0706060e09 78
    0x11020200c8441280380c001030b903201609210000c0706100400256070055092000c41c800311109000280e606401240e050744218004140308001c040700c0c1c24062009000d03094004e18558200e000d40c181810b0a583c0122801c8181402d214400d11407503800c007000c81c1c82007180c0e140c100003096040e9207542c0d0510441c01011407012004500c013000703954610341c0003812002d0201399140488152a00d00700740d00540100d91282c017850350050429840014881d04940380d460040c40240000e840310790095101602042c02c6001e00c20300451032183c503000383c105071442072006540c0c3c1d40c90170301d0b041590b10040c1c2004907000001c02480d209100700081d1241074450b48118483d4180608906403011282a0001400f9500b0320100307c050040c103500241d0403101110140b200d142c2c9000400c404100540110000319a1000c0c184c0c84455107036115076406581d034102003401c02c2e100d4100c0d060a8105a030110f5000c2c2e21024140044205404c03c103410501c0c5000610292000411890381c03000c140c9441c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 529816258 1250 529815008 529815053
    0xa0b1f0311030c160c03021c061107030e060706110403150b040b0f040c031d06010509071707031107060e100608070602280204020a020601210209070f0201060b030c0703090909 77
    0x1840030301210b11005e6008545c01401590700c01c0e01007800c14103401442c0410f0341c1207880c0a844880e140441d0040314600c55050751050f250071412010001640c00071b00381a80d49558901721043d50483c0c910003130001c3c6008000b1001540b0000d0f4a0105480940801034000c07400c0c24241041d6440383c0f074101c40c5401d41100c000c52801360065003100105400c45083d810801c0c0785540800c101404a00b050603280e040d2050503c0b6038070f4220940710302070001420700b1042621070003d141e4510a50250001590700308003d49462407944801068a803660a1010700790801d010311200d4600038801e540043c030034100500002d500e40704003e92a0700c00d01030001c51865903040c10302c11459400d0307000000c09500600843d1180b018020007942e841d024012000c100c940901017118002c9c1202d940000c540d8010848001c503550314004a68003654818503c09540d01d6000114502c4c1110b4055841030440c0185681c4070021f078240200541160703407001100504d0710490001046c1d0720000711413180c002100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 529817508 1250 529816258 529816297
    0x3050a0f020c030106060e0a051c17070b0403090e0709050907050c01020913020a1b080a21050103140706081e0c070b0a050f1f030303050a0b1f0311030c 67
    0x810303428901c1c842485035055280040200b080c81d00700480c05098003055580e202235035107550501031550403541424800500d01640c1c40001000d081d500b00346603500d00082ca080c400c682d59405c0c240b00094808401040f00d6913010b010a85200407426484481860201e80d6240340c040403d82c6c034040505920100680001e17846038608094040350892a0040c00308800500a480d40500035048000e0b01c00004030025454988500e9200d503021000380c00242291410220241c182e4006920f05804201d031120f060501104c2c4140d48034060085000c1e1841c030700e8250b0703031170409818a070080d0888000e000d00d5800740b0204551500f5140300220018107501041e0322410341005032805581d000a03d01d171401c40420a1440a54100c0e6008403010a9034001d0794681100004d06907944200d02d001000703104030304002283c0710360489074228400c1117000442c815070070080f0300300220076031130b480c0d00e8544030313080f541a0f56140c450503806070034014601d41503041c0032158054a10030014040c010710344d00c07036 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 529818758 1250 529817508 529817537
    0x9041407170d03060537030b1008010e010e06040f020102032a0106050409020303030f0406060f06050306030c01030605180402012115050303160b0405030d02030705180d03050a 77
    0x10840d8060200c008540e07030044825028641c0e00c081410300030002a00740b11000405090000701c015074040ca1070004100080180751208001007880c181e03501c00e071004c0d40000301044140304024007428145009203502820202d0b100c0c2910340c0e030324007501103a242043c040d89562012179139681050388000310021742d00312400101c2c6540508402c60b0b00341132001131440400021404440030580c2440001e01120381d8500401003103404100c03011307415800410009000003036451506034860300c16000052a26141c04801000c00d03402e81148001c51000001e1082d81e150410944e100f091091130107100c03c50411010610511841c805040b1641e4420081003c40e8040d000602c48500d040030105103189410580001a101501d82207a90b254103040115940c140441183d4107080d000070250b40c5540f680d551216031000c0140b00b502c5d50300050007a020032007403600043d4016400d5660300c6861700d000f405070110040c035400c0308a03c04d01085044200280d0820140c601c03440660802109684040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 529820008 1250 529818758 529818763
    0x403110d1a0a06061e0f03060b0a12050f100e19020711182a07060606090509091b0603040809220f05370606051206090402090414 57
    0x80d000105126035104101100e20441c404061184092400501c4116918441903603404d00079929004c040c903410b107814000900030305c84203149103201d02d800900780d551610800c400f0340055800070009943c44003c411007070740d40c2c0909074208480c84264145410a54403802c0b0321940d82c415081c4510a6400149560501190071459410442819941c4036041d2030483c5140c048a040c991080c50102c642486503207075882d659116484d01c14080d80c400d04455602544503e0b40080d43e001414100052000107009004d01001030403541c907141c0c1450f046c002040510100249048616403103502c0440c41810403450060110000f075a00689d03c2e180c07130501c1450340c420043d1140c0c2001d0301540002c0106004107158001ea16010810003008190100440903100d040d110440031508842e0b4030100c101c40f80300007103d0203848580100c0f02d1001c0300d60340700c15030f12154407a5000c101c011a80100c0009900e10045e8424404c41c0c030402d01d0b00d0194001851004050409010a13400320102c0104003c01c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 529821258 1250 529820008 529820029
    0xe01020c211905010b18040c0603110f0f03151008060906011b1a09010608070b0c03120901050604060b07050a0314133201210b040608030d0606050906040311 69
    0x140205810840b92424014007a06143ca1194042c41c4010a1900c6071801c14150381d00583e4000b50fa00c41540c50b00408802409a48840040d08401005110120703145000109a401220310700d2030b0322440d05103c04414682d5048120b0701421001824000e4543d0260580d80e0280e02250118010b4a0b0700d00100c8103581110f800c40401240c00d2600c03000d01107011112014000f8487c1d4440180e038419944c1800e8522510481c82a40e1045105018030748100700502800d01019003101d0502c2c45845119800c4642600c80705610b940d0340003404810704003030060001512a0010701c03807812480c0d81d0307602d41c4c600048074041c1c100100004640c0040700710340d044031070545903110b805861941310700212a152108035403100040f20304c0494102540c100d903058041104e4140c6404c5071580120034800750700003c03c50514401c0307136600c44c108515903451182401420506004680725030a18035103a04485044d0080e609005090080201607511034044800b981d03400300d00701030300c0c1c820b24011607080484d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 529822508 1250 529821258 529821283
    0x3031503080c011424010e1203120912180409050a02090a0213080c01090e04060b0a0e0106170c0405060904020403021c0506070e0619021509010204060e01020c21 71
    0x40000e100b030086601504800d40d2459000c82152080d1145601a00203e070755554000c00e102ca0451107000c598018200100725000c040c10103051080d0068000341180d00c00c0b8050b04807208142c0c00d000112608100ca04404503883e0b00803407034a40e080300c2c0c20710343c03420802d03509105646803827000081240500c01104601d41c068501c402900b042c0d01e100c0d002e50440c04040099454400c0001380d40607001800108062041e11000b812604101a460401340001e1003910601c0d1520300c48a115103c2842000003420000320403040c1f07505050300207110840c0488040112141c950078450300305494011203044500031078080c2c2d52880a40d0100c1c019016650010b50322201f80364082c40e44030003d100160090348140d043c1e036025955507200740c421380008084150010380c00e00800564000c89040d440800b81c15004a41440407501079127140303040207d0f00300605d65000308082020507045007213216900d200b4000340800341c3c035800100d1280c10301c011032100c842410008a141481c800d100780031103941d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 529823758 1250 529822508 529822523
    0x306020a0207210f050c030a11031216020628081b1206121e0d02010c0513120204060302060307030902130e1507050c060405030406091a09100201020903160311090405070303031503 79
    0x3e1403810000c1030039582c0c00e149c5002e40200904d0000505548044031440084c448200c20f0051040e024081e25030407980d59884e0002c1e250440c0b80c0c000440c21045901f0104603561440c2e180342103d4400c0a124135180d0a07000c2503421700081510006031103807030754050700555a441485450f050b44925101c543c0740e004149000e29841100c603d4004200358007080c5640d0028040030809880c200c17001d101d00c140c3c1c484880c0e0100000d01484036018000d0070114001800441c03182c1d1130703800040b01a0b10503620300d804681e0740e40d107260440c2811081d148808880e0141040260003810460382c881d0107492a44070852007403c00103020b00c0c01541940e000d007101804403804d46c41c2514280e9900c0c0e10500840010501d0410000341c054504e1600c0b441001580b01154108003c1105100040820480d524150f54090100382402e8604000400c800890342d0040c2d50800d2a6040c0443c9044c81212900e00032881c020410000c0341000030407108a030b525203000a040f40b60740f080114190340c2a00000c0451 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 529825008 1250 529823758 529823773
    0xc0604060e0f03070e0a020a230306040b03061324061d0f1017070312090306050a06032d0f0602030906070f14090d06060306020a0207210f050c03 64
    0x96032112841c00465410340700200180426003c241c1d40300550300c52001078050071000200300c10215000b0705200b100509100c440d804135188420301140c86c0751120302d2983c0c0080100051490700340145103143c50168003405d202e0415402211189040442c081e04211001d40003019001c101e201905d4100c0300408104102600e500e901c54000c0d8811685042c9000450b0200d1321a15150640c640030b518205486101ca600d80480303528006402c0c20f9030340c410701a0000000c00700e0154a0751b11b0158819907034518a1a0940ca0214200c42000d860603940d149008800d0001841c16285404403011540003010240c11801c8188010b1901d1b01000788000c40031400401008200d40166000344030302c109a82044d0340d44007048450303038180da03200c800050b0815030606045100d000284401d00c00031340081c84280d10303500c03940192250b42e40b0480394180d00180000d10716505110001c05040031a08000614900d860b040c08005000500540f000c42c8d80558001000800c0140e10144500034041c2c0e17915 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 529826258 1250 529825008 529825019
    0xd2102030c04030308070203190e01020f060f0a0606090308030601200d0c0c0e0405100f0b0306010b12010f060503270f0106060f020a0510022d0309010f060b0d0c020c0604 75
    0x1d40c200d0700c811004030f04c400d0003044c8107500100544510b00c0300e0716000609501e2107041140ca1a54140312141540070702120031954140030b2044174426810700b003000c250350420389000d900310b828517401841045074005046c00015042000c40790406424a880120b0b14401c0100602d0828841c602040d24420034400c86442504014904007560048400c40540e954450148100b2000ac50b00203126400015881801e08810780c0f0482c206849203000091000d0860007191514400781c011132120000480e812880c11503a507410340c0541046043c0448152810001400d01e0001404c2c403440d44000b000014641c00c08160038040c42240c49007101c034105924004107000300700502420000a14804160803290f00010703501ea61242d0080003440024402d129200c0290000e0a0300103460340881202d02d5108105c0b0081c900700000c844101e690303800c00961440c02c40b8240001c803d0440d00700402003000f5858881600d200c00710303040e000302d18682e006030b049090076410060541c0c85000070901084 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 529827508 1250 529826258 529826281
    0x15030507140a0303050909070504050a080609060a020415140d020d0b1206070c03050304020f030f0d030e07121506091104090e030f031308040f0b19030e0d210203 71
    0x2261a89240d41c0801c03a907030310602820b42100c2c000500403c40c1006003402c581010602c0903404012407602c5400d0507122400140f46610f503038420340c8554460424450240700901043da04000752802c11440d083c82c0441c503110610b20700e005502800342415000c120001c513401241d2100020140c11903851b050064060001e101d0944041d006074004c0000703109110f000075400d03004108076150381091940d2a81c1c2200c0d41d50008104a801c02e001c80d4542c055502c0812451034010f0280d40500440c90101600a089034a0301d805001d007039110480400c034181400b00c00c00c01031a0015405000440410b00c1c2401800b01640314000c103625088400d800301000d50b01410544000100522001d8201428140e0b01c0c041c681c0065040503041000c42c2121a04220756981280f085203800c2c01c00760748407844644554168404008500b00240550802480781c2c2ea0710100840d5040822998007480440b0760340b49500781400050105141c802c1e080c0002001d0804505110702009542e285402640c220 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 529828758 1250 529827508 529827523
    0x30e01080403091509031a09210f0d1d061005060a03140a0606030b09040b0c0903120a090e0f130b1503160302010e01051630030e070b0408070e0901150305 68
    0x103c4010401058400c000120501c0b140a103504c00d006000040c1c1c0310310b403002728210350840200d4150301080f0160201c02c00c3c0700071b00780c030701382d680c40c00910700022070220b509501c0c00003140c0c8403c1d00180c0c100f004469519071400241e0704140d0f40a40c48000c804019801069108520b0745030020003002c000084a042c2c1200d41540da007903805004501c2c184050002402e81560024011500341c0c0014000200520141000e40c80003030484111884260390902e80b41c0c048000c1500007210360005022844100300c8154200c041c80010040901e4160a509001c80c500900100b5540a50b80400c05446908500000301e00340103040e01c11010a0038164511001d061004030b004c2a10400e507007031158040d00a803401030170360340c504c080752604541d9070413040c128020308880312140720366120088005010943d80c0f0f40c45603440000340002d54420152402d40250302406000781d04100500c405a0081844022540780e090480110b0f01d44a1445000d020803505410300c04084036400814008000382e80f0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 529830008 1250 529828758 529828763
    0x60f0305192d12020102160206163009060e0f03070b0424110a0f050a0602030a020912010e030403020418020d05100b01050412110a0305070602010f18030e0108040309150903 76
    0x200700804044e030a0340124030000481d084d441003500050300f05500107100502d609840140b407204141d0728102c42b4007140800c5031050000d400c0107a250220300c030788010380d203c0c181032203000c1038a800002000b012031a107d1601a100d099034041c51524104802005860f85c02c100c9612581c1322185c0c808852000490410b00d03480d06107541810700d000d400301d41c1003000044090034941200c0c0e00e9481a40e043c901d800c9500748074030b4607004045500380c0701540c010003040b200940c3e0307241c0100400a42a40c400c132000030a07494082c10a01365940001100c0840c0e5040e500400c62070400f40444101c0d04107040c0180d00600c500300c1a84c00c001001c6515540380c80002001c01c0a01d900c81b0044650303000e180aa2110403490742d4000380411480c0d400c0411050008105402c007030344a984003814261198000c501503034445020302e05e0742c03216006e5003159001140c810742d4040e807141c40c000c10340d419070300b481c03418040321901103005c1c54401d000b084080d04603441400402c035101070008003041c2e00b500c0107 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 529831258 1250 529830008 529830023
    0x8040b0d06140907260a020a12110409150801090606081b031e0309040e1f050609070e180106080f0c0c0c060d0204050405090c0103060f0305192d 64
    0x200d00e00c0d580341d40d80451008054004062070761202421703584215800c40b9032404007155560500c0040041c488030303100e00f02e20b040240e101c089801002d4001d01b10120313043e0782d45080200c161485418641517500b122040301e00410030012140d00ca4000310081e400c4a40e00f942070000b80000d000050704100d0459480c8001c071101408500b0780c5481905c0d403803900c90b0341038000181644075421400c8401000f042c1c450107580c5000312000004040740d650b04144081e5401c40503056a40742c001401403c0f0031054198248000c0c9003050024401040041c2804180700107800550b03015203070030b400d44025409401c0300c02e06550b1241005062030a04450094500d0204000501164903110a0f2a945c00d9150010320311080081d08015007500007038188000240c0c01d01000816940d18000c0a0088a0303020180c1000003000000500f41c17030440c0c20080740c00c08007090400002d940003031034210b440860855100745080c02c1c60140f502e6082e0b000010001c11000201510707040005110010302c9114811 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 529832508 1250 529831258 529831271
    0xf030b06010c03120b0a05100f18080c060a0216080f0705010c0312090323041403030f0a033b0d09060c08070c030614040317010b0301120f08040b0d 65
    0x1101c609461900043c000f95801d00111807a0400c1d03049035000305001040c010101d900c810108142c6845001c03020000740349101d540303143d0750f008080070307241042410307032003011605180b8400d9580b48540c440f01d000703140c0020091801442813041c0d6450018503685a003407540c0e81c01d80341741e0761144609509071a0080e1440020380e5801041003146d07280c1c2c076442e184030400710030b0180001091005420340a01c40741c5428a801c044100c0b10203498400c007004510b03140c504000300d00230030000445040d070083d4000c00c03500308c0d00600002501e1714607032107190114140c000001c00340e08901d24010303441d079040c1c01011003449150341e50201ca0030380101141141c0d01401441c10440e4418514131500b40860485100310000c80c00040c02440c0440c005c40419038125540c0c0e88034070071a401d150240754030050007001d100415600640b030050710100d1b0010040746504042d42810170b8401840350b421f420640d0340700c4c0c900b00009080604286904034603031603142c50742e48032406501e61103004220318a030315201 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 529833758 1250 529832508 529832521
    0x3080c0c010203070b0c0d1d0a05070807080a120513180b010c020f151c0507020607050f030f0405100e07050a0f0b0901050a1206030515182808040f030b 67
    0x206442d000340d048007150341d07175403a040748048403a403052010004494544078480700200300b020b4038a021494123001400c0d114081d0424606045494102d4480f5801580341046100c0e0300060840480f90018101110f49545030801d84e010b1007038410090101c0051303007000600315100c8801c1404003a00f04410300c05c40100c1d1004540502c4d0800c0001d50101424800c0c0300302d414600c0c100c002444038059442c0c40c113150301004a0360205105081210651100304101d2403a40c1440030760f402404a06041d81081c440c03040f508400c0c0402450031a51400c0d0500040a02004021418418080c4c0c4410000c03582030980254480700c850044901420880900090180301800f05000301caa0050815081800c180011280d41c0e1004804a0400c42c0310408004140b0302c611814000310300c514001d00200f410144d416010741c1300181a85001c0c88035140c11b1030000400300e00420f0380c00c0103c410b0301240031a60054001192902c00c0544903003800b140210340f112080c00d01d90162805041d0540c0180c0d03414 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 529835008 1250 529833758 529833763
    0x10f03060e0f0a0602031e0412091203230f030403090602061501170c040512060109050f070813020303130e100906050a181d0c0108060a061407060b040603080c0c0102 73
    0x305038840c0c5a50040c0c0c03070a00803400035405941c01a1f14074001100c06a040345c010025540e094400342c64000881d143c07c0034140e004480000100600b80d102c0031606c46503100905102c1148001d02e4040348008807402e80d0358250802c9480e4030301d000e10069100d00302803c000b0081c2c0306502500d805071103580d0206102d490329003100e005183d8160343e900f01801a00c0e00030008684d01400c000600300092001107910340e01c0c2c0001c9008854240c0050400390300d4030400c072040e00e0f40500309101c403445682c24807200d160700c00c1910303030300442004600301490f180d03201180c40c510544100041e80401c103100030482c800b481614134040d03100124a034a00030345845039032044448900c1680d50020424600700040341040b01000b4107a070429500148080304900c07000030041018040c102903400c40e901301385a03507070462845600010252501e01c3e0781820140d024004152002d40d04c80085400300d07a00e410130a40340c03c0040c00510190040c45025981c0c6050f100d5600001e00607240750241036803c0c191940300 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 529836258 1250 529835008 529835023
    0x307030b191214161d0105010c0f1410020d09020a09050c0a0c03020c04050705070618020a051c1b080727020703051603050d0e070311040b030f06010f03060e 69
    0x1100c080b00340208140d40c0301020144842c581c02602c1c0140440d06039480c0511119100600340c0034003400203165400412940104160407a6061003400d220b0340001c91145d144080444d588030341b0000c2561219603040740f420003000862a01c40340002020042100b03d500301540a510a695218043d512071192000381d8108491041e9591418454401102d06c2a40d10340c1c0d01c1e9000b40159906040340002003419204100c0703544012460014401080101501c03c4201200c008800c030340f1219403039400100c000d802449454411062800109101121500f00c004443d0340203601c00e90341d10b1044488103164409114500c203c2c000c90030001862042c45820284615810a440b01d040000e042440029003280760207908000085c400120001da03460741c1c2281c030398026155a5240d41c41070b081031041da9080340204007580c1000c901007000a40081041e10290070031240817403140c0500e0080391615000301480252442203000014400351140918003c1d61300400e0148003441007072030903d40c0c5850 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 529837508 1250 529836258 529836269
    0x50a0b0f15030402091b07110f040903090b0d1104030b090607110c010f170f0103060e070b09040b040219080901050609090c0d061b090509010807030c090203130204020307030b19 78
    0x108000090041c645580744a61043e0914014100303c96025030800030354011f020111902ea07110445c00d0100e1910015041c4110002c80c1d061108010540d0010301802c03007446203802181e004501c180300c446407a0401c09541e143c154256031115079900b8a110040d40036903a0344058041d0b14040380720030307200315042044100e0701401010414035032001106c000b901c80d00300328200913009918a02c040441c03c40300b800303140040003038031a80d41141881d000b2181541080360741d0782c1c0507040c1040051290000c2d258510421100081d04000940124019101c0c000c007800401d048501c0315a9601e420204847c01544914020891a41d6540500c094440191989019176005040074840e601d00701e10510105480307014049591460740f00d1280d0744403c549542d002240e140f400c2800356007041c0070003500400341c6030010142c0707500e50349407003802400d0360082003219600080040e03d808100e140d10b48541e60302030700c01c6642c1d1070003001c002d00904445500d58410f8129510000325008040c200506880 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 529838758 1250 529837508 529837549
    0x4021804200f0406030f0b0903190819060605040608010f0302090f0603010905060126010c0519020c1519030b010f0302070f020a0801060807060503010b0703081504050a0b0f 76
    0x144000c2094184421100560740300e2908910b040300b64440e07000d408001c1d403164041c9170362034042d840c1500c1c0e4032500410804080c0d10501a02c0a22142283c5800d4184a1400d10150640b2581403214060b10802c191050355420580001612075001000704111000c65540e08950792f240d043d0341010300841c2c40080d610490340004100f107003000c074208a402800040000601d44401c0d5101c1c0d04000c0260701c20481940201500d58a101c0341c0c0385440f0740800a46c001300014004014082d0050081c4011600510104082840312500030850f00c6140500106202030218140040010540c40481c5440b0a00301041031118040c1c0240601581008140c4803e482d06095102c220b00075000000c0c10b42e41e01066896000142c0c4030f52164601070000d40001042c020f0a1590152800340107034000d408000701000100219041d1000b5602e00550510301343c58903444075104060b80c075041c4c04d50994031034504020f101c00498107070300c072650280c419213101c440c41450790f041049215994104200c1d40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 529840008 1250 529838758 529838783
    0x70c02060708091c030302190503060d0809030f1c09090c1205130c0e070305060a0f050d150f0c0206130f021014030f01090621031805100804021804 65
    0x50044005410000c1d40070340030b480303500b15400140000c0e02c0b40110a0740407d50004604001600240c103000801d61941413052441c1072104c08125101030649016210500103e00c4401039a018444c200b1241302c0b901c200c6032000880e68840e03042d507001e102c3c800041031104000043c4030f803032030040500c0c2c3e00741600e401d01002410b8807110f02410008140c11816210840c0c24000510052404001307440078440d60a424503191b10060100d840c0a454a032240c9500501044200518aa0720050b10010340b6510890240d92900803a029003a0001c503400780d080902045803203102d9401016210040e03800c4a8140e1a82603d00e410444003040140103c6082180c1a026082c1051052020500340c50900314055001103004000c2c4c106a840c6510040014010054180b143c0655005448100011000b807142c00c041b40d02e1003003414200500740b160210b294840d0b030814403a07480080402401042944601010050080204031422403040307040c4140b2403102c0f000301480d280704640c0800c43c620324 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 529841258 1250 529840008 529840013
    0x11090a1b1101060f030308060a0e04080f0a09150c020a06030608031b15010f090f02120f0619180e0613021504090609050708060334080102070812070c020607 69
    0x240300014400366484040014031321401140b000000c500941ea924141d040030010030107540c845602840c2c1c50311182081c0800705070401e0885921030078a014103a40e444808000381e8003490a0703031050443e4403106111154568100003c0d10055200719801c0d0034164480c41c0640450714680110340607940f05110302c2c16000c0140800f001c520448808440e4004614800c007108554242c004101003c0d07a130608200b0b078059805020030040c0700c0401542404018078a44c40b81a000514801003030303c0080103c1c0c87c0c6e07182c5d681c800208007a01949103290130344450300181218010001002114504840c80102460102d103090062000314514a190f480a030200540900d60000c05079254608001c0000d10100030b106e91401000c1d00c41000c6038506e01004040c18008000380b0107030207030304100e950824415880c0c01c80042080703292444542d0000040e126404030002da0450881d640c0b000034140280003080c809011501000d1500840b160380b105400c55800b0b9100600070740100050105800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 529842508 1250 529841258 529841267
    0x406030f15050112021b03040303110f030703050304081b030c0c0a030b011a04090606020109060b0303070308010323061005090112051b1f0c1709130507030b030a11090a1b 75
    0x1113600201000b60803e014179492607043c414106540303c180c1d000040c10802c140d00304540b4529244030360090414011766040060300c0b44120440102008000400130b010400d440c1e06481070003a0700c5044088441d40180e00a80c2d9034002c90a4460521590f080d0410070301c3c00807544d2007600d5000c0010342e0300ea4071309018540d407a00c8400d2500201c100912002c10300c64190321410006103859400418410058200385085402d0103490354001d030401c1008201092b0410510707411a07610090b444072002c814a41450742c10280341011030741d40601c60038000d00c0184020348409468084503414002c0c1d07603500c050042240c251038020001e0b00a806c00e484008501080f40b919a41d002e8043c000c8040c10612810100b0a0a0351074404500c0f0301c030b410001c0c030403c1c40504801103100995107141c9982c460019042e282d400c8102c10300c041e01c4070300107002c00703110b600101d45100c0082c049a00c40b04180c41c0540c4000302404506003d01401c07400900722111a000c1d00c1103281c003007840004100050202110b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 529843758 1250 529842508 529842527
    0x801021c0f0902090903042c06190b0a05090307092009030a02100f02070b03150402031e0c0a030c0813060b030f0f0705030610030209062704080406030f150501 70
    0x6800980c1c650b801c01c00741c0c5500b44000d1107040b0310740145941e01d085c0107144e515607500c161411803401800c00d41c101111046c21080741c200e1030440351a000021007010a00c9410b4180c1c2103000c400101050046d410b2b50024040d10040d6811419240440e031141c45c03000494041c4601001c00942120328071140341c0b0345800900c224071014082d240c009526402046006080d208a0070000707a90841d201703151075040c040c6201030329182942510b1410030843d40c0201800300202c0b00c0c401e40e0f0000c041882c2013250b0100700c6c8800e200c0c00001040b450000c1c030141c041d801032460340700800c3c05c007041c01303141912401c0c280b48513152803150740c2050540c80e1a80001061041c0f1051b405208103080c00303219100400c14000d082000c2c000804040e821314003807504152000d4200300d803000703860300203000594640c452258000d0064412400c1400700c4e0051130508003152007007069196071101070005008082005200303540440d1001d00040d4043c030700900031910030410700303081c1115401c4d09100d190b1141b040781 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 529845008 1250 529843758 529843781
    0x50105031503060c030619061e0e0a060203070302061e010b0315040e060114030606030d030510120b0105040b011b0605070201090602040906030c06050a0203030106140c01020a0c06060801021c 84
    0x1c1100074220320100b850705806481da0b8111480200c10803c0d185030007002510128108030b00180002e203050000b4041c44118403108405100328034040792036502c103030506500391500030125800255070b100041d44030341c42103209900501070440001c500030401100310000c0d851901031007105030719281840e00b0fa508040d00d1050003d07100713880500565150f0044418071540c1c88040c2003994544604400b18484010507580260410420044140d8001c500c1c0700c20074003d42000b20382c07503131200303044000c1e07500c1a008260b010441615010501c4270400081d41a180140c0301000f08100000042da0b80310311414010010001440e0b00c1000604160000c40c3c0110382d600001c9021102652904240d0708103420030001141c5d50201041840270010403203006205900301985801c0300c40c40001d469100c140502428410960031244188030380c00100c5504030780c802c2c0210349528100c0341c0101643c811480c1952118100600450120018800c13100b21403a09003180754a4269141c2001c060480340004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 529846258 1250 529845008 529845031
    0x60503010f050f012c090a06140f012d0f030921200615010305040b070e181603050c04050a0513020d0903020307030f1b08070501061701020d180203030405010503 71
    0x4069003920065094110510345d1070405015000120034080025401840c95450505007401045251001e840d10220480283c1e00030400d1103107640160783c1107001540071a10310440e0700301c42e10002c06004410501d404960f5540000819052084042c0d940c1c215015202c03180f0747c1e0140706144000c00d40c41e100d2120504006020621440102841203018008035071031303821103001c0010220207902c100b070025009003020482418561600103540b48010035200920074035844030140e90340d440c0241541e001d80c050b0412818a1315810b480743c03a050703400d07017040031a041c1004504003048000c1524203a41c0d000d4202022140743c0303020410f600f45403191740e8081c643d0030804030304c2e074140f00d001d0765040c18040d400560742c41182d441c00a00c003900011400c810844c88a083d00904240380702d4540a00b0b801040c85500c0c0c41c0306003000341c010803040e84004031410204d10106640b54064003d070007980c1502004029040e1144050300c01c00c000c00c000258035030000c01050260790f0040f8065500203c0d030008 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 529847508 1250 529846258 529846277
    0x8010605040512011d0a17041d070c02100f0e092401050712050418060b030703091a070e1201091509080408190b010510210212100e01060503010f050f01 67
    0x41701400b18007801990643e400143c0844240822180f12114410503202920729043c80c240c0b00100020140c03005207880c81410000c00c060b035108407030344001c1c3c5400500050491002e860040c03d4100300e00d100c80f0110f1080001207445241514000d841003002c04550290542c0521a00395150032109085041c40f20910100300416410595900c83c1402030700d4141d621030815894003981401e40d00440e40041c06d018041c001180316000b529040301081c28041a12041d5190085100940c0d04000d0f00603106801040405070f4410380304010400b083d10420300000300d042c40c4034240c0b03840f044050818010302030206810703055944500a01030103410118142038440400500b88458035040d104003104a80c0084180300507280b00c90b00524007194503001a40d1018000f600006031111034229042c401400709041d507a150301160b0840b900c148100d210b505e40444034103500301e0940a0954400a990000b040d601d02031011603060307800031000c00038624900b03001c01000800000416040042c1c610b17 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 529848758 1250 529847508 529847531
    0x2060402010e03190f05060f042604091505040f0b030c091308030108061b160f0305090a0b0706110307091a0f040611010f020313060509070e1608070801060504051201 73
    0x20741000036101720503100f2400c0070760504501e0440003904222802a1110900c00056100c1c00c05012020354080e421300e034000c03002c0007550302e4056540054845410292410503c0f03041b4190707002920b90440c0c0400500c610b0b00c140c04100d82010030b8094040c0d11070700300a442c518040d2825540a4052060310038014030342d998010468000ba0702400c0c6070790048003032256008030188140a41c03102c818406080c00d550360455101804c07400341c068141a442030001c01894401d90480305001d50181c01c7c8902c1c15078034003817165150301c601400d880e0a440c00441030310005404084a02680182d82d411890320b0801c0300f0b105610500000610303002e4000c2014034004147e104c0072300010001901c036400c41c1440150307a00c0c20754400c3c2291005880c4100200410780d111203910100480d000302c00055aa6500401b541c0380119a400010100d02c51004200301441c44400464504045684079011615181400d1b100d1078020b0086c240403440034041031100d030902d200c03100315000c4030b98000b05045c59501d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 529850008 1250 529848758 529848793
    0x120b030f190c0803030f04060b12120a0905060306060301180b0a2705040c06030e0c0d0506060118050a03032d0503090d091202150705190b060f0102060402010e03 71
    0x407400307001e107001030034250041c403410b00d001800510b140409545107107010310703d5165001c00217000412580d0764600f4450240c442e20103804804d602d2108a401480c1c07040205045a001508014006020040c010030301e03040080c03e40340a800040c012074110390070140c10a14044548007100015030381e55001d480103603141813400009141c80280b02d503a500ba00016900e000c82158407401e8800d041c402070000060703500b889901101c1040c40c0001e00e1400c40030205041c60040a1520350040c04083c00005011001c5290360144500740c941403241400c3d0b1000721154050391250651251458500300302190003500c1506a003203085180381c0103060b290618654064840c00803400161001c0308006403040104040c845034580703070500000c1c1a103008000600441e0200000340500e28440e00c0e0409608407100303550750b290b448803d4480040c0019210f41490680c14001d54542e81110042844e60414060701c01c0403800680c09400c0701d64481c1c0041d2001c00440b81695010720a1010000305020b85 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 529851258 1250 529850008 529850023
    0x73f06051f02100f020a030c0203130510022104170a0804091104050d14010f0614120f0616140a02031806160b1e071209051f09050706020c01120b030f 66
    0x6130401030b10b4916008004045600004001080d98410000140c00700c00c038603000e02c1202c408940d01c070100404064224180400813190300c0054506100d8880191118400b40c01600d030509100c1c80d210f120030034059606e14060f900075041c1c030001c100070300c003104032500a0018a1340035481a454241c1c0c03200400c0307003031036080401c0d208861800c41c2c0081c40c035000e000c3e00700c00c105240400d10409043c4551110481800c803070340b82c401d1806520a500104040c040c0c3c2c003e4401440544800c0d103840700c0e03100c100c0345400208000098401d500c0754548100e2000f5a04502c0d01036000f18281381c2084501040840740c1c60245034040000c1c400c105800040051025606200751410003ca04010405e0407a8006054100c4a0342c2e600b43c081092055010700d00709140008080080340300030950034054108040051751082050240d99200ca1030450358004040d414403403021115699a034000403603c43c4001d40760240016842d4891040f81c3c170954000c9203070712031b0081c01c3d1030024800d0344001703141021 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 529852508 1250 529851258 529851281
    0xf3405040f170c0415141908150a1a010e010306031502042c0c0a1e0e01170114130b03030a08091b03060609073f06051f0210 55
    0x34440c0c0c030200010a0003c64040f420507503041c0001c1404414400c1c2150090080c034190107480a481e9038140e640d190410303000001d8800c454046900d800d103481d04c402c503444c188001032100b14040b80407900c03d0703c540e00ca0090b002070380e881c2241034240110751030707000d0b075001d10304041d1106804400b0461810203010f28496041005a4840c038196800090917903880c8170078102680c2503503296044c00611384541d8050105040caa5580ca05070300241c80f446500700028407500f1800b003c40500341c0d009100c424551038262103540312406002d02581e02d103102409000ba00411507503c409030390411200301d20500403100070105040340113002027891900008066800a00b401c1e00f40503800c582407000542a04001403a140c1d09003424010a070703500005082c1e980030380c02100c00641118403030441e01a042c01d401d45d061070b0110010441d01c080c055400c0c0a10102c54031800c00400c1009140301d804100c0704050180c10420402200d01507510074aa0300f44001c5d80200e5001c50740400c00c1b445000d02414 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 529853758 1250 529852508 529852529
    0x2012307052a0102070b09060310080d0504030204180c06120e03030a0203070e09010308040521190212160e2701060e1018050402040605060a080f3405040f 68
    0x1403280c41035502c1400e541402410340d00002d10900100c18290100c50706458107403000ca640780c65003003003140c8480740369000d20030b68050500b80d050110350180c01001184d00031201845100b2a03e0500c40d4502420b88004000201c0954100040b6000d188641e034520001c041c0040c0b60700c03005824a046510413038a2021899000040002c010340001481a0080f800c1d510904158119641d01c54070340700740d004582c07181cbc010b01d2003401c42c00c031f1300715180105030080015615025543c942e10541d10380c020314102e1291a00c8680b07a416a0000941400e0005405401e1980c1515014144c1090f40c00948420010703600b80c2c021180d44042050403200000510000040c2c50f40b8000c0d08502d441800350450b42400e681407810001280c40740115000c00c485444005103030748451000500a24247e40a507820803008161402c50980210b1510305ca09143d500d038941c282d441210080003c54400c80261447d849125081c04032200888400714504050500b5442c007a2900191078040c020355204c1104032 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 529855008 1250 529853758 529853803
    0xe03070b010509090a17072306040308010519050103090614100801050108011b033b211b0a0b010f06110c0112020f090a1508130201230705 61
    0x505020140c03036071010a80000d1300c29a01c2030b0b0b803002d4240001854001902002151f804284120943c0c90f0202042ea103000320031507a90800c009844401c2140c094001c07031854800003030079082840c074a11102200c00000400e243c20724005400403c01c4d400c0070707114240d640080c0e030013502e001031209010b5508501d10f209900d1801072002d00350349058208039840d904244400201c03070036601c2910041c00c8241008941c2c030316000c4803001e0380c02140516882c0644009001065407024038034007030102040c44141e56815624820742480031504d002012403002080011505089003844100c00c200251019120907800030348800e45820420380007100458446581040850342100c81c40680e00c06150103000b114849400203000680d1075984100b10980000c1c0886a00130207104481d14881f004110000e107540322020700004202c881ea11802159440002c01e00a4104242003c00b03075038141c0da000d120b024a0300b140400d00c120002c1038140c5a000780000701c000740043c001600d1800740c00417500d250 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 529856115 1107 529855008 529855019
    0xf0d1d0414010b0a2c010806060403060c120c08090c09070306080f151e041104092108010b0a050423030307060c0e01080f0a0905010e03070b01 63
    0x401c07a6108000301c1c3d640c03c1200034141120b110395454503201618412071114250f542100b800b415000307803c03150290710688613035500040242c2010b08003039481e03881105480591403c00041000f40d4804541b020442c881e28801d0101443c0c507103103604003500c3c0c0c140c403800e402c190f05d070140042000140049003e074104000900c214412107444958051103c5d45826800c540c0848140a80011174061012504564a40c0d441e08051340101e8076a030351205090003803050b0301608903807139207440c0c070204056124042a1102044821001000c2410000d0040354140c022850f13124051081c8107620354414180d40581e821100c1ca40c03628031801e46440030300d00c2842d038007560500c400250001080482c2c1c001c08000700d40307502c414880444810042d501502c1c00c6580e03010079148200011681d950f0360308803440c1c240c0100e000140403410188080d003035500c03c803401e42e420440170004000 = true := by decide +kernel

theorem cover : BRFrame.Cov 529676258 529856115 := by
  have h0 := BRFrame.cov_init 529676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 529676258 ≤ n) (h2 : n < 529856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
