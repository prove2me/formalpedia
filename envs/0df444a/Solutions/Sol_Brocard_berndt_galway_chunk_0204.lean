-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0204
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:26:10.969544+00:00
-- url     : https://prove2.me/submissions/12e5f53f-0a58-46bd-ae6e-b76ed75b197d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 36510796 ≤ n < 36690652 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 36512046 1250 36510796 36510833
    0x30307060c020c0906030606040f140103080c16050607080901120c0806121606081312030507080a050f241e01080f0702031611090702010b010e030a05060606091c050604 74
    0x40051405200182d1f0703400b40500002e0140b0380d2800301c5d1028072203541024000110741c080f080c1d49540c0d6482c018442e03910450f0790541e41d0003400362408101c0c1840406004944c0001c040760b00f010f02c940c507921160313032210b18280e041c850340940941c0134a00302e0142001c81c2a0030f440c0d0b8489840c00c4024820014641d030b582d420541c06c400b200d501100b40841c5040b0582d005883d092050307544040070000c11888080300600b40c034010030130590980358140c0045206220f6a6222085500c03408444c00640748103980800088241b0000500c0400ca0a0440440006612811100c0c216004c001c1b0f140580704000044c21070b24081010581540c10100e102d4000ca0040f045083c07618165800a4aa01a51198107580040b2030781e21010700c245944940f5180c00010081d4441c3d05203950081d00a0040c8041540805c1043c00c48c0070f25071a012850071400742c0c100001d864242c4e10103003000110b6020340041544036003080e00440c0d16000140d4544c3c0c50620420080c409424603040645103a00450b6080 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 36513296 1250 36512046 36512059
    0x301050a050a0c0e1f020c09010803070c0501030c020a0f0302030409091a09030c0715020a06020408010c080606040f0920030903040e130c0509090f0303090304090f0501060504030f0501060302030307060c020c 91
    0xc110f240ca54040354411403e0918178103180c1807100c0801ca0402c0d10b5103009550100c0c42c14004a68178101100170043e852142e21750343c200c9950b40f4015401c0c2d407010645800075801840c980303030200c0d1100e030940070300c60310a10540f440d26850786040c104645e2100742c10340384580200c0300c0c04548088074070056000352132403005500304407640003600c0c1c2d900380c2801211961a0550410b18200e8002c00a101d440e42e4403400135034445484041950003040c00321002800a070f8014040741507420544110b07020354843c03c0e4150451801e18005201074041d10300a445a400070036101c2c0303800ba403440040d60003100b86401075691a41703001554240c07100094031048640741d823000031a0000741c8041c60030040300d009981d031400036a02e0301c1e40e036400d00c0341e0464409458003000041003285200840100301380c41500a0030030016800310130000450b4000d00404021607401c010602c08619103000c0c0445d050b1003000040784040c2c0725408a820b40c3c02c030140488519450300d030140c2d03040d90140420b668102040d01e10 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 36514546 1250 36513296 36513317
    0x100503010b030a021c0519060506040b0d02010801061809060303020102090a06090803030109050402040b0306040c08071a0307030b03030f0f030117010c0c03260114010306060503150f0f0301050a050a0c 88
    0x1c02d280440f2034051021144080e400c070030003109010191841c0345060351647c0c0c072525410014003606040303030740da07110354541503000401c1d25109007000304454040c0d42e15441c0da82442800e40b040c00300c0c8484100c076030306407110001d0344010328012032014510070780c00541c881c10039905029041d2120342160080c00300524042c02460700c0041564115805503001142544490011400400b01064410b405024503401c110038000c03512503c0080342e803031108850f05140d80307081d404200200c2c0c50300807003406410070109220038480d0700300b20452200101941d02d030030210a84c1c0c0070140d029200f4440300003004401002100341a040154002d41d0f008002d002c42d10b007000c0002c00b181590b401c010203002113002e4010311140310005280120107440740104d0070396114000030b181c420703036160200d000906000f17020800601c214152800380c19001d00900800f0000403c022051111842140e01300710b0002c2d0820313a5590034028103014000044c0300203610306082c0da40c1030560f07000b4021a81071005c0c0f880e4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 36515796 1250 36514546 36514549
    0x60a03110c07081e15040618050d120e100e120307120b010e01020a0605190c030902030606030d021902150a0c050c040203100e06040204080106030311060a06030f1415100503010b030a02 81
    0x280c0c0c0380401c0285c0c0c060441540c0d0391034100000c214031050031192004d220314550411100103180640f100540e107480c0c001079007404404044d201c02c01d10001168101800c41000301186406c4942400318800030b580101883d440300201c01c0e00225040c000041c0344600182c03000748140f040106104007882c00501882c0c500c00040e65034510480c0081a06545000059101c50101e0109400940100301407004040350348004024003640802644240615004510380385400140c203040c5444a4000d029820710b40100a14101d03900074041ea0841c4034103000840154462000300300c2440d50740c0b11004507461038200b4503d049010400140603620400030310860120000d2031170200c900d5040f4854a0707581d1280414060b00503940a01c40b83c0d800d00b40040205600f00b6962103560565000b00d52455840b204603000399102c512015120141c0e4284641c0841c070310b82c80c401d4003812288115016104e10b81c40e90b00c0c200e002200c0981600da0650342c284507610b001e01408060403812030050228480030b40 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 36517046 1250 36515796 36515803
    0x10806010e37200301050a060f0e0603071d030601060e0d03020307080712110a020603060f04020702030f0f0d0206060a060c050a080304030504030606050405040b06060a03110c07081e 80
    0x1070914120940b0000091060703114507540c103020714000c0031450b00250040b00880050a20206110300903090502225a03030043c490540341201c03801806038150615000054458480142d00c0c4020000404081044ca07110b1000450292886a0b5201100fa401f40c00f04030f04031803a000424030035040b19004000302ea92002404042e520115120391400b400e0b882c05a14510985100809050003c21400140b242d40307a6071500750301540c0c44e800c0242d01010040d5407270f80c001c0040290301501c10300200346075080203101c0180c800e030080c100520345039442e00060b00d0314403180403242c02070744102c0c80c0a0040c10309010707038510000300340000c090078100400020501182402220204180003402d8030500808120480e903054100c5211aa40e040508004100c0da0040c0402c0d10600d041c007000040b181818416107120b42d4000a0b021301e03a4903074008004803a40036140c01c004040e102c4061485814840c001084a60b207840000c180d42460202e055003031000b0b040c8800500410180304900d41907020 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 36518296 1250 36517046 36517051
    0xb06120609090a02031209100207030308010e19050907061b02090103120203070803010905041e030c02010815030d0201020304020915100804050102120c090405090c0f09150907020a0b010806010e 85
    0x1c4404024541d00e02030802c2c640104008007941c903114100c4030405168420004104001d000d072040c00c0d6060f190702082c3e0b516855480001d000401d0301c001041907401601c2c109400030f43c03182c660840f83c00c6407007003d010344506888090654000d031204210f2950496000c10745200f5644044826a009030005004488c051001500c0e015404100306c24042c4240200c40c100c6501003062034807546c44e0142c00c0014041110f00b141d080382000c1d101850000d400350401010365142ea201814081a540112070b44000a0100d448506611034251210398040c0b00c0f1179801d0041e0f900058480c0f030300d40100400500042c000c48503440c0c4550b4040d8440e110581c00300301c004c5490824030910b0300e0368940300d0b00a204105071030301d07000071010510807036502200060190030000c80381400284c6813410a02c1d1641200c148c4254810240c8a034011103007000d001095110010162206280d19020086020001d00320390070001600261b01030b41c20005010b03e924003403c03602e03004009540c1004030f241001e0300007 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 36519546 1250 36518296 36518299
    0x70302010302090d02060a0906231b330a020a0f211505030f0115060c0606050d06021b03040e0a02030406090c0b03100909020f01080c0d060b0a030b061206 68
    0x1043d41c90f136141d80420510782c80c0c2c0603002542c4d42c480b0010040001c401e9020b0b22000400b1031401c2d01d1400801e01c2000e502c0c46259400780d142a0403001c3c030500c5000c2039484101c00d8050b00c00c02902a0300c4040c0d0458529500400700c440003d101018900403074002000c83c85418414001150310380d500005262402b440c0b4180b20001509020210404045070010b01195600303002c04440b501c20114201c008640f4141c00b1a099891540501c0e404d03a240031560031200100c0340000c021151051813440c0116015407000124a0f03229400b1a00f40303280c140003500c400e0340002c0c055540c400a0540c07080d10030a074001a50402d17040100076528000b01030103c002e01d03074011002c202031040c1d40d80030031503455214030784011036642e4000644803a04215032a968a0302040d10002e24540c180c000c0c406959402007800d245420224011f468072000600400c44003002445010b007902000d20541014084ca4800d00352600f841141c014140c400f6440502d0140e00309001e56190202c8013019503403c00030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 36520796 1250 36519546 36519551
    0x17010c030603170a110f1b0102010507020a021003090b0c04031403040305100f0e0d020a02040e0f030d0207050c0d080913020702010804111311070506010b0c07171002070302030a030b0108090703020103 88
    0x20644c003254a1440d01245030002e0040c0600c5050007540020070f000c00e100c0e01d100760035210b204940160300b203d40484035007001d83c00c424040340040c0b41400c1ca0009007543c03800d00207101c542c1501e42c0006031004803510b50141000080500034040d500b4503004048540300d005600d0710b42941e9507151a6407880f00c10965541d204c0f14240300280305a00541090000c40301119401307003408000139a10616410207a00881c13405034030341c0825201044071700204404400075854050700c40e40a00c020350000741e060b01c55010302030701400349568034140220954000c580d056120b00424040000030070703a0a1060301030604c10090030300141d8025034926402a0400c4541d910040b58001182c42000c0070103000030100c0c82e0415800703144003000c6c05803004030301480480700c1903170301c13400a440702d440761100c070924a500c0130100700006c1c03540060300c10742c0030054002c0c0d40382e400362202c40c5001da13000400d0403001740e000828031015481c0e0520410004a400f480c081c819400c2140b00c850b107806076408003904258 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 36522046 1250 36520796 36520807
    0x213061202040302040905030702011707020c1e0406030f03030f02040e0601030e070308030c070506060a0305030f1b03160317011a0c12040f030b070f0203040510020a0c17010c03060317 81
    0x1541581502e0045801510074001000301c0e00d48261a13a000700740890100e804214180101d40e40c0015142c46016940c0081511000e01002c00440c000c042c420040420384031500002951203c0c06020000c510030b501443d0b58515034038014041d2210003100c0c4600b90310601013003140c0d9041480280c1c00c90400e08001038420030401d0030300d0600c8400d0b007000e0613000300001070114034250306009101d41ca000300150340d03050311120708020f45107106100240040d0b0041c4040340085407128024030b1000c0546000204445c1103a000900310703000301c41c5207002082a80d10100a05401c80b450300344111654821211540c1804210114a000061012141034010035040c920400420650101402030521191607a41d00ca5110540140d0303404106c0390403a01501060600b40203001c00d040c05030301d0380c02440c1003500b46001d0016140039522040e045100f1014400041401c03022280058103104400c0304032084912030080c00d664001c8074607010985880c1e81040800c0c1080c031280900181c0c2048030b540e66 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 36523296 1250 36522046 36522077
    0x80106110a140607020c0910050f180c091305160f030209030a11030d020312010504090f0204020d06090b0f1302030702031c09020109120b070e130c0809060901021306 73
    0x112008000c2c00c00b21002c42040c074603800083d1040c03180c0c2981e0301301d0b84d00c65014002e0240e101c400352100f1b0b00d1000140f400b0b010307070b01c3c1000848045280c050481c41550b4004070030982488420380703e003001200f000508140c6030a140c0c5d142400c0016100c01840641400c1c1041481301a80504410412011800340190b103442a01243c4810310000c0880f1507080040c28040348800c6440d080911921030b84000800c19030004c01514001c08218818015581c07030f08040c040523004504084915810705030700400180e0b1390384040d010059154000181c81d50906e0500740407a07110108491140803440c0ca03e18482d034401000c81840780c00c0c0300340541c6a0b12441016403860158541004010070070070145803d004480d40045402d90013681d50038101c550321410320003038130030f0460f01401400031000043c4886000341c2103410701c40c0c00039164048440480300e2542c11140c01c00e4074080014072401c04d2028808041000c00d030010011030085140c0801e1050b400701c030020621402d0300323001e064014443c0a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 36524546 1250 36523296 36523303
    0x19030201050d1a15030109140c0307120f0c08061005090607081b0609030c0706080411040203070917030c060606030906060d0f06150e0a06060807120902101119020108010611 76
    0x82030b4041c00c0c1810018050b543c885107074000340505887c5c3e84c41c2c001d0705280d0310303d0b65003120701036151114010320b15110000200c1e44a020016030410300740e19119080720103542c9100742c0401881c2c5645003c02410150208507280d481c803003101c0100700c010b2040342001d40e6250100c945065009040c140c0d5081ca1541010400b11030348bc01600900030801003201280c2c0100c0208440c100440507a40d01c07544800c826141c485060310082d00c10540444890b52508150b4011a0000f8580c2005509650380e03009808151441080d030222a0300003140c0d0841c03941c01007080c15041002194401c1c05d6151859403d6035540c00200a40d121f00d071081d414805111308180a02d4060b0340085041c02a1f6030501c90400e00e000d554411064100c1039a40007501e8244903100d40c0741540c859a545c0806030300d0f9004200d0362100950040668580d86224400050744c1300e409040121540f91681c1074401c0040041508040500300174000a9034504040b40040c1c0e0300c4004c460649120b401c041c1091504100450715 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 36525796 1250 36524546 36524591
    0x10806060d050a02102a0804060f020f0d0f030605090103150c0917010902120c09040303051f03050a030e010c0507211514010501021f0209010c0c120219030201050d 72
    0x10442d00d004600c4001552011203242d5550782901d01d8601e80e1500b041d181d1b040141000c01030070104050200740705d22440f402450740030210500c11205d04c0746000c0038040c10003c0035400c10380450120840700141640601844009010490303400460b0341c91503c98041c410049000c03072424955405030340e9116030013108040c0103815032200b0707241851002480c80340200701d07590302a4032900d400d0901c051b5104002584c0d841c034440141404035661290340c0e06501500307001c2c2c4042c080851403000396441c442d40020b43c1c0001c3d4068402000c1665840c18050005100c07109194100004071b0401c0022a800242c01c81c215080c03602c50000d0920f04001c210702d4844070b444020b000103074414140340701c1d52558000303409c1da5046200340750003a6070761001643d54038044407604c407019014441e80080300090b0390151101c5101030400c03460b0903c00d690f03005800394483d040540201031030506841903044c5500d461384180040c030461001c0310301307540020300203010306d558200b03c1d50b4a4030240c4c407290080c0710b141c14 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 36527046 1250 36525796 36525799
    0xc090b210106080109050c0903030a0e041b02010603060e12040e04030507080c0a12030c0215090703050607210b060d090201030b03011a18060a0b07080f040603060501030c08010806060d050a02 84
    0x15055611800024000302c42031058005e000e05000220703981c07940901c00c98a146200600442c40e011415205803041002058115800b43c0e642d490402450080d082042c4402456400082c01c14254601002200c8160001210703a501c5404000c0305030301d00c24102d80603107140200b804e03a10381d12841c00700d8040c40f0b0480700600c64000881c9291818000042440e00144a00d4143c80d5102064200300c00301c1e10280b0303a0700c3c01a44202a500202e420502030141c00c0000807044d40e0f4031680300d888641c41e0400942e0048001744c2005c500320680c000d0007500c02c4041c4542c050600048012000240c0b0300c0c000c2c04000c008140d5034010007411603009900440d0103d00c090000d1140c0603c00a8241a008100b6001e81c0103486044807802d01c242400ba805206400003044510501d0400356000000e400caa102280d10440c10401c03000160134003409040140940c0d9004160b40e0301309800141902d0a0b121203a051006000c01486203403c003090a84d4440c409030b500d06007d000508290f490580410b2029 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 36528296 1250 36527046 36527107
    0x601120f02040b1c0515040207060e03130f0f05031209030f0f030306031020030403050f0d06060e060a020c0402160b0c0901080609010b070f0804080f07030c090c090b 73
    0x70320303181d0704405403030520400860807138040f0035502c000080e540102c5000b0015240c0102c800c001d840c1c5940904940c900440001600c410103070000c0c1c0c039540c00101d0040300c80c1a111801c00100340f034035603410b002d84080c44005001d1490140070030394410407840140c40b0b50304007161880342510108885a0303003003d000120303540707001000300554a81c0d00507501a4003c0c003074032042c006c00e20344a0203000311902c01914080b2a51908160013105c1c0d400c05001181001800c102d2100f4458042018180301410300200080f500d25100020b829404846407150007034106000581060b80c004c9503201c2042e1060701d001d642c40d80b02548108040152100081c0441680400d10042060b000c0c06016106401c1c2c8403082c40e03031104010440b02000c2446040001041000390000144d4003036907014140d07108185041c10a80c0340c0441900341040b0400c0301400394440b000800a03c82c06604140040004420400c00c2c140c81c1d442c0200b0030b41060150100540300002c0000e00c60b403648141c005401c0c114007a0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 36529546 1250 36528296 36528299
    0x60203250903031d030a0605060d140c1813030c03050904020d0501050405130b04080a0504050904050114070315030b0603070312020f010b010203090f01110a0503030a091b0305060601120f0204 84
    0x181403101c06010560000b034920001c00200b13045040020700c200e40040041c0340b10016603940c0c0000d000003d240c1900020080422800242012610030b6411503072405400d46154580071710000600c000ca45821031010b00050140017800c0e03104102d212900b601e000a1005000d003816907440c412080155009817000442603481d000c941c0c8442c3c180c540c100c0d0140072648502c3c0b50101020303a269030140c283c084003404900060b03c0e8000500c4c1400305801c1081c10169030f00c000801001c03040b5810350381030351210305581d205d080f50982c0561090083c10200250070702600c2051040165000c0107101d46008000708a00c2e0384c08000c00001980d003c10b0b195000d042c0c1500080d26021090b602000030b42c00d04040d118507600220644260f4500909185018060b101c01114420060701e85132586000d000c80c07002c04100240f004510404681d80c001c11081c20500e0511107002d500e8803011500482e20704203000240c4082a10740d0006c0b82480e00b00130590703d41031240002c02c0d600f03940700c07955440003c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 36530796 1250 36529546 36529621
    0x20d0b06040b090a1409061b0a030e1903020d03060305030d09021201090f050f0111090f0d0510020406110705060d02090307080d0e09090105101712030a0504060605120307060203 78
    0x1c0405140340680c1d4002c50711000e070120b54411060b200d011500c500340e058540403848d400090071003204245804141022400026400c1c0240c50348000c2c41c1054940c0c280d014943c040081110301161840d0800007580341d80c84468907030140e50105c415443d01c7d41000030642d50b17810b425140400d68000204011106031410115010034400200c0c0c80340103401d2415901035040c03043d000d603500240340782403500b02c04000304404061804400b60740400c00780b0000c404030701c0400000390a2280d03030b1401039a49003031400140c2088810711444046074800c0005000c182c07281c6003994082414000090f84400010002074204403858011152034480c08240c5c1207903070381c4141d41c01c01000040c2e41c0460706440b0880224203031038084176203441c0d0186100c03013003041044403000aa020119101a40d516030701c210801400c40d401a1004042c164a81d0f040c4001d103d000d1045c030005020448641206003401d940d0a500d074050690003130907056002c40042c601c04038098180100901140098000040485 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 36532046 1250 36530796 36530801
    0xa0222050c12070f0206060103090309091a0406050f03030702060703110d09091b0806121204060c02040c050406020a060203060a090c03020c0709060b221509170604020d0b06040b090a 80
    0x1468075550302e0400080b070395990140b85498010000c99000d04055a40e050054001d07100420b4201d0400c6803c540016912603c0d1207188515181c41c1d228800001e803110400090f0740c07040e00503910a184458140140380d40c000215030b040c65055800715107400c12803c0540e0410448600d903140b9000343d100d01c2d40d0305076002c441c19041d00c030304400030845a080410029110704030201104081119080070404603d4a190446107403402a400c07102e000010b580e4120190704030342d0010303001c03460134030074442145414024940610600d1501905003407034581700035550600203c020306415400004224651100c11010003c3c1c1100c803010b104641c0700c002c00400941c8207881503c228001c259010524884d0b41c0603e0307044600c240d50450519a42504071109910800300760305921200c200e0004807444030112210301d080c00c0361100500b5520740907400d1107800340710a000010350000700401c0f00580c0d561000041c3e864000c0070700040c60b40d41c400414020015440690341c480c1445081140320120754 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 36533296 1250 36532046 36532057
    0x40b0406080f010b0909040219080703021c11090c0903010504030503061906120b0607020307030f02010f020d02030318030904050406061a0c06060415150906110f0a0222050c 76
    0x280c0e5121038960700c182c201c0c80d8800c2e081c0913040d20000104400e8100c0d251000340a5042400205451015040e50401810140c0ea6502c041110f400401c010030a600c0c1100441c0300302400c4a51300240c0080598841e480e610500054600c140c0301720010503442c4c518a0b040d00c00380c25024008010500789401e0183c40d9130002c0712014400c414040340010718515511000e0300711603d41e1186540c650a506034171010f40350302a209a081203041c000c2d540540d40c20480c0781c00841c0100303189a14000300740001440e80b80c50281940565010103806450071341d000003144e0b4440c101070140c10b10400d88260081c00c40c400e0f412416485070401c824402804401d910420845408502442c144681d030141c104141c01040a800e00b00d40015000502c0c0d82000c2d0020b00c80d605100400c04122502c594101d110a524281d0704070000c4d0042a041c000746400c86440c8030201007060050104d58a0390880540e0b0b8460310307200074000c1c409000c521a24580603c00c02c1242140907005010900e00103c500e1040c0c5c126 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 36534546 1250 36533296 36533309
    0xc0c010207051006060512071b0c1827021306090e011a01030c020c090c09060307020f16030203060402150d090609120302090105031b040302060304030c050601050102060c071103070902040b04 84
    0x1080c031300160440c016422a101d0700a01c581c03001079039540780d00507100101200d1180a580503400d042d03e000900c0d01440b24051b101585034064900e400d92000800c4a0918100e02480c803884102442410003c05070000d1655045407280e4003419451408030240684d90f015000f0181045c2840c01e1250b010b4203c4411500b90141c01541041c0350001103007668800764910003d6000700440300748504000c440300e980a200302050b90701d0155180003040c4c05600454a1000680000f4500f1906070300600061083d007000e1201c0f2011175003035030002510707140058402886020107808040c4000e07145000c0d80c40100884000300100c0d6450306050014004010f822111864241d10002d5181e0181c42035a04260040c2c2d2510b04654030648003107041502c40c51804401c980c20300002005036103003030086100d10322940e2441240e05a62905501c0c10106800480c150b4014000b0000103041803420390342403540180aa0441c603078030001290070708400c2d4101c02561400024045416007001004200301e808 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 36535796 1250 36534546 36534551
    0x90c110307170f03010e041202030a0504090209030a0507060f090f03020a060804020d0204050705040f0902040803250b010b04081902060a050901030b0d0501020309060a0203072102160506010503010c02030c070e0c0c0102070510 99
    0x70b000790f00300c0e141c0c0714bd0110000824801c1c030017408828400d60107004856009000c40354281c0701070700d4031450310030907900400000d11480c0b450881c03542d01000500c0144aa62032980c0a00c2c1180d0001c4c403010b145028010400c411900010f09554506e242c2c2d0907000c0d001740c010006418482001091580035005284039500f5804000803c0c606501c01c40b81242ca8907406076051841071854020102d0020890282e44080701c10020049071864088074001c003002e20300150344914003084e6504107180340030200a09180100b6000c0540c4400382181c45141341440d00d59036a0b00c3c0500182d005120b0b00811942220300704030b1800410005500450041e030f8240110b507802e41c0c443e5108820392000f111403600040d1101c010001410b40c0c240c148050405040001d801d02e04075000090340640030190541d001e80c030450040000d42420721418241040c944091440c0c085810002c13030381e170042403054280d100010800203608a03a00000e443d00042c0402c001c0d5658112800d107031740e907150918043e420151 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 36537046 1250 36535796 36535823
    0x10e01080c060313080a020a05030313060e031903020d11031501030e0a0c09050705160c0e0105240304020a03020d0303090302010b120a1b0503010e0601090c110307170f03010e04 78
    0x2070482d0036244070300c2c8086032a0300140c00e281e4681d41c05d41c010038844010f500c2840322800c000768060026511488519a243c1c22690480c1003020540b03c0901a0b080300360030402071002800086074900c13020070050709000d80d84e074141d514544001e0a000b5601e0403035020202c10f0040d01c1e000400307600c3c203101003684c0500507a6280740f4095101e0031603540081c410009503a0808c071096440d00300d182e008120f03041c80c3e030030500042d48911221a1041046451440c076640500c5450b21032481203000d0b2000b07840c800b110b010103034a04221901003001c50a107014011000804540d00e07031104c100507550140c0f40c2e601030300891802401400007440e04401550a00904c0e03101070500c002c184448004bd07000511130700f082c0c0d440319007001c40d00c1400d29402d04281840482e00d0b8034240500444e00d01c442d4010310300e1390305d08031060003250101d40c0320303404004003405800002c440010690b109503401054200c0c04074482800130900d441009003030120628080000642111004451403045009020425148 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 36538296 1250 36537046 36537049
    0x301020306061b0a0f030c0b0c0405010c11060f07081201052209020103110408100608030304050717010204050910030506070c121103090a1410020d1b02040b09010e01080c 75
    0xd000407154681c0150051122460340044000c10518a038800300603640c0012a94940076194000c90b4002d5010a058080010411049007485035110b2503d609090501d401c0c80002041c820303482c01c0181c250320b0213901030203180c0d5541007260050a000401190f4403401c502c0e1040b0150011941c00c0001d2219030000507260804140d2603000381ca80c0d9901c840c010312020f010320001c200c040c0e016410148e40d800d4004104510b03d004102501041000f0043c0c91001041c040649071a81c0202079160010b105010018800040c01c2c81a030304481042400e540760003030028024040c550103a80e10841c84003d110350801c0c000040001d4a0258040d00c04a555001046e20001d440346002404282507190a10000f4401c1780701840c04103440c4140d91401c0f20031400108580480d4108141d911180b40ca0b0f0400d503e0700c2c2c1042c14001002d4005080c0f1a07072340300009003001c041c0b460160041c4407100c1500f0210355032644030318070110004120003081d5031140c051468a4200340103034401e80c0f1401261001c41d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 36539546 1250 36538296 36538301
    0x1908090f010905070306050a0f050a050a230103060507110a0809010e03010b011d060904090501050915070203030c090609031507030507090b0403080c01090203031225020309090711010e030d06050301 87
    0x41500038008194841c07175940c419006200080210741103e940380b446062644090180c1405440c0700304c0d012560b0b043c01a981d00458407025005101a245488031695020b40070200343e0450f50008000546660b4804042c0e400740503280280b0b0150084403100f80410507220013030101078200303a031f91082101304075003032600302e42404445502003800a00e156100040c102c0d0000f0f0035090203405035041c00180c1000c503050340c5d40c1580448250751103c0811882030020040243d501d9600700340000a400c0c001b401945910014040300c1554400103403080b20f0782c8588080303030001c3c403002d030464501c50521507400442c0034040e5601d40c000b0b400c00c004240340c14407410a040a684110240700d180500d035a88400362540150310f4411655222a400c0c00503a03000c5c405041d445e902204480d0031031402c0c2a21001074003980590f02e04221410803401411540001507810942c0d05071400c0c00b158858200589031f00c1144415000320350b08221002d09104004006414103c140c50001d000e0742d52140105401d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 36540796 1250 36539546 36539561
    0x70b030c1b010209030a0606030506090a081c0615050c0705010806180a15030b040c08030a090504050414010e0d020105010b0906120a020c16031509110d0201051908090f01 75
    0x404200c280300c61003036190721020484003064000001454107001d400401c0c204030710302c1ca041d55031039a1103030300700140201070105560203405074004d4450b41c03803603584200290140c24002d5015a0416140040d00e591a500c4240507000000810000c03449021005000e81e1299021468034040c60400080e01e5024a54160207a14001c20701075a0003900207051450030300c000c050b12921900c070146511702c54680031140c070103140140200c20540c45c00f410075104503c0198004d0b2040e500030008505c0031944004c0c54001c0d10000c550215441d00e41c1c0c1480020031444182504c41540380a242c41c200d030000048410304041c05400921540c0c2c3d03917082c1382000b07004250226801510421425038a10451651154000d403000c400504280b22900c2807868061456040074190f07241c00c00074403e100542d00c00f007145c00d4130303203c01340102480341d80c1d0341040d140c1400e80c450150a4096410085a0181095801040000c40d40b00119003041000800074401515280710300d00489142c594100b406029004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 36542046 1250 36540796 36540811
    0x902031209180c1c0b131b090e1909050f030a0e06030105031c091206020d050109020903120a033213200a051008060109050a0e010509071704080c070b03 67
    0x5083c421044c6520120b0003d038801c0780b140380e81d51609980140d995644410850192400028031010700b0024454041e040c0c6c110a414000080000c00000c4540008194407002070500d81c52404211500382c4041c0980e000c00600c0c82c003e840d505242d090000000d130100c03120582d03415502c0c14002080c4002c600c803c0c0542600b613048141007030b05100126100074410002c0c0e103856103095989201c03d00d8120321561007114145d80014000700744810130b00503030f40581440d0303d045242001000010356079003040c0c106110103000c042140054039000340d100c51080c00031140c60000412486180c10140d190f2607443c11481411603000c503104038410400d041a4950204111540c040f1f0f4015502c0024444000698800b403d4038003c1800d8030303403502400c1c68002135155041c0700c0c00c0c0344001600b500380e150849030040d480b6034010005040d404480904403007044c0e40591072900d4480040352020341643d07031103440740d4091050000b0404400010901c00e146102a1482940c442d03c4c00c561600c01610b03841c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 36543296 1250 36542046 36542071
    0xb0a0b0d05040311060a02070b060603010b070f05030d09050102030613090201080438061e0d03030b0406090204180b060403020919090606080c03010e120f0706090203120918 76
    0x19003803004039502441d000741c001d00b800c9241100754a90f141c90703c0b104450000c20160045101010489411401a01b2020403940d507411076051800c01042405407001c041e04c13002c0031a8003030301441400e2003200c44075150450240140c01071030510303901130340c02902d0490149041c07884819078500319101e40000998140d44036941c0b601c0f0b940741c01010030079629000143d40040840e8042609c0001e40a03c144041813190024525008081110720095943e45280000c1d02d803640d00c200781d4401c03009100c842d506090000b07009408030081001095160007540869100050101e034000e0060000070b085000c883c02030000300084410b00080707001c2c52000a410414000225449486800011240950f901000900361500d81c603a0000d88071140e00091043e0405900304040341030a0080c03592010910000303007040148941d40705420310940c00403000c2e0040c085039008c1082074942140c642c0c01d40050440d030902e00142007070481503000138030030f600c2800980f80c0650343d610012422481880b104020 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 36544546 1250 36543296 36543307
    0x30b06060c010e030d09060e0c03120d090507090501050a0b09090606090102100c081005090115030207051212010608150102060a05090a0f05030909010f15030b130207060506040b0a0b 80
    0x40c001a41c001040aa20554844280e507845031400c0018254445144c180403814038254282842101e50600300e44900e40c01402c00f50250b510002452040340300003135101a690011051500300030030b40b40320014024021404009884902e5400041c1030718800c0f1124051555210200003051040b51901d64102c1d002c000000d0062800e0805480c0c00c00c0180181c1c0c60902c0d0b03e840c6041244c031524889008a070318101030044500030301c0000d001414040c1c1e4844465410020403000701c2c140c40d02c11404142d00091220204030080c40540b400700300c8000d40540f90081d03119400280d601c01d01030301c00002c0312500024140c03840c40f06110300280041e0042c0500d9103500c888038003e804028203411040c414050060000f8190203119040180620007a646400c560005c001c1c4404040c1c0c00140044503440080c04a80c0d154100711800d20510700340084d1046511000c6170501100601c0300d0402440890300d1018070090342c105030f1003508100c0d010000d00709a48200f040044060040300c0c0d1402d800e001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 36545796 1250 36544546 36544549
    0x30c0509071b060515030114010905040c0e0103030305010911090609010c0305040b0a1d01030603020102340b0306010e0301060b04120809090915010806010315200a0201060303020c0604030b06 84
    0x14454220700a4549001510544009819415402c803000c5900c5603440d010002440c107600003218101604600910007604d28200c1074070010301c1805042a265914004503040205510741c007030062100c911110000c0d0f80d20b04000d40144000d2094030151428100b4400b1302d550082c04486000c1c02c001c00e028207100361003004482401c00200110f090080421002c160340c2034002c064545172000b542d0b8100448000000410082c51890f8900d060508044061005030303004524612a44e04000c0c0c0c00c2c840b495207007049401d00a003c4203800c00d040c01040c02089010030302000314460102030f00c03152105071019082c507088500900c200c0c80b40000521041c00900390036518075040c540221540c6040990340380010341c900c1c20a540078401d83d4020381c6a4100804e10003d01d07401418510013070241c942c516129175810315040202b01112565070140c02200c10000203241e204002829a55034641070340c407102038000d0595010aa01500c20400782804070310b004421076042e25804142e4054540302c510 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 36547046 1250 36545796 36545809
    0x30c0711150c010e01060909080a0503040305070c06081618050d02060d140601110a0c050907020a0501051602101505040c050f21011202090c1e0403050d1107030c05 72
    0x1400203a100702a0040c68030039035088030142440701c00b414000a51955410001801c44100e0340c09010032500b8004003002142e86582911482c0c40300b0b0810558036030302da14003201c0c2489440c40c001c140c08982a03002c01c00d00d5010403528814501c4620194210203481c1064480342d101c80031a000401584030f0610142c1045d14060740d0191019100070708107140640f10b10151800e2041d064040b640380005c103c0c0540c1d0000c484150f80c46002c029050403520b50700c55044080e510300813140076618850116a00c81d00c04c0010300d00d51070f045002005070b0b051101c201c0d0345240801070007230010f12840003400e480c0c04141c030904807000300e40c3e00c10021581c0303846d060001401e40100c0302401c0c0b05043c0121016a6a1040142411160304208040d1107441d107624050504044e0041020031241d4400c140050704c41c110040d8100640a5080c0d03194072800780c03440c01421407041272180d04480410000300f048000100b41204020603225240c9012074105a142c1d507024512028240e1000c5110400c6a401c014 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 36548296 1250 36547046 36547073
    0x30f0708090c120705090906100f0806011509050303130306050606040608041101031104060210140411120712030509030607080601020d080a020d020712020f03040f030602031302030109080409060b030c07 89
    0x3e0003640d044550b0758001a01ca031008688044040d00070303100f088500008030014030050b10382c12320500780203402d00040c640d0b1030205010300c1500494510482d00107a0040b441000207050080c1142d5541c144dc1d121542d02c030740180b2040342c03894246008103c82d840e0a405440584155546651823942c2d60b0b00e560201c2801100818145a52410842684240383d4002c04c041c0555400820808501c0364121044405122603a05a01010011300c400160800c95419124000b101e2920301c400c2016115824181da50b4840caa289408210900c201504400500301c1c6400c201c05403003440d40d07000c2003035030841800c0322114016008841d1000c5414029440c03590401c401d100014100001400898102c2e0b2101000781d41c03441083c0caa11034110303410014003c1c1a00c94002a608003440c1140c0f44e600a03d490000800c80c0c0d4010001800c510f0002220b03214180d0018024040407400c1d01340b01d0016441401510f00c072909200022a8015040c82280d0240500411b5186400e8142c0c50f07410141010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 36549546 1250 36548296 36548329
    0x40513050c09030304081c05120f040203070e07020a020111060f0606180406030b18122a0102030103030504031202060601020312060d050a050d03150506040603090218010803030f0708090c 82
    0x140b240b020540c030104090809048080300410603175030300e6140113030b000c020103075408100301c0c1c104210b901e4031400c018884d40100c02e81d640c2158a4665100107070030311030b4030340102000e0100c5a0410196a0740024408411030017a00d40741b03103040080078100d0315078800316035041d442031044001c01c00b1814528018456100d4940d50312140e040c1100010b130565545038801e5451080e80f80a000307480c090b1001c601c1421001500034581c50188030854421402415140d190010b02c0100c800130310700f01d2260403800c903028400210340d25070b140e10740601b031a04540000d0324180c9080b0444a555800000c00c50700486050300214206004140d40001f146001030589800c000c03034140c0013001035402c00065101600c640081e10918001d10002012070b90b1080d280c03480801c03018001c120355143c80085405407503a82c9800b0072180b0341400420364226000074100c1601602c980009044440030001d540500303070604400c49180c442c030404442c80c5209407a44003003a0009501e00031030f03142c04607544059020 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 36550796 1250 36549546 36549571
    0x304080f0304050106031502090a0608090f01020c010c0e150405190306050a05040b07020d0c060f0b0901080703030801140105030f0a0e250f0303120c0e060a020c040506040204051305 80
    0xc1500c080035180c00940b421100c0760b46030312080c006c1200b202616258000005e01c1141007081d6000000c0c0444503900c108030500c601840482c034200700502060111240e901d009540d1110f1230400700d030080004805c10310010b83c02100300d10191904001a03030000f101116091f04241c101001c10803021040c00c04504a1000364100000052890080b00d1240000600009051034607091070b03010708000a01e4a011500000313003c1400e5500203423103101c0113400c40800102820142c1c00304c40285094080160711483c501d00000d40803030700080e40d00c192846035440000390703680c41c848160002d022131103d90205205000180313901440100082d88281013030000b080b040810b07100a030030081e0a401e030b008180c02000040040074085640c5100425107041c0c4030f0b2101c0d16580f00280500d40c5c03568080f280c15100c1301c451001c00c0c45004200201d4200400c441d6944526203406980c40d4241c91605000d182000c002076583c3c9414400c0e80d040780c0340036144209001d1942000c40040038001e1410b8250107 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 36552046 1250 36550796 36550807
    0x6220b0c070b0c0106150f03060e0907090504050a050a1217010e01030609020103110f090307050303120c0304030311040e01030b090c0303040b0702180a06061d0307060e0f12010605010f0c110105030408 88
    0x2114240c0b92003071b1420384604100c0340301e06c0401010f80b034441c0c00c02c581c0b2001200078040030000010b10714040305d00d400e8001885490b585003040c03d1031014540948940304040004041c000080480300c1407480c1c540390110900801075440c0c2040c4400d2060307100d0020340100410106246030000a45070748140f40004903904540c0d2112910b800c0a00d0038059483e0104a00180d4201001750301c0250000700c00550a00c2003040202c2c204400092100081d4030010011504241c0aa00580004101824119107543e00c07040c22601c605001d02c0155110300e02c81001c038414003c04103101d070302440054061071034107080003611540d5910240049070008460741220f204440b420013840d005034010040070811928000d0b0043c600320607100440c1a1101458010401d0b41c1d000480104840860500307030b020005400c009980039816000c40c580200800d00c070000c0099065101405460090b280c4140601e02e02200300c99485840900920040380c004000c40150301460203158443c2c800c10a1902e0507 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 36553296 1250 36552046 36552059
    0x5010501090b03070512030f13030b040308061804032c030a30050418021603080702011d0709020c0106030210050c01111c05060301020906220b0c070b0c0106 69
    0x581099102808441d070b200540001460305200400c01000202c46541055400f488510744a00c80c004003008050390014444460351341d40c00c0003500550708007440060a03c0c040c14060400c080c11100e003442202807203500c2891010100807980a550596100c410409a070101242408114011000c031144a005000310650382044480745d00c43c0b040710a051140d8030140000303081c2412008001e8040c01e4051084010340e88a02030364216003907480c00f408017900c2e54181200034030640424500d0610203081c0c0406164120b01114040c06090740200b01c42604190003d80c2e00d0b0022640b07050540042c00100f040341c480e038010b44420308801000280c01ca0f40c80d40055644240800403401003140032a04105520b4281304161103801c442c140d0520b0890402d43c50b4215000140005e04c00603991004a4065103096060383c907005005403030301c6c1e655241780105050310880f0555020a0301e03040b80740445d2400104c400e803042456042d0050101d5808d04207221004d8024115a544039075035040d0008a0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 36554546 1250 36553296 36553301
    0x51810090203101107061a03060c0913050a021206030715030b030c030d08100608040305040303050c0a0611040e0603011b0c150606030615030c05041e0b030106030605091302031b0103090501 83
    0x20709403150034081da41d00c146d240c80815500074401a8080c15130b0b140c80000306460200f40194413488000d405641d0b00c2c01702000850808054000e2008246080d04010042c2700310740c0140800040d000c4030124a5070b94208169071501c40b40510354000141304550700d0068000d0f0810640c000c401400e17035034416040c00c040f900d41b540503420b59002540351001d024181c126511060040c21482c580041c0915003a140500f4612a43c44010200180056410b041c21014408141c540f5444801480300b40c00e54800c08a032034100f405001d840421100118070b251030144503581072844142e00c0d0342d4120003044020798001a45850a640400c00954038640c00400c6201c0e94000e80300545000a145086c4400c0d4030f6400c0b4090710741c60516103000480e000170f54104c010741e0301310346c0c0d8850040d0f00315a07401440c01c81080701e580314920450b8080000300d80d80e901504040705803203056030304003802d60390760401d90701580b8250317406900368200024803840601c41d4245010b2404040c1004190102c0a0303442908 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 36555796 1250 36554546 36554561
    0x302151b06090616030b0d02100e040f0218011704020907050c060403050a090e0f0103080306010e0a0821041a0706020f030901060311030109031b020d12050a0305181009020310 77
    0x12604031a08004400d201850006413102c243d01e0100039800d211804030f42050303603c4002910421a02c840344203000d1254041f080d030050041e2040c480600c549002001a42020010001c04065040070031115441a000041c100c01021070750402074603139400b0301145000251a040400008100c81c01200b04200301b00c5015500c2640d44564803900503000070314021894100e8411031240500384040c203181d07880540d055a40004d9995500c1c0c039000c005a68101403240c1c103035004403c0e0000011540808a1200010900e100c2c96900d20721020034219407910990080264074803011150710001142c01020b416071903c2110b00518004460594030b6041d0021651940c2a0303440e0042402007011907912070000070300680c000d10520003141c1c0d02401d1100c0c1d458000340441103080542c402c1d0b581d00c603128042113801c140d03900954201110001c0031603000d81044000b2a08101c08107610013a109004c0303032503e0040004c0c1c2044c0c00480c2c0128050008508180e9252040e8100b00b030010501d03204102 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 36557046 1250 36555796 36555811
    0xf021905040e070c0809121603060f1404020a0e0a090b01090506130506061815030c0307030c0504060c02040b0d02060a05040302030c0406050a0605070c09050721060302151b06 77
    0x3901e403480c00c5560300700762100401082c100308240307101d40001103020b0207480e5441070480791182400088600189055600c62107030322404c44004001084c0305c8560b2040f540c162088000f4480c4082e480d880c4604090b0955000b03400a2000404011081070300d140700303030480c441798000300d00000d140e10b41458040c0d082e00203600080da1801071004030b142000b0a40c2004051050a0080d441e00e6000510140103824030000c44c7c01c0d03081c00703901103a55407120740084103106030007150f100d00380130b03160740030f540c004407a402e02092400801c081118040c0081e2012590a0760752656003040d45c1d403c0c07201406190141980061110b00d0000040e40c4800c0074000d51016691415244c82ca54010940b0b008220038503a4000d81c588078083c84076850f4045200151209810b1540c0d03181d6440c50400c20b08a410742c1301d00c40c418600030602440c0e82e0b12078520700c981c80091407040b0825031149510400c5460906c4000e50008540400e13150030f040070005410803c0080d26100980440038002c0b80c2000c0d012110300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 36558296 1250 36557046 36557057
    0x3030209040b1005040909110918070b03040c06031d0729090603060d020607050708150901021306030e0c030f0106030b09030f0904020d0603061d0d210f0219 69
    0x901660034144580b9010b07400c2207031070790b030000c2440a0182c240d105178000d243c40a520b80d40080240403014050380054203000c3d10001d00f900e407a4006404100300c0780e0142100d03000b6050002641d50100d42524050350708401d50540243c902441a801082010b0b4003559200a1400714070b403400003030010303070000d10647c190f01481280340100c07087d585500409480310480103004090003a01c480c0b080e00d42c00700f815100c83c2d49400f490700009040b0700810300014a14464140d003c11498804030b556103180c85040440d1880385c48000c00d1901342d0007001110504c000c83c08400b004868407076080104400c07540307025104031981c12310200e8100600602c5400860303450740030410401452802d00c6622502a0340a181000380921000040380300b8075040c144030320b801080e82c0c200c014213580410300666024208000160070301700b02c0098440c411300d51714980c2c01214008503400f8000d008000d410b11440ea68080300c0381d0070300307003500003485850030b1400e070303554280100c00004100c3e040ca81c4103c03050351500b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 36559546 1250 36558296 36558307
    0x30712110307030c060b030a15021306030c050a0c03050c01291906120605040203040b0601020f010e0a0b040c03320111030a1a06030a09030e0409020a05010c080c0109030302 76
    0x19000d44018031020126600410500e40800c1d0701407040c0c2c071210390001000c6a91000d400000f071070440d980201400007080c0221400c0000c90a500400940302e0f2142e00101041d0744803000d4044074a80300044000c90f43c01c203d880781d02e0b4828000410300a20a0400c1402d003060030f01000d08450881241e83c5480710b00d00003014885c101d058840005100495843c6d4440e10703140440c254403c0e0314032a1201f40304080c1b83d29a00140e150b0440005041c000d4070854481c5018184105860019501a800b5028440c6080081c01040c001c0d00d100e0700d045c000902d4940c00c159600b00c2c4070740c0c009000f542e04c2d102031000840000c5508507084100c5031800035480c420100d0008000d000c0c5500309808451340c0c9024000c40310b41c0f86400c2600d40c0f0200c041d0002072000c072481c00f102000d54240700056031105d400401c021001e8040d07806031407050300a9a800324100c070000c05200494954210280d0711a0745010200610741c030030300d40c1e00d050a106284450510b02c5210b049801d454045004a01198020a0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 36560796 1250 36559546 36559583
    0xc0504030b010b39011406190e01060507051006061107060c0b0105010503040602190207090e0609071203020f010504050a060f1401140616080408010606020318060703030605030307 79
    0x1c0e0640500035440001e494450182400100b042d001c400300e40c1d054041c8103880d021444a11494000010341e00300034420885101e40c2802d4240707044420354401e080700d00703070001c1c840030640103d0301380e03100c849854100da401d02d0002d85180d00710820841e0f1a104000c1042e510030441e02030500108100d031905d55021b651041e015040007895000202080842600ca00104d410f40741061704441c1e007820480e075280c45908000010784510240d5220b11b0070301c00d010381c1180b0350010329001100c000d81800c02c054400408819200c2c0b1007540d086440358049101407022290204518002521900440d69140c0c4094203941c02e42e03000f20741c03d841c19000080101c09000c40350190002c1041c036410104041030640b41c3e5074031020010f010b48010b141000c200d1440946401c0d0440303540182c0c0b0003000e41c0b400b240d0301c0c091015900500504d441035080090005995000000740c41c00c8080c988241729080d01e0500600c506a0010103096081545442c80040d07a81c400384002c0051034091460f090b01c1240088 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 36562046 1250 36560796 36560813
    0x209060d06030c0509130b06060708180405070e010c150e060403271d0702030f1204050f010203040c030b0604111801090602061b070809041803030f020a0503010b0c100c050403 77
    0x1844580a410031104000d46d030b61540c6a10300d09107600100001d295124400841c049011300702c00244001d10008000b01d40143d0402410500304080b80c05101c641d440b60070845025424014860210741d000014500107074042c900441050145007000408200d550075044c506001502c040d0085003e50520804240143c01c03600308883e050b4090501540c80d0620540aa1b1082042c3c0500d00d070040380840d100510034411103142a082c04c81e2301d0b407101c5400c00c00354180c10059604581300c0c811485030b202550700600a036441140c010040305000c600c0c503200c0c103107103160003085103034006d59803e80320310f8803a038860140c01f10a40c070f1207910284943e03401c0050038114044d040f1005652002d0204120038086e42c0c10910041a0202c10940354801494060482d008445100b40d000b41003424150394401c1011041c3d80d12400f07a174090007901d54525800d400c0b48110210b11000860400051200800d070b48010200c401c0d0000403a94010f0f01d100710f100488101080420008000003400c106008086 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 36563296 1250 36562046 36562049
    0x207050d0b0a09030c0219050a05040e031c060b0d0504030e0316050607020607120503041208060607120c06050a0b10020106050f01270b0a080124080a0209060d06030c 73
    0x99a00d40c00800903511000700c00000141180d80054883e4501d90806200b44000014541c1c06030243c18100c03e1910241004140340c080c0d1030040342442e03c0099a449d06000700301c00075207807038085c500d003054070072902502d0321200103019104da4445030001038090584005205542003a580014503052a180040481840441795440b82d40300c820f401010b030020f4120541203881c100c2e40140e4480c11840401c1460045540c060b10300b551041c02d0240040e0000b000f98441c91040c0719896041203030501c01d0300d880d201900d0587d041807051101100052114005100082c100e0402000d00149035a841003660380c1100c3c0d0f28a00354441c512501c66060588001e00d1002040c0002c0c40001e06040c04035445060804000f030420440150660b0220740c030071040a03807820500020410580c40301c81d070038885d500801c007200000e60494000103621159090035030445403521911444050420411268482c02410071800c2d0b07a03080021104075507602c00108007407205064081030070341c40c5052104c414040c6 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 36564546 1250 36563296 36563299
    0x606110a02010212030a14010305030318030a090302010e18131506050904110d02030a0f050c010c02010c020909010f060620030301050a1203020106051002010f050c09220b040c0807020705 82
    0xc0c4151100503030b00400d4180c0b500d10010300c2d141d00d0307660f2101c04c540070780003010741981c40103080d10012080c80800b1006611881e5503000120b00b003000c0328641650f81c41000044030020b40f02c980c05000643c03140c501e0501d0608024110b40f00502100100035131014240c4004802e8000c001214040010004502003030700c0d0000c100300801403400c4c0110341701010040000308200d0a545801c2000d81d28000d082c161203030003500b244c0100e502c500c1c21504144803048251003034402e06441c1c118643c0701d0307602c107140d0f41e6069440c581300920590a100c15290080d015503a55529002c801b03044803031901c00c030720040c80e0707503651680700080d2046000841410350784d200c4401d4000704014084c0d600c0d08174082045405e020403140090006007022801007070075410066110325141604400030b507054000181a09500108000603150140540c01c0b6101d60030000390411584441c1c2000c10b1243e491120703c49480c0c00c0041021003914000508036040518954041100d0200f03000d11207034100700c854042d020 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 36565796 1250 36564546 36564553
    0x6020f060a020a0914120a0b0a05090c0a060f020c091f0e060307050d0302030903100f0c0e010806040b04110307081902030c16030309150501080d1b0201030c02030c07030501060611 79
    0x44000500400d030300e000d555041ca680d009140215200c035071880101e0184001950028880f0b490102343c2d4403400d0304c41841705420070001c10342059003c00c1c400d841d903500a20a401251911405656907403081c4c0001d029030040e241c2c0c0d50142c0e103405443e984241000413031000c0004510304140d01015482c0c00c0403503080d11910030001c545d14005491002d035002190300440b0180503140c228554441c10030026054062094034124480c41e0f40c102c6240c104040c2000d21500013000c0041f1032030b580492440c0e00094030140402c4075414145e00120440c1c00241001c5013401e2200060046076005035138900c0082e88200c00c000d048200c1d040105000c1110745001e5196040c042401079403401181c08640790302360f4503445402014020f60001c0d440603844031880f00d4044094040b5401004240316540307a500840d0600300700325200300b103130080e81d075034201b0b02c0b0014458540045006000094903007082d44030401000080800811203131000f14070035000401c3c46400c0920052800f25182e6503d0041d61 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 36567046 1250 36565796 36565807
    0x280617011a030a02060f0d0f050403030606020102090307210609080c0601080d020a02060315040513141203130503071401200708030a0b210304080c0906090f1f06020f060a02 76
    0x80e80810000d03d0a50111881038683c03450903061100d034422030340e03400748044c41c00c01c2d030b4841100e00350040361065002c1e0300c1c1000050b6844505900341c0c403803020b68a92540140c0800c2c882490702e00a112000308200041c40324040060f644c580495016040a0f41c003240d01041c11207070590104045030142c00042e000c1e010f880314111010b96100901203000384201c5001c0001844401c0902c900c0712035450040c070038011818201d4911b0703c140442c1c141903564110075a04a0202c0b031002403140c008080540d4418655920460300c080480c1e85540c04541c5404100103900200703031381050000c44250b0000000412204440e00c208140c15600146203c11200b80032110108018000341ca502a05100380403030000030300c800207029520010320303000c0900020032403010050000005042a5107211086940c060030000404c820744100701c8400b80e0041c1c0481c00a41403084282c072141e04640c00350404551001c50b808004040500703900a0f40050303120303100f070081400c0d0801c20b440c0c0004003010210302c0d02 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 36568296 1250 36567046 36567049
    0x31704060f030e030d1409010f021305130f050403050315011e05090a0f0f060e0406030c0510350f060108060f06040e1503060106031103280617011a 65
    0x3203884185803041c0340c0e48480d003c4610b4401e1046070800f589540040151168140219854144c00d42e404100c9603e0310010381c000048905c212080c5014075102c2c581120b00d8101040440320a501c2e030381507125150040f0384006007203030003280c1c025031281c0c9400c0c0c1c403490444071526200c00070309481e50401071401050a04043c14001612684d5000d10b08035959806960100d51f205805a00030000b411f4160300000d1103600d24464a81a9011580c500c605105c00d0000c000a07510940005408103100c80303000c1042d8035212800c40c40c86c6510381862002e5520005c42941c10810140a00344030b428461118540810078070103099009141e5641000c0c54104800001d001da80b000300752501a804821003844a40d03941030039580101071056100b1220701e00a5000188401410001ea0180c4114000421014000e0140c8140d501d2020b211030308695811240310b05040070a2014500c04485825035480c4a149000e04800b81110340c6da07034400001b5a91085084400e00404000c007018010a26460b6 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 36569546 1250 36568296 36568307
    0x11030106110a15020c0a0b04050c10030b0306072619050708040f060e0114040c030303110a14090a090e0703020307050d0f02060f0903030d06050112091a090c0607080403170406 77
    0x2580c460f00005072600070641c012403070302076120030140020a29a0401041100024035036405070015282c5441507919000c0a07001d442031011503603030540010b000100c1080c428030290000c00c080411000b0701c01126207210003622019210580c0d940d18449403680b2103009070042c07079007003c40fa1409186c3e901c0c00e52500314820b4079444006180355220b00d40700c410703400c4c25000304400d411010323100500750030a441d180c80b440705c040c402100880c1c00c159160200032146400c0d00c1c03010585450b50343c50350440d5850700005a01c210303400ca600c00718445004c90101c40c0c03445106c00d41d42070070004100c1c42d815401010315109a56020b10301c680c822091007000940f209004d020b00680c16a0003584551001d00700f04200d00031901c01c02d13090300c00425000c0c03904009030801d00858801307884c0c0341c00520503810b504042c0c0310510000352801c0003904007070b110131032202007003540314680200340c884603c000e0000980980c44860305940c1030501050070300510640007085c1c6c0340702c050748103501c0c40c1910f4141d01030700 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 36570796 1250 36569546 36569573
    0xc11030703180b0a0302030603060a0501030f0602030a090c09020c010e010c020309010809030706050f0703050108010203040809090702070915140307121e05010c0c030315080601050d0206070611030106110a 90
    0x2c00142200140b4a00c1d40c01c44020003501034a408140c40b9010700d40000e0094008a40c05031080c8130b8071000c03c2d00a034407403107001c0c1a241c11200c21002800c194892130082c0d40080c007d065030b40d0341c8110040c041040c06080c0c2c0080d20305d100c00980e4406600310094207403003004440340741592400046003039054001040b40d006031001e0030302000d2540c0e0f40383c540381036000d9035201400d41414001000764140d05860014407820013614200483d0342c803402a42d00704e010441707004005150401a519503890300826095008407070340304503101c003510303072510030295142d40340d01c000a05080c90081c00400101282d294003e14103030000d00055185ca001503810b10303103512002c1d04860610022400c020014140150306a400c0002805040d0451800800302c1030150f40542c002441d010300608a130700d451380b5800880380504010708881e400c260800031600304414040f0f034807074010401e9800048403406891205c2076030403213040d01c1c3d40c5020340240200441c0885000c00c1c0d086203800e880001c00d0f1320094030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 36572046 1250 36570796 36570803
    0xc09010608010618080f070806011a07060207020d050f0c010e030a08220308181e1f050c1911090403090e040201120f05060f0d0c03020d0c0e0405030405040c110307 72
    0x107078004c28240c000381031403c0c60708820000d0003000174040b07121310009483c40482c0c1c40c2c00125951a80d0796088070b000c6070840b0126010350340741080080301084840c0c01910740c075800103200c00c110010b555180b500d4881020318075102904140170b0a04150f0300143c06c01103400c03080c1d0183c0003101141e602c02107284109444480d40e8502003008040009030b41e60900007640c0e200c42c0175655226204401c01c5081c020641007840340d10000c4583c144444041100201402d000d081040c000c40c070207800c02650768600a0b42c4080250901142900c2c00342080200007140345030f281d5541444040c20300c00c050401030b240341c0380150b80c2c2c1d50501c800250302c0824141180c80354002014651110b1004031011110410301c0303030680e41481404040160150303c51800761740101c0e1592414000e0f070003400282c2c0380c1c1c0880a485412222410000741c10700724036512003207100e61014000544c0340c0d078811481000a031001d4404c2d82c008101807001e828148036014480c445410441c444c622501101d6542e03104403403004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 36573296 1250 36572046 36572057
    0x60b03040f2a080606120a0f060209150405040c111b030a0804080105090c1009030b060607020402040f0e0a18030c060e060108010e0c0906010c02060c030c06010303050c0c090106080106 81
    0x50144000c1d554040701038401c0c2c2442440c0e25880721001904442240507080b01d07405030002041d41860310082c240070000706c100c013600600c0f1440e00d80c0010b081440301d0589010350204040d810303a40d10b14804003203c0c650a40c6450721241411b044c001210b00c0380d82c0c0e00f024414103101309000c2d4200021840f003036038811460310090984050100741400c551850007866400081004a00110190410341c41112901c0458510b458098100041803020311821400f04079082d500380042010030010661000c00901407502e0a9400d6010904a83c880c0c0e000c2d00360401031000a2061800c2c140d0030582041c0000c0c410301080812040540914040c01d03001418402404202820000e80d1741080103100f10348015580250f94402c60369028068807061107650f13008181030410310f0f00c0c200714464040d03441039441e00456a11036080c403507036900c41e02040f58184001d000c3c0810250f02002064040c5100e0390b00c0c81d45882a5002c1c25103881d420b8404a44683c520740c0041c80140d0780003140f90f044038050702d000c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 36574546 1250 36573296 36573323
    0x60b040303090b0a020c0d080301060f0c030f0e040e10020703080705030c030a2a020601180204030510021b010903020a0201030605030a030c02091807030b040201080c0a050406140906120a060603060b0304 89
    0x680c517200c00b0b481d419400a03503020305a424003801d0b234007950407584181c5809064a90401044509081544000340400c0000c0c0241c07035541d200b80d00607400d034031000e0b00001c1c080035402d050740c1c41e2181c142c640f02545600052500205940b00840941020550800c0d50071410081c0d4040024040140b2040700071350f480e07070210034940b07415030114141c2e002e01d080140340d4a40040025200e40007400303282c540c1c22441c03410005100e154400c480880760400f01420708014200f4108c40a580300642c0001d80c02c14180201980300c900707100b45402c0c148030790010a6000c5491001605036040b50780914841e1b0052141080800d8002c218030520560489101c41c241c5d07550405408d59603a90109000284206c0001104029140a100c0c2c041da000740c0b111012039445907601e1010784a07503003c49001a9007031000b00000c600503441014071414450119080403d1382021034215000b8824a81900a600b400d01c402c84005201d40c4015124600e014881c1030300348012800180700c0584010602403035103c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 36575796 1250 36574546 36574567
    0x1a03060103020d051501030b06070c03120e1002060105010228020904260304020f09040c1a0f0f03040201110708030a0e0303040f03050f06011d010303050703090e090102070501060b040303090b 84
    0x1152240140104200020700308010b042d20b00078403a00441b4042803800b08010090f28000041c0c4034001e0b400714002c0c504034195601e10344100700c08454901403104080c9000d070f17295620034012440201590040005614040c002071070003101c1e2041403408041241600c10030035142c0c1d0000c20403501a5041c49181c0c40c4c0e846d007441c41c070440030501c00c40545141c0010b01c00160400086006074000c40710320f80894035400070000c03403040a603070041c4170009001041207000301c2102840c9041d0606c0c004941088902e104023a0281d01501d916482e9800010030401190380006e10307000c910500d43c00802d012030074a14110380d24030a03c51260140100f41c0308840c0b29580030002c030743c0600070000540e00e0060b80ca152a079618407400d107442e48180144000030890342842d40e2000341d07180c8030104200b1642d1940c0c6090b250b035801984280c0412411000c003160060002c20654013440a607400107903144210304041d07084801d10b40042c80700328000c100070030100382d101c6002c00039100003c000d5561141440b1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 36577046 1250 36575796 36575801
    0x2309010210110406030b060408030403200301020d060512070311010e0307080a06090b0a020f0a050307050c07030b0a0c2115030506070302070c08190b061c0605040501060608011a03060103 82
    0x2078501405a04000c800b03070311400650040c1046941913101406440076810400c0154096402941d2081d8010300080022805200018041c03074041c4c01d008030900c040102282c266071110002408983e2030380e50412960520940f190810400b55024180c0d41e8250383d01d1f40202c0007904561810019001c44000c0c4603035007406003130010040d00088a420000d94603000c8040d001c3c0300402d4500b640c2a50000300303410300ca4004ca5100c59850240f8070314102c681442131314190005448002045402e02032010154410020b04000c2e41c02040c05031000e1a0050003103080d1280f40b804541040700c8802418480705145d02c0142c1800107508000c15913102e030a210313584240e00ea500142c0148a944240300005030954010403c15004e00e05c02c003412500c0c2e62002e5507850940c94014242c12030b0303280d0310340842c0400c3d50064011000410312141241d166821070200c401590065901c66550020710080000911480005001900b007108187d894400080814940f000c0c004150f5100000015901da2195 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 36578296 1250 36577046 36577063
    0x9030206061e12100507090e0402040207031704110306070e0312030a0e100b0415050904060f0e010c05130609050303031906051c050709020313060e03070b1e060123090102 75
    0xf60514000803411509550b0b0f541c902c05200920900d40720101380701c540b00d030581d0410f445a4062a98864455a00303000082d03024010540803c1135491004000f42000340f001c0e4001d90003203800c000351510400805003800b030041c12040c03e000c0c48002d5601c2684020510000c043c500001e2161070796a0084010702904a181c4600400c0c006c81074000c000c0300a55001d4820f00d40c05982c200007001907044a50b00144a900815600002e000300250001e0095004686010344241e40411100c0300d80200a0940f54403103840c001140000c292501c1201e001d01103500104454500040c0305483d00b00869220301c800303030104090505a101d0b02e1080c0d03400d034000074003c0c0b0014100c0c400c0482c840c0c8101e06282a441011503ea0180c3c8100048041082c003d0f03d001d400c00750314100d51600a9590000182140d41d0302c2c0080340010b010319000301d401d02c0a50342c401c01e4021510000d070070500280740c81c1c1c0000100070030b05000120455009a045800040d6120003900d150360340d8a20703007000140d2401c001d5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 36579546 1250 36578296 36578299
    0x50606090a031a0c18060a1404090209040b040501050105070f0309051c0501050a050708060d1b062604030c0201030906090b070908010c020304080c0603070c0803010e0403090909030206061e 83
    0x306100041040207011401154080c21052010162102107180c01c203441000fa0402121600740340b004006e1402c4401030842c40500d0403c0120584122080d060a400c99800b9100c42d0394046110005800c0a000c2c004030391800301d80401a560600c40003030842c1c00740040c041d0407500541134040806000d28a02c0029060042201e142c58440c03000020281c0100700040300c985d401c0c90007003a020001401058000c9400340c070f840704140c2d107500500c05492501c10081d101003001940130750040301141604000340101e0b5403041000800811801240094480c0c6413801c6d6030781c0010400442d0744020f10f40000c560910340480c030000d480c103091014207941c3c140a401017520100344961150406d12140840d11300c47c0080c010102c40180c1640c45e40200c0c80b038040c46400081c4a00410b103071100046a0001c00c0781402c0040000603100c84078507800903040300f401c03560480b0038001495000255003000b064161410b010103050396038000c0d10b881001d840c4600524240c1902240101160840c010700c0e10b0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 36580796 1250 36579546 36579559
    0x9080601030f14010218060a030207060203101d010308030103060f020405060307020607080106090b040302060f040f03050a03030b040c0c1202070b070c0f060806030a12050f0708090a090510050405060609 89
    0x31203007450410091070460450f0586411910400c0104040c025501c4030030722030345800c2c80e0300c410900780034259205241810030103508200c544001021031003d94010382081081c502e6882c140204046092203450030b100720aa211801040040e0841c400c803030543e41d000714045038503c111344c2c50f00060300036900b20503030141022007000030007940010f4191080c2100c0d035031051680d903900e009403a580880c0c015810810007c0100380050f0500c40018038200758048505460b0550b5a0380042c500c041a0b0030885207a0000104007082c10b9140c0900248844125010416034603c44c901801f002c2c044c0030000c180401c1c150440000342d000b80031842c011718100c1c44503551140145840f1807045c03810300400c402c040b240000403a006100750901481803201800810007a01030f038807030f25541c045204c84402000400c10070850802d95100c05801d0795031107643c0b40c0d501c85041000b000390098a5400a0702c1052412003001400700b1840012070494078140c1e00002d0356214000451018401d241440d80c0010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 36582046 1250 36580796 36580799
    0xc0303020102070c14010909020304050307020406030321111812030d06090f050601020c0603130203120a080603011109060f070b010807050307090506031513060606050306010e120d050a09080601 85
    0x54040d0020004030340b00300c800d80b003450b0319100c03801d681d0304000175401d000461020b801d205003400f95000b9508a0300860443e400e00d00c0729400503050320002c6c0c10883c0001c0403a0f040504095802c2012103042140c01004d010400c592500c0618600507400743c0025401d03181050300c0d90744c882c00003040f100c0c20102e042d42e03603c1d100d040450b40075281078420700380302510b0a00ca00d500d048891260902a940503400707811040051000c10a00d50806020485512000c0d9022401a503003001200036840f0001107a913151032000c10094181d4000503c00ea029905040d544959180340d801101d42000080391296180d0a00d280610810301910600820941c080400480c1c1400c0010303500c41211030403070840305029100c510071020764100f65582d039007551049040c029803010301e041c52603100300c04c0c110fa10718482d0b6030703252041500c4040e030120700810000001e00c00c040d40e022a09040e010300594160500000c1c00c1041c13561900030b551031800b00b02000c00c0c1c05100520600b4036030001c14002084070039a5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 36583296 1250 36582046 36582053
    0x30612010f06050111070506041427040b06030f06010303030e0f010504060906050108030a050313020d0f06050403030c090303091502031b010209040f0603080a030905240f0a090c090c0c0c03 83
    0xb48034900501c0d0220798140303044041407070002422401c0d20005000181014070707100d002141c452452284580c4503814100034000b0362018401c2c0141142000200e61041c00d050030b09241c101000382aa81c042c1d01700d0003881c0c82d100f60024100c0e04403645450005100e045a6502c941003051840d41210035508003c140700511a098028400040c020301041080340da07a8020550b507885051031100c0403403002e00002c0c0068402c2c9241c50b030340600280c502015848180c0e500d80c003803c00203404480c1c05940e1070900090603071611464070072401a0500190050654401900a0a0500c14150044e5491200040c2c4900c02d00c295072046c46101c000d110100c1e40b444000d4040d407c414507660140c0e10b400d40c0041c00000074040d82088a4211030749500d4090111001c8007e004444015241c034801c4d801b41c0c000000c2c181501134142c0851510b0980070b41401d0300d2807010414041c28087e6a2070526041102140c00074014034100d840300c2c0d2000601c5403066506862003500e01402070444a2140800000e0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 36584546 1250 36583296 36583301
    0x1060f0503010507210b03010b04060909140303070c080c0a02030f060702010c030b0105040303120603140a020a0504020c0607080907030b011d100f0b09041b03060510050901020a0305030612010f 85
    0x80d03820441c02402142e0b40c02608850001e001400490400c00e1402c541090b07500075440071502620103000801c5410000010806440b19644103020341a40c1d0403101081c00705590b502e10003900c212001e10701d103040403900100070341b140306400340000740002000e50108004100500c0121b6014090719203486070040802e48401c01190200d01550030090400d070014441d110381c194510058441500b008c2c1161822600c1101b0860302180c2c6d6990342c00040040f075081d00103c100840084028900f41c45184140900c4c449180e1040e40035074018403c596200f080811003960081740e07803801d140c443d980c0701a010301c0c00d6030542c00039111101038030020070389041d001904840590488421030290315018032040301448140314850400b0580130080c007040d0842401429001c40041002c80d0454400c1515a44a00c00110113004207540314000c0100e42032080050019140904001e8203141c80e00c0b001135206c0c2c12003600102080b00000004010ba514510320400400c0b85900810141c107221080100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 36585796 1250 36584546 36584549
    0x909030e030d0c02010807080711010e03090a06090b030a0903091206090204050106230901020a020a0f05090f040b04030e010c060f1d2404020103020705030304030801140607050319090801060f 84
    0x1d0150b0144400d000c1d0003000940920b40d4180e548010315a1341030f0089801c240094101e5040181d515980150321a00740901d503100c6400740c000e035546503c40010008170b200c665001c10f080c840498410011003c128042e2580500800c0307000c6000c1d045850200c1d6441000d0b00804922000c00f42e0240522103260b0041414034801e039410465662104000c0d205201c01c1c41d203054006651591701c0100d0460100a040e641d0010300442da0000203650009017240c545401c0031200c2548550100003a1070400082500250429802e40c1603082c51f8494540010300200098180455030020043d00c1e44101e211501c0d03690060710030890803002110308000b0340040710f0000d9203103007209003d0300764880104031042c0c03185100703a292224408035040b1302a04400180149c0c14580d090040300c011402c00d0000f0f51003103100e81da90103c0c56047c101da209005203d41c0207035008007800d129880000b00c00104a13074030354040c44c00320100030b0500c000440f00807582d41c2140206500304540040d40e14059082e010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 36587046 1250 36585796 36585799
    0x1908060312070210180f060302130504090302070e10090e15010e06030a0b1b03010803040609080a02010e01050d0603020a0612050f070c080703091a03090d030c020607030b06040909030e 81
    0x1109041e0451a5440c07a0051907400303540720002044042e82c0f00e0140c2c00307103449003002d80f01d000a55540c03190000141202c0b0b40c0000e010a400094480c07942c081464000081c2c4003c4901300100d0155860081d9a4452030140c4980300c0100b2010035215660844910010800d0500921509601183d0540c940c03080740300c14901491100b00101d40c2084400e6014441c00c00580180504455502d0b449900540a08061160700462071050240203400f0000c60180404078020755403585000001482c010781035000300d0994004525000050780e100c1d0b01540041001d1904540340c85541c0c03040301c000c100617800254850109140080d54036080034481b0801034851000300300740d0303a411030300c20041d0008654840000311880070580000d1540400780030424013a1400102d80c503281c512032024071030210101494084040200203105404000404100c00d4525050120010302c0c0c0e0080e6407040041d0041041c142c8600c1d20b00725030f032034000c01e86005100014043c4900c005500340a01003800d1a031015 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 36588296 1250 36587046 36587053
    0xa030903030c0903020609130e01110c071a0d0203072006010519050f010f1106090601030b0a0e070e060121050709050315010b07020f03010c09080d030b1302070819080603 75
    0x10200b42d0082e00c0740801c49401801451400c884030040000c1c1200002003051119030781e00c640410080c0910520000e001c010b02c00c5950752465000c3c80e854a02c2c10352048002070000c5000b100c22583c0301040c1d0b92100c04000016849496026055030140c82002009c42c1c40761001c0080c0200f51000103d144c103d0308141c1d00700d27180300c0100441c070008004501900381c00c00c280a8003007050303500c40c404001e0000300c2d0386080072807442d00c6000c103820403d05403080070f403c0d841400148284003c4500c1c41e9000100c1d028100107190041d56001e407100c0c101d01c102146d400701c1c0000a2481e0f40100629015014110b118038600310302e10317500000030203054904600040026902241c24103000880c542006240c2d44c0c0300f083c5a01e4481c510206500800d003c0760041d1070050300c4002c07501d00b4011840480007036220f200d80c960800711014a00b0000ba42c03075804050601811125036240c2081c60b00c504018600d002d40d403207680341446802441844445003d00040640481d0080c4d800314140d80100c8044095 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 36589546 1250 36588296 36588311
    0xf0813151e0216020613050a1805060d0f030e031c051801020a050a0b070306050616020405060105040f0302060d060e010806090706020a0812060a080106090c08100303081308040b0a03090303 83
    0x510483c06454501d021000e03011115001510740300010789410a00d080c2d0400c20140c8440c0811408034040c0c4c0011110f8140c040c600c2c880c415140105640000c041d150b500040300d00d1340300c0c420940f6900801070107102e800d011100301600d05125800b071954005440c0368402c0d007000d00c010002d40c400c502c190121440005200d03107075840407484408480d0484003e10780c2001941754001070400250000042c1555010001104c0e21650003400c840b00000702c2c1e44000020a0060106441c401030400b410400c0821090101e8131071004020103a0381c0540d0210340b5200200c0a900007045260002880036003c440005408500000c0c00ca2003940e07180d0075106055954841030b40c1d20440241c00034105101440b028214140b01410981c3c07020008020380071007603503610f03d9421103120350004071070141c03038020800c4503580040c56540c004800d4007503810788074a1501c0081581c10007500111121206004000610038400103035800340444240896444000a00140003400c030a10100c0100c3d080154 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 36590796 1250 36589546 36589601
    0x2150f09042003010303080709051003050a050a0b0303030a09060209030601030c05030706020a05070e070203130b22030b01060c1401060e070909020a0c06020c010609020f18060a0f081315 82
    0x1500c5103010b00450b182c00c590841e90196003000b00140b1840c10400340c0310780014039598200b240e5604d051103440000d018144408400c054a40003805240c3d81d5040182d00103007504c001040766884442c5800001d242074803454800007900c10722741c105625118034800402801220842035044400c100d0864030b1607507031010280d07260000c0c02c0000e410b40d00840b02c2040410398103c00654003040314410381e0710b891200c041402c1a900c07942c126059881c00440c880394006031003003d442260045142200e185441c5039101040048140100b00411117138042e440d040100340d5544807a44410040213104085c0c6642d000c90301e22034101c1d401ca0000f000c0200c00601082c5038404c5440303810203035071101ca001c1d0703050b101d100c00795128851102481d90399403400203450380c5038405090498180c0d134030165281c000303458080d0081d06005030309102d84030401010710016009168000c41c0c00890400c0010780d59000160200840001d4005d03000c0d035801d5443c005c42011540c044034400724a8802a03201d111104e4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 36592046 1250 36590796 36590831
    0x1205040506151804230a060501230609041107050a0b0f0a0e1b03120c0102030a0e06010f0311030309100f0314011503090c080a03020a03090803120105040902150f0904 73
    0x1103d0007122200f0f0086400300d09a0501d5500507031556039036a0300c0c18a01d00c505890840309150540f078965540c00148403c210b600300c1800d00d807001098040c4030140f41400a540d503c605400c0600c12a40c481700c0000c0d140c0c010050b6089141c0040a070382100b1610b00f4600003144080310301c00004001600002ca04d241144a05000092554000e000c0941c90510300804558000c0703201e40c0c18882c12104504518144008040d01ca0300000050380b01e0400810040c20340d2440d40e0500e240b42c1041c001444403a0340380c02d091040725045450034510030350003030101e41140700340c00c0600e42011051000d801d419030081c0c40340c038441038941d0b0704000d64807054201400d20701d001c0c09440c1128200b00070380303030500c1d00c25000900b00034040e019501502d81e440614520b0200d007110114096001384a684c024982c104002d54002e02d10a4003851528504052030845180c05005031885107036a04030141c1503413908501d510f6400d004c01002ca03511801103400d0440c1f500f109841920550504020f18088082070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 36593296 1250 36592046 36592069
    0x403120302120a0207051005070201061d04050303071803060204060309030e18060f0103060905090a02090a11070213090c170c1e01030e0a050604030512070e0f0f01120504050615 78
    0x24410b04a44402c850140a5417010b202940c0503c140d03000f040895000348503036402810150000502c0b20f01d019041c0d6041007407000303442d01020250b401c00c008584080102c3e98800e0b85840d005000710108001041801c40d160000b5000782d202050100d20b058255112012241c02a00c40c2d400c411075a070704021000450f1600c01c00480e04039008a0b2a60500c1e0750a41140d140504010071080c2c1c8600e00002110002c9455101942c00211442d06500703224030b89a0304403986010601aa504400195899200b1044028094580c41c600301560703402030760002074955030025131034000f140d80c0c0703066002001161141a010b4041c1c0c07c0c81c81814a4401003030a100700c14450b2000850003203000650050142e404400c103580184011000050000d102040c0312390310135201d060b01d410404d40700c894401001000301d07003400714003914480c0b0380e50f8074104812101401c540307400d110700c02e10b0012500e40c0a0908000f403018106024402007020101c0c14038482c55540d0760f1710908100d118200319211000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 36594546 1250 36593296 36593317
    0x1a07020d030e0109031e060b0102070608010b073003060b09090f1315051609061b0c080109050109020f0a0e041205070f030c0201030501050303210a060503120403120302 74
    0x20284040024002d8000003010302050400d44250b5030b9076218074076140180480d15603218809510402004881c1c8640300c01440d080c4000c2041c241060b2000c2c00d8800103020304042d628021440a0030404441807040f06420182149000007404070500d000500c0c0f560403c1c4046410210003103411004801503e59058004000c0304040d12100712403e134031003002d040d11603040050300076500800c2ca1001c03413035040301140000080a15200c0058900710b02c0c0c450358041000901c803410068290302c1710b140c821141d80d5000f500c9061100746850a841c1d00e0b1540002029420442c140042c402c0640c4001d140070b0081d01c0700c040308101d0004105010540b4090300302d50491010200e170124248008205030050382d41401d41c0f41001c0c54440c6003200030020412400038014003204011968903000d0140100360903402107003000e00c9480a5800c900065035103424079480340700080d03080c41654002000521000e0181c032400b0354030b052803058951050200360340e68101000014699840780c400c840c0100003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 36595796 1250 36594546 36594559
    0x1902120309070b0304020d0b0c070309050405070c060f06090e0f0715020706050703090f0f03060b01170a021809010306060303090e070c060e1005010801051503011803031503080703020303011a0702 86
    0x100b261411444e080a07005036007254204540c0740002c1d6a0002413402441c00c419440e03260039052500608281c02900454020760500c03051207240c1d50406e07804c2d501c16501c0b54021600140d00c0c24280c004000a921544074903040c0075107030414902c040340c0110080e074800241e41035240c46080684642d00c048403c84016400340004220141c415005803030301c24440d02c2c1c2100156581c0c041d11102e10301940100c04031082101003007080140f0ba1291070a485401c0c2020140c0c403044119220180c072000f8111100720f40c000030b0250b043c05003559204404200200510980e50716420048002c0c945400200c0c049903290b440403820034192780320140705008683d03030007080d500075988003009005d0394451000103201d550180c0b69007080da070080c079004e029010000104c0385815204503500c600c0000c0698041d901d0921000401e1340c0c0c00c040e28240e5501801d000c00e0411021807610104011640302400b5254040344a40c100341e8040009c5040350402c40b00d0120810340c0983c5480d0321702c07403040020352260 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 36597046 1250 36595796 36595799
    0x30109150509040b090307150b040c030c02060403080603070302030601081c02071202060f0d05070e040b0a050f040b010203041a0406170106020d0305060406080a0311070b0f040e06030a08190212030907 88
    0xc0c8041100c0d54001c265105603402c003003607550343c0840d99072031400301008c1e65183c00c070a0000341814803480840b40e00b245800d102c1005841c8001c1c2d1583c0b000f0b8009010400000002042d0341c43c00c01c0610011980541110038940e511000c0a40b56146404c042850361b4610440c4406c040c030020b0485d0582da0514004c0b58818603a0f0308102c1244e004100c900001078091046802140705031207078900ca5909034840c00b15200015041104948400e01e01e00d01c1040d02060600850702c50f080d4180000109a0300020000301ca03d00607031a40c065a40100350307030a00509001840c821a01c080e1080310a140c039021808070310b42d440302c8051031007409200010f921119055410a00c01e030009500004003406c0090320f940c99580b051f06103200180c0941c0404c0c100350707040c1c0c04010100803680080243d00c0006041410a010030707101032185100b540c00102d80e031008119240d809011001002c1d52081e021543c030a6242840d11814684807201070140c014403558010191005080b24828001d10000c0c041c0b1030f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 36598296 1250 36597046 36597053
    0xc050409120f020109060e060405060f011401120e160312030b0127030203030c010c09080a02030a1425150311090114040506070602040e09070509010b07020d0c0b03010915050904 78
    0x1c001d000b2500f191740b00c0200f02d003c10046e00c601440e003104007000c6c4c6924540750814a19190010744110403924003800100000501003001940303001003440c6c60f810114103003103c02c02509600540d42400e00903081d11461a10386900c885084a00c142e0045c0b900078400070080d403c40d40014a2280415400c00b80010b03d500010a840b20414035080c000301c045441380c0119165401c5111850440ea6507240224041e0f038002c0e13200c8000300b481800404e45001a03501182c2c4941c2c000318003e000036000d41003600d14490500c10080030a8880b0a014101c8070301c0307050010035014900c20200c4c0300d032001c80e201c881c0d544603000f880c8201c007061f03000302d1070a98142e00450b51820707000c0e11202c1124044c00085490340d900c10043c0380b0749000d00070240e122030070800e58030002080544036010381e51003044200f1a83d143d05102d2411500710505003910742005002064280b07950380401030000e600744101195080c0248060344c1a9001e0f0740b420000a9555008403d080603079003d0b00d9481080d100009000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 36599546 1250 36598296 36598307
    0x60c040519030b060d02031606020c030115051819020a030c080604140103080f090301050901020a02010b0306010f090c030204090e07030501180503090609012d2d0e01031e05040c05040912 82
    0x2002e01c041c7c100d641030070726802084840056508136000603002940301580e18035007401000074001c9101c40034919149440001941100329800340a80e030b4002c00000340c000c286020741229003403056081036603528907041005005160070303007200b40491801c40109031503041500c20340d111040e84201254031a401d44d1544d9009402c8182300c2d05200c002000842a1a01c00b800f90703502480c02c40f40050303216001041e001c0e00752850504c950b8001d030b00071001005451403442c0d20700219a40c8550010341d00f51461000c80203840340350480440c8a0404510803542e5800103004c004490051008028004211241d800c1078502c400021385a548284190407003450320800500610005042c5007090340000f92804039510402e11032840d411740e108100d030b10b034070350000364050011540d030301d10032000607040741540f0316a540c2d01081d1017080414640da07605c2340d010b54480340300c003190812106c0841c1110003200c0007414044808450f445145500003c65040034010203856660001c048902503900c0c0404942 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 36600796 1250 36599546 36599569
    0x1080c16020d080d060303030f05010509040305070308061507140c01051c020c0709090803090c06030709170709020309010b040b040b010203040b0a1e0f081006021207060905060c040519030b06 84
    0xc0114080000c3c130310029052050100a40c460b840204016000800d108210b07001613002e00e001e022004104000a54041d04643d441f541c1410300e09400e490781c2d408071303843d540001c007103081c031a40004411080c820a0a800860410304200302c540d02018080115042e0007242040c4824442402020320315002d29006171000480e001d0031119503aa5560109081e10002e0303405071840c007000410b12010507414000c00500d1403003034981c00d00d1400c1416000302020450f1056024a10810710864208001841210010000e02c1000e5440e414101080e60003840c07074100c40c6108515064100b9030f00c1c2014094030a0211050300510b091a2601e4100300c0c465000d0b0790003030300300250203c004600000d22100c40040440075628141d01c000406005480340a0140c03889441d00050402002120390011310800c801c0d02d2145000d4841d8050302d0005c016220b8071070b00405074003400d41040550010f00d005007003261002c940b00c42c20001c80280c1d04140119030b00001d008010403000140342d07420706000805 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 36602046 1250 36600796 36600803
    0x1c08030a1109040c0f020607050405220219050c01150302060406080702030c01090606050a0b16030f140301090c0e0d0b0105060310050306070e0415061205091e0c01080c16020d 77
    0x14640031181d800181104c11070819080401c40c00e42c940709007103a04104d22948080d40c0c0c10720794600f0f81424001685100c0c40d10140124500174809044102d4040c0c055615074503c804c0c00880c00d411840c8098040d03005066608990344c40d04144264084000c1881400c071b03070300980403a2901e400e100d42140c081ca001404481503100c00c0080301e084840900c50701440350701032000091920300300400c02c0682c82d200da015800d6540244402c41c0702c4041040354980003a40750922594105c401d0100b590400031200b540783c100300010000140310300b85070b00f00c00080159a42c851a400003030b80100541c81c40180d03c080d0842640c6070041c481d0342410303c000e582216141da1402000d542d10030000317140c040704555000005d0401c0c2a0400036092a004000c0b12604035500d80c1109c0e4204440141801c2001041d01202c544800102e000040d00b800780350420080054180418194402d40941d030764240b40d4017600088009002501d1191117805413014201c0411a03800f00f820705400300440c03a44101c4099 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 36603296 1250 36602046 36602081
    0xb060409020d06020c0601050a231302040801140901020a051602012102091002030a051c020708070807120504050913030207080105011203090803040302180a0e0105010e061c08030a 79
    0xc40541d6486a081c1000303845940b0140c1d8400e0315080b000c0c01c011041e0b0040d07020741407486007031003020782d43c107240150b0200150620300c01005801c0040c0b0020344c1c0080d89901d140c03000401280821042d0428140404610038a6646032031701c03175881d0300b03d104800b034002c0000d8007400440300740100307111070381c56083c0149080300d10b000c083c48900c00000d14001a2080c1340e41c0c0010710b54000c1c00c1c68245140c0da020079001071800e00c0c1c01268003400320f2045204100300c3c1c03003c1e030207048000c1c92503038181c0e1841900101e07900e854150b249021601940641e0098490340b040c0890481d0a0307101d0f0701103409944002e04141410b807291940c914091b60b2030b000c00c41c2580580036020030803c500b48111402416980000c4003000501d00b0090445000c58200c440107410400c81400540c56036a204a030450034013065a006a40d5032a403240103281d10b080401c02c40d420000009401860325503124021002140e003451942000300d00195040040480105010014000110700030f040da404020700784a080e07900d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 36604546 1250 36603296 36603311
    0x1221051017070605072006120115080106140f0c03070f1a06060702040905030702030f0115080312130f06182a03080d02040e0c0318030c0307080a120207060e0f0106030209040b0604 79
    0x107807e81c0c00c500c080304041550714004022000100500c3c1c3c4241a56040610b10742d4100100103100b4030340d401d01c582010200003464401c0031a2a011501402032001c2030765240c0c401440d04500c008140707241511020244a81001d4121a688005003e0301c0000c00702d0b45024841ea0900c0081e180c404810744e41408103214030800350b02d0071700006032140c8846000050086083d09410039107201ca0700504a03580c41804402207014140d1300d003c0d0040c01e010b5600b0b000c0c00b524078012030100702000c0010085070505000b5030440050100e9807000d50b100b02c07100c43c030342000912000c1c03250b01c203840c000b10000d4010780100040345400004260341440408003515050b02c607130223100c1901042c5c90b010f07540c100020811404542d4400c1a86811507080302452605500c00c0c0010355078020041d01030800000024004000350190b601d50700038000000d4259221a400c0c02e007500203100c0d140c1c00114500501e0442111807006100d440292030703009048000688958859800d0410000e28242d04190b40d480c0c1c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 36605796 1250 36604546 36604549
    0x5150d0906060e090c040c0201020a081524040e1b0a0f200f0c041b0e060d06060c0302010b040b031905010b0a080607020c040912210510170706050720 66
    0x74290310900013100108024a040c07403c0c1700c12502110300c0d4204592040c050000c50070382c400b00c12900192401c0704181407403070000024003004004003013104071050400e00408911803003070103041103a44c043d0b0f07a40c2050350b921440ba0300d01d5482c5c141c001c5007007004004000849005130701440c000101454403a4b910341d440c00300310301040b0190007141c00316484801c084000410400082002b0b80054900f44030750212a0b04010510303000c0448201031207800800c0c4822a150041903882d0000c00c00000d0245580e2000c014140501d1080d00750015420300d50700c121681850b000d180c04c419070140081c1400d419842c3c5000301c1c8001a03e00b210790303540b41c440ea404036030f8901a109002d010780c040506840e05141001a1502241e20010b6000d1383c1044103140c00b00e0000503a0f0f20000510342811220344500c0c2712403410070801280b80345249403800782881a41156107035601d05032070310102c1c00c0d9030070b5003502d0440e0ba1394451071007080009a02000b0070400110300d40440c2d100150a40c001c2a85443c0e02030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 36607046 1250 36605796 36605819
    0xa08040605070507050415030201050c0c0303040303030e0c1905060708040803190809010b030627151611030301270507210207120f020a050303010b0309060105150d090606 75
    0x40c0540002036011890a0a02100b4000f140c01040110b50821a041c00551200700700d804500c4080d05200e00428004950321003800000d08010008058950340c3d9200e180c050000c0c0032003a01a1018031034644281954200f41c0c4a500c103220380b02500f001802c0ca030504021059000b00300c02c40d140039040c000003400c02006c20150509080d14204000d00340e0160a00500c50200100480c0042c0e040003e031000b25100424120380206100c03006000ca0320074000b05501d000d0401030040728500c40c141303e401e00ca4803c070003014051003094130100100c41030b6606c22249101c504104011540003000108408900d0001c245208010b550645100030390310f0701c414044510850b81e803008502c2d8580312030080501c100d603854512042900c01c504064954070b9107000008001c10450a20090381c259a403224000c02c048400e46510800710b80c1d680da10349511481540043d28218118414180041003601c0c000d0713002402d0b1200040700c80d04040d008805600070b002041c0017514441c1c0c1d29000810780b035a010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 36608296 1250 36607046 36607049
    0xc020910050405010b1209031303060b0109170706030b01020c010801050f01020a0b09010501030c0e01060f0c0606080703030c02040e060f0c031909050102090306071b06020f0d0203070c0303052a0c0a0804 89
    0x16091030b40b01c600c40f40b00c18081b654010103104440c0c004000a0311020701904082d01500e411641c0091480c41d114016111032003182c20803910b5500410540000d4140010140f00b505c0d1541c0e802e0003020040001139a0701d905198106001c1000706006110501f031203c00302000c01740510440312400c4181c1c4424010003025110030364981d45560052041c0b0641c0b000800c000c010340d9046815540c50000c0080003040b9a4481d00d00b080034009000c014003405401c0b820107030144038150382c01e0f01e4ac0d900c3c002e800320301d02e0942240180c1c10008c4680d90f02c1800310381144580300c807035607004890b07464440f80c500982c4014918400ac10b0036111011805a45201e03e0614034030034000181c0d41c3c11500109441c3c040c00402110400c0b2062003442c003d070180307420b41040d00717511580141c1c40304103907503804a050184983c009119403020080214450380700d007411030424002d460030005038030b034998505502e401440510040c03d54a084a002000e203120043c18100611416145804810380d40c051069000c3d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 36609546 1250 36608296 36608309
    0x6020904090f11030304060f03050403110303010906050a05030604050c0105070f0c060804230c041107060f02040e09030c030304080705010902090709080106080613121803060504030f020a030c02091005040501 91
    0x642c80c0400402400b451058a003200c100e00a40c00c181c074040c0c0c010720700304080d039490003095203c0c000300e010140503400b4060405400c1e13054948960712800d0317070f000600c00c40c4034083c0f180c881034030000b40d03a00340811018092038000025280c690380503001920303542e010080445590429108103008a80076440c00e0b80a0800d950b581c0039541401d041c0902800d00d06200101c844040d0386400103040b20004490282d0a01510085101d20b110046c1042a0040b00000b414003030901007000c1d0050141c0d4018010750703030790705c16a0300e075900c5c0c800043d030383c1c1e0003541c9074421554400c001150104501d8030152440038401c034004282814030768080fa4100c5c030300380d9100d0007040c0b4a45043c0300b8402c0c01c0c0100300140c500b01004007614a840f0000410101e080840a005403114181442e00184101025204000c13041c0e841c000310759481c40c0c200e00030003040780c058000a1502902c0580b85d072003c0703044050250150f0b50040300c00d44940800c00711702005002c91a851035003000c001031279140c5000b440c1c0200788 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 36610796 1250 36609546 36609563
    0x209060d0501030b0f09010b090412031e06060207080d0c02010302030a0b1206160311030a1a030a1103060106090e0f090c120102030402090106080403140f040b0c0d0e1e09040602090409 81
    0x6011111045000c00030304000d072980d0501d9a2408d858071065802030b032080c0c0000740600c0340c0360168020750003081c500c8010800030580d60f100c0d403200650781e00910300320361750f5500f1180c0e102e90310307404103444d5000c405040d030000d10340740009409588282c02450b017000c1001e800240310501c100c0002c40200c034108695519400050811130800b0fa84078443d41400344034102400039a900640346145403100406500c1032565841c14018001600140030301881070207003c5820727051250070015980100560000d100b441003a00101e0301038407e60822080301c0c406c44810400780c9582103e01040345c8020505a45440742450f403001c5599041c1ca840f20020000000594908103401400035841e4160001000c2c40210b03c03c1c0300029501160720103200301d8280b6100d4441c80d0b0001000701038072442d0f20076451441e011520460304900424070b817041c0195510340080f1090002e050000f145d03030307a00802c1c030042d2403451581028103240d508a503105101c2e0710014501180d4900003421140c20301c209588114 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 36612046 1250 36610796 36610801
    0x3160503090901060c21090605070f1703010f0614070303091a011404060e04030206160201200301091407090b07050109020a0f0312020604051b01020307020a06020c01140c0307060209060d0501030b 86
    0x3003d8140382e81b403461003903440a4403c15002d0090f145003503902ca25810171100044070030078040c110035030f10782e59640000307070040d41c610041d81c074441a0000c0c01081c9941c6c2d000f003400283d0394001d440840a603001c0c61079090030030026440940041c40c003188140c2e902150081001d6034510100311060107841ca034091407030303035400500a00c411189150000c946a0002c1e60034000400e400280059103d907008103201c445000c020812070151150209454601080c1104152031464080245043c1c0d102454200800560200340ba8a0950291040310208100740c4007400200d45c52402440440d008000200d41503c40d54041400c00103168401c030301c40508140244200200c81d01d40d0301c045040e0348000c121505254440035142c00e94555207a0a04a003d070400140d64024000da0345416001001d8612031a540c2c20040d440b0b03400d00d1212030000b89401a00c0481401c0b480548280409010055081c02650b030703500c000030361209617800d40c000d500380205150030489001e40d0b406184900044480c1c1d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 36613296 1250 36612046 36612053
    0x6030a090c0603020c0d0207051c08071703190c0e010f0203090604030606030204140705090f0d050d0309050712050307150207051902030c010503160c021306080703110102060903160503090901060c 86
    0x246c03540a03d81e046412401d01044aa542c0c0d0154000210f01c0b88244082c082240c0f80c42c82c411f02c00d1410081c094620340440040058050015500c910741c0d082c402c442480300038008801701c86440e051040451220710130321710194800c014003000300419004a919101a0600240041d0406d5000302e40d0070b91689024000c40c2024016541d11260701d0800071414189080003800c036000b44181603006255000c03070310080e5034440107010640ea40010030b95601c000c030804020050072081006550b60304ca03600300082c0b41c240c05031617600c0e0550010055030401116980d0071100e02d42182e205280c4640920a031000300324144900c0002c2103510707001c411301840303a20500d03040008200040707051000a00410023401000301c101c1c0003541152030303da80409158030010343e0a81c0c1d60301c50003980e00e24203000802c5c1140c00259200969010749105125410041b00481c0d82e52821117501500c0d402c24000da019002d80b081f190989944180c06881c02c01000c0300100707481c070200340e12500001c1c00358841041030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 36614546 1250 36613296 36613303
    0x90c1b02061e0c15010e1f090f0b21030a032a02031c05070e0108040203010f050a0218090c091c0203010906060509090a050712031403010305030306090906060a030206030a090c0603020c 81
    0x3103440501301010355031402946000400e03008025070018001a8440500b4800031550400602000362081026030044902c16006100042c0220300850b03003200e250300b15040111142411007949001580750440440d412070181c2800603940740c040003185088260500300301005811902030740c5c0190380302c00c0e44d1240c40788103003d0300180e6007815250605111745640d101f10101d40208013800c01d80010340300da03c00320303005000040f155a001032801060010318401d54004100750140101d441280e404200d0400640300700a44e1b03240d01d03005080007810400d0070000d40d50f904100c00c400401242c1071068000c01e0950711070f050100e90340ca69480381480f107880c201d0052600102602c008080c495402d540f550b0f640c0c4124084c2c480301040800101c0e08140c407c8680201003a21f540395580c403540e40c1e246caa50ba0342c1007500c02d14491501c242c000790140c5000900c0c10301c0390000801900440c1c1c07841d0203000d410780c00a4110a944d60301c03a4800c3c0042001e68240b00000c05890303174016600c01002034160704 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 36615796 1250 36614546 36614563
    0x70503010203160801090b100c1b0303020d030606080f06040506030709020a050a081501090311040b031005040204050601081003060207030e030d020615040614120102090a0602030403030801090c1b02061e0c 90
    0x45980c0343c90103280c488d40300d981e04a1980a901e040101640019003070000c002c00400005003d0300d40c4900f80481019408219548200b2040d2824443d03030351594400d44e50340c03904844019560000d400000c01500d03003a0003298105101078240c81525454098480c1640d0051040030702090000480500c40d540c88030805d540702281c5039040c25109002000204640001c0c40058020020012002640c3e6030300d5111101130030006041391039501ca04150716014100881d4103070320861806000078055401020100e2140c0d540c0301c65904030300e080d5542c0000039040418154100000e0021031041600c00f00001034010340d0540041c805d900c1c10707170024801e0011400c2010302585c1030071001c0005502e80700c12401c0304a4200c551810710b0030f61302d10103402401001c0e42160f100c00780b4000064425004401042039901980c0e0382c581321380e21000d00c1e07016242e0700b07042040011400410740c00036180110040d12160f00c014802850804070b1070048480300d0821903c049503c800080c0e02131401c000300103108 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 36617046 1250 36615796 36615809
    0x41205060112020f1003150f031104021914130308090306071b200406180506010203120109090204110a26060f0d0c0e1510020106050303041205070503010203160801 72
    0xa607020302d03070f8041001c6202c1196258010325180503100304180c0a6040a411001014202c1104590320002c00b50000c0052005555a0340c001c0403590460619008032280c0d40c4124a9804041807c0c04045425040c204114111404c0901c60000c81950003550b001c000d6005550982d01e81802c04109414110050302480030701130300d2040c02d42050b418036295501a50441541e4580c0030b2030240075201070028600c100d60003450300318045000401000026140318080a0401c466600c6400581c0d4a100d15044a8158a1008010001030425030820f4218a2001c2d00101d12803071442c610080b55042185a840460f5800115011a42c107020054182085030b010116444c100300d0702051001c80c4141c13040c2e0180002d1200c0c4018014480005801400d695091282614091190344105a44d02c0e414a2003004042c441000e805e105008000564000401941c038180c03501c0922440842801800c854034068000002070540d001e101851140c108440b00d10b01d00c1000740350080040c0c40581162 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 36618296 1250 36617046 36617069
    0x8070209160914010c05060705070506070e06030f0603010216030807141306030b030f100b0f0108040320010e070305060105041b0804060240090b0d1101030902060412050601 76
    0x90303000d61040341001202c50f4102c02d10024880440101c50f1407a80510140c010b100b003005014001d075200c0000c01c890350107101a207480d030700c03401c004a800000c034007540c1c0da0140b01440030032400000c1104403900140000d000500c1c0c182100070f40c3c8110400404150301040426040004417078006108088582d000c29070325280221f01c0c9060010f072001d50243e47d04040d59140d855000752810055070414441500c00c4400f1051568400d5018220b040c03083ca0240400c190111960b50243c40c42e607000d540d043d26048002050010f904401104c2c040c5406410740d00e44000034044101841224050743c0540c2c0070f880e480d810706092105031540c61070f8000200b86d40036881e010580c1e000f001907400c10384c0300d480903a5500150758003050000480d811117030929007640c0700800c2000400c05c0011100100054000076681c0d482d402411940c2078898940c001d4414400785000a155445062403940141000074a03200941c01003a816002900198252070040c0306040500004000c0c10b0300410500415 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 36619546 1250 36618296 36618331
    0x6040b0601091a0c01020f180a050111060a05060f10030b030105010b09010c03080402010507021c050f011538130e040c051c1401240b07030c050f030708070209 70
    0x503c450b8420180502c0c110410116204466882c2034045a9001c81102c40c0180c40e0100b541000c043d108400d552148201143c1100241a50113040481c8102a503200548483c1e83c0c3c8561110190100516260340481040c2c9081c042e692008030350000000301e941c00055418034801414212441170704011000d00c0b00b4001099a1707a44580e0510f442e0394580b40504041c0c58600c0142d03068007079070500030352003a0b06010070311044008801d1a0304203801841180c1c00507500000d11800c0302c8100780c0382c000820b40301c18144070403030880b01320b1329955030140320b00c0b5a2549050302c50712400070b442600c0d00b40c03000c00294960726006032400c6079000e0480a001101c0500f040e5a0b984800e58181c410280100625500c50805150354010710300d40d1900f2814461502c402c100b4428002e041d056001050050070b01c54a8450481001d803040903a0340044000303103060200c0d1002d440c01b50b5a000101c41d44c0c0f040d0700b840c1e40d004070188042c2c8460b600c584039030342d00e038201441008442140184881022000d1885 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 36620796 1250 36619546 36619559
    0x1020610080a1407050a030807050c010801030206180114040e040201020f1f050403050c0601032303041404050c0417060106140306130e01060e10030506010e0103030203090126040506040b060109 85
    0x2c6039600741d0703440792000d400034800701019403c0002c164055030b44440051000401d00182070007d1204e6440760095070721007518140113441c4084d00f804040d4011006000b1340164404a803000380810300141444c41c1c035104455404081603000341c0001041d450b400c41408110750301000000c50a020b220060049550403130748201826200000851a00c1e485001040c24140150221004e100355181a14082c0da10790a0840104c5150300d0042034040c0460500000894080190b5080e500d8607418428440805403c00018103c0981030803c03c42c010040040c8030082040c50422015041d005041e040d89085005040081c001081d0b25003c0320800410000c0e5a13282010140030800032000620b038148880c003503005201542280d140001c4240c03e100405080142050449114004651041e0317290700111001071400e10005001d0390081c0401c1900e0b6011301800400350a050b80f40c0140e5180b4003c00c8041d0002c1a80c064455070085410301c01408905205150301c41001c2c00c0c412501031500d01c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 36622046 1250 36620796 36620803
    0x90d15180b0601030b0604080a03030b010e0604030f0b0402120d0908010b0108010501020c1210111305010504050303040605210705030f01050a0b04060c0507050303042706060503060f28050102061008 87
    0x14085410144d40e480441700c00d64855050320094800281100c415010780e103405401000d10700d40e8540443c000c0e141910b4249400c0b011181540d9100c1c100f10903035034030340d568103254060143c01203a004629286180440100b044607203100c81d02d9a45046a040ca400021400c64840650190420030b000005001990700000c1c80340c040c0030240d48200c1c09050310000241440c0d594a42810810b080003034800d100354040010386010080039440080c1e1a0f51140195a0b81c4114807600350540c10520040040c54040d001500d654401e0540315441d00c0202ea03200340b607071041110902d01044011045c080c00120500109014100c01d44250044504100002106005900c90380d010010036050110411000b0310050000300b4018040b40d466680383d16440a0f48240152207400c2c40600512006405a1034042c0c40704807451a241c452a549440b0284011650311120b06504840031101421015112050416107059681d00081551381044002814a800500040c4000a10039010311030031b903020 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 36623296 1250 36622046 36622051
    0x40b0105090405010902040218091305070b070c030501020d020403030e09070518010905031506131404060b12070906050a060c080a0305040507080601030c0f1514090303090d15180b 79
    0x11104024540d4a500c3c00c04c2c00741c011071200a41181c00890340c40710007280c0072858803140504072000c040396581c40e0251202c3c40243d4034050000d51000320108465252400200b40d40b42c0141e00c0065004c0d00d80e00c503142a039100d13070b54842072640c6c00502041070541c804c10413030900c1001c64a0014900304030303100a01c98017400201144124034400c5040840e070098510071700810002d02034070747d40260098146a40c01d8211552409404142c080080c2e442c81403040c03001090620720200c00c50745035925000020004418490f40014000000302c00141d01003284070000e00e110500072645500300790034085c3c0087c20f540980309018a809002c400900329a00303035844507865103000110b50b80c940c10a07514002083c1d21038105401420001f20a001c81304008200360348184c00c3c12100e1360354038a2094000030180281400046500c90710090b6105040018000c0708001021a82001c08000003d030500c0310f001012561206080601c9018441500a10708001c6500008407004085a2a40b20340320000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 36624546 1250 36623296 36623299
    0x9090705091f05090301090c1707030c03150e06090105070201061401080c0f120a0906140708180c1504050901060e1507030201090b04050a03030b0303030c0f09040906020f0d0c0503040b0105 83
    0x10307400b150002d0301c680309607451000028020300c00c1e0001400d0100d480c3c40175014013081015600b5131009081e80000c0c1c44002c07603034041100000c192640d00c40004c13103a065000800d5054a40b04042c6401c00c04200a0380983c4030f030780c000160703400c224034080d007140c103260320622a5031046100003406a030032003840f0741d000c8000c60405940700b0044200400a21443c00d0b519540c403068030500004440b1a40302111040c4601c0041100c0c4d20011b9585540c0d2404955040003c0c1070000028075085009980300560941c0d14101c0d1241c03041c00d400030f01407104600b09481d5122011500b000030b17241280e01c03140100b03101d00301100248000c40c04184000c4503403150907001400013030a80c1c01c01d4800d52004038511340041b0200c0b001c3c1007600c1d0040d114503900300290002410f021400c40103142c007004481c01214a0712541c0c0c03626400d40340f00d000a405c6841d010364170603a1380f100351001c64800d0000704002890116819034501040d203a2504594000100070708001051040100107041903558070706680e070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 36625796 1250 36624546 36624589
    0x8010f06050c01090b01030c0609090b060301030f0f051212010f0e180c090112050d030b030c131506020f06090706020a0201050c1906020301052404030b0c0403060c050909070509 78
    0x4003102c9007400352070030690050074545400000403e001e002048101900c00e40c0d907a5240703da40e601d0344101035070410103a141c0d01100c104010070004038600300015025108000100b45185a038071180c0c03c004a0341652a42050300181603083d25a62070013480c0034050620f070035800b02e82020810b10450380000c045010001c8152810207510904101103820307000000c0c414001c5685910f05020129000c107411102031280141107079280380240548044080050002c1003400b00c4001013014140101a45d401d01e181c2c0c443d901100c0891203040c201c00b401240d0018116460140002e0b0302d003010092031041d5235003181c90144505a030114030140401d80900e0125112800300400301e0901005046603640d0340c0740381d0701000400c4040e401460481e44111007000b245240e1b1040880400c002e0351003078401c0e040800003840000d0101c95070a402c524541e01507424a0f441e03513038200480c1d00d04c107201c2c2d02240011030ba1510320f00c0e0852602d940190036140041c1818402008650041100300d644400d4030b4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 36627046 1250 36625796 36625807
    0x206040f0809010210060f180e06041106041703030601080105031902060d060504020c0d09090c05030103060504111e090114090711010e0d030b0415030c1406121e0708010f0605 77
    0x138401c114650541c86081030070080507a0b181414040c00807a4460080000d240034500c0ea0203502a10801000003000000b82c100c0c0d99540e621043d20703841c2242c610794008420710010590081c5070b881000c500040b840255501c0c1030190015211130300583c4110b20076440030b2a000b02c7d41d0f80321600c550415a05850883d00c4141e900d480d01d0151540b81c00c05900103102117080401d030303c40000c04003c90041034035035150b122703142c2c04024161401c00400c0c80105400b0001040044d005504c003036403003401544540d100032680d80025007880d0300200c1c1c1d680354074a003500000803480c014101074010402507007040b280190285c0400d491200080450040c013580d4078003840e00c0f513030070340051900254907020743d04026581031000e0014801004041c0c002e0307142c800700c841c8121104007a00b055a4100c1c030700030032161078904140d68414403081d0054210a042c000c1088655022500d18020ba9468444001e400b070144001e95591800400c40c404212507440104400284c0c4100e040c188c4100340f0300030380c1daa0b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 36628296 1250 36627046 36627049
    0x306020d06030f0b1b0307020d0509040f0203070503090106090b010804030509040605030d0c05060114012703060504080301050102010b0306040c051203040b040308300a090303090203060a0b010e010206040f0809 92
    0x8080c07550000e0540d5111024070003c02055281080c4220800440a9003524401400200c0740c001140c3e5100035a101c42404400341c1d0040001c0c18006200500105044282e0f06030501139800071340d50703140816004070500c19201028014040034042c0030208001aa0040000800301000a000036040c8200055603080ca9116604a00013404024040300c0b131107083c01500500c08004c0103002d803044d000e40d03000410b401d041055105506881655003803c0004c0028440350f81800d581c00d0480e044200e2000000050400d0117032910590180030b00a03140c1d03162100182c2542c1c030001005100b90800c0d810071001031541801c00c001e580080e070315070400e0007441e61154074501c9a03401c034000154020500008100c190001445134100356296010700c00038481c030303554000720b40c03012007440c440b4000f0000c1d0311025550311840005000346004100d00e0015008607007010406e03a0800c186649400e00000746581024142082f5a001e100402e2240b40030b49413003414090710307900189166400945410b0300e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 36629546 1250 36628296 36628301
    0x708030c1e010e01050f06101b060c200307030e060306090123040e0105070207080a0b0c03060f1207060305071d060c0102190306181a0108090106211a040c0306020d 72
    0x40d05143e8020440303800c04241c00604100300321000c03031080380b4580070380411314410711424941c0980c3ca40c1e1120103120320703980d043c0074003084069503003042803440c901c01503202c00b40000c001344c4904c40c001d0f582d00c1425060045c545a4017410050203a1010818003840e43c5850000d24119105800409011124a20303007104561510000c0c591050401c100c1c6004044194042805a0095000c8900495503044091744074010800080c00786000e034400690204415001503034440d40007000905040c1e480d00000b4802c1d4100d040c0042d81d64043d01007817000c0380d090300c130311a0403141e241003003550382261280b14540031000008140c003038403000c2103407805034a007501500d6054030036808000482451b003000034010002c5100783c50159071540949804c0d15854419a02c2120700d40900001602d059401500c892101800d03000c215035a0b81d100003000b00000f16909400d8141200a141d40c1c812810a000b82050720f5105149030400c010078400051500051801141d9200d80c01603255411034012400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 36630796 1250 36629546 36629561
    0xb090d051207060f05161d0114030a050a05070207080a0f02030a06290114030708070e12011e0c090e0c091801050102060901090203060705070f050706030605030708030c1e01 76
    0x50754004a294801c100c0d09030410503410042010800c1995644031729411030440c070082050228030400034854120401c8402c01d100030030181000d042495003440c0b07001066008440314502c41766288103104981e40e09008035908031102c5d20051861a041103074031b07a140d07580d5a03401019080144040800c64170103005480065030821403c203c0002450908503c40900003200720494008480b000f07403d6000c4c202482c41c02c28000d0006045540b440350549900300c1c0904143d05124108404580654030b840c3c00e40c03000108940041480d00300450448080320b203640212240300e05110b800900c891380320103100c00300c4003d08240f55264540d07610303603c0c0a1040302074140d00000310102104180b848114074a04aa10070790071607a15984500b841403ca546030000254143c0056011505251090300603094980c01046103140c903215a6860030301d880e010740d202901183d11900e0801152a040c0901c1000703101ea040554a030158405407152520740c180e56030840b90140a0075510100000d40c0041c8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 36632046 1250 36630796 36630823
    0x30a180905011518060e060901020a02090c0c210706020310080d02030a1b020d11010311070501050f070207060e0904030c02090712060803071a040302031e0a0201060f0b090d05 77
    0x210a50b1244071428074002c00f400d0500c040fa4240f541d1030784040358814020100ca03030b940d0b20f821a81642004001840d40304851660461023812a0540541d40306541d041c01742444064443d0394455100c01e190030818500d5680d00c41490120001320b03049042412186425440a401a940c0e03403021840d445550042c0c102000701c0c416030350288002c640000013451030380c085480d03001e100b9184403109091491b83c0030000790801e07511074201c0001001442c0003550540d05050104658070900c1522103240c100c0402034940b61344501c18490300123521140d958210325548041d090680c2480d4024204030746100c4800d0240741800700003014184030b0343d109072100750b00421480c440d003003880000307115044594000e0415458198000b44408000040302d00b00b5a01c03150b0380e81d040e03c480301500c82c0a50018026425400200824805859141644000f4000c0901e00036240c8089000003800c54210390490f00b5280b0b0300c908140004a1004140c2d255981c04882c0382d0441500c41c94103e081035028400c00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 36633296 1250 36632046 36632051
    0x20c060f09010908030f040501050a02030112061e11040e1305150712090503030901050105100f050f252d080c101b0e0306070f0c06090b04150b01090503030a1809 71
    0x20101b441842d41c0d80900d0080b0000d04c076030f07180c0f00000000c900c02807049840c21082c410141001034444c2d0032030070b0010310785100e1f190701c0114045200103440e42c90b404c000d4a01c1000400f8002421240b4039240c0091490011034544490750340c0b99981e0385a0340702c0c01e00d41814118005504607200d40310201d8140d0104206000312403591a1032581c9070025203441099501304000802c5a040055000d00510900e82d9484c075202510070041d0351310307400b03c1d11950140008001d071328581d8049030380300c2e8408182000740c0382468aa6040480e1012b80c941c150000919000c5008d40c003118a00712140c006513004024240d50782c0d1384400540ca0000c021500c2c885403370130001401c00280e011000818801c1075626500001c407000c10401d510747c081218408d0105044078260710445109a001e00343d403034400c801c00910401c5c5625000c41c250002c0750100e44080c0e02d00c034540746800403230007140c200040030b003008080759081074002600d80c000c00d94148208150021901c0c4042c4192407120024699071004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 36634546 1250 36633296 36633301
    0xa0603060219020f06040b0a1a0319170c070b09011e02010e070b040b16050f150117010e0a0308150406030f020301060b0406050706091a0a0501051201020c060f0901090803 75
    0x42c101c00e05407125204094000c058104801000204840744202d030b0115120000d55501c0124800900c8018203144420390105c00c0d12100d82c90400440581c0c240f00c0c01c0090b0410581d144c1520590b04514400805640500c230080315004c0001382d100c15203d03044841d42d111940000100d5034140c8038030070340001558089c000450b49806601a070840310004c415142a41d0f00c0300e29080613441030340b1600b84461810081d040089651a07100c50410b44a8003d60b065401d4041c02c2a240c1001d5a000218000c1d511004001d0080c000f041003038083c1d4420002d21080303200d1032000e5107070011b80402800b4010902c0001e0075901c114864015000d20042c420042035459081c004a5400300d02c400b02e002e50303c3d2030700c08101c0001c00c1064904403912a5100d0f03213080300960300c29015041141d03080f01c0072a40600f000404458011603035100b49581071000540358540030401000c8210700c048201d050340f0400c10181e01c1079003c00c00607403100058690b28802d441d040e040ca4010110007801a0845a001c0700307 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 36635796 1250 36634546 36634567
    0x24050103020d1415010e010309050c0411120403090501080a0c1e0908030a0e0907051201060e0102100c0f0f05090d110d0501020a080a0b1008160908010606030c02010f020708120a06030602 82
    0x350201c03492406e80ea401c0d403a0003d0801542100e00c2001d02170495404401e4101d15468990042a81c080300b0102c80c904055814030006040842035034110081036030300b04140444d50b071141c1c0e0190b1100507010140031813402c0c108042c0c801c0141c00700c00c1904840001814041d42d000d41c104000034202d1404480d540c5e02e5208c0000d1441e02c900d25a54071880c03807071000c159614803a10a90b804410000c1c0300c054564030300b240507500a0645102c05055000740005091601c807203108840900f03202e9150344282c40135100c2c0c0105080d0b041c1c0c1a880c140f00081c0514003032521074904000b00c044d4040940003a0041c6100040c01c8038022500c02800d940c00050030068140c0d02950f40c6001d401d80e04014044c843c1d0101c00c0240c031800302080200020850000039680101403d003c14080085060041c0c0094131882103c2c02e42e04503422900110351101c4801c0007840d424400c1c50b407028041c0c030085040400b25910b00c4d403140305001513009400060804100300444d50341c80030300115405802155101410380 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 36637046 1250 36635796 36635821
    0x30a021e010201060e0423010f020406091401090807060f020c0402040305070e0c0301060f0815041b110105060d08090622090b010804030c1b030f06090624050103020d14 74
    0x1100c241c0154203040f0001401c0d8880504203015562080d030605499280b02070784d141c501d520424000e05903480d0b405180004074903100410151840e030781d508203900e040c00c06804040901040780c0c1d042040c1d0000030800c11101107152001d540061138030503030100c4542412885d0688800740503900c50700c001000010082c0009007081111910f4080050903580e001204882d40024841e01020a50741c070055a031040c810507585901100c5004850403140034900450300b19442010714078502040003190401d003941180511f514205984006d2040f0305d44527000c10989080000c009100c41c00c0400e0817a800c0d56402e040d10000840c8075100d03101c1c10b448008280b10140c0b5071140d214028039001d0310052552140514910450300741d1111008c0a1056440a202c104601d0800161003405640880041c0d08000c210400030300404000c582e00000c3d081c0b10080f18224021b020300c0d40c00002249000020941000782140d4090a00607212148202e8040c0034054542003400144400010001d40745403c6 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 36638296 1250 36637046 36637099
    0x906120f0c120a0b07120f0903080703151a210a0501031505060306041704050406180b04050402030d030c0e09040510050106020c0a050405040602090607081803060c040b09030a02 78
    0x845040075070550382c00d0015240d2882010207031a1901d40800296401e000d0484004484014100040e0740001600c10388119072990b0000c90001e00002c0500c02120340c9030049400c1c9a072090340d8004100c2c60503010b040ea03500d03d809850308100c40070540309c9203014400504801d24810450441142c07030500240001040c09002c100c410300e860030174003c4400154421544590b40140003402562915103030031095040e90031000380320010400000c201e64440380220002000106d61098200c030200c007091040d183c1000032103000d80c7c980750810000d6640020a0078070032030981400a131700350705003c04940a0715050602038011481c0c400b0300c0204400000c0c41e240c2400c01c11400c02182e43c88820032a26940c0d181d006550201b030264040c001858030b0b42c025074202c0c2c802c00d0014504128140481c110740c000c40340944202c0c03004907041c01c092900300b600d41038030f40701140582040d28010147c800d05000d070313000b00307401c1da04042200901031b00d0400070040290f07002006c0c546800e0080c582100c010100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 36639546 1250 36638296 36638299
    0x405031201030b041421030411130f060b07020a060f050705120c06070207050102100b030708012d09050d05071a010b04081015030f030c06020c0102091f0206060906120f0c 75
    0x414105000c0740000c612101b40d030039882603240345803950110782d030f00c140c00c05841074840700d401c1d007512002641c40c0606580800c041400225001c1c2c0403040e480121010380d401100301400400800c80140d494110800503240c02d810100c0c0c802200b0b0104441e0b034020f07090000c1c05441a401d0003c3d10010180c0a80300341c210040489200e580c980030200e840300707024401c0070701607445070303581b0500d00c0c0180d00040940d0b440074040310791866030b0b140160300b03440c08116140004194489201402240840c0c1a050f03003c40e001d042c48070400b1070b690b099070742100f105200c0c10041c1c0403501b40c08228825a81c2d0414550312880d05603196100d80c4050000c4d4814498030005105003100d1041000b1540140c4540190035182e01c0304d200c0c5503498416590000c20704c214100159840b9460008040f440945500329030348000580748d8901c01c0078040481140b4203404446825a140b10042d1540007444942c0101e054828020356124a008101c0443e6100c4118040c1d00801e220f00040b43c20004e50458481d00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 36640796 1250 36639546 36639563
    0x1202030d05060418030e01030905060a0911060304080703051308010218030610060207030b040501060b0d0207060b010c02090a0c030b03010c0509030714090705090a050d06050a0501051e090405031201030b04 90
    0x2603a404100441d40140951010300c80c10f0340c04c407000300e0700030742019402072010304001c100b0703640c4c664a0608180044565005003a52002c041b018000c0050701c840807440f041e00c250740f445c149500d54140501907554000d040160004030484035105640d40345004194600007952110100e43c001e10040310782070b0b074140c0030340718642c001003001000e08240c00413205150060800581551607400c08200c00078800c2d1080c3d900c80d8800030304807181800510441c6019000181c170b8002a141034001c0e1006202c0480c1003000582d86200982e03140703081150043c01c111741c0090020220581640540340301103596a0551a0040007000103400c0300046c407941c401103050301d040a0310351002e10300240f07050b8141d907003250043c000190010f000d10003d1140700c00c0208000300055503400001c11050710901d003210350548850030b105040c0d507140034107400f4060442d141320655116400c1d444a10f00e89440452151120402217000c1c072200384221411450100e088240542e12410044040c9200307880c11a95060b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 36642046 1250 36640796 36640801
    0x907050304200609040b061e07030207080c060a030e0a08040605041d090c13140115030516050d0903030209090115020601090509070501030b0609040c030b03010f060b251202030d05 79
    0x100300b01c15500c81c165005180d141051441d0040c40010a869807405030040e03820044c0e8850780d02d181c03022502e46101d40300070303941e0380c030003850002c0c18164282d0101c49071764001ca0300c0d0501c5648002c1070782c211061500d40001c040d840384e445035151082c203038405401c181c0000340101341513510600034000c0d204280a00c0440280720342818400c4a000c48002e00c641c5c0001c90907013414941814024603480c08100702242004881186a00045d400e030b0060308464111130858040d0b0350540a1254084440c004100d074901c13079044058520320950f0210300300e8903a102c40b42ca00701030099060f078800c400e000e412015030350b03110010000c5a8150041d91030162003404000241074085001c0c45106600c0344018014036032030100150041d107281c6c011a82e0150051102ca90561035078840d00c0c41094103982c01284c41c44030034040c0360850b6102c54030300b540c1c98109001400b84054500807506080303070312101c4000c45c81450314500304132040140c0003031044650880400f01c03143d000025001c4501104030401c8140c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 36643296 1250 36642046 36642083
    0x2010501060e12122b05040204050601020604020306010b0f040b0d020a2307020f0103061205010b010e010f050f0307031503050601031b03020f0d060b030703050115090c02060114030a020907050304 86
    0x1504211a49141d210b86401c4030002130b08000f800d0031000800c0f00041900e1121829100e44140e5002a82e10035030315800c2200790701c1c0c0790140c0c0307030401c000303002401d454106500031076150034050240081030000007904038000711aa02c01c80b0020703c40139985a4803039240300c5001010750300005d24a8002007d9508158040c84d126800e0560381c464019440d2500b0040c0d0700788002030001c105650306042e5502e41c00203100304030541d000da04902c14400000c580da00c1e80d0001d45200c0140700305504004119441500190304142111144540700a6082d2a035450f020100c007e02039007840824201c8080c08004104000081d565069174814500c5880d01c0c0da00c0c9400850024907032101940c050040c0c1084041070034801c58030080c40c0c0c02002e001c036107850201c01092801080ba1300c206c80b169903d0750408284040c80983c500605442e0405018040129000030364a00040c0910518058150b4596505540c1000130480c407d078040c0000090740751090028055070800c85043d0b603a04e00d200280c1150 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 36644546 1250 36643296 36643309
    0x50910080105130b0a1211040e0d05070b150307080615090705071b03060516030b0405060a0e150301090b06041a09070509010c051203061f08010e061f02010501060e 72
    0x1038034030240c40310508010f020000380c0513244450a0703d0304070842c94404201d44451000116009000e00b0741420b40004405c1407004945601310514015004100c00702c5d14285e0010484001e1a040118a6010380300c9107031446080c02c0444070140d15114000c000210f00300041401403158260341d40f030740d4013032038032200340010b0740c0c801c84005c0c00154003004141c0003d0007401c0118030304030144058900c2c898580d0303a008102d0300281c0d48000590404698050020f0b410f0203112501c00050b02e00707000604144021034042d180e203006d942c1d6036204190014600880e800c002c441c507004000d000748006040f5080c8000c0340700040d6980c2c0e0080c2d0501d11f258030701070b044c801e9070082c920000e0031a00e16603a41d000100c80d541c0055451ba0704000da451028004508100081c0000c1140c440c0c10540d641040b03020031085984d07032401508240b1018848040407a0041075140c11100200c60b40d0129654540009418102d62080d6134070710368a580361844016815403000c2d060320602e458800d1190058001c0080 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 36645796 1250 36644546 36644549
    0xb010f0f020a03210905010f0b0105070f0204200d0209010e01050307080106051608040f06030b12060601080c0d150e0612061b04030b0c0d050c070305031807080a030509100801 77
    0x903a0144018070002032040340d044d13038000b055104400d05080360701d140300c1c00e40e1000320050710141e450341050a09806280b0030051510024281646404855500c0380b8070070344484806031103030ba503603e400e00b4a0055144120300a41d801c4040e01e559550700b08044c1b009410491143c0c1c000390303e031100c1c11001d50040084038019451038894450366071900208942503070040c549115151410014080000c81d80030203000500b41c071444106040b800c0803001400c40305080744440c843c00c5003000b1032203c400c1c0807490b650401c4081c60454030036035400d50142e5403407056554480d0018500003404010100103840041600c940d000c0100c2d040c1c6802081103000090894210240d400c144082100e59030040f00c0380340c0607400158a54145035494555031019841191107100750800091380c903107030322080d10906e5032049608080c5410521203071401045800003c040e001248100014885102c0e420000400105450b80450703441c00d5003413038000c000781c00442c506401158642c480404403800790a4003030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 36647046 1250 36645796 36645827
    0x60f0204030b0a091110050d20040603110405120a050c0102060606090405040c030c0b0c060703061508061801090b0f0d03080f04080d0c03052a1c06050303030103060b010f 75
    0x5195100c0b1240c0800900c04c0c000100c911600d02c0300200034540300d010400c000009161101038030340b00284103220a403000001f6411644540e860000c10301c0b2603c000391000c0c0d821501d40020255180b0302c41d00740c02d02c900d41000350b0100346d100c1c1000b60030400188080b60f40d4411010380d0b0000c540301d0016a82c40740107540c0203501c130106002c8980f06003842d5222992050003541d002040e15520748a65031520300580000295000001d00b448010504206003608121245010804030380f4202c0340c3e0f240c48007400450401c0042c0c2a000c9219039953ca40c00070710880140d41140c40b0355941d844420f00a0036941d1840303024047c0e1241e00382207450302944035411540c0688840d00c0310340d0383c03070a03a141c0c41400034002c4a070b2080c244034000482c1883d10903002c1c2c0300c036903840024081c10816181444c200c2c400402072840001510940990503180080e101e05c001d01400c1c54840700c880c900310001502385038010940520012000206008254000405400f800c2c0c9500400a4011008580709511880c0ca82c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 36648296 1250 36647046 36647063
    0x230102070f0519091103040b0903040308030a110705010c030605100509060403030c03020a050a05160b0304030e190b03160e0d110d03050c1608011a01140c120301090603060f020403 79
    0x2008941803682010702c1074440c040460f0030464032800e20701e0407552107880d9080c030340801000704000c0144210700103801a051348001d500f428995590403046210040ca81803101c0e442c0c0344c2d40120007110340709a44001e13a00100901102182e050020010501481060310030550480c1c4405180e009030b08580700944060f11851506040d500c059400348211b180460840c800c3c02c030003c01294091000e0144244100c3c00340080444454a80400d40032580260084900070070600000941040880950748001e43d007406052038013100c001c0d83c0d1002a40203444040300002003050b0b0941d45400c1140340b0b042d0f80c0311800901c5a0206000283d8658840100825492281124180f070003102c0148140e109247c11458020561002d03814202201c01c0c195041004040a1224543c28040c0c52a20449581810848844a000200320303c0280f40942d41580000400b8001c221040c041160980c030146482a0f0300c2d691141650010240752100340c0e0602d1800180d098921504e000b22002c4940190781d9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 36649546 1250 36648296 36648299
    0x5060c090a05040c02031b06010501080a0209030a02101107090e01060603060803030c070c03170903010b0f18040503040e090304170601061d0f0306090309040501050307150f030b030601230102070f 86
    0x2d03c001130540301110401c0d03100c1800700c4d0b5414101c0c8441c2000d04454040901410352520300090050710700038100110300c0340140908402a280014420400307901144c1003215204114003e4927038a6041c050303c007850041c03440104224960760803006e03010403890020002240e40744411001c1320310740e0090910ba90030030400310b1040c8000d0805050002d00440c00e42002d00d5807550358010040f22103484a0301800041901d00c1140340a02c1000c01c05003040c1c0f070700d540019403030780060702c2c000ac8000748014042c492008101809020400d0310041d1207550110205410412149036880d0098030a0408030003454144480e40c3c0d8000c10300b5030403620341ea100d140d03554107a40541c0e20011410314090380c10889a603410b60140d80d040054a00a0092602455803a1805400c0c003059410503007100d4083d0348203007020044c0d901603c040312540026843c08402c118103a02c8110046e10300300030f0041d4144660000402c410107101c0e1102c003018a02107030460042101e10069841705100d00c56200d60795910b800 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 36650796 1250 36649546 36649549
    0xc09030b1806010b0f0c0a0c060815090a0c030902060c010905190c0909050307020307030b01180603020f060c1504030e0109061d060a0302040308070807120207080a0303090c05060d0905060c090a05 86
    0x6000411305d13803d03140b0f00780803204440d41d00c0e1100520303080d107240201c64800c210098000c840d40350803915040d102c2080d5014000861000c92003c0c00889080d50f541d800754005521a50208541c0f940c0142031607a240007600c015406800c51120555450065511600461050440c80c508042d84602d81608180c0b03006020b00c0149842c103030a440d1070204001080050f5000d01061015600c1410703042e42d80c0d41070082c141c59020b141d5982c16440c0349404418030160755003440000b80c05004445403607588002c981c5490420078510505610388806405100405403c50440d201c002020b90354503000c0b40e601d010403186200c200166a00ca408000c4c0d000e0303a05d0a12100404000880c0e04016141136500d644090550780500b2003999146404580e81042204403001480c010000b03100400345503043c0404192668003002000302890396840751801040341005120b0300a24000300003a450307082501d1050064408880210b401c1d0180200040c040f01005054030701e044800f501e02500706040c50f0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 36652046 1250 36650796 36650819
    0x8090607030c140a0207060f05040b0306040f0b120105010305010b010302040320120d020c0a09020c03030a090204090210020f0c01020d0e0120010c090608060402042409090c09030b180601 82
    0x1e500004022250f280c420350904401c00814007000301d079005219503413600c00014021100b101076503081040400c010010f8580440070340c0c0d0421421900000d1503001c0b03280035402017503605155500300608020044003800c065000604981c01100240324410210004404a1041c0d0200805d29204034124191080e0004070700140524098401c2420078058800d1b1707032034481002c0e0240010307442140300307604c0341c14480c204070014080b01106600308090030303020a8881c000140050311340341c0d0301c6030048259644d903000009442d030050502612100340400003511051424143c403032074411710071100c085510009038074040c117403507a4400e100d0b18200b200445107110729180009454950a4140107800743c28401c42c0140700d11512a80304662901d0400b4003124001800980300700e00c144410031030ba01c0c0141c1c44150f0300e0080c1003441c401a21102c0250740807003480c1c00142c00c051a2003c60403c0f1a00032200d842501d009880004141d84c0b00c44074000c21265040c51400c143e049440100300d16440c45 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 36653296 1250 36652046 36652061
    0x8101e0b0a140301091505060c0c0d0c0e010e0609090d1e020a02040c050a020f0613020607060f060e0603070b0903030901081012030c03120504030e1918050f01060809060703 76
    0x41c03604039102e4000c1c068040706600281c0000c407803d551540945905400080d5140003800244d84290400318244402d81d00c84181102090140c0481000e07034080005010341c0c0c0000d041e440c040348046584889103070545590884000703005e03105100114040300000990098a424141d5a038000081150003602e82803508a809005603c0341501c000c00594490143c80d08103603035079441e41e4440c0c0c070800c4002e00c0d00140e03190303030031150f00040c080c0441c03c0c0303258011889160701502d94555400142c80c06600409403400c1c81a40580b8080300400c10340700740d003001c5000b40012001c80d89901d440700c648820b28420000040d0b816402002a43c407294050b14040d54056a841c040b074915595540302921101e4001e2001c40000b00c071044080b04142e0003802205440803a20410040c070310b4141d40c0a003e000b405e004041c0708030402c210511455003c6118038010301912004041c810700304282c40c002602c0c09803003909040c0a038100224a0034401e420152060504000030324003070700c074030a040c2d00500d4003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 36654546 1250 36653296 36653317
    0x20901050903070e070f08150d0213150602010e010c050306090402040213030302010b03150c03130c08100209030f010207020108040807020a0b07030c02011806050d0b19030308101e0b 80
    0x103100300070070303642c0034803c08004280750070325079a00c0c5c030780304e90700a0050013040202024410b0003010f118403046c2002441c28035030001e81d00c1c101c030010b050002400c2c00084128101210b07003402c01554004150301c42440480303000390000e01982ca60703000600d00b682d0000350998001007042c00090102c1c40c00000e071940185c0094001031502404c3e81c42e0b2021041150000c4d40580e454007802032080c03c0c03c01041a040100000c6030001d801d040c0d401c405d2a21010b00070502045403400010213002c2d00d1160b0900a0050350300726416030700b49000d844065001242d0712407181c000c2e0112002c4001044c001c42c0c0e0392541c16036440b00300b40d031650360341105078001c6942680c100040403008120f032030304000113100039400707915108280000d500c001042c464403201c2603088074000c014200030f115000001e071241158103100110b0314202c0d400c041502c00c0314250f000c200d80e404500000080c0340d0000105ca000700c0040d1882c2841e01d440781f40c40142d0048960800c003c801d45d9804c204201040d81c806090704100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 36655796 1250 36654546 36654557
    0x50a03020318061e0604060b040303031d19060f060807030f03050405060a11010510050f04090609080307110f0d02070608040807020901030501060513050c041403030d0609050a0501051f03020901 85
    0x209109000e2511000301c42c06013a0360b40030b00b51040d004015011031076000d60111424400300e8107001c1d040c3d00c40d01a0f4031008050503103030014103c0d15414104020f503544d0310b01c4100c0380484050b03802d060082c0301400003a108240351502144807036071240219015900d5000050802d54515a6a04a600c03904202030b401c000c014400414555504401001410340c2a513841c1c01080424407907508550001d0301e2410000c007016002c210302d440700810018009030407580080c40c0700643c10800060300d240c010040c12468000104207416401c801264201c1607403800311107030b00d4215014107030707a070141840c03120142c0d001d41e401304800c502c00c176403403a4841d11401030b1a0410f1036660100710304003000c1c2c100b1103199441c1c40d402d02003401c08141d6044103038400503091180b410101c0170144688580d0141004142c4000301d6540d1a441c1002110381c50041c024080141c0d9694100307580050006a800b0812141403100000b568070344131200b401e41c1208440701240b4800ca00400b40c1c000d60068200906100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 36657046 1250 36655796 36655831
    0x306050a05090c0f030108010204050109120314030903070803191503050a021003020405030618100207030e06090103090b04030206040201140306090f10050a0603150e09030a0c051903020a140607050a030203 90
    0x3211980914007c0c0307440000540c4542c1007800140c0a0704603034110390100000d40202c40c0109921886c0c005441c0c26012000c1d50726207424403040c0c110b10803c00040c0101000106000741803541e0202a100c00707801210821250840c05041c026042041c4000703002a84030711072000240c90309090b1b004c620320301418018502030741c42001c2402d02e13904980812000034142e280201c141814051036442003000d0034214500f010654000d01f9140748441194050400810b20070303590b9000c1c1d800840c00315008840c0034003515103403500969800c4119412030018148071458401c442d81e071420b89004a03c0102100400d079111403c030703981c5000050106580c8803140c607002400e40c580c0124000500000d550208007040341724411405040d45a00078522010380a04000d80c03420702205a8025900034a4a038140e0106c506000386000d01c1c00710303501031403048200500201a000500c28803900e115504555101c140541c3d0287c8030070b01140c0d1040442c004000c410b441c14804c1d8011940b10200154407100030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 36658296 1250 36657046 36657067
    0x4050a0308090a0b090105182b0c060c0b0f04030c0804060201090c1a07021309021309030201050906070203030714070c081e070311060d0914030301060f0306050a05090c 74
    0x48505038419110311500240d40441420030031030520180c40102d800501d080d02010000f00325109059007498441c0e960401281c070b0f507a80d40b480024182125092000100003100f40ba5004520407500701c0e40c640000000140b2580200b440210640d0012a244440d40d5081020444407500030030403808c1044400c82440010401130150020386908d80c000500e440c07243c0b80c6050400c1d416000000300e9100c0f4464426980603c500311482c0c540d0680f50020700400c0910fa81001e00364a40000303502095940d00c0980d0300c07c0035481491064003c6c2e00911880e01d031111a82e1700c2d50400d8403041c0058101f00000303800d4038040c24405c880c0d0004c1c00c00c01ca180200d5502c8900001d6600c2e046003989811a191618140400440104040b1f945001070041700c0e142d551042d580450001545018a802045414036521990311001a050b04507000c1c1e100241100c8903203480764401d002c0c0340003003104408100c829601c6449850183c1e1006000020490305100c208008064004d000000c110710411611015 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 36659546 1250 36658296 36658309
    0x6030a0908130b0a0e040501050d080a020712060b01090902121503030702040f050702070602060709030b060d020607030201140a060b04030206070203190c03150e060a05071b030c021f140903030405 86
    0x10544041210348070780051134000d02d9945030444031807196080c200140455966210030048172584404440d55442c00014103a04054580d0322201c1e00c8012109064144074203a00003114490090b07071001d040d15180e034800022401802c54a040301009100002c80d4402400c00c0c00951640003003c43e8100466640010203481c59900100b09942c1c4034010b21603065010840c041c06070055001a0080c0e242ca000000d008046070300c4050509201040810015241e03030300103c0c502c680107000141d4441e45414041d010307015031186001c030202d0400c009800b01e1614821082524070489089241c98907603002c000c6943c000c0041685e15000d1003c612050101c0040800100f45c0710341034811605145061591002c02c00d000e24030003071420418416424980414903a61001030700c440003500342c45620781207504042c0800b14103455a00e1541c40300a02d031300864600503442c4200c035000d0012000c0d080c4e03440400d0119550b9004144c503202240d0400800c1d202502d11a00043c040305d0510f035031040010340707 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 36660796 1250 36659546 36659549
    0xd0921050705010b010906080c090103060b070303050f0105030105010f090e01020f0408060f0601030c09170c030708010f050c0a0c020d03120614120105010f120303060b030925030206030a090813 85
    0x315000160800c20010280a907100c1c031002424540d4046d4a4004060103100d4001d000c01a007060010b05108079038000e80c00ba8002c3c1c0b80081015884601525018001346400e41d0516100c0362503030000221480c05020381c6041e42d001d41141c40a0038a0809128080c000328545405155000d0042001e5582c0b020702820040403003100814060900c001905007690780a00600d04041c1800c198001e0a6003101c9880100c0f0a00050700300d2280400c60a181043c1c044c0c03051035070500518000041001054002201c450f805001c02c00c82030301d41c42c800c840607105442c141800714146501030400b51410b40d1b507141d003c5000e0304260548009076881d003411109950000b08844100ba17814030030710304100481c01d81c1e1907129002007106504050807440241c0c054850b080c1e1032001c0044010405100341c211800030816403038155102e0511080b2261680340c0c0d08000840b804075118034848035441107401c20103e98000d00480c1c07458032180c101c20f0141a0b8450103480c603e81c2041014040b0041544400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 36662046 1250 36660796 36660863
    0x2040e04060c1101050403050405090702010b03060c0901090f03050d0305060a0911041401110c1507020d0c0614120613090816030e030f1c171008010c0807050d09 71
    0xb0000c010a00103424090805407a01290303142408010000360050111425154115032110060b90340c404124094110864040c2d0540100400d005c0c2c0a0302c010007424035101c00b41c07182c220003612061010b8148a10b441701500d1940604103042d9454001c2c0d00c082c1c2c0194001d800b000f0aa9202c031040ca0036250041100201c1c034100040030482c541130b80f86143c2902d0005d103040740415101c02e1455036035003000d81501e4814401100f04410058842040790f040d5540640712400f100118144040c00d00c00f10f01c201c60102d030725222102201e41c003070001c40c0c8940d080c01c204400d094031520700380511b5032404010200901c1e61100f02c000820010f202900051070300060054020310640350040c288540300750340c18081e600895981c1080b0f0030124400003074038480c80c1601130a00c1074103401c840000d10044e03000d220400b0302050200140c400002c0038156070001c4000c1c4403004040d42c00701c905040880e0140006901807142c622248840e400540400e4060581803c01048107040442c0e044400c45125 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 36663296 1250 36662046 36662051
    0x2b1107080706120204140103050a150308030405070b0906120c0405040527010209011b0c05040c0207080d020a020a14010908030d0903020111090307030312060b0d0209090a06081c0302040e0406 84
    0x400c850b41c0d00c070315000d9070242810310550800b458940f2485e800411080483c0c18140c0715000a542e03c45c00751300005141c0b00007a00300c0141503481c1130a9120f54410340b403e582c54007481e040460210001e50440d85d0399400a084189010200c0403140340007107000d445040030020811001490f603945000d0341c1d00414900391750003003c04c007140c1a64009d000c4c0e1003000f03c2d00d0b401444a21020383c1c001c08840b00810120540b954020054034020100c1849904044d07846880c040c01008400e600003500d20959249100300c403590a501d0000340c1e038610f100741c0001e42c001240241405441590f42010002c050181005045a03490705400c5003141c102113841c078051503a81681c0028198240950000c640341c140e04a0b1800880c480401e441c0e040e14000130b01404815144140c11402c240d0004c0001d02c0320103012502c492000c413000c0c004e9070180041a103d04e0480c000300e1001812840340600f15031008004001d200c40e403026082c50311102c22401d40902d682400002403864060498500c00ca100c1d5100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 36664546 1250 36663296 36663299
    0x4110301051303020d030f0b060c010b090a02090607060c021e161208030f04140105040b04020a1d0f07170c090405010614040621020a120b032b11070807 67
    0xa050845400521603a14900002d8118000c00d4003c00c484c0f41000444c50042460809952090040d29510810940009001610451080301940426541d0b0002c0b01c1805c89a20b92a221009030701580003801da0164003041030800146141e44817580400035801a03918104031100c401c05940700f0840011071a03000290000320103140c81c01e00c07002400c072000800603e888581c40d0544075000041281020b9203840021030240310500f8440040f00302114000d00492405180c0100c00003000c1c0c1d02280681c0409601087c1e040d03a8440b80942c544103080550b50740e5032190704004c201075026002c0418003080200b2403881941c02102c0c2c80c440c40d4003402c8540d4550064040c88115030050744034004200300400281c01204001084030105c9800d46402840c88207464403402c50012041d03035040340d003480000c2445c00b003604011980f140c0d007803a05080003228105814181c880b011200651040038443d07668040c0703001d201c04100d00201c00c501d0f1a050102e49841a24070700007690b040309203141e01a440 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 36665796 1250 36664546 36664549
    0x506011205040f0203210d090206070803041a15010c02040b01030f060303030218030613080708041706040c0f050a05090c0d050c03090709090f06051504061721040e18060411 76
    0x24100900f04800b04641c40403806c00e10355a0540102103007042c1840d02e0f400c540095540b22400d0342d87c080c1e0001d45066a0342490300d07104803e540842d10408a90720014001400050380d0b2505541d00501130b194040141556402c22006164481d0301d24141540d50640d1180181d1500c40e140140d8403175100141c0c0d510039a107019883c1d03202052464420351095080003c00f02d201146078200340d81c400059502c5448500d04807500d8082c54000282c102c410009548040ea40040c074280664011802c010712551241d65009150103180078803900078259074010000360608081003640304120f20384a6052000c3e8101080544005441c0700380b141c403000c0188103406a0a1200c1c10003425000005c000402440da103c0c1c5000800178000342969681b4000960581d0490182c10301c10310300180100641902c500b0100c142032480c01c41c40c1d00d14860816942250700052881d0306c8540240c4400d00c0c01e0610340009140c0c000002401c076901c1c080345804041051604000b130900552080c054500c02401d840c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 36667046 1250 36665796 36665803
    0x501200109170903012f070f050105070c1104050403140d0209030303041101080c1e030c0904090b0a1508190c0305030f03011502030702011d01170406020304031413090506011205040f0203 82
    0x4001c02c540f55802c0c03200791040c40f007280c0b03140011446e001c00c0d143c040758103003220b00740f640e0744016004e54241f0b000c1140c6154082442c40c0001d11685495040080d44018041103031030440c4d0040100701c0b851030482000d5a080b014140b40038425801624004005003c6811070300140c40c2100d291444583d44102507800040007980004c0c036018840c01c08940801301c07402d005002c2a814400400000400c640d01c2e1880100c0d120301d40d010b00180a0140c1519104c4000c98040360403074200da01d45040d00035403080315990b400884149070000c11510864140d03460700045030540c21142038501e8000000001c5003400a0300183c428502182c0d120762505102e20504039409002c1310440d0405c02c20100142c0e00040d201c400000e8404403a00c0c0707045413a005030f5078400c0c0c00303007812108090007080004000c51600250701c5a40720391703036031042403105e10748075145030140c00424840700640e108140702a0b8990381c0038035400001498894010500f4440030011101c0541d02034440d0061451024151704040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 36668296 1250 36667046 36667061
    0x6062808060105120402011805030109050a140c0a030b0903040e0a0509070f06080f06131103150d1502030717130c06050306060702041e0c020d0f050301050120010917090301 76
    0x2800c0031494024a84804c20380300c600284001c0c1030001d07409000c00050a40844a1301601018000b005003075540c3c20720596806030040202c1e8003410b02090010f4014006c50b600e1801c010203822200003505555543e8058240140f6415051109010014030211520840d90092078681c0740080c5500308042c036030b81003441e035401503452803c4c2c400c0100302e001d41c005403c1f80d2040c480e00c400c0d440d07a01c850f40003440320300c90300161401444c10051326000b50f8810400840c018041c4e0400e40d4031a1404900340b122282c11030b400035020490034400c82c20fa94059400843d40001e42d45086280e00107800101c070f04810701903a0501c07408619540b15410010310078240405041181801c80c154a00f510011328584600d04000703002c0d070348074500c0314100f0300100000290480c40d89130038007070a90f00150003035807050442c280100041003603807400402c5000b5821641a00c0040c0c4d01c150f8619044507409800c405001203144096580d0015000415035502100c1ca029101255407540d5102c890100b6003500d2a0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 36669546 1250 36668296 36668299
    0x3130b0a09110d05010902040c03020901030b0a08120d02071208010513050c041701060305010c111603050d03020304051c05040801060803030108071514070507030209011401170606280806 82
    0x141907400011610507200d00c03400b4281211049140d00c41440c180b4054040c5a200a410a081c02740d00d4405640640141003509020b98081001c00240f400300240e51605100b0a0a039410184480010a4281c0e0040003509a2401d016240a086503a91880042d00c108020f002602400042c4083e15140d043d001e0240013045040c802d505001c0144625480703103201f814006580d1480356401c01d0380c00c0d00000000d5400030000c100c542107601c0301030544001d0085d80303840c038012444040d0307031810365825440540740c1080040c60803444840d0242c0c020360010b4800e95640c4510020200800a901006006a10b081c0e4815847d07a2903c000f41d1700b506c44030703044138299400500043c0103044000070401c0489070903040e0007030710114400d0305071030681659000311540c0100041902c140b05000401d4000c4920940c0c01c0c20181c0c3c0e94480c0e40342219440c551343d50000f031001075004400302c2807403c0da5030028401808185401c03504002c03100c02d020b502e0300380c4030000b040c50020203202d500921030a500010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 36670796 1250 36669546 36669551
    0xa020a08130506070e0102071805060301060b030903030606090418050109020a0602150613060b07080a0206070504060e04050403090504090506100e01270209060d0207050c0a0b1812010203130b0a 85
    0x120b5503456844003402042c00b0100310200715009026031080007020000c064002001c0200003004c521300018203022502c0360702942c213109000a40550700780490b0312610040010b14110303210340c03003040102d40c80313a4000e07540651030b0304030000c0000414622860b420322560000500a50720b10500140c101a0780c040001d54105440300415900c40d01c1c1c1c605e83c8944221051020005c1c0400603000402c50394000105111380480c0300c1c001c21041800402c44508260210754a559950100301d9440c49140038840016030009849031850402c0d400558016207e42040c503622502c4502150440300309001c250f881e030b031040041c416903101c0d0240c2c1c01c0c0980003001500c0b40660405085040344564400100f140e201c101800c2c8008401640c1941e4412a00400c0c00b40d0b540d89030480340c0041d4000d12400e56a500401c1d031004a1890300c4079035501180c85400100e418980c0700d168080307010001850454202242e1500700a000c9020300c01144240c4800d44501490300752810301c140307840402409103500e0362 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 36672046 1250 36670796 36670831
    0x15080c041a07150603121806120b120d0c2603040209100b04030804080607210b060418050106020706080403090311060d0c031e020405090403051608030a020a08 70
    0x114900d452044181c054444654a00e40351400d00c0b0200084104001203e1811030003000f0402c403c041c0f0400304039903548045404100c00342d1032911103118810b54001c54020402d110040010350081c0300d070030b04010081a80c5506c61480a4145281600c0d03640008084600860403c03851160341548400b00040002d8050328010b40880c1701e12010700064494038681000030303503194400120318040d003240340d48591556a2850f0603004d6400c04c3c041c0700c1c02c9016140006106071311031a075110000c00003042d00c0c900c4030705040301c8030b0080c1043e0026a8200703404000c0401e10018042c010103208506420000d015890002e00074100800d5400000c00c0094550610010136072004413542580d4126011700040c02005000807801c0c071560441481c20307810085c03c00901c1c0d4055102041d01c1540e05940b1003241030f40740c0003400303c1c451030060340d41c082038200c041780209101d00003034241e03122030000e070700100d00d540d0f15a0111504221803e044083c1c00007901c2c505164055521030b04006126038150400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 36673296 1250 36672046 36672059
    0x8010b03071a0714060403030c0c1101030c0509030102040b0405030609190809042414030307050312090106050310020309120405210102130603050f090a05071202030c040615080c04 79
    0x301894410560001c410707242c800d10070705503603044070260399000441c40e03490800708030400d881d44011107054010030300e85249c902006000780c1c1050741042e805041403041d0715000d070056000300400c011090800c02c041c0300014803900c00344010300203001c5880c48952614500410945491402002d1020982100556101031040741c2ca1079010150300122054655008002140090546c2d200034015010380c119042d0385940032141c10425100404281d40d419182d110905a41c1d22440700010029402084404c200e4900d802240b5004561000041a502e41c0c03440004d1030000d00e800703040c112580c000140011640d0070051140c400001c2075805080610744000240c4054601209105000701101d44100c09602941100c003450041c0c803a82c03011a450b20b2000f001440201c0310b0410088040001c14245c200c00142e9400302035010b8020542c050809aa529036201d050700100d80520461104507140d568038001c1c0f00103810900c0c0010000314228000400c03201010f400c00e283c01404202c240401c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 36674546 1250 36673296 36673303
    0xc0e010603020a050a0f030f0903030b181605070606030f150506030c0a050d0309030b0a020a090b0909070f020a0b01171605011209080d0908091003020310150c050114010f08010b03 79
    0x51403086c20240802d14a41d28242c01910785081ca0501c4540f510031020b00701a010f9000d03c0c0200c400365103806205404007180440f100040d228240102c050b161442c83e001d128000030320b00ba5110b42004624696030340e4138102c503840099421a5903486815150060410a116459101e44114009c08058101c907000c039810030003034080d682c003840b443d0105034281030182170b01000565106403136003558940f468015000b5003000f00381c0c10000d0410000040e01d040400700340c4a44200c020036040150700c95036401e4075842c0103800e4280540c0907007114000843c2c18040704600a041c1c2040c0100401c0c00c41c40d4550414040b5241511740001021052103140d0307101c6104080d0101036400020056114140154603004985c0b0340c1e40f209081508200410082c0405051889000d54410000c00301080003074060303020131254041142c81607034040145500c12010740c401a080d6003402d900c0b80382075403a0142587c603010700500407250100010000c02c410b240030800286031010081010a042400003502d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 36675796 1250 36674546 36674557
    0x10f02090126130614040302160506070b0606030907150e01030c08040b0103120507020a08010e0613051002031302040f05070f0203120c0a05040816031e02090a0c1107030c0e010603020a05 82
    0x256461605420f0301000065413050000b401e80035011a19440d146c40c0080d950408051281d01420b88500c001407a800c10704192115640c1c00100c000d06c0e941c0d076a040c171101d50801001802c0300c0c81b60341d00020b0190b18071017141710070300540e91305c000481800200140540785520581c0080200d83e030f0400021408003030919042d641e01c5a0030503200b600322401100e80f4010600065800380d5120300c00196920150302c0300c0300c00340c40300c0c00391900c6660b498181c055030000f40030083e056800841055115441ca54001c40d03203c0b000301922110307443e031900820b048034202400c0104050b960010f100740340d6080110707030307900102c1440214a01540107101750103522010f030500d20194004920301c50040d0150307086ea8060a240012640e6803894103010080760030305e510080d50a11007a908072051004900d0300c1e02c5419801030142c5146451f03035640c80c1d000340540900b071001c102484010f0010b451007840840001c60241000c940301500b410074105400310182d21130810325104128244039560003000781d51 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 36677046 1250 36675796 36675811
    0xb040209011410110721060e0a0f030305040312050f18010216110303040504020705070e0702070f1503110406020706030b0306040201020c1203040801110408010e0a030e061b010f02090126 82
    0x21030088400d03c0181c500b04158200c0d2800e04140b0101c030751186e07048a03031030a1050060b0070a02c00c400d8101c00307040e1100d10100c00902081d901165100c0440d0082e003100d03810511a2402e21040c0d10030440c1041120000e860b8501160484c8090002c0c00042c95000c0f0850f10100c4000c528051000c52a14950b061482d8000d020b6000e40603000c01d90782e01403003550010007000d0001c2d9960000761406a440313012030301400d203403001c41c8404074442178400550ba0095076a1603210703a01150400c9603c2060107200d0b2005410591903405480304c6440e1400500010080d03900181103407030601e080035095400382481c26003c1d038094410000540c0e07000402c13285441c1c080d1010048501d5907414035085201c1c41d00401110f6013442071074001d070b20120000b0411200c56000800240e29140880c5464140700d40001c0c00041000c14041070b80d01d000f1004004024101c2002482074084085a50139103102d010030324001c0e03601040705909941c10250b222504140c001119812401040f0401006900503040c3c0703 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 36678296 1250 36677046 36677057
    0x21b0c1c020f090c070c0b1306030509011b020d02070b070b010506070f050d0224100e0a0e06040501020702120d0f0c0609020306150423060d05011104030b040209011410 74
    0x34000e40d02c81e01040152148050006441460300e101490302951000b01704455113000e4440001d135502005c41911040103803c0002403517181340413012009480068540c030145d56888641041006044242d00703a040e4850b0003030700034612034242c01790130148103074042864004200124400120004441c60560f0307401c81c1c0540e04e076642c900301105080e00300003000704103200c1c565100c52141d80003e4070644258901d40b1140042d051082e40c0c2d1000102074802449424070f90005201c003458280c01070f0b82c03140101c0c20025000042c80c0d1000d14107075003503c040d10240d60000c0e40d0f80079410903226060700a201400104600415a000200320801c100d00701c03420032051007456000c1110b15000075201c190002d00300c840310304280543c156554840c00c003140c402d0340b501d8480c4160b0702c000c4c20101440821940c603820343c1c3d07035034005111442030340103030032642c955a407055040116800c50180019501820495440d860304e0b205100c610380c010303000075610540384a0003103c0d65652001c90034804030b841c50030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 36679546 1250 36678296 36678349
    0x70e0d030f03060614041208120117010506100c02120c0d080c0c0607030f03050a060b07140f06090a110303070c1215091106090a0b0c0a0320060c03100801090303021b0c 74
    0x3072001d03000e130218080009d8a607a00000b00865401c0c0d141c0304401c5010005c2145440c0d07107013041080949240384002007038003410840050f2400415000400300c0180030b95004840200020702c516008100072a6a0640030038654050b00c1e0810000d56150300581c0c006242182540b4003a064910100c2d503801010303241c0e000611050403d40004000704140c000140c1c035140305240601e60900c41c488010454810f0003044c00d100c800009409015401c100c0180c220b040550300e03030003071551070001400d4251004112140008082e00303422001400810840205a449480c042542c2e6503003c40d003031603850410fa9180e01180d996000b08040f018202c8090760785a880e2804503140500c280d0112480800110700702c12101408917112511500c04d40c2c80400c5404d48994070b1103030200b401850034281d0301000c0002c00c7c01103000c00a42e040010b41c004080c030107542d40c1c1200d0a480c0c03551002ca00003038012070882901c8014041c006059010301002c0c25607104008045000000e076042d060b104d1100b00d803103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 36680796 1250 36679546 36679553
    0x30706020319020c06040e0f06010315050d050312130515090304060825030605040e01050c030109020c03070606080d0f0f02060a0c030e10060f061106040605070e0d030f030606140412 80
    0x20807550300d0010b0f05d1551919584c030000100104103c410440400c082000104150701c644905002c0c4040400c01c1503401c0d04160621070b03250110752040312903210800c080c03120b401030044006d21410315020019500b1841d4501642048014003032480340780c40380c106202c110200030084d14203440262503d0b01565444002c0c001364030300480401304444006050002d82154150000400d1701c4080c1c6044c0020000a510355080700c40858070542031040c01e000500003c84c81d078004284050f250310860742800034a03150081228601d5004101c0b5603c50022212129045450114900014140724204c1500500d0280d21240002c08044c12540e407a400c000c80180660700680114260a040710122400700f42908001e00c4240070b002c0030740039106000106180700d03000070042c1e10001c0303014003a035072034641d1540d01410f001707450740c0140f000d907402c866040d44504036800061070181d51100702c00c11007000d010301111022b070805c104110b4500300403500c4125000c200c07800c481e04200708850700c0d4220709 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 36682046 1250 36680796 36680803
    0x50f0d0507050418240e010e0601030b06040807051005040303080711160b0c1006030201051c1b030b09010f1d10050603040c0801061d18010603020405090d03060503070602031902 78
    0x404c81003540003d0342c1000d03100f6115078030003094203140e1502d018040440d03004a0721808198030400441081b440018010003101c1075685400840c107040214180d0480c40004813513400c035401c2001c04c1e900c5014104010302e8007090500381c240f0b46040982c50316045880051072041e008040070140a103980e20800000d908124210b006025249004503c54036614011480d0780602c064113110322403035600b44d0030b800b00351107280d01b00ca6058440034a0807a070344041003440c14074049190403095807a0200694122222507010412455a5000035915181c9007045442001030300211407900045000748401030301401d05050540601500300704c81d81c0c1d40300c0d1042040c290354012641105002c014003042002d04122441604c04030002800750a45640307000150f010110704502071200301e08081a58545003100604440c040d0f0340001c10f0f4581c0f41e80108050710410b91309224154071401300d01200c00d07030510501001e800c0483c042c00c101450010029500c0c082e01c42185100e884a21103c0503a038002c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 36683296 1250 36682046 36682049
    0x5060604230301151403010c0905011101020d1104051f021209030c040e07080f06060d080d020c0a0305090307090e060a180c0803041d070903150609020403050c040606050f0d05070504 80
    0x9000307020071a19590b44240c0034003507114a1007444c13000c0317010701c60916040c040c540080c0240ea64980341149003500456006060000340b03600365508000070560520701e806280c40e1207071103501035581c540c80c01050000c02070341c2e0484a10786070502d500500b49940e000c07840300c80740040101f0958031021440000390030f14a0002c2a164420302d0030107101444040455480101c0e1098000d80d90200890304200341c603010110303a1141c0c04048291030000080031480600454480d0a0005091a504441440c58100e00c03100035008a9408038032203c2d02e240030018540030b014110010b00c0740240c0e0361803203652808058401400a40c68a000441082402c940110b0a54129220740d444941e5503400d075850b580720b4011185903801a40d10b80d80001041c11685002d0b0040350360760500e851440e06e07140082c5c2da0702255070411075184c0000041e46078040c000382003e18060b4000d032000100710300401088a259501c40014400c060010000049003401910100c03982e62002040b82d41d1003103812581413145 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 36684546 1250 36683296 36683299
    0x3120609070e0909060a0506011d01050f0d0e060a0b0a030308060607050a0503030711010c0c020603190f090c080106050102010b150a0e04050a0c020d050301052407080a11010c030506060423 83
    0xa0804000b12a40d00048485c0280c6c20240e040060352138940044414034030501c035206040d000410945880d52003000108840480c2c000c0d8241000c42000e00704040d50040c0c480a24140d005000b40601c240e81ca01c5400380c0f4030703411141404113514542e800380c60003100030411072080c0700c04118002401000d121744074005a01070240d036580c0c034100340c02a01c154089101c00300c2641c80d141410030901c0c001c020010348250010311490550361101012250705120b994a02c4071651907040360200115140540541581301343c407030400c4a4108030285007181d103070b580043d045a04112100300300e5118038045491003150b10050303503500e07010640b081e9810211154004e400030710705402c00c031f003032400c41d408051080d0290f429202d0144d00d03c001103d050100b80209644408202508402c400c038450410110900b003880c800d0600300f03952508d80706500400702510103d000d104520007507040038855500d00005d542010015402d10030040f800501031400382d061010341444041c1c0c41240030418100352101c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 36685796 1250 36684546 36684559
    0xf212101030c03030e06070b040602130e070c02031501050603010614130902040315050106200c09090706022802090402220f0f0b0306040f080f030702010213050303120609070e 77
    0x25070380740004440c01c140c4801c0e40043d9041820030b0442c5407107000c0b2800c998100800c4001c40d02d540d15800700030750180122400c0c0c3c0304190800a00b10840042c500d2045806440303404580c2d4060051505002184498200461810340140030307694070001a641585c2007441c0c400c1611000245000540c40351902c411111000c421000400d000140c005006503440744108085c0380b040c1d00017a03020380b5402c0c000c880200d003641d0001460407811244090708071103070300c085812804184010840f290010383d0600400d8100c1142401000d804114a41c28034061200f100c1c060040072103010505080382c1e01c001e2141941c800484c06543e85d518070303c01d00300c2460a0b44104801d4103240c1e84c00810070190314080450400010701d402d10340521070900d40c004003a024162558859441100c403c0b9120700807101c10038140400c00c01d00c9003040165104001e42d400041e5114079810041604040d2944414030035071040000c032455000b4026040d41040050f10103024603204c1721410780e100d00356084040d41140c1c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 36687046 1250 36685796 36685799
    0xa030818031815070209010902160b1906080610031b0905070e010906170604020a2006060103051605070303050912070b0a0b011403070f1b050a050f212101 68
    0x88140c1d4840b0301e5070200d407a400205401a0540110700400a0113544002480c00400c034403501500107022240d00034606c085124025900e80782d00d008103941c8510402030b095400803007aa0107104900c06000d03920000c00d5549084d40301640d06021b54080205204001c0742a100d960f2582d142610103071010b20000e11407482c101c0c000070050040c4110181c0054022100002c0e00d9000d0441c6200030385800c8199034095480390706100180d405030341510b0821801c2c0c0c0c501221100001001500301c2c0400780030384160706000c030004048d030f10058488401030f01c4000c3c0020150350044111110a68142404251070356402001801e10501c90007401c450130000a40404002c84114200d22515089404002024401004565545801c503080f09550030030004209501c0c020110a40c09241500c1c210701441600c00c0510900050003104403010783c8019203440401c034050042401a42080b40280306501029648551550007000c00c1060351800007600001101c010040d10b580f0703e000c4800e0182035 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 36688296 1250 36687046 36687067
    0x90209010c0b07020c0301150605040902070c0e010e011502060601051b0109050f070303031104060c021201061a18040c0206060d020105040b0708040f0b040f0e0711010e03180901080a03081803 84
    0x842100145d20b00c01e500e042400060b9800d1a4111029a880340c0d075601e08145c280b0358190001d621031203080d01d00031440040091403124080c00580030345142030801c00e41d9458078640038814030915021200707540002080001780c2e40c1c08419500c4820309806d454210016882e1014010080c85402402c580603007045054140d100194003c2142d21950b020070040e004040c2d40d00f034030b001da4002d5400040d140c0c6400d0300503140c00350300120006011000001c02507910005804811040c1c0c2e0300082c0d881e400709800e000c80d81500e0300508003403410354080c81010b600440003511a40000c0100c0d02c5561198070740c505592003082550041c00d24002017907555141d6003007001c1203800a10412103140e85864010614210305000d4804445071817860100c0c2070700301400112550401440300d820454568647c2c202e10f2004d0003101c0004001002135540c03280c1c4442446c4013284284c98041c0101c2100300108036102c0001004c40080360036140404a6489644490740d540b0343c1c0303031020841403001086e603683c00c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 36689546 1250 36688296 36688303
    0xd06030303020901170103020d0311031201080703110102030909010b0a02012316090e0c0d020c01150f090e0303040209060102010b0d0c06091211010f11010e0c0f030604020a090209010c0b0702 84
    0x1100d0f003600c131040804c1480d0540d40281d4006d000080d0803480282070040000d016072026402100c44d0000c1c3c0381090003401011100305000d80c01254142e01c1010204144800d0b4960380030503513001e10141d031500103000017150554006216500c40c8000c00249107121a2007235001c5003400c3c0b40c400c0c4115403150901146408050103641051420000081400d101402140c41e0700c2220190f416403c013594406094007600e80008a070741503125000c0090151265003840349844589000102c2c400781800c290a05c1000b00c819000802c0c05840d104200359914800000c0da980950b04451042c00b5075240c400403800b41230790b00c0d60580c02c400300d240031a040040710146c03901a0b9001d940d5a5080304ea40c0e03006d0000101c0b00314800f0b00009050b58125070079520a1149100c00b23182c6043c90b0701302d900c200103050300319401203001402d03540100044d50300a2404905d0310b8504042203004000d01d043c03a400103040c5490700d10409400c1680020b10b42050f074090f00d0080902074000444d00d00704e113800c14000c0c1d207 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 36690652 1106 36689546 36689557
    0x2060c07030e0a0611010b0301150b0d0b04110a02060c03060f010309020307050603010b04140a0305191505040b090c0301050f06010e010302040308040602030912060702030702040504080d0603030302 87
    0x96070707220100f4100040c0b165594105071786205a149600b112481c1400700e00c01e0b4100349180d0ba0003011102e400042e01c420128003030b5141c07290241500103002840300e50740c0080c00c108180e648098500c01800b9007100c00e03000c0e01e210b03a440c0b4403503504030f02c02100e45640c0a2080f100d43c180c3d5510a03804081250b1001d0b00b183c0c01d0a40303800c00500c140d0000d0340840c0e00e5040026007448460440e0740141c04608040d24101f82d613a06690358107495030351490400084e041140b5010081c030030480d0341c5d4400b8074400c42040016040c07134180043c0500003100d03640c58500c80c5030806241c5050500c5154418169070300350006036145d01c0011602c1d100790b01e119504240e001d010100c0400c00c044003c1c8020480d9800541c3d8524690091085e0707080c0354001c040741e030340140040003a4190040102d80c0004c2d811039002840359102c2c6042d01590283d0070040c5185481c2c0b0307502004050700750b0700504 = true := by decide +kernel

theorem cover : BRFrame.Cov 36510796 36690652 := by
  have h0 := BRFrame.cov_init 36510796
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36510796 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 36510796 ≤ n) (h2 : n < 36690652) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
