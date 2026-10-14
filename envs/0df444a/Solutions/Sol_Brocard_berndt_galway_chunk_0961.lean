-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0961
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:31:05.430314+00:00
-- url     : https://prove2.me/submissions/0aa7f821-d625-467a-85ab-69be068cbd03

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 172661870 ≤ n < 172841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 172663120 1250 172661870 172661921
    0x512151c080d0f050105041103090717070b28030b030a021c170c070f0e010b0a1407200103020406091a070b070503040204050105010e101103041215050109020715 71
    0x10f2003410545626400002603035414001403100725152401c40c41407003a820814002003540c0040d499080701e5581043ca800210000703202420314040b640721006076900407541003940203160aa0380d040c185040003004034010020411415036165100c2940c168200c1c0140001508140f100c44040030040898175a080d8003580e0743d131044174208441c103400803a01050791b8612050500140000341844141c0d4542e450070419200c03e01503061085e540020000224064628000c1450300e00030010103120341d4580c0c1d50703400c084200b1414103a807810400f400e07103013000003580a0300c00c0c2d4007030b01c4143d034880c8200b604008002c544110007424941d094040ac0c8042000102e050000d00c2c80303850300d0340e5069183e08061040c003054480c180c1200d8103100380c40c8603061081d100c0705291100c0480a1404018040c5080300b050f0a61117140c000e03a01c28000700071140e0500c911070800f5004601c40c1e000c100300a0f0381c3c52a280d4124060014020400e89009803002820405a004145516000600c0e19621400e0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 172664370 1250 172663120 172663147
    0xc031b081c06080706021b0604050a1211120607080f01210c030609140c040c0f050a0c141e0307020d0201050c0c090406050103030f0c08030a0e030706020403030512151c08 75
    0xc1e90105d001039025114044d0030188040590074031f0001a80d10310b060604107400034200c1d074840e004050032042c4104401d02880310002c80e184401c00050107100ca04440316003150740300d90b802c980c10f0b8003041c400300120300d00c20000600e0358100c4070f03041c20030700c01b246080c0c1500f0600000301e00f0507100700304000d0020000c20007e1055000043c41100c164079101d200d0720016083c07910403c44c0340e105a140c80d85510081d074200c4c4412482e0b101c145000c5a807010202c50a031070300c242c2c4540107401e0880d00020300e0f80707090001480a4070708070b60b02ca1803003540204801d000d5403031080c000001e402540c0f0620101c010f500540180000c00c05207170030344030090107203808a80b1401c0b040703170103489c81b5466000420505802103001c11411009240511074500d41c1e8540743e686100190a60b9a032039a0740104d40512402841a1209198032000a5680301e5681c100140103801000c2d0f4013610358200300100d110041450b00e04030201c00094084280f9204211589414000f00e050030b0310943c00401001c4180c000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 172665620 1250 172664370 172664383
    0x160309060e0105070f0c03090306021c0f0c0201060801150603111606020d0b180408030c040e0411120609060103030e0a08030a021b0d020603130203030c0d0c031b081c0608 75
    0x2107030300004007450328a800918804002c01d0b8031080c001407940d068080f0341d0216080d000e0340c0e0410009640c4036200307200544441d215a420760f065034034180b483e00804203107821101c810b014a600a000140d141e1484500302c0d40794110006003504000406c002c5a4003c3d0041c85d00f440d4201522410300311001c414544620314402e00f12081680010f03556000c82d014031555103043c0c0207548039074041919440d0302000c15400b42011300f402c0004030000d40c0c808841c200b01c402403d461006e0b440d1a0606150030b09103542d1000405100d0030005126012650002940320700c03a400c0c482c010310240e442c64400303440c3d2480c9000c1039604130200702004982407100308014200014158020211041441005440381c410304000e507104500d64403440c009a607440303080e20f40222000111802110141c800a441c610840c00600198010580d0081c04180c01c1a1551032003800b03901d0350292045007010070088020911001005208140048940c40990f4650a0155023038400c0005146803140c010324503041 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 172666870 1250 172665620 172665641
    0x2070e0403090602070f0e06040e010609140a14040308130201200607020607050301050109030206031f0b030f0a0203072a020604080c030f0a031e03060504020f09180f16030906 77
    0x600b001010000141e0401015004201c0441d82e000505c5c18400038550710140640030a1143c1d44030040f05510b0f070302c00e6100c1c100403e200e24040249020042d41c4880f4002c0072030300451094503011214070404c9096420724462681507a0b0346c0e070aa95185483c01c3c0d140000c610580c100004003a50301d2b0060300d01e0914a4424003548014a403615000c03400a1406030010300030001c1080c01c0c00100160303600a43c082007a264111840740d00d03580c0f1243e19140c8a100c40110041ca00c5191030001032042d9014001d41c052001e20006121540e00c4014401c02e0f81b0090341c0047c00203c8003503002c140803c00100c400400f0140f00c40e041940b403c19000190b8a0300503800905c3c2c01d82102014000c0351404103d002e1040d040d00018020f00009510050400d030040c2040c406440b81050034681554800c3d400040078000c002c0046440707107154100304200c1e4020301181c0340900e4034082004200402001014403d01a00c0080900f90741c2d085001c1c601703001d8025801c0d0a1644410603440080e40500900b036048 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 172668120 1250 172666870 172666877
    0x90a0b090c0c0c010e100c03030b0402031302010207060f0905090603030702040509070819080a030b0d0f0b0708070809100c05210702060610080703051012030801140301020f0405040c02070e0403 85
    0x1400c0c410b111905001e288580b8606000d0a60200c1c6402d4440c0c9407a0110303540c0c1c41c10644207000075818286e001d02400c1d00f946610500c000200301d081c1c2d48040314501c88034003e07402c90b58540d444001c140c403001d41c0d0a10050100d40114030411042c913090360416889030b00034041c0c0381042215400701e826504241c502c0d81c015088428288410714013000b0340c0c080c02040341100b561101c20741d1690319031441521070807010507450b25182d00e440d403150001016625480500030488102c40c4c1020100c2e503034240c54080001d44a10081682d00d8822410300b401220300358047d20250380c1074960100241f200c0f1845206010080c420f203011580b01d14078084030310110030807151311440d00e00ea0003400c10000070000b034810f00c0f40c89c4245000c3c1d0f900203c8a5800403542c00d00051507140d80540004024950740003021851100385001c0805500c480e005040b143e2030b01200310b02e101e0b4841050309030b00607401e442c11040d0b028002001a480c05410029900003c2e00549035141c5c1c448411054000b0f080b0b40c240c010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 172669370 1250 172668120 172668127
    0x1c090c05030c031b0405060102010e060a051f0b0901030f0605041d0c0907050d05040203030403140d030507020106140d0f0803130b091507080414030d1508010e0c090a0b090c 76
    0x18281403040454042c4100e000d00301c009060305440206a400c060360602840d82c40340020a1039000354802c1010700140401c50f99146045452100070b040d0495507181c03200c0d00c240080782084448118075041d5a00f4140550500d805400114010491044941c075400d441d00340004158441d40300d0b26000003540024000c001c3c0207180510701d481032940585004080713a604206040e54000b06035130a4180309040072445444a0002910710b0089400c0540b03c4d0301124000903014800045e038804020058400380150390300c465059003222118860589040045c104408031460309020321040c181c89044150300c00640703900c0700c0c0840d0b00111408095800580e418a041c03260602c6c1095201142c40300801b0030380d07224030300c00c244400c0103400c40040c040702d41f020404102d203869072400131150b03a2007143d403902c00c541d2500000d405150104420390100c1c2001180103041802140801c3c803490000b000c00a40503801d10200c42401040d51140c0c940d91031140103a41d0300d0090f1580544110494580c5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 172670620 1250 172669370 172669379
    0xc0c170307020a05030724121a010810050312090409060908070213090203030a0503070e0301050403081009091e0302190803040204050105040c0c0602090d0b2d070e061c090c 76
    0x2a1840c068000b130744243e000c0c003000c10919041d9441d13541910000000b81410011f06182542c01081411502d1116410a11006944c2c0001400310380000e01c08d036920b035815121900892407000c1ca501450390035400c80c1c181071800150350b00c000c00e04540c019000140500603610307042c08482d044401140c1402c00000d03040c0039441c2200150703000d401503030000c02c01032400ba40001c1e52807054590342410301c0000320000350094085c02c138441c600c8ad0060000e00c49481c00b4a00141034001c21101c1410311050244080340300f5143e4031449004903030080c00c1031100c0440880501414030301140480461080ea8807266400d80081d104007000c0d88030721a444e071242001d1042001b5100140c100d18091850b00c00f01183c100e50101400c881140c1110300140e807410320f0b00209841e0395a40402070980c0d10140d0500c41107480040c843c62004100c010001004000455a090303580e0003500c01c00300250310500d61401900d0070303c00401491800d014036030100005204140c06407450201e081d1948520301c0c00400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 172671870 1250 172670620 172670629
    0x15040b0108190506010e1210050702030309150a02070204021308100b06041403030c030a1724041a03010606050c010e0a020108071b14010e070b0f0732030c100501050904030c0c17030702 81
    0x1a00302b001400594118a0210140340e070750501c21718521304000c3e22030049150320003039a0445800c2a0050401c1d0358941103101d5070021090684611003c62180040200212986118284440c0c43c01010b43d490301d441d0420341c2d107201aa4808442d45400100440c000b1420b041004009141c030a444104003181c81d03040c880416030000b000c07010441d1190005011002054181c140c0600080703c00145009941c8803680040b51809c3c41c1c02d81545c6082804160300340c03c8400741c0488000f01d4020f028900d10b16a106031128001807000b404a281d04000c518005d010303258080c0c896102e00b190b0350703018005890f140c00368038640c1c0d0703150311a943d90100715425400610000028141b0b60f982603140ca08481071007070042c40750040203001801805003070000002081e013001900c42c480c85008140c0a590503249890b984546010340745403013011080c140c0b03029240070343c42c1280e00062081c070481cad03aa5201950440036016040328102802c5401190841c0b568036204000404d500c0110b1f01da12041c4140b2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 172673120 1250 172671870 172671881
    0x80d0e0607021b01050a03050703060f0609030b240616020a260718090503090402030c032a091c0f030807120513030e0a03050615040b0108190506010e1210 68
    0x18103c11035507402000243d80001c125003400c885d5140006441c0d4480c0c07822401000300c1c2d040700710341864210b0001080f552107921203040d2405191880800e880340611a840440083e9840b00f01d0454014032003c1403500b440074040c202d43d00c42004030f50042030760000c3e104d401c441d00f10b50f0a000000801000080c1110b80b12041e000d207250040a14a04200380343d4500e802c00009844110380707a0300580d007044424019100d207400d020b00251b480e4203000760a104181c00444802d114030442890202c0c04402e910882d4040b169411400c41c5414004d43c24000e40c0303541b9808240c0d114980050140008041c0783c2152801030080e03980c0203035410a6800105103859a414226095003041e042c001c40e0381da240822454a903240c1405d911004030440440e0410340030760304c041c12a008040420013007141521500313401d150219020041e9060100040d5103504050360800048400c010f94418000660741c0169000303c4141460000c0b19a038100145003024200720705100381d000003030b00204064130750040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 172674370 1250 172673120 172673143
    0x1c081206090624070c0e0a0b01050703090b1b0303042f0120120f0910171302060408010e0f060a06060f0f0e0909030711040c050f07080d0e060702 64
    0x2080141400d00003e0344003611503442140d400801004800110440000c0b14107181d030015003500e045584889444001b042110070140745070074030130070010030340c0301e401101c0c1160f604d500c41000103400c000d00c500540c2c1200f210818107035021a4110034000042014603c918030030b06403080000116542140d00e0308450030003864600e04020ba0b644960b0f0406181400c1c070380f030041030030050300344899003a107401d07459180d0300c07004800050b003011501d850f40c0007082c13404c0301074607035054400e08004100c1d00c29804050080c80e554105000c100318200c42c60701e25140d036000501c46030506072150030443c2106d40204488081e544080e211749494203040c007180d607000b14020810080107150440150868081c3c6a240382007000105400f071025004408500c40450041c0c0b2800403481d1200b11580d90f640b00d10800e5582428070003071018946043e000f195130718440c030303541c507801c0001b44003406106030002c1e40700300e680f00d0081c05154502c800038400c1c1071041200740010426410011070190505008030781 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 172675620 1250 172674370 172674379
    0xb0705010f0f15030303051308070c080d050711241303140318010f050d15230f010c030e0613030c0906060f0503070309050a0506010612020c100203061c081206 70
    0x240d8014054208250444c0d8145c140815181d0340d02210b030b115544c03840c60080a82c4400b01717489003400481800081034a03502c40032118040403200054070303d801111402400c01c0768550207038901e41083c0882c100524000340c104040319031b003c20500441d8000b592800031040c002c800130401d100b02512240a0402c21501035440e02100c2c0d010318404180c50748005045c0814056200c3d5201d11030012078801e00c0400c0342c1080841605980701d0310010f600d1143d82140c3d080942c4648640014406485110308001d0014003500b041500544601e004c00400740c040c0000b640c1c03030075010384a400051160b04420000007a0072070843ca0842050580e542001c0ba40d58a40102446110f4000842c0009c80005041083d00c0c2d0b5646d03c022009042e0201009042e0701030300003a00100100002c160341604c80e20303201c41000801000c200700403801640c103031201076805a544008a08400d50045821800c098406080002e806440b8502030000003001c039820000020100482c0101c042c541c2d0700110102c5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 172676870 1250 172675620 172675631
    0x10050912040f030206071a040819050903060f0a09050601150f090e0408030a0207020d150b0d0203060c070c05030613050c01091409071e0203030901050c070803070807090b0705010f0f 80
    0x1e0b03584a441800d0b000090040500048400c28404083e1741a28005404c1c10075100303c5c94030f0f16000d07080d900000c0d502400c1d007100e049200d4a4134040c01c00e640e0802d101400070500c03503a540015010201c0b020b42740075115a41c0704000340126a007401801e002c0c1408800c4106544844400245280e032083c0c51541081000700e8180440366000c07030f203103402641200c81a9141e490b1141180d00a00c02c0c10340017940030207034404840411086060604500e101004204000414202804503002100400039030541081c00001d111001000250070b0090040880040c21a110000f180c6880c1c4107442c2400d40080b085144401c025042010700b0101c1d41c20310709a44e59920f011049080e44100c5610103100784114000544041d00c51260b401c0309060b14a9100c0c1c46080814002c3c0d01da42c0306a850806079400c010000300300d03805490886490580c401000c0f0325659400d40200e542030b41c050031900c01c00c1804400003914025102c058890303d0300500000802100b1030000c6800c4034011000328103000c0c01d00c03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 172678120 1250 172676870 172676879
    0x1180c050d080f0f04050915040b1002100f020d0c120c050f3a06170a0503030c070303060e040804140a0503030405040b01090e1501090b07321005091204 67
    0x15420764008050700c1e100b03a502c0721010343d01c03500706019030340061f504030440c1d82c104142441644140d040014080e2001c102d048030480501011500181c402e03005684107120061a200f46603000c4406ca4082c048018180410b00c540d900691720408015800100e0303101c401c030a04141c51003104c031500c0079400c00a00d06002c402503000d0318000c510420b01d41c4042c483d148182201c181c503580c10000d1601d101104000040c0b07011030020302c0140070303030400c40410042d412503544001989500d00358015004605540e1200d84005c03455010311402c4040503210000000c1c00654007001c00d015500c0b4414081d11181007210003010308015003503081c41064603030400c211544001c01200d0a5031800e03240070590070498801a600c100f5079504c0304504160040800081c2d600c2c4990003102200240ea5441020b699041c04030b255000c0d201001d40303070201303038847c10448549940340e0b0700c1c0169131046182c24170300103003000c07504000c94183c3c20306100e070300c41080040d40081401490290503071800b00e01d040a081 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 172679370 1250 172678120 172678133
    0x12060515030702030c010501091a03070509040b09031c1e05070905010f020f0a2108010308090d03091d010302011b03080414010e03040902040e011d040b041401180c050d 74
    0x89900c05510200000100340524400d000729404030038540000c0c80f0a50303645020300f004041a1843c08940300380702120f9035052401080c1503040b40c0c1d00070310300f0b040b84d00e6544842d0002c94003c0c05411851104201d062070070348104803880c0c81d06000160000b042203590410b4800304620030300c3c0c5000980390500700035040c2d0300719105901b51a028038141403a85c5c600c01d0240d01c0c050680d4482580b1348907800c00d20007003040c3c0468102d1001c505024203030f032030142c10340d040d142040213000003400400300f032211800a04001c00c124040f58020b181a05059030341d018060614003010000e2100d61000c2d800500c00e5580007580c0501c001140480807802c0d4015880082c410000903000070207902c0c101921600c041d409404c1841c05058603000d03642e559655105182c000d500034820030340a000300c0c000001d10f9030503c0c101011405681c1c24103000c960364035500d910b00c10400030012a0145044911038140c0d0000344900034036003855480036482031442e420540d02a4810b54442e904c121800070000000416 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 172680620 1250 172679370 172679389
    0x30803040f0219030506061807091503020702060313050706050913090606080609031305030105060d121710240c0f05070305010c03021c110a0e0a050d030807120605 72
    0x100038241d04516407440c8002800b034501c0002800d240200f03550b011080c0302c00031a83d01d0142e8401c031745c070510400310740866002000040300c8550100365007040c00c101d254a80c1803550745241c06454014507100c2c9550005045030410b69501c25400c040b00500c0c01007041c108a400c0242c041414500c2c213051030b81c8000b42c10341d80c0c0600d031118490344452210040100b140c0141d0050000442514254642016510f03a40e8005241c04c80d05103459080019107410103105441c05000003a040c030f003400419495602c56032021085c0c82d400c1005a403200508010b01000b02c0380076500f0850030241c000d00e0540451801c1d00119501440c180c003416203020502c0c0c02c16000d8104540c001c807510f080310642e050035801e021f0780340e2002c0c20319400e0681540441e40c3c558010400c5032080008d826070406008038800407118030100840844030100010507030030740241c41001d418180101031800d125281e0021508802034400e040700450190350a10840030f401c83c41c1c131a49400d507004c081109518200019480b40e1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 172681870 1250 172680620 172680623
    0x1b0a05010302220306020a020712050a08032505040503160b090904020d080c0c090702030a0f03050604150902070b0f0411090a02070206071a011205030904020d0605090115030f0603080304 82
    0x10b5000418144070b82030145900b1580310500000c200e01030782ca0500c81d020394840c1d18408018002e6520114110b2200c0803155030b400d030070070b000309030040e542e0703440000c55031010b04008030a0034a00200c0b40180010091105541c401b56500394541c9d1401050615080103400701140c43c07404240306204486180040d1035a0446c11990b10400f5111800071544a60180201401103100001e20b0305041c0c4000030f001d0070744070703081e1041e208540e0b640400321780324040d0421902c00590710702480c1c400c01344650042c5c4d81003a402003002842c1d21900c0031007203e01071668800e40c00150007041c3d400500c032580b07407040d5100400c0380780000149850f40c1c580d0807500c540c4c0c155603c641e041401081c000149075041d9000180e01030200e40c1ea800c0241070806d030405903008109241c1483c0000400c2500202d0202c03828258018006c504000002c070070400a034000818207515581d030340718009219995800e41c07500910141d1100703242c11034003202c001d041d1243c424510110380c0c2801d1040000400c0b120072698001e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 172683120 1250 172681870 172681877
    0x411040605150c0d080919053a08092112090f10180b040206130e16020307120302070311060c091206070207031412040b0c1b0a0501 58
    0x14000a0000c10194105030b07000340c504210803030058042e600034000e82c0d01603402c0310411004000101c44441d400c43d4500b406402a91042000960030984d00d22524071030f04c00d55142c80c62020203034018041c01c01101c034052001a40086400030048261070058445282080310780c0340c03410b0405d5460100004802d4000404903140c2400d0310031074251800070039844404242c2d414400e801590704d8015020011490050118400801019114501034000d225110b0f40800700301342c40310003012000400680e0004010009200d003400030030000300117040c4100e051505400c180c1e020141030442e004050003507510400c002c801007044031000d0300c003440140c54003590b10202450700301e51080000000c12110310400c01401501a40c2c0f0300504583c80007510384c14400403114802c0e0360745103029160000503800c141d00900120b035405c01c0c0001405000c800320349030040058980040350380a58800f14030401d004c00c010625410502c0b01101d00082036100503220401d902c00212000290312819060 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 172684370 1250 172683120 172683143
    0x4030b090705090a0b0103050916180603020907180f060215061908010506030d180b1b070f050a080303161b060911210a0305090d0605071107080f0604 66
    0x26080100298400782c000545040b07010f0508000c04000384c001d9000700b0380800c0c280400107240c1040000c4110312001e0381c43c80200801e103050301c0784c3c0e428941d1103c110303201625258040702580340c09842500030388003a940c0d40e0659940c04156989001300741c005901e6200c182e5010000507900048083c40900e1000e80520240c0380c50300040c0c82282d005040000e0031002c5500041c00e004c040d408641300b020140c040d02c5c1103041c00c040c12100e0200861103a48048100c1c00117020400d40391009c1e003048501d040300c00c4154142c0004140c03904400b6448242c19400e0b602040c845800e100e5086001058404011411401d0072415607008600c82d0403004100700e180b580051180710000019074a464100c0810800c0441d20305113100c3c0310410340c0406004000030048a1410b5048200c0070500d01300f05000341c2256500c660341100c2030740c803040141d540030403814918004510070b031180c140038003040d0315400e41c2a00c55408103401c1c826164485107150f005598040140800403400543c41580500c1c00c200b03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 172685620 1250 172684370 172684381
    0xa020a03050d14180708070b0706050406090f0b010819050303070e130c030e060610050a0e0604170a15150b0904020d020301060c030215130209090f030d0209040501050f0604030b 78
    0x10f04080020600c282074a4060001c50740c030320809000000c6000081e1000385449404056503803000e40709103060384804201d00804510950301080d00240718620200f151042d5442c1c43d103105002e64016a4038120f601c00401c0f07080b50800c0841003150701d0741258481032109480301034880c000102410b052140c141480310040c2d0342c0786940c03e0f00a951a004001c0440352800040041c042c50340c04400500c2098081526898082c90390700c6022142c1d50b509180600d81c240454040400143d001d8106206206c0030410814020200c0240d40c808070007000303016254105103044059944224814238a09480b2014060500c10344009450b0110086642d87c5021004100244111200b1f040254800b10002c40d1103a03000c0780b001d4503030b1f0090f0700726142854501d0b5800b0382d840096034080d0004103420381c42030050509103c03c561040300e003000c0c0c5550754400005d160035603001d190ba08000550002e500810740c0340503c29580500401c0d110000d80c0399801d80451400d1059000282c140070003200001e6 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 172686870 1250 172685620 172685647
    0xf010506070201170c1305060405060307200109030c0308151c0516060908060127090302010b030703062304021c050f01060b040501030f1517030c06010e0f06060a020a0305 75
    0x6105030401603120f4554600009914196000107101540c0c461002e4400030340343c94004149d0301615001051705140da16540f0b425035000b00402c0c01c884003102a0958112401c60a1044142141c0241c50300c255520705850003c1102d031004044116400714088240c9645d2140000d1003415112010100444030260400500e00114041d0301c01c1038101910001c81d28030703400443c08080711031030011204181d0b203400c19041002014040b0b00420440740c510060785480c281c00450f503c60080c000017559032030160100703040003420341041d0341040e219124030010300c601c2d0700c00e071000403402e009807091424240c0c001a09031900e1111440d441108842c0181480014011007040c2c0b8580d600800071281d44034074402050300310788a600d000c680b0309400e0b40001281c9014540b0b5924400903600c0c582030070a010f00c40c0500500314540d0042c4010f11000e24204001c2150ba8040c150002440d4850f01d007910243c4c0300300b4001025540100c4041c0020601690000384c012040d07681814090b480e5603038000d00d032 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 172688120 1250 172686870 172686887
    0xb070f0e011e0f030b0402040b0c0d110307031404030206071109070c05060c070c182301121b08300f03010605071514040605070809031b0309060309030a0908060f010506070201 77
    0x90f80d00901c0041c000030340410500051480d8001101038bd10303001d000c0074041e907086202c6070b150704140d0030030072030382c40060b00c204401c0c00c01d44c01c0040a1810300f9243e40101e4503580041004030f49501421603d9482894429485035101d180c61404c03024040256580e82c1d2074480c0644051602180480d60b101003020003550343e000341074106c0c5a540d501d68070940d090082c02c080c44000b000702c000f0342a0480a40585001541a41c2000a41c0042034481e5500c03203001c84004002c917201c100904102085003079013400240404034013003d52180c0c480c030343c4c03032008843e250400c107070748015000308201c0c07207449240c0f401d03079044419500b0482e440c1c55036401c0070a548230705800c00c10209450490a0301c10b11003c0100c26001d0760003440c0401c96a17440303020558141e00e058848403d140e000b0f00071880d0440ca24003a20514803100401e807820710074040c012a42e0b9070401d03140b400061b000410f170400141c3d8064409001040302c0c200070b28103410a00c2c10740c000e40406008560090ba000590b00e02507901030301c0720 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 172689370 1250 172688120 172688141
    0x90a032004020f0301140a030b071209021002010c080a0212010e040501021603030c180f090207110a03140f0606060301181808030105040608011119020a0b070f0e011e0f03 75
    0x940d50b41d065200f900c0556072003401060011b840319102c404032424100018401e40f64070918011444c1c41e50703c802da4211a6481c80380c4c4205071160701010050b103550042454040c0d183e00045003840003140c0240c020000100840440c0d803041c443c1c110449049200300d81100c525860704031542d00e60b424103901a215844c0340d2056601081850340c1015495800382e07012841d0b40d52001c2a401096600e01c01e4040d042c80348904101c0d01d440113025241c1103900411802e4820080d014000d00b0007008941d28030360b158820707110031a0402ca0403100ba07200b07000c4c00e400684460090b042901d00710000428030301040c0650b09400c000c401401c040c112142c1d004841a11401c00e03030544000c11751030a0a0141d0007400f42c0b9002d2800c2000015040c001401500c3c034401c101202507003040002c280c402002124410820114456002d00c1c602040148540d40c0c05015982c0e140d8210345002e40c0c010b00b0445800d81000c0c100b07e00310f0030800800300a407501d846103803081c0c40c00c0341c1903802500048001d020500300c0d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 172690620 1250 172689370 172689379
    0x19050f070803100801090b06040b01093308070c0308040606030b1003060c14030f0402030a02061902011a0d140c0618040c03090807060c030216030c0b010b090a0320 72
    0xc0d05000d100107070020758410401001280082511440054241c80c000040144007807980408648c0070703c2d00c0e0b00407a00c440d00616000408554078120862101100300d1504120303243d051800d00000c1407003011800420150030b061195090404000b8211480c81001500b04448103000c54104840754011400560304084c4500c8103051141d0480ca04840922003180d41c58a0403144001960003079031618004403944a10501316a160300410000307010041049034580203581c002401a038401c006000115084803102071484c1e624030001c0d00716000c04c00301c1485880e0440b5445070980c0c03070b907031884401a40f00c416008440d4080c0e910b64542000c10343c2c03960740554040f450310b61203586540383d2001d10384119824046419002016000c40e9131990000e0704249040001c00301280503034000764030740c034003500d0b00521380300d4020030b40940808442c40031000100c50044000900100f1025507014100700c41c022841c008080c800645505168403004041c06a501041c100c4804400f200b00000b020182 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 172691870 1250 172690620 172690627
    0x191e051c050f090d03060b040501120207020d0302071802030411011d091e0a06080303010501110a080301030609050c1819060b04080706110d140309010f09110a0509040819050f 77
    0x700b0303000c442c242c102c6101e181442604242004d1510901800040310801402146024100401120400721045030f00c1741e0385400704051001626190030b1001c0880c0290701a10040e0b0801c120100d20b0341031041c89200003401441448046440c3e20035000250b5400d003820001d0710b41d9100c41c04401030240c40d405503c40400400c000d5280c1046211051840d8074030020645035a410340d00c130301214070354011540a0343c030a100501655008940e085440724601c41200c500e4001551440102d43c070903041102c4c580d44541c40802081020086455400c20480711a0b200e9244482c6041c203000000300b80070440c184580c83c000300c1c1c031781c07907400000644440d030740315940d503611960702c10354031131840c455440041c1c00704100d80d148840220b000c500b2034034a540d401c04440103016015000b80c0025140c902c16550301d070001c030b54440c118480c02d4042481507200d03048080005081107131250880c5e210ba8002e011f00e1040000195040044401080700c0c0c0005e43c0074007041e0308003100d9500503035803404116400007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 172693120 1250 172691870 172691881
    0x1c020d1d030601170f0105041205070206130602011512020f0405130b090a020117010b120406020f0c010f060b1303020d080717040503011d060703050c0d02040b191e051c05 75
    0x600e004540d800f6103004485034451701040700c1e03003202d00c1110090b000c40508a10303514a02d10690051101d54001030065080000380e1044400d40e105561080c0c0240c0c0d5500b42516421701c5d015042c10060011605500600740150007041c021740c07825500328440e40d0340d540003d040c2611200784500e06030301310744840d00d2890100c0007a607407801410b0040c3d002c074002c00e00d139003230131001050f0725410fa51a0380740ea2070a14440c00c40d40081d600c4043e1080b2140d40c2c0900500f0000c070301038805030050003407840c0003003200d2a10800550448255400840c61101c080042c80c04170300060800c0d40440c0c2e4192030f03580c15501700e400d22400318003034000010300c0b4103034001405441904020181080d00d40441c000c2250354a100342941100d07440d4005000340c0e400c494009000640a6404150b02c262951812031400304548180c1049a0060300b0102e43d00303134003240c1a1701001c0c20090308840c040607424010f40205807000ca2020b0740c16618062400c118002034045035100e4941c0300c100e00c4018614091200b403c18 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 172694370 1250 172693120 172693139
    0x1a0712060b030a050603060403120906090204090b0a050c360a0605041703070209180705130c030b030a1a070909020414100206061c030c0b01171c020d1d030601 70
    0x3500c08048003130400000c1021480c0101300a4000ca81c142c0380c07980b81a40501058000d050380c1a41515115a60a0408003684490046c614950b10581b114102460b002070010100c5001401003000741d40c0a108064040103018840501d443d28400b04940d40c400c40420800d410680701da071030f6081b221902000440035002800340c4180c910404088140710361211050ba584e0081120180d4003806120100300e07e6a0340c01030480c1584040415038044c40d44981c04104a181c10f2844500115660209402c2403541441040401c21080340074041d1080551070b46940d8819608190102c03640d020302080c0b9075405003840b080100a01c00d8150341300c0740d540142e4511111040308050094220078007511a0340d00c00701e810ba110b10b100800c811000c5c01001d038002c1c038824030342000300c0501450380b0000e004903050b141c0082c020710522421b0407444041d0381d69a4107244241c0d8100e200c0c8801e1041c0b051030150042030214440d0001d140c0f4050400c49d0f140c01700014050615043d805018100001c28104078 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 172695620 1250 172694370 172694377
    0x10c061e0615030e120d0f0e0606131104090e03120405010f061409010e0a11030c09030d080c04030b0a110d090501150e010b03060105130e160504031a0712060b 70
    0x2a0007507400030554010150f068400c1d00c110700c0f0103a08241603d1a18151310005400080c45450001900c094121850000c40e0010020321400e07034052130810203285048110f0040c01c076140442886610070300c0c40d080b6528040c42c01103681041c1c0350b01c00507000304002c1054070400d00c0c810480d803009007081d04029009000c20078001c0015800d1010200f451050120301e00c0042d80c1c0a00a001142c0c0b810003440c80041004d44411049502c428403150060118005980191b000e4100107682e16940801c061070111002000302c14021180108400b005421060301c044982000302c0c60400c2d5642860040100301d0180303620856140840c0340b040030210b84d8030520f41e05100742c3c02080150340d42141c2c02c10300301c16407080c0e0304058940401803100401000103107400c84010b050007820020015203100c5080703180d400c58441c0300711300b00c104607030140c000c105010810b5090821740d00d802d05540b20b002c00d9848407060300301010402d40c0450071140c810742846008a04001d020840d194989012030400da0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 172696870 1250 172695620 172695629
    0x1c0b01180506010806042a05040e060a08030a0804020301110705210301050d060906230405060f2e030204020a0306260a0b041a0c04030b070f0e010c061e06 68
    0x922800d0319026080148142400381c141616545003a82e680c03010080a016070f01d542c0c000c2c079000d22002071462014540039001c00f00050311030944941c180703400c07400010802800c2600c1417208403420050400003004030744014940703181020440d070711400400c0c094002c068100d40340c0703c2c3c00103051061000c0031690382082201d145840c90326880044480300b140c0002e01030b4644c440f0161030700d07a000588a502481807076214100101c0d24501c41811010308000011090030a004000f041004010040c002550311a8100301d00d80d00e9810b100302d00e2021029040c002d00d103008240d14141207060b00c180c0d2400e000b107500800030b55540c58401401006000144204241005003903214140444a17010085802c00300a00501c1c02200300d480b241380c0e003900904181e950b00c144441c060300171101405024859805441c1d8140da5a181d4603143e100340e44000c0c040810024015801104290700400c2e010344c100c000d18115071004c0d054100080207290100f60404840024058003201c1d11a6400600869 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 172698120 1250 172696870 172696889
    0x6040608131e03050306041a010909021e131806060c020609041d1b01050c06070f11071203080708090717030d090f03080603160504020a03090203011a12030a0c060504021c0b01 77
    0x300c498410910240b0b1236242d1b09010030742d0000c0921405240307134003800c240e0710074859095182084c0d50140b41594080c0058000040d2000e005001c1c0c0202c42542000010020f802000302d41c0c94504001c04a44407504001c0c45020006016550b44c0e0380c0e500700600500e41a408807000701c7c0314650442d9190390482e52a03d1017141e4a080c49899802039007510b19101448010305829984c1d0901140d0700a20b60121000b4440300c400b403d0b56154003041101c000d00440c02a0411000107814080c20382e000040419007005800000c00582190200f002000c6502070540216504030043d4000d017075005480020500e1458600c024050024180300c1410340c600a854041090b1102001d041c1c07905095034400e490f4100074081006181000d5004050b4128a490001005a0316a00083c2562a40758400070705080015980d9620300c1c01290888401891000851501a0440d00034020105072140a050380d5a540300003415512020005203404c0c012841e0b1104104c030b03d04d03003482528400c1c054020f0a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 172699370 1250 172698120 172698131
    0x927090f010c02030f0d060308030106030507020714030c01080702120f0711190608100506070803090c0f0f0d0606030f0507080d030c08061908030406050a020c06040608131e0305030604 81
    0x303488041c824440e000c41a580a1480c1c884000d452910340c1c1e21814482c0f80f00ca640701d0001000c14040c0d0040e6018042a94000c00c1034107180000038a495503070b4000c5202d40e1160101ca0301143c7e03000403a90320015007800d008456030f8440364168148000e18014101e0306000203140d99012103034000500a80744508010303c0842d0324107062081403000c0c4850354408042410b010322405015040d081e40c0500d0558036403081603110310100d081500051170846da15213001c811312005a505000c000706002c4280c0d1031f1821404900300086071101d69050440c0125082c0a481060140940213071000e980c01111200c0426070034035009941e040c41d4450310300c0d1406070071170001d901d91090150076506401c590380c020503030b20740c0c10400905c07a040c1100e10032121031400002a501c5404e002a00c01000e00c3d8560644420f2084400b90514600002003803260200f04800d2001e1500903403c80d030030040c0d030480f0700c0d0209040c1c40c1200d001000a41e0522172141d1501d5100c040640c00b00c001e5105110907203080c080c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 172700620 1250 172699370 172699393
    0x1a010c05120d020a02070902040b070f05010209030a1a0f09030d0c18150206010f03020607060c02030d0c0e0111060405061501170c0a14030f0411010221030906010e07050906092709 79
    0x228003e60084403900312b0100b26510128801c0d2916884203406000014502007001c00000e240c80000481100c460454400984403000ca400701c1c1a4007203d00c400302d550915046140075100c0c0b250000c41108560340e51810340c8580d01c0f807080c00000070081001c41e04010303200c160340311460320340b40c4c50301c001481600c0000c140508050900011242d000d0700c4a81444101c1d07590101400400080c03504500c0103001041c1c80c8111401280401452500e0307407070a800f40c0d803000501d846c80c01b0b0904060f81d4007030428080050700005a40d5400401403085403054140100100c030368501d0b0300703009030b5400c0546040c48400c510b000001c103011006500c41c1603004024494a1b5030b00c1c082260500281c224101c0000c012440d400000b0a001d4014030580d56101444022101d8051035540c5000c0300c1c120100401c18440d20403c5480e01601111111501c1458103510050083c85490352250288801251642c03040d00d6006002e80034107454103038071440032038a141c1070624040c1141d48500301d200d1060b031090b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 172701870 1250 172700620 172700639
    0x28020a05030c01020c01150b0f0f0d09060e010c0c0206160305090a0b03090601120503030708041b0834150504090c030218010e0a06110a02181008011a010c05120d020a0207 75
    0x41148d15060130701e800c00c40e00c0e81c4a0b0f0b50540041010240400c030070440303644000c000c0e2145d28400383c80744100207152190903443c142142c0300403a800c8188240d9012500150742d40a060b62250440440c2c44c2400c080c036803900b01c80178001c070140c03075822008410380407414450310005944282564821520070341e0f6104401d40c03148411501c041c00c140c104001080c1c500e4400d150b040d80c414001c1031007060350200001c0400c144042c0c0d40c0300c0007454000b84118003040d1415083c01800d1000e00d00886441600d040055280740710502c241c442000c29003803e4041c0c1b40c0640b00742c0d0300900741000104007540240201602030b600c20b20362002c80100d0109032064030360003180391759244c41d0040d00e003402c5241000015030300900070104a01051080800e000d0050755110949242c40e4000c02d13103480103080c00ea0120003000890340000e00d003641400701e2500d90341524a0b00c1400054240307811094828039042140c02c102c00404c5900c0c00e00f0780010240100002c80e001090011840e0307080b01c1103140d840c40b054 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 172703120 1250 172701870 172701911
    0x1c140d050304320712020112060518090a02040c0c0b060a030503031501110715080f060904200a060e19120809060c01050703050105041128020a05030c01020c01 70
    0x144140c03121102c945418015050100000c5614000060f40700e48142c40540303041c0d500c0d80080d02c07102001000b80110350b4408d04803001c001e480f1900b441440d0600002a030003062491090141454000002e80020f10801c076049045402800130031109901080003004000f05100a607a08510140442c803a8189146a10100c80d0020042c50554440340c1901c20700c011946030403410800d00d06d88000c0c0d1100c052104200600d44c000320003208140300706c409800f408004000751000359940e010040c054860880c460703031050b030140c01e00c0e1905102c100043d44087d064004544c000f07001c10340128000c2d8100300902c4030008102c0304e401410000441d004003020031406186800452480d0541c0015410005070840c3d0ba0000c160500f000000548182112021508180000c0d19a40100244e06161083e1506800343c0c120003454030310300254a441802c01000e050340b42c0c1482404c035038001c0e0b100784400d82c102540201079a550b00b100c050098083c2d0011059400294649480f0516500030100384 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 172704370 1250 172703120 172703123
    0x10e03030c0a03080c0408031803010b19030305030703090503030f0403030e0c1e04092f013605031b030105010501020708070303031e060603091407120b061c140d050304 74
    0x301040b00c42c036a8110fa10b5074010b004c5c000211018400829001028000361420420030421541c094060004042c01d40b0302103401c0a0195107146d601d241c41c0c03c00d044242c4141c07505418450b50b203880e61141200101880c060184ca640004014448030b80c42849909000e107000b5902401980034aa0403642ca900440b4105644891315004103010b403081840720310f81000009100064013080c60f140d504d00c1d4040010090400004007c16400c40d031000c20150b110484280780981180420030741405090308201401d10039a030440e0703540040202c01d00c0404005e0701000c0c0681d01d0045142d9090001c00c000f96402e14420350901c800815554030015050040b82c104000820b00e03503155440a400030b01902c840360b42c0b007160308224800650b50a000c1d400c000d10703c030390700051a0506402c00d8640c0080c1c420304042c0c0360304100030030400c40706900104c000998100322003080985a01c400144800031405024100001600b0f01d0020f00c85400915101c003610882941d898640c41c405c111446e01c0100c60 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 172705620 1250 172704370 172704373
    0x2160806161d0918010203090f100c050d18140a020109120b0106050c19030f0f0305060112020c0703020d0b010e010603050105152b020414010201020c0304030f0821010302010e03030c 80
    0x2140d6005240200f0f203503411203c04c40307680354641018840340b82a6482226a0341a42d4401c04005211203404c100c40a2010000c10f0300301b140480c0034900505601c5282c0d0005175403078503000200100c030322805e050880d903544140c0346010401d111804540750780301c0100036800700ba140d02000803090f000d05a01000303660302000e85007445e82803034010b9525400c040c2041c00144100c100c082503003c907510050154500980300d4402c1c4000100d030052000e000360010404060405c01402020703604603850501b589000c010151319040c00410a51030a180313640040d42c00030642420105000800b6005810b0340c1c84000200a103a032240025015070301c083c0302e601d401201581000c00700d140000085d00300e407150010300031504c4940038400f207000b9102c0c2c0f108140090b800603003008025044140c085950200f80000e60070112605140d580b41d00441c4405080b00c0003540407001000660001c9605e000d0a0b51094100d076007a03070308060040b0800340012130200b0180d09202d03e251a000080d603400051040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 172706870 1250 172705620 172705667
    0x307050d08071e0507030213020c060c0a0507060501121101050a08010e0417190e01030c080a050c130b09010e04060e0a0b01020c030a03050d23160216080616 69
    0x680d400c0070703940241826034410b01d140e01000e4111980d200b8100381e050298000b4184181103004000c510303401401c010410a00c100b04030307410030001103215a44074401e2040139444200c0080140c8036845801001400145004000704264600c0308001926070301032489482c46c84015401502c3c00c0c402d041c00303500412005401040032214030200558494800d40711b80580400205480001e17400455841e01001c0c040000b01289c194800c06001c4461001d03e8180450160424042e01d501009010820341710b84840004011006c0b5204072a0380c100f460034900314850b075035103c2140311780181019500099005040d440c40d0718041c0900415903840003855042501c0d120583d000504258a4403415402400c0c00d928075640c4c244510156103000380c40e219600d050007001c82003112103179140da101038900600d03413001c000150742880c0c1c0e1040210703021405507900e01500340c0c601480c0801c100107040b642600401d020a000c150180208030340d14080c00f078400905c40a4a4041c44500641844040071 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 172708120 1250 172706870 172706873
    0x201050f0a06210312050c070b0609150909010207020904031707052b0e030a0306081002190f03140709090b0109032609190f060507020a06080c0d0903080105010207050307050d 77
    0x10a40b40c3c0045110703040020410344224160300694104942c0b038400840041030a07000d00441c03400055000304201c0c1c4041182c82d05000c1540c06a000211590207668007400241494a003581100c0030341d03800400000c3d51385000c0c13074024401e000c011300050300941c070b40010403445030150054400440d080c40b4200d80c4007088036103818105c99080b0403042415160a200100d0400034030003050803414582c0c000c140281030400c8949000a00d4825110151040240d0307021384074100a104410521807078095000d0380407900c21400780060240d8080107822900902c041d0f40e8101c808041128000441442459034920040d1540d038018440a0407406919054003882c500f54102140000300242180f41024030000208a02c01100724201000e803645803014448803600c2e0070f410006080e6441c180d464108154045551405188030f8002402025008228030644540c281c42519408a5003081640e24500300140039610070b1140d64054001d05901081c0c0d81800300300403064071005400c070420710b01d08c1d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 172709370 1250 172708120 172708169
    0x50a030f03020a0b100f060504080607181a0a17040201080105040c09081c0e0306071b11030a030c060507020d17180304030507091d0d0c11030d0201050f0a06 69
    0x30038104030218016a0211000110b4000700d05003d00040010420024240384078010b036504141c2001c814444140801c00c42d60b0030000c2d02036440880f902c1e0100000d91100485c100031714040d003110543c2e07002c04607000a040c0d050000303010784040f5652104100a1074445404441e6000d950190001d2150401072050b4101904010118007081c0303010005c40d5581d0074550300384842156034007108880100f000009031303482251000c0300a421400340c0741c141021440580b030282c625404a60140454941c0401d10800418440440c500074003640d00c01002440c1c002c011950441c1e040303488070318243c08982c00b14800035800c05c1d4100c064a0303c400030880f9420403036006100500c0c417106580d840d031070b6941841060002c0c20003148124001c081031402c00c4001f00c19114444403a00c401d620304255281180000078102c0036070705490504888054190501c0c034000802d9159243d0944900c00192850b240c1c1540034a2040030081020701550300e510380040d054442030302c00c001030003210070074140729840c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 172710620 1250 172709370 172709393
    0x2130e090a0314210402040e2b030f021803011b020c01183204090c06110a061d0c060f071b0e0c0c10090302030406030b040221010510050301050a03 65
    0x15440c000d606080d05040c0013824046446240d0388a070320010180300c2182010702900d0348243c6108003414015000c19031070901080ea40c2100071030210224805c943c1300b4000d43c4500c58200308501c044d590350102c05140c41d03124480c921481c1c0250b18100c0d81d5012a0940c3c014640382e110654080c0c40b001c50900011a8100316850380b013064146100700000f41c40348680d40d14000e088104002d411035490010b90710b002c040521441c140079505140c062000100000c0302d0000f511007d0805084410328001c0c000d00d0640200c00051660340b1741a4034055540ca0360309055100f0f18040201c2c0c210400080030301c01940204803003140148402e00061000600c02044035994491201c05801410b030342d0031115008034010781c0c00341c0d81e00000248040354040c05020700700d203103182504180704400703442d9002980c0744190b2007500704042d500c0320004041c3d03440d0740444402105015101250350560760609105078028800c00b88200d88030f4004008040c000d4060724100c1d03038010440c0d9040d40c40c40d2243c900206 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 172711870 1250 172710620 172710647
    0x6062310080c09040219020f06010905070f210e1b030102090a0b0a0c0b04060b010807020609060103080a030e1f0c140a030209040f0507030501050a080f0705040b041103090102130e090a03 82
    0x82e000e0003030001b0116001d0744c005402030079038020050305030381020305400d140041e0400002c0380e0400b001c1101d02500b0814108140d4040e2901d0310109403504100210b803418840110a500e0600080030390000e030010303180a05283e400802200c030b03443ca00805080340301f0701c01820740205089804202540d0540060300d01c259207400d04101c0003201d170352800c62114040380c0071506c90359102810340155a20400d800e500084500081405040c0410a03540e2004148001841e440001409050581c0720303800440c00410158200c1c1e01c2c407034410100b02682e07503031124002e4800e4a8010030000b807603c40c4039200f85101e5560201444c0070b050500c00c80196201d410042c0d006603d40680c02100382d124822244181381540d8001100d5040c0b40401c941c6040702c0d40008410b07030010440503103010002c05c00004869044400040900c00c200c04a00500707840080701d8a82c00001c010003142000c1034008060500381030f403458010b00d48800155000010a4802461640c4210080780000f0700508140607002c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 172713120 1250 172711870 172711879
    0x90e070506090d150f0f060b0909040302160603051602030906071506050604090b04050106050a05040509060d020d0302030307180e0106051303120518030105090c090408040306062310080c09 83
    0x4400d40e02c99442c0b0728803903207a5068031a17841c203400600c29018851215210340c0182e09001891911441074030390700130b10a03050720540c0540c0106081500801110350000c01c11020810155900c010203001414101d4030025000f01003d21031042c0345c070110468402c40c03070007040c060a04004d9101c03000741e9120840e184d031802e540c841c4c1c00b01d000d40c0c0e10740c0600001c1c9414200460245030103014001520010b034400b1081c08018014032140c1038000081e034050b96400e4404203000c0d5990000a0720080c1c640001941100300900e401d0141540840214030451280d110f010081d98801d07180382074030929200781404064048014080503228100038101e408108459103241603c0e903d91907500c0b0f1007030300301d40040b0300005076102600350340304184019100d08500800c030f1450701080c169260524003400341d11600781d01c000681004215402c0d0303000366030824410404592540200c480419240c00d55501d0b89641c4c1c1049a880e1a14a88108040856654881158403048414041c5412014500342d10 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 172714370 1250 172713120 172713139
    0xc040c170a0b060f0a1e1407051207030908190803011505091305010f0e1909021201060909231f0902060f03010e090313140d050a0b040309090e07050609 67
    0x85030380f0700002c0c0000310203c01c01960384d0255010098018003650722107408607000c030801d074808650001107084822038410401503440d030161030300d141410703052000c020440c540481c4c010145a0b2000401003035031490801c4820644080c0c40119842c07801d044014541441000184020203040a000c0818400d42c10110300302218072001440202018003005205582c0310f00400c407206981c0c10460007420f010300420b14508100c0304c032081302c0c00312051140e02c0305e85a10300f0390219180c1d40406140360007020000c110041d26200e0000241c0040c0c1002d03148011080701c0c00c0c134040c40080f0080350181091300203054003004002110b112210850300801c4c526a41c030085409a00d0300c000030801e200b8084542607481d03041100f807482116000d170200c80c2d13940c801c1c811a400f00b45d58001030303030a0b40e0300704450510200c48580000c201c042c0720300c4020024003c1c28000400c00c03804006c21070086203e515165001ca484e83d0042d07040740c42140c0300203196403100e1f00402280c1090b00041207030300005404401c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 172715620 1250 172714370 172714391
    0xf080a0818040b2e03110d150f120303050a05090a03030e0c03100509070803090603040b060402040b04060c0201020c040b010f2f061501080c040302060313060501170c040c170a 77
    0x50711003c2d2001c1d081c440d44001d031131009450390a038400c6401c884074141002503180082c500c20190151a1850380400d64900c1c9804022000e94072600041c402203072902140c030385498040d0b80030001c24000301d002c41e0604c1c011803d411250b00a151045100100411015000303413800c40190100c100c0ea0f40300ea00034801d894140d40c506104c58404051500b6000c180d500745031403c58030f400b032070380d004507000c1d0400d00c01c080c0340742e03640300440c1d40084e00608038000544420001800910950b80901c4051030700080000c8c5040d0441c0200c1c5000c2e000342c00307841c1c0f071824030300620068072600c1c40903500280384900d8403148a030046115400c1180d4080e04e84911010390300703104900b0787d1080c40c809003560090742003004100310030310f04d80080300c800e00e0004c0e03403410b0401e8417500c54011804000e01c2800048000b03030722221110380007040711350011014401c03965500844241c2070a1640c0201c20350240003c503000c9801c20780100c900c810241d41d80c8945040c0301000c0308412550160404075500d440f21207145 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 172716870 1250 172715620 172715629
    0x506041109330403020306180d1409040903210618090303020c0105011d07090f0e0a090c1509050609030604060c0c0b090705010f1d0103020c0a020a0e010f080a0818040b 74
    0xd1040740180040d03030f5480c207500425182c2940144590001c140d40c01920a20400210303201446004030f05259074800c8156404030f07000c0c099090741135003081c500b045034024140c2c03104178a0845a800034040d2540e50f15103070707600f0a40d006800b500c8400340b030080500d0705028071a8481e0300d0f5540179181c01400d282c41a203066094a0003030340062050f5510864440000c098080c0c1550840341c035040280c402481c111340300e001c3e00060710615004080350340c00180719a403160040f151141c1e100240000e1180c440346c100c2c80b0001a00a840001201c501010500d41090030842d8100d1f04010010b02980c0c6d034940e20800a4000c00512404000703111042500051700380710700c14000d0540380090302400d403d00303000400c004d0800d00018100014040390122504107004c562681000038139001d6952241303000e80b54500314420000035001601c0c2d5000040012908000768180c0b02c41403005070302540d45848103540c4011031000604a0302d4204840c00310440c000040d55817000000c2d0000c6104d000910019 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 172718120 1250 172716870 172716949
    0x8090a060f050103020307210f030909150e06030705010813081b0309040506040c0f080408040f060203090301150602030d15031e060c03060b0a08090106170a060506041109 75
    0x10000d0b00c03100188110b24041c030041018000e80b100c3c0d124280b124203c2d8030021412001c001d044a50307002000003d0604c50361510000d415603140a02c100c5140318a404002d045a1140342041310700034000c506140b40200d04001214416035650600c2c0d01c030703024250031002105a04a0311400100400c0c59492941c3e010f411000400101031a15505d050341440203a900061030139101e185401d070b00501c02900000019144082c80c0303020202995289804040c0b486650007824210706c05c0071002424a60000007000c5d405001da000307110884031401d00100d081070301d005041c0981c00a0050034a144026402481c0e84c81c6000d1200548680d08c0d166071901d146c0f84605c05400030701d043d110400384502030290f62124070341c42c542040f00342d1030842c601440d0b004486c07501c410007080b40c01090116500f500b2180c00341c075054145d4001c14104000305550380000004c11103a0a0411001a0003450180f11703000920038429015840d2044c08070401202c585405001c5e1207021611120a076070840d4507040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 172719370 1250 172718120 172718141
    0x31008010c0c061104050d0809011413031106030c03070c050a08030106050307031415012607050301051003020418111615061403122a070914070c0308090a06 69
    0x81801142da942040030513103d400440000c0740300f04000800054689203031490308990840728207900d401a50b00101ca030000441002295031300301103a510500e10441d42041c040381d03c903826100c401e40c024001c0c40603030b001c1100d403496485010300c006556580a00308000c02d440c89441070343c0243d0440d03668000250002e82215000920210811034055090b2080d4051500e09045d4100326241419080d0040300c072030b200e400e041090f00d8185581070740c08006c600303405402c1001241d15a140c01080103040e50070900c0783e02d2242d45270030f0520b180c0f107000e442290156510a440047c110342d01500d1400544090086c07081710580c1006010084910341c01c61a600754840c10400c001c80c00341450b00300554295811142c20101c00e1100d0841d01d0350000341c012801d40414500645900342c021a4082d014000c40c0030203404200c2019080c50f80c0d402084405c180c07050842e007006440b030402103249c2d210f803045940a001c42d80014041c0041f034041c605490f0300c01142c40440c2c80602440d0381d214281c4502e1183c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 172720620 1250 172719370 172719377
    0xc03060e030d0605041404061e020c06071b050601051519110d030b0306060d0507050a151706090601120b0a260a080f030402010903081c0b03070614031008010c 70
    0x1e00b100c815440c1c0c01008000e0000311000d0100c40f1111803c0c1100034400b40c8000c1c1401d540b03000d0710340c1ca4245007194406603064400119110f4103001305003600c03a9404c450700c500040f10310400c1c600d00c4d07131404070101007280c00c28000d0010f0b80c2400c060001e15403682d0f506004882081c0000e030600e41d103c56a50000b01096951142c400d05107080c0b030f5162403e03225001040c582401c0d58805daa880009110307070700c00001c4480c19664903180c200f080c200328840d0003e0350865240300c80810040300c40c110030214039016555851280408094201d10b6803020b9035160f5110100c0000701d51950310a0349603c640b840e904200265041d00c02002901c05259035201e5a041080284441000216070304000e0310003400702c01030700103941c5a030b5070702c1c03000e100c0c00700400d007420030120208055900c506903420145521620b41c03590340c440040154040c00c0355901000c6028200307000102c1605000c502d1008942c0b1396164450b004c1d045408a0905400080c4580f00f200d021400009a1410034015001480c82c1500d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 172721870 1250 172720620 172720627
    0x10303030c090b190e0f0405041b08010c0c0b04060e0f0706031a0904020d110316091b0806040905010902030a0803040302100c050f0702030a0f080c0f0604050a020405040c03060e03 79
    0x7800604140c1d403c3d07201c4001e040b0103100f0864091185a08900000c1613842c01400d8448414001140741c00d002c001560030130b2038001000f040103e80301d81c0480c103107500400e24002c6562004a60f003a82c1491800381c000074400c00c2d0030800201d03c4070050790030a100f845c0200d003420144a0080c6403a100d002d01052541c80500200450383d05442070024500424444009181200380860445140130301700901034040c0704220014044481c1d003071800d142c0d00800342c1c5d071556a20703520074403160007a0040c02070941c50010a000c8600708140403c986035515203c80e0a00d43d83c3c1c0b82048002c001e02402903c3c80d54a40ca17001005031340070302c000d100d40d500c0340c5001a00c9080504000349030510481d0942d603c0ba01c0d01045440360b0750850140c1b101c25601c40c66841c2e030744c1001d102007802c0c20860f0000078001d118000640f420404440c1c040c2203290214801ca5038924a054111581c4030426140500f00b6000f40c0690000b60915411281d1700030b0184002941940ea0703640c4400032644456802c00a40d000403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 172723120 1250 172721870 172721891
    0xf0905100c020f1e0a0501020c031c0216060b0d080c03032d010909060204080f0f0120190c02060c0607030605090103021e0a0506040603021c060b0304060209030c0901030303 76
    0x18407034401c11103035030310062011101480741140d803004100c9014403028520131030b80d14003807020004ea0b44403c0d1320100a64941c400340200c10b94035000b200380081c00362240200d444034801c0f9807095a0380000c440f13011002000041c0c031404000c00c0c1c100c4030550040b00c40081440810100c100170127600020000655892a0080c806001070907600303480c811481452054041182d686040c042c1541c5003690002507280192030f05000a00c240c1e441881b0500071410800c0640d0b0300494000c2880c440e2400a200f5442e2181d03d41c01c04045014544c00740f25002e20083d40004d40088810a40548505004041d000c06400040c0203800484044140da4400401c00c09196803501852000b040d098445e046607504690000e03080700700c204482070720400c039850120620703a11007640c3c030010f24001c4c180c560b88640740d000050183d80319040d0902c3c010b4502a801c95041b100303200708822140449425410354a4541e500d0380607601c481c601541c03512441031142100e5840404050003107210352000202c1003030a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 172724370 1250 172723120 172723153
    0x1506010e0d0b1e010308040b0c1908090301050709052115010b0705210a030203040203070e011701110a0e010c050c0a090605040c080705190c0c1401080c0a020712060f0905 75
    0xc100e142000c0300b08800405c0012903410580d000ea45c07880c240790380c440a440f003039a443d00032124010340042d100403c540c4180840e42e0003d200341c6030701394024840e590b11154246c0b070351410341c400e15802101e040700c940800043c4c40031540e11a40c40f0029140a00d5401c845e034032044a0a03008241101d5000916000b084030803c41d80300001400641032044e40125000b848040c0580c0c0500d000741900000081c00b15074003442160042c01c040454000596100ca10800c0008450b0080418a61900074140000068142601e004c0300b1030341d440343e0541011100454419404401c1100c103842014a07010b1555140418480600340a40c00081c18a290204220540301100c030102e0078070410300d0600c040698031904980c0307414001101030002e000c0440045603464401e0b003010300350100c5514003041c00344054418071190102641c40c10300c0c60b02e60254000c0207104250201002d64021101086129010400800c4990154400140f42d030003d071103040030384183e428100c4113a041840c40b404200301 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 172725620 1250 172724370 172724401
    0x10c030c0908150c07140a0308180109020f0d03050c0714150703140f04120b060405090619050a02091903020306150a0b03041e030e10050a021506010e0d0b 68
    0x2035400c010501d10f18680304000b10390001920454441c040007501506011640051040d00e40101007180e80d03515050400801100c0151100001180e5040205c420b1250502031910225001054102d2b59680c007000c00101d02c821103003c0303040c02030502101040c240c0a0044100078020800f0411a5202c450104900e1401c00c00c0c9500300c00d84140054004280d00080300080c401d041c0b0043c5584800f0b214140030305010795808080800710039049071007040a00440c09000c0e880594060100303841d0700f0f0b03d050f00e40d0001c0f2440c820001150184030021245038202d10380041800c44e00516200441000c110050700380c88151204015882040085040070049941c0c028403c40f4829801c62007040062a00e0b00d06110720800d024001c0302190a001c2905501044404080340c4a06a10304900d406001c1070f045060700313403188030001c0d02e1074030040c0240112901040d40d44d0160100400c0303141705881900c40548424104064100c0c24a0151a44030b001070342c00d070140102c1003c2d0710708404500305404 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 172726870 1250 172725620 172725629
    0x51e0d0f1103030a090201030b1302071208010e0708040309030b0708150f01021f0f0e0d030c031503020409030903020406090e061605030708190f0e01050603010608120a020708010c030c09 82
    0x1804a400103880d40000c41070f240c2140c1c0810000c2941116400101c014200d142413203a4401800c0a452880a120b0385c001e2005500c150f421100d4480162410f40d803804c1d00744501100313000002d00007103046110360201070380f062090400b03200054581e210100741101c21551200400d486409110800400a80001c803600040701d04180c80c450410000791641038600000e2501c1081e888881040f0000c0e40180b00319042054040042d1100b00300c0c0b141d5940182078000b004a450036440d885510301c240124140441d07020202128549503609110003046001010741c01c10032440804001a03030b6601900005001404000c1002c40a98503003608140e0080c003180c8090880140c0345c1c0310190400152030b0b00c100203081c645d005545014102d0040d107440c8640f400c1889c0782010520b0350881543c08112100c0b180002000030340c2c0c038901414200c0c1c1140c01038140302ea202410031405494003030b0092010401c184180ca03645035030f5080e41820b41d80300c410b071080883c2c1ca030340782c403948d071a8482d500d8401807 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 172728120 1250 172726870 172726877
    0x1211060a111b0304090e01020712031404111f050c0c03031306080714040324090f080c010b0a030b010302030d1e350a0e0309011704051e0d0f 62
    0x90350890a039076424880c411101518099000020703401c107200f402075400402d900701041c0180800090194002c1d030168508480840481000381061480380c030030042c1d02c202601c200301703140e1a65240c5a0109660b48400f6500810b80b04035a40700917580c1325181003030006506c40a498050740c4c40c1460a050600a15030b000307074002c1c032100000180b01d81c050710403200c00e07040240040c0c45450b030894004042914003181c0d0200043c000041240003d400e90b1040d000a00800341d9a4150b0000c40c26100e4456019140e411000c42c40c1b800f20794135000071300e5043d010782c00020f0503505010220b01c02890fa80e1050781c0e80e02d02c180c01001541800c1c44030704400c40b8180340450741d11071004a50104111944402801c11104000021400c00d07990243c071480c00740050b80000707d1141e140c01603110501202c004040c41e080c18004600010f000040e58480e107016102e0803556001c01c086002c0c02c1c0401042513030244110038481e0b00301ca02108120134814031505c05054450144000904882101c06140082 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 172729370 1250 172728120 172728131
    0x150604050903070f29010f03060f0209010512100512100c02010b060d0b0310050408030603070b13090f0204050d080408011505091306090c08100e0a02010905120a1211060a 75
    0x113600c21250044299210007900340445040c40518420b80da8000402900040380c0d0001c2007400c0c1000085048034800c000c14130000580c9150340c800d81c0039850303050340030400906c02d00340e40c0340040c910f4070f43c070120383c001080200d030355100069100c5108000303000c49504840c0d40b507035510b202c0c4e001d000e00c2100340740001d0160100d0320010543c1845403d481070841540c2c1c03980310369a558240701b03170051001d11000c2070160b42080d00b00002c40e03038400d85009104e4420084000f8800d0718040540e400324a010071110307000b41c034003a4408054421341d00c462140301d60030000410b641d0790303011003c0320321406061500e40351030a0100490845850a81241605410301400c00580e0398403400143d21050080d10301107108094070300072020700804a0010424290050040b43c182400140749040c20170804c2c050003894540900c1c20344900241710064000b035880b000520041c02c0641c2c00d10605e4421364200c4020113440d0301d0f812100c8240304201c80001d4064481801e0540040203074940050114004014 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 172730620 1250 172729370 172729373
    0x1021b0120040302060a110a03050306010e09041709120307121b0507050d0303020c150702070f0e070818010f0603020120070302040b120105090d081602060a0b0402040815060405090307 81
    0x745401940720003031054000065241c40c1c00c2c4260803c0d03c02040d1841202c23800d4845203070152003a0821a010307400110f64030308520181c03070404540c1d4002c5401c981074030360344c55030000d1254403a0320140b00340d50000030040005640080c100020802d0a0050b0038004a01c51540300041c29800c044010201442411912001090002c201c3c1c100302c5030b045440c212552030078503081e0060b004000130b0030395601440000b041504d80c0450300e5449444a0b501707a54000391907031443d070721383d21250244001310600360000480d5903002d494510381180c1300b40f484101010318451102e007503600481580c0000c0351113004c00c004550704100ca00f0b90045640d0b00c070190300c02210070b0031540c445251001903c00e0b6280ea0303030b210483c1c50700d00d401c03904200303074038024002881c200c951030741e40308100ca0540e00014000c03030004a070b1040042905520140e03580c083c2c04c09840c0c02498801610354211000d40c041c0d030030000096010410481109605402000360005180450810040300c100502c0035110350020800b0780e0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 172731870 1250 172730620 172730681
    0x51e0f011d1b0d09080d06060f02010e06060d02030a0506090705031b030d080c0412060920010207030b09010f141005150a0c050c03010507021606030b0d02040f0e01021b01 75
    0x304030000380420340b6440e503044044003030072080601500c07085c0c000a05007002c415603000402135410b5074540702d40401021008078202c4504001d100401c3c0c22032800f0803018501444030483c81070005084071101021500d400d0306003481a509005203a121050820040c00c0500c603008180c03095619504455080801003038460302e4810004080080c880001044c07207080f00165000380090141c0e0003108a0fa9250020080541c600c05445658007054180c00280c60050b05c4150424180d015000283c80c654a400d01910094030744000e954a070001c210045001d0302c0b43d507111501040c001149410100c01c200c0005445400c50f0303004180310f003400100c03002401c040f281c040b000c0d45820ba124200d18100917013409a268a120f42c035501300802d000045034009001c1000a14403442000758560756075082d81100c50501d0050b8120010207400c40140c03900e640185862551110040b030038200c0399822500320317030080c0b4249100810304800088158800d00c1150f070016485030300300390200500000c69 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 172733120 1250 172731870 172731901
    0x1006090518060111010c0c0201020105060f0d080d0e0a1a060108010b0a1404030b01080c1806030606011407050616030c1809020f12240108060904020103051e0f011d 72
    0x500e07141000d004a42d25901c2020802c2c0d00e40d1181000b0041071802d020010080c2d40c022906a0056007440007003409880c00380b40e1410150030007081c030000c895480d80d4072405600f0034038107e044195101400da440349030910141405603c5a01900301803450620898000c5070043c00290410410310018803803503190030125150b140301e504141d0380a10880c02048564032950300000d01030702000000003044140018010b040340001c544882000c1420b6924a00420007160344a5040d400340c4007095155000d6040900182001d4003030f40c1ca0240d940c0c841c18a091025a07001c1100b820a400482c101545440383c0d009903540c1d450080c03000c100482280c1700304030b100c1c060704d44204e500080da40c80401c0c104040381c4034641814041601c030300c0d000d600074500801e00c0d2024101080030901c640c0f06580305080c2d05108001c0141078a500740c03544d8004500400000701881072004058607621000760303d400b2158411140e00007110781642c100010180c0c4058003007840c4005640301c1e82489000050100b91 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 172734370 1250 172733120 172733149
    0xf07030e060f0903070203030d020406021207110603191b0201050709050a1e0807061805221e0207050604020406080c0102060a02070809040501120b0106050306010e13200310060905 79
    0x14842515418100c3c1d0442c804d4120082d814400041c90b102c904c001c540241007210f032590240e915880d0601007502d0a0721031000002c02d01e41c00c40d00c1c11b1070180380000180d600310640d03c682c900c1024494100100325a403504901081d045180040b40c0441e5090080716444074442c82e022220324030b0030713010401110460040e201c0404440303180c1c1403201e451101d6040282035100456624554440b40540684003500b50440508101c080205241c1021740310304c10101c0d26480c030a81450308281c09103000f09810744880d8550611140092080700e21750025100082c0a80060807075410710348104000c8403110303404070440c1d030400214003960342c2e00800c3c1c0c20f0f13101c40f07418000b59607180c082c5012801c600c41c400480358010720b024000300740340c0070850f00804010304c0b6030424611a605c03000c0540d040d000490302c9500017141c0c40340203501803d0265200044074002c0d44041400c19102400d6414a5204445910039100200800070503026108211004100904007050f80506003404154508040e05d103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 172735620 1250 172734370 172734391
    0xe090d2a02060f0a26040317060d1b0612060605030105060c03120106111b03060112060204031a04200f090726010602070504062105030409140f07030e06 67
    0x540035512600b0840e0b02181d03c031001d0a640b12504080548950700f01d401c401075619020fa039a010072403401c0140d5008582640b03d03080c2540d8040c81882c1140001030103c2d810845124a05002a07034400d003030f01000d250411404401401e0540051070303d2400f124001d45241000301c204800ca0300501102e055070002d40c4c01c11740c0e5110000040d031451240500380c40e04950303075000000f840d81d804240400c15403100b800f542c00f00000350000403003280b090310020340d140d0480801005a0754080c144000d120303204000140c03d240d41c03501ca00c60864100b4501d645810380b8001004104990f403280011000b81461002001168580c0460060340c031a4242c507011306a41804034010f00c1c040c60f00b1040c40c001e8090280800a0074400e00844140e0a200b94405842007550203d203601d4580614030640e2560700c0074120120802500031007546060f0800e9845000401c400700b400f440034015207024030032102c01c00b84981004910036203a054001c102c8800c240c9004465002c2c000c000c680150400c218070b1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 172736870 1250 172735620 172735697
    0x14060408090f0102161406070803010801050412031b08280b040606050f040603090213020315010e1203030a0c090e0108010b03100b090a050604290906011b0b0c04050a0e090d 76
    0x1c0c0400c07c0340c41500005040c40c400440001109c40e01504840e01c514800c80b04a409901c0c407402c142d040e0b40300504460a00d40744086821162403040303820541c88040001c25040c400301980e1085550007108098616542d00e910400c00d85040034007501001f0005450840e20780345034800c180380305002c1c038050b0400f02361320f40b0301c070000395036540c04010040c04c1100001c55680c106201d450704242c80d06480c4902203000104800b4680c03500309485205500c0f0035025600d107030340e40e9803d40000c040941d040014443d01c060081099094002e400f07018040f0300000040c060302c080101403404040c400d5020000d810181d4410307480d241c2002c16508500320b00703400329181d2030fa800020301a0002403040030b58001a07800c1100240c43c48070701e114880b441135824580340d031114801112101d1042081210001a0200800015102c0740d0700640c03024140503410304190311180010000266548840d00588070745082c07100780701042c001100508420300b04424101d4110500c0310807134882101540320780c020315 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 172738120 1250 172736870 172736909
    0x9060f080406020702060a05031e090d050903161503050a0b01050f090102010b040c180801020a350a0e1911100507020603040b0f070509031914060408090f010216 71
    0x350169080300d50300400b42601c5811111004160389c000300c0c0e43c540110122201d80200051070b580a44c0a41000c6c4080d0032001e8010005540c140e101400041e018402d500541c2a4094002c100304040c240000340140d0344240a038005058900141c039440c00140340c502180003583c4c221003141c0f40100751400b100c0d101c40e203260040c0d006020b0000c500d50402e08100c440d0310000d91108480c50803400103109424074548400e0100d0803405149a02c4000c90462090301801501e034800146e00b40f0582d10403162041c03100000c0d04a0204151900e55110391901e20803651000d0034031102d10401418103840007a84095156660503001003814603000d062014946025144617104450380c1c00e0300030b0f04441d541c0c1400e02d42052203241c1252003500c1c40030741c0710204140034031030b00485051280040c000c02d0035080c648100d903040c0e608244210307440c1c020004204000481848aa849103018007441900c03403240f841030240000ca00c40c903441c1150854000380c0b100907202d89149e401e42c2c0c0b00300100d4000c03003d00c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 172739370 1250 172738120 172738133
    0x10501210e0709050106030e0f07140d05010f02030a051e0403030e031e0403020301110a0503010b13030209130b150a09050c070c03121d0619020316030306050a0609060f0804 76
    0x41140718955000d2000040380031a001e412990403101160380c01c014030307051021039645902000031809001d411104041100c45544000740300d028000030402d07805400380d5a00c2d00e00f114070f107441690030540c010041000d071800f240718165001c55001e02d000310031031a07001100e04125005000030203041d40d8406100420000308190f440807070322211549006202c074041a80707a500103202c101d10960a2003000c0310314a07a020261003070234a035034917601e08690034419110f1030781c0c006501c84c42500c0d400c100000090303030f104151140520400040042e00c00d8003401c01d0f8486400080100170250a0101d841d076090321861340000807034229403000103032505e8102070503040d0300c100c441c003600c940c80c810004002c1c04200c03200f0b084000200c0d00c880c503000c686554200c00020900503010b60020342881024528000306a0000d590103040c41500d02d4140c9050826000030300c510002d80010380e0301d41d020b0015003080020200034110724209207001500c0e2130002002c5200504048081101101c04581001704 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 172740620 1250 172739370 172739381
    0x60e1c020d03030f061707030b0a020405010203190201110d2406120f110705030c0f0a02060711010e06030a140901110313030c020604030b161d010e1c0303021b0601050121 75
    0x982801c05207410386e0f0703002c09030340d150761780c0c08252407013104c1002180303000e4071900c211000c58034186c004c1c60a01c0c480c541e01e41d42c440715044084056540705d0f091050303054520001401e016280c41030020f149800e01d14400084807410b0144024000e0a48042c01042d400800300e00300c424640f41e005c24080a0359001401805030a03140f10544040881d01d0700800c14048080c0c11451860400c982600e140788501c0c950b100e040d104003a4201400b0810040480d0031603040f201da4032411b040c035090b43d00140c07004c2038040c0e000300e40080410380e41c0c541d80f603040a128031216410411039402803042c0700a0170b403844450700c0041d11804c0c0c01e0007140e402000301030055465030b103031940040880da11550780b41002c2c40d248108484c13040f051400041e490594500500305030301c904000c0390f041180801d40030015134000400521080d4450040145108018010032030041d07414441c1d80c01585406030032000510802d0115148820b94100e040140840e036032299000c0c0d118005009480d4600024007000e200904 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 172741870 1250 172740620 172740629
    0x80f0c12030906070815060406031a031f061d0c0306130c03060603050c030702070b0c07080304090c02070614090f040209030a210203130504020c010e030301060e1c020d03030f06 78
    0xd01004120061801081e0300b8401d8055031a1107580d565141c0c070700741d0800d50b13116200741e06c00030500003031080d98401c0e40003000d40d50000201440e00c00022002924084409243e03c00da825000e55a4028a20901503c1d0080c00c044203012203685c1d640480c1005488002c1070816200320200004501e035441028401c50011410001c002c0ba000103c001000307000d2034000c80340403d0420010031000e05164044a20540c060350103004407034207000602c3c49a6106c1d14082c0100d2240c518089407144080c00208003c00c8070b01d1001900350107103407020341004102d9120380184580842c0322019502d15004072541a4011100a211607500c41d0002e030080c024002440c0d0980301d50340711a800c1200b0040d10101c3e0001059030140c0d0701c084d1503c1240d0f2407040c5403d1102d851400b100070801414250058042c514140c1d00100f051342c01458082c0c65500240c0c01100003414240051046081c43e007891105640305141ca2000c00740d103500403032078801c80c01d00018201550380c5003d8804070310302e5000b41e0161 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 172743120 1250 172741870 172741903
    0x712021602060f040312090806060901030807020f1f032009031009150203130213020a050403020405060307120308010e01050102161518082b0c0f0c0e0c04060f020a080f0c 75
    0x104000800180403020500522301d107403040001184007403800300700c1c050403030307911440302da04d0501903900340b10301e5002c3c0402554000d030520200b1250109aa56413100b0b0138236550380003880718800c400001303902400c8215061078020402203550f01d030302d0110f0040c007031400c01400030a0400c000d25024265900c142c9207051074520101c14402c861500f40040e9404e076000b1a100803503400020715005c124460b2964186c0403500800040005003803070340085520180007170030b82e0040c5a5680c900078210121060450018041e400188800c0e0303541076a00c0d000d401c0a100070046251034040d94001d10b038490060040b200040c900d24038403644070b00001da111002c010202c090191b070701e1842e03540d298242801900d0a903454007040c013051102c0071201c61014016a1000003030590794a460f040921118400e5031800811340020540350f22200c040380c080c42080001503550b51501c40014505092b440340c072002c54204107040c40110f1013000688409912403580303035035607040400c0440d2800440d200800b010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 172744370 1250 172743120 172743143
    0x909032a0105070e01080a0b010509130605062a030403020d08222705090c040c020a0b070207051201090c0b0c070503010510050f0a0f06080a020405180712021602060f0403 75
    0x141ca5026420b0442c000c421b8840d0382e0551a2020034034140c5001c00f9031680040ca0a1108480600d1301940b140070329a40e40c4000107006840700b001c86c03c41d600030304100064003c0d291406509003c04859405400e208002850802d4119800614540304900000d00504004100002c01c02d080062a0710540d05800c58071203410740c0d400640040200080c00240d02d461880340d15080f02c01c030b034001c030761090300d04502605017007011400b040b00420a10140350114810045504001000315041074002c11050700203001191030034082040c016000d80c030000301641000b9404001070198002d440689807880300e21911820a040307524034018441e4413042c2d056007000d00344010405580782150a48005940f80c514044003038043c82210702c0d0b54072540d85050076030b040400001d4864605c160f01300e000c42001500c1c05949400280107408041d20210300c4010a0701032010081c0c01001310091444e4480c815410614040e0000d45102442d54000e03009200c001785040b20718410004817006140c0c404202d242 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 172745620 1250 172744370 172744381
    0x903090d2301050703051f05130207080c0a0c170a060b190b13051801120c030c030303020306030f0706140d0e06010b0c0709110d24080c040b0909032a0105 68
    0xa00004c0c0d134404003103454040424101c0d400d030002c00030104ca0030b07110040d81601d4039081c80041d81c011032a003a0120382c00e0120314000b90f0024014200311408100809801c5100e040901807a01c140e8401030f9000e41400c040c000d4200045402240184c103c0c1d00007862203011004609080101152001c03841f13a0807202188510a190161a04a40044402c5d68072078940d818803824652160001c8038000750400108034441308101018006d622540c01c0c03003401503481e0348102440483d50806c8000c26000300800409040c10888801c068a109008003900c40c68075401900700007040609092000c80090a10b0300c2c1c4446410075401d80351035800321500e030b40c0e44a005103010f4114030001c981c54041c184c80015001c83d64000c1c0801c00a2100c03074689080c9130700018000030600d140a02444914803460368201d400c640714604003d080010190400b607543c0004c000c1101c46080400f4800d101039014842c0c2010000203444500200014100c3c000c241140c410380c1e091448180700980358240010801c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 172746870 1250 172745620 172745623
    0x903080c0a0302070e1017070302040207060501090c03093503090a0209090604050c100309050703051b031b0f0105040f0b070201090b0316050a050702040504060608060903030903090d23 81
    0x1c0d460303000c0d0342a82d80e640d44603030081c19010360a4500c2003021103500c2c018015803038842c8801000030b440c40200c42d9203a070740380d001c41c0503a0404541510260792714401044103a01502810304030750154603040100210700c0c0e4500c110841010307035a2138542d14080d1000420814000300c032240c204110900354032882d0190026990700c0f2881c208a000d6100280481c520280020324180556031280251a04000c410140300c3d0300c1c02d2544451040503100c0f180140800d0b02440b2120140d1f0149014020411081000c0d64401e18140211030003548400e035030342c80c40c140e220b00828110108495511074804001d0040350140a10781060800100900d0b00103400d101a2000300138440c13003038842006140e9510b444100d81e01040303030102c00e02d00d00141d00d00c815505c207500812000da0f803400c2c1541001259000b1400b102d0089408840741c559a08003070110007001c0000076400b6100300d0003589140b0f48410307095168051002002e000702808192002000f0550311911a13662044030343c101c1800050348505d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 172748120 1250 172746870 172746883
    0xe071403010909030f02300d0e150601090b07080a050f04270612020f060c07180b06030106090e060a030b0a0507030b040b03031c0212090a060c020312010b03070903080c 74
    0x4a0100d0103445c0c040902d00e0001c1144503c441d84003440b185450000440c08a00300b10760071403000510001c0100c0d14071150a4451340002a41007001041c0e0041d01442c1903103d02c0024104a042c824403000800501c00680308981c1019400003046407034003254582603038180240303044607a54000100700401e05070703190405201c55500d10100246011410114401241d40c14001e082070800058407070800350400f541190310031a00a4074052501c01d000310001e0800c4420b03000400e0180d0a0518008051003d0240f100d00010496500740b40d94034001d800f0300300e810a0b2007400700e0018140005541680c41101480007103030803082c20a56840c226101d14000d180440309200442e207001422200b506003841451043c00c0090000c5103003041c1c00801014a004503010301c01e05903000c0000d804046034980d105409040614024034110046d8a480e0b816507070095041c0c021940188007002e10f0001041d0610f0441c1c0c0c10301e200c5696610f0302d00d0300f1a0b84600302e8102901400001034801c0c80c6e500c0000d10b0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 172749370 1250 172748120 172748123
    0x91917041505340b1b03130201020601050a060e010f05130608040219030305090d060b040606020c030d08071209020d02040c09150207081b011e050a0e090601090e071403010909 77
    0x40d54a220942e41d89a0f140c004080d00d0b01c2c0304110038912000003140d002e2490340010040407469040200901d071610294000c40d41c40480c4407030364480c8002c40d6010050180507000c00c071601c0c42918141070005010000c0184070b00e04100c0388000d000b4605008800329003000c100340d0f800001c80760300d072040a801810190f41c200c1c000c0c0890282c0c0012007020030000c1c029030b070340740c3d0b5214900355000003007024807000317081b090fa0059500d8002407659a2948110030080c00550003500000d00050704041c10140c1c2c800008080c026940b041154aa6100c0107140c3d41c44072144000540d24035a00100300d8604030703140000c0d0480e01d49646000119080103401c0103c550002c2c0381000009140000c90304e0303107020711618001e0361005068203510041010038130034a0106242405240c50344010100216042010f0b035808074a00050300024154401062101c40405454000d240c0c1070080c0003c01c5400180b28642c2a201c101700440c004902c52855544030b00b10b400b606d0b54495031107104000092a00400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 172750620 1250 172749370 172749397
    0xd031707030c0905040b0109090b1207080a0203120c2107061508010b040b0a09020d1b0e01090f030302060a0e0c0607050f150c070809010905040e01090209091917041505 74
    0x400086074617041c002d080f401c0328180e44182c0d00b5807404401c100603290583c04280e10140124002380c01f04010001403006103180c000401015030383c0d0040c9400c0170003215160718056410040c2c0c804e07130310001402042582c841c022030b046403100804401032500403103c004003003a04205042d198035100700ca4100a41e0241ca000304540480303841040102c60700032480c5500a46507841c2000010300d02c1c0d015000c440c64041011800d8030a240b420010142d001d0418408a80451960305240d41d120050780050048103088001060039520041d60700d81b0000d0900c0c0b00c80351603031000440d03030106000c1c1d07003050f80000d4205520380046250598940c03d04d40441d0f80644248080443c10403010001d80b030240c000f80300102d1078500130343ca40e00540c0d8090a6000d06000c21001d000403562200c1c81000f25170341240000054010303440c4100a01781d40003a0200314664807480c010584a121501c5510813180e110710041c040c078041003c400107500882d40910301d14000950070041c41a04480108000401c040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 172751870 1250 172750620 172750637
    0x604030f02060108191509030906030b090106090510090305071412010501051023030f01150905090a09030215010608040b0f0c0a0309080d1a03070b090306060d031707030c 75
    0x40c0c00300c0e5518403d00c1130300056440060003050070300d00390300550440e5003d00d000582d6865120412000c3c1c54100e00100c00241e0000c00400c94030341c0c035220345002400100c412641d40d516104005042007132500805214606d607004c8441040d0041d4009001964803005858140c0c0d561030b106084155681060760041004079402c50315924180b24150581d8801440000d4031000d00700f084400c4000044104084034020450a410714075140103148a100d0b04ca200d54295130414404042c2034401250315030601541d4bc609100a50b1481440da41c4a040c5410000e15440700781000c0b450100c1c44010007a0702c03070083c4008a01540d000343c0c014441c2d40120500e0b4580d0700c1c0d261002015420840d02403181050500c003107800c0c5c1d4841e801030744105008135030113030a04004107600b004585044001d4170701f018040c0c4035826030f400c0601840c801801c0f42c0302d681d404c01e6880004241c5450700109402d1050801e00901d008140c0174201150345c0200500c1001c0c024600103034040c0060101441c614049075400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 172753120 1250 172751870 172751897
    0xb0d081b0a12050c150f070329041104050d050102071b08100f0f020d0e06060f18091504050a1109041a0c090d031e05120411010e060c060403 62
    0x81e0400401c2c0d100040c0031809921460864180c1c201d0031038081e19000d241a14826a070702401c4080c050f503525911103485041400018085605d904840e0341c90101c21054500050180c5101003080311081e00c000c44c0704444612003425030320807608002d1b0300540701c190b26828004154080c1036000c0c410884a0032414031014801184c80e01d07882009850303400024016441c10311070704a500902102c840c040f07442a00c03090b90100341d030010f055540180d540c40540b06840b2000300a456084802602c516240245040219070a01c080381031203640a00881e0200d01606c40030011211845021103250400f81001c0c036085441d4095000196a414126407585c1a60310300590141d0060f64485007460b0b4400c4500c0b0f0003000368100a2528140000621080c00c26454002481010300d10aa0f0303950341d0b0580c2c2c5281140c01c40341052441007004001e011400c42882e54214040e0010b4201c2000301c1d0f0034101c41c0040364800c1160704000d412046c04203003c0c21814000513a540514405d031111a50741e03196 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 172754370 1250 172753120 172753123
    0xf06060e0603030d0905100603050f0610050a1a040302180103120f120c090312050d0f0c090b07050c04090b090c0f011b030e0a080c0102070902090a0302060d0b0d081b 73
    0x1c0e00c810354950400c2084001c900d00315407140107103520800584a045210101d2581100c19503030040ea07403034014107118550440140601c65009903034401c01d0b00058200307000b0408001075030081001b03001c600e00440b20a6228102500c00441d40100201e410100506042420030002c4c4000c40c5d05004460402803424002d41400d40c20101650718564990522503a00c009415801205800d2240c05000800452041844415011140c1d200c4e155190245140a01196006c901d41c0d100b403443e02002840182d4010300745d0b42150030400009403151400e040c030a0504142101c9294441e01c0d0506c4d15003041882c01126200b903c07070500b601c010744c0c030711b03018040d4040398582e60b940060403258002c03410841403a40d2642841c044c0c0b40c000708850301e107804915444500d1b00194013651101c4d202580940c2d04010101c003401094206604000d9643c0101e40a8007060000901c19800802c440088074080e520072107410380020b010082e140b04500b040c00c1d041e4842c0c0c407003142100c0300c100c040180e00750 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 172755620 1250 172754370 172754399
    0xf09120503070f0f06050a0209030c040608030405090c0d0515040b06210901060801020304150b060708190c1e1203021204390e07090e0a0b03030d090f0606 68
    0x4005018519205450b0f40341101210000402c45001407081011000f1844900c42c461041b555085d005070345100c02d808144c50500c1e0854114420703414410103110b584c20102c141c80403900c0543d60010691a06d8103a01000d0050b10031147c3c0d0149444208662400410150890102c1c20340d03081100014400a0048911030703911195105400c0c6440042c4c00181c0d10800c55010340114000500c1c652220b040509a9005840070390303003840340c224507910b070240074481e008503408100d44107803400c0c4c40355841d26a18010782c280620800b061303858038101240903450007a0010741c0300342c03000007401f031071251480007442c85001031b2601e8903100391602c1294020310032604030740c2d0f0002c40d1800c03690352039903015002c071060f101912261101d0000e80c03c11b803090181032891201960038500d0004e080c011044a6500e0003000a000c00c0082c100402c0f508410015003a0407071003824010480c07000e143d0110340ba6205102110700f01c0e501e800e10010a0255480690b003ca0344500414058142d942501002406 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 172756870 1250 172755620 172755623
    0x20103150509070f051c140606040e070c050c0a090c11011104030f020f060705150619150c14010617011109190b03070905040b0904031d0a03060c0f0912 67
    0xa41e0081a559806080c8841d10490135282c96480e0400c01102a082d035241c0401a00c030242c0c071811941c100c1c800010501d580f06009494a038240b07460082c841c000d00602400380818001e07a00d9603c0b09014050110031b800400103450a403409965504030303001000700140450010b0200702e8144482d0506000702c4080d0641060f000b824103055031a50848080100d0702281d0100564070f40c03104030f0705c5003006044c40c42d002d103000e4100b180755200c07902c03035006008045500c5942c01c8846a0b200c00440d142c1c010907140f03440d9030385000c20004803041c0c60010404030003404c003011030b141070b10070041e05401080603500c20b07081d450140036442c04030600740c640e0f250541d011903009002d00c03c220f080c046c9202c45000310303250311055136681e2031004129952064580200203240e020041c00541418011040103640583e600c40680c64542c0740240440d003e05100c2c150b0300c55001c61310030280d889001c5940503642220040041c100000d00c050001444c4200040c0842d22284000030001c518842c41084203 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 172758120 1250 172756870 172756879
    0x90601080106031a09040804180519050705270f0306010b0d0e1c0201060302210601030b072109031407080a0c0c120b0f060d0507170a050d08040201031505 68
    0x9900b405001d40c0070700381c40c2c0e000980c00e2040304040400355551a201d2070185000d61110f0b9078981c10100c0c1a180080c4207940740102508100038401c001048513903281d070780c141c107d9000807107403681c800407141d40c891000b910341c508121501c80708011035945030045c03550304c080310007168282d503a1092540341c40c000d115032260300c4018003844403024031a0b0030180d822030804040d50001880848107040c04102445070b100180c0d514101402141001007038041c018100c0c00c01080380284103076180d44d80b0401400010120311413400850010b42c0035601c0c04030000900c1c83d444045e19004104c6000034061028142c00042016202c10710304a4101c00304c411554001101c14580301e1665020740e041d40707a1100c1100c8500f522040051503042c191241ca0485c0d1141280c00d403e400e02c40b1003075250f020060280c5204070700840013000001d80c002060b02c1182c10350503605242c1840d1681c16410030317458110107001c1740a0150087d01940e400300016101314400d0300c08104103004241400d1601c4194015030703801 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 172759370 1250 172758120 172758137
    0x90201020c040b0a0305030c0607030c0c11010f03060902070b0412080c030a050402190303110d090605220515070303231f0b2208010c0525021f020c090601 68
    0x81c0d050070340244105640107891615269030701c0d601c81c0d140d944107940301010742d0440f60510510075454040c00b81d40034228034000788402c5164072200110b043d2800300d64180700c02d003001d4071b043c20b00030340100008100d403210442d2035412a003031104031540115821102e00c408a0b41b01070300c2c54000d030900c1e4014594000e101d821079a070a4801c000800001d482664850b5040705041e213412400c01100000e1882a601d0740e03007080b074041d141c0780f074116203403102014840c515400384a480e03407010566102591500d9140c5508902c000f05040c0007099802c20343e0403d9a0681030300011b2040c0c8018070313640d07100740e40c00c014a001407003500100007a8100d0410107124860003003043c04d03003d501448045050b0360380101049540700c0c000a5140e026075040e4100c2104541d2001d0b4440310740c60314030300a09800000340480c00c4002401400c1c4e1180d10144420450401c005071801404092521100e85c0e000e0710044081043c5104520a08150f8844600500c110a20307a03400d401d140e8440c501030f29041e1101c148 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 172760620 1250 172759370 172759393
    0xc05041a010e03150402090a020c120406020114070f030c05090307030305040515030103050a030f020f1c0f03090b13051c08010905090c090a020913060b04030b091b10090e0f01050a050409020102 85
    0xc011000c0c00599072207802b0301000e803d101040c801c100961085280e070a80c0c651410074060309480000c0c07503003a1084002800c000203203421604426000b4400c8c40c000641081040c2c003a20b05000d4551040d1f0544a4a1400f004050f0003400400555504543c811100303003800d00c45400030701c02400300a08a40001d030048000a010700500041d06032a401640c0411800624031440d09503081040c124006002807505490360b0000205104841a0718041c0a00f105d107880342201100c019204100081d44900000c050200900c100011381400c40e2585401070903a40300184062401c0c050205464500400300301c045600080712200184054010000ca9460310318100081d042040d00c5a0021381c50340e500c51261103580b14a1f400f0f40600e0002c5a116030a5007405030625100400c0a0b80c0c43e84607008651000c10380203900c01034803004445c00d11007aa0003540482c1d0b027201c6944801d4090345108107115038155000d1045068440903264000072607554410001034540030003010303015800c01040b004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 172761870 1250 172760620 172760629
    0xf030e01050702060c06070806030a02210304050607030f0201050106051801030f180f05011b021507021509012a090e060f0a0b0a0e030111040902070c05041a010e03150402 75
    0x4010000506100d410000c50f900400d10359480840300a400b0f0b0003080030800381c3c0c0d4108400c1034110300b00364000c00415285601103529142020001014060403072004009a0000c200300c0300584806400152255860714000d050068030994040141d4244000460803a100b1020740d024118002e50300c0b407a00d00c0c0e10b401135004051007100400002d0311080070083e0030340a071060b10b400621640d841d400c400040e080c050700b10303440b142068004110204500845543c00180f50180c5038030302c2c041c1045500d640300142d10b402d5441c0c52141c854130148041100600c410b61005d000b80110000309849008250340c00300e0040c41c0d00d030101c000314103001c40c00d00c092119815442c4c7d102c8405001441804582400140721703009560000c0c0c60240700043c1000921341c0f0291980503250180c0003808040415410305485008602408010b25400310703a0342d0500c0509590a001000068402c110110485813092191000c0024260109411030320f0300110341000181c17100180810840c42145403610760821 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 172763120 1250 172761870 172761887
    0x6040b150a08010c0513170a03080a09050d0e030d11190302100f0207031202120408030a090605071206080312010b1605150105040501120506040305030934120f03 71
    0x154000c40704000119407070500340703e004905009030310f6260700e404c1c4038a0780581121107600141090100d1503080c500640c00010001c440766890b0510003c0750750b45c805400300808d0410005440d500c501a10102c502d60002490100c1017029010307554800c11030181951421025958041243e00c141140003d04c0384050210320024464030541c0e8542e04070360280c505689044482800742c640c0091800100358011000c084034070b420f000d09604181e07802d00070404d04280280080e009090000c0003c8c140c04142e40903041c41c5601000400071030411210041125180c001400074003494614040f460309000400c1d52840c442d89400b11055a080801343d403299042038500e46c00040c0c1c02c10034600000d8090181039102011003000d03042641c90801080244c60060b03100e4181282d0f202004030101e04040b85065000b5058201607075a600d404107107074680044401084c1d10400d61090b4660079885002c5c50741c034020004401c0300083d60300d449501e000e08a120b00000c0101801c02100400240680b810 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 172764370 1250 172763120 172763161
    0x513060b0f04020408060106111c0309061107060501090e1614030f100c09050907050a08090c040c020c031c0801060c061103150907020c0a05040f06030f1a0906040b 72
    0x1c01c80c0284088020800360f8200e900000303000c3d000800180015075105200c0c0002c0d50303a10006100d030104800f50f0b4401a018214910308040d20391020f401409250340005e00c2c940d03c41c2c0c0d42c150356007070541810801400c9c28001c8103802401e05005801401e8000341c10039141e4043d4013007070303201ca00e000c24040d8200450030400c0d4050107110307046d001c0e0f00c005000c100703d41b50200c800861100450407006001164070381115104081030010b00108560000c107444400409081407000ca0f1104110f0510700606484105e03400f904042800040c15400302d0402c1e181c075003e8040382c0119050003045040c070302862100d00f00060903031004200440c40b03000050070746030042d4000121038107010120340d480c0d0b0044980c104015034074056680141000082650301a0891002d40000d503450f80000d41090704a10076a40324a403600310240c04c044e07181c0e0140008550003d0540507a01003840c07c0e104504580170b00949580441c00020001000810071510440c2d01081c2168542e9800c502050b804800104 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 172765620 1250 172764370 172764379
    0x405100e1306033f03021c050106020a1e0b16030b04110304020306070905030714030c0306011707090605060a051809100f061d0d1a0103060204090c030513060b 70
    0x240c0d2803100c90300ca1403014502074242000c0700003a01901c03c2180040389804194402180c0482204e88050700c181070400c90140390161707840e0400b50101a1410700c60321900c80c80352611000044561f0005041480c06103e040000c90b1140c0c2c01c10780030382e003041d0701070040c0035440340d480000c181c0000d21380c00d048017078400c3c100001c0145403000454201c50751414a20007500c0001700748420740c81d003044500d40c041c8580c0342440c003e50030300c00425140d607110f05c03e642c031515088481e501c05035003c6c080000c0741300000c0c00305c61840d80d642404690000c1c00500000e41c6010f10240480c801c902c90240400b90754015180d11b00c6e120200008545543c17040c0c030401010640000510036690303444036401d00540d402d0301c078404001d091020001a6a01d541c0c016030901110303a008401d42c852120114010b10401c40c0c00300031512050400c401d0310326006203600e04040001c80040204a00c0d58060000c0d00c070018401c0141c0d0640100580071100d041c3d9401e40b1058000d8020390008406070091100082c002c1c2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 172766870 1250 172765620 172765639
    0x4050c04030b0103081b06070c021017240603010e070c0816050f06100602070b03180d02100c030c230f07030c111503070503100b040315060504020405100e 68
    0x11104212080c0030b030400c03511031400054550011400040a101b00313194000a000d0340d0030011070282807080b05840c001e0040c4a035032031f41d03130300d080c0510b040050800c1e680a191107286414540120001c0c005030030400920b2901c42200403034203201041e45e040c1d8134a030060035065195040152940040d801045841289c100602c1000b0b45148000990540c4a8001005020300007031006003440e40c02004c14030b03055042201088500e6000030070504550703807d0079480d039a80720098406292080c20503000182c0c4030300548603540c1a80007c071101c1400e014001040401e500e244200c0541d4400010382001456030040c880d403651503420851200c1c1513066480c6d00c0d02e4400b6601c1200c582001000340c0204a1140800c0e0030f0000700ca101c009001c02c1225030300c074840d5150050315824000908100f04004010001030342d030300200440c0e0005030980f0408180c4560303603450b203d08a00c00101c00c0b0b00c078840c2000c1e00000c03141014000e40f4280e130b0004001c15084640d1440480b4410745000083e03034040c4860 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 172768120 1250 172766870 172766873
    0x906010611070b07060c03110f070f0204140106020d0807080708060f030c0405100e0a0626010603020310021c060303020c040e0a0b0103061b0c03080103030c020d021915050c060604050c0403 83
    0x11004102442c171900300424100c4014030041c04583e02002605130b000c4082101309024201c01c412200300316403118161070013206500100b401401360302800415818154004103085070002078051000b0700c0b81d42ea144270341d607070b041040b038010806460002c0070461010104060740751009503400120710241c00c070b030704098034000040c0c2038520666056860352681074003404884c00e0783d10030561110484105200b1140303420305414111528825000c0c070300350015541000d00c002034000800554008080380c8134020680d540d04002e500c9448440c2010b400398101200704031007402410200e0350950040d00c0c801c0c5182c0144005040c03140d001000d40c5c000c14014500144010356024081c5002d12000985500a20f03828016818440300740d8003070203195002030700080d82c040c10b900c0c1902e46c145000d003212040c80c4089202504c04d550025405007a540041c0d01e42107503400203400316a0620504c003000141d5010940c0d9500c101e102c0d22206802040010b03015003070580055400545145600789025074a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 172769370 1250 172768120 172768139
    0x81c0906050d09120918050408120615040b0a030605030a051e01020c0601170c0d0c090b010c0209130516030503032e030311070e01080a15021308060f0708090601061107 74
    0x24044200205500d00700074800c44418841004006c640c110003000300d41405c1e2614001401505081041c0c650f810000480c26100c000c80002d0403d0404903150300c40da10f8404200b460703004580707a600064580040003405203000034000d40b000d80c001c8050001f11200c0d030b0070a007024041d0306400740c046d9020001030109110403c10b1a00821000000c20303195540400014105400304030111b200e1101541c032400800c000100c00400c1314000c10780042d00440600c0180c0d043c2c0345114000c1c2d03000d20300c44100960600c80c1842d08842d0b9105109462202100c0849130060f2035942c0000b8005a00c103200144041c11b40100e481609442d0340106814074028a10041d00320351550011400104446204880241c00b00000c1010748800d0710030f00304070360408400c0350b82c507242c10101420702503658010000a1a9650446581c9a041201200880e49640d00d1996a050589150303280d400f4842c0015040c0303100712040d0340a00b44e10405043d945c1d1901740121091038021550900da03005050000803450380 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 172770620 1250 172769370 172769393
    0x8040c12050303010305070b040602100b1c0b1e01060c060e0109082206081506130f090204080f0c010504060c03020c0429030705130f15030c081c0906050d09 69
    0x1c030350015036807981140f03420f44c02c090b09035000321801a0300740020b01ca42500030461405100f545900011074420303c1c00090002c02525111400e8021207003606800c1c05004055203106009011150152011a030000010480c09200380c1002480c5d00380000005519a04003100030003000300040381040c651780b541c01c0d039584000141c0c0d2100c0f00048076826141c40b00b0324450300130003860070144580d04e0000302d403240c20454101c1c030500c6040d00040b0103903210141d0201601621f440c03030210101ca911b448581e0000d602602405080d44100036a5401e035080000394810103440c11f0b900e4078106440c22209451503151312104170258010062a440365480d14410448ae0803038448805e200e20344003208002c0c1d1140e132240c006000750000d04007071010b038841701c100d450501481c00d000105124001082e5006080b64840c950029005600c00001d214446603200c09603080e007800d90308000401200507001030110300ca10004240318040c100310580c010000f800320300c806a000411200f0181e40c3d010f00305103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 172771870 1250 172770620 172770623
    0x8070608060307060309080f03040317150a21140319080103020a050d0f1106070206270a030b040206070f050d03050f0702070e0c0a05040e041127040308040c12 70
    0x15034100400400e40b4081148200504003030034200b01c0310340c00b078075241c0c281c1c03007001e2880c80004400408202054800d0840d0752a0010703000d00b074941e03424584031405015001e080503d205488a18022980d001882843c145480320000600e103481100ea451a216852070841b00e040303804184142120b800080710103c01e2580305940d1a040e80d811351040003800c21143d00030303a00031490f509485002400e802150030701c690300300c40082103010416001a50a1003413500003504800c0101d04180a032500341103e41a45040b0400c4841c14480390044c824481110310010f40f81990b408042005820003c0c000c1140b00e0040c0005544211705840700c500d0030a100124100007651281040704210080034180e4001d01e1510152000e185807000d07100c0c02034409420610445000541040454025001c4070000c10150494040300c0c6802d0404010201c2c0054045001d004e81a0325491072040b982c81d4071040d42c501a039200c1d1a03403038a032411139039400020030490b403540000030040303100c400360b1503d40943c6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 172773120 1250 172771870 172771877
    0x403020913021003020f03060d05211315140c0709020c0303040c06020d020a031b21080901020405010f0f0c170406110a0c030b0403020a0804062601081002090a080706 73
    0x8180d01c140880d019980f1112020148140300c40400c825038002140d800c0300044404804040d40c40c2005130800c001242202a403d0043d07240c107000ca000c40001d00f00300001c2100008000d6a034a42c0e40c041710320100284000115521442e2034010040c0b0054110048428102c82009803504040d0701240d00c00b030405801988080208010002580400d03c00307001c2d544003030480c15141483c0603680d03800f00d050050a1101c0e103074030309200401942c0c400b10420340100031081710981c00c103503809032802a612078900040c0301500041c1885c505008813401c60300107039129071008030300000440701e81780b01c00106001c0014203040c117008503c4c100d48a0340c0d08480c041400b6035a524040025290894024003a40f02c0d40010414201080d5a80b4171301d400c80e60459080a202d69441c83c00320b04191848400929101d400715000ca1354640c004003a161841d01c0c00c0550070081103a0201342d103400d101b4420345215a203c0451000c096000d1380190206050190602019946601069051454680105000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 172774370 1250 172773120 172773151
    0xa03050304080d062601150b0922150f18020307030f091b0e0412050307021f060f05061201090c090f030b0f2a0304020a080105040302060f070201020a020c0d060204030209 75
    0x1018140030920f0174603503941c0000c105c4c601c2c159000c02d109070760901c41d0b0074088c403000c9a50240b07038849000e0080c402c50041c0c0e000c0d40841004007980d0007044034841c00380700303500c112602040e41d454801d604c90075a140e414203034020340e00c140056406940024581020076445503104210070b422401180038403841044a9504078a08070090601020300380d0280f5212299040fe0101040050100b00d904010703510b4800c0c1d8a558000302039240c005000308070010046404955070800e4050790101e000d647c0c44001c0c00c0f000b5a590010072015010308044007410b2007540004005000c80c1c3e038030175200610181001e06041d551070f5050100f1203103135441545e800900b030040140b05c403551001103510140f030b48483c5522190a0f460b82202e401107003480b00540d40000081000c4d90b41d4010f0f804014820f21009000c0ca10f094500251180000e440b1440441128000304031080e0041c003e0b200c000312540e009040080b1040108040060f0703c00c41546c59550802c0040301603116051980e00ca40e100c0c9000b60355 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 172775620 1250 172774370 172774409
    0xf1305100f02010e03041d06030705120106090f0c0f030b01020705030709060504050903070f0f060f06030f110a050f06210c0406021c050304060b2101090302060609090a03050304080d06 81
    0x2940e130740740141c0c900e94204000c140b0103030019a08160f01e84421403c4148590f9070780020030303c1d0900c10b4000316402410101d600c3ca807400305400203000d5516082084c440c1940c8644083d003560841c01811002ca11860b2543c003100b40300764050301420340148102c6010039a207902281c1098955000240510b03100c0e44288080e04081c0100c4d900602c1002c02185071221986408920110400c0b000f05000400c0744c40000b405819081001c105010403010002070366249081e40d00700c2d410f014122800380c00784080391400e10700314045404440001c1e0503501031120350001c000d070b03607803007031600c0070f041300428228100c25a0410707491485540e0709080155103500380301c000fa15101005420080c00710500700c04400595100040d00e400c240d11403004581070704503c000940c04910030b5030600c030b50042c4110080e40ea100542100e49158080d400b514290341322207043c0403200f1402c81d09081c0310340c840e0340031400191154005640c007034005d1401506021510f154081600e50561052003040380d000590131 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 172776870 1250 172775620 172775623
    0x10e0a0f050c090a0b070f0b100321020c04050f01060c060f05010f06020f0318130b0915131505010c050319020303011d100302040f020d290d05030f1305100f02 70
    0x1c0d1024003017260510b0710a950301111010f034690007c3c6200b80440c0450a10300e4244000e50203113134800310600811100083d041100000c8000180c0184504008403215007054480c2602a10070030300c4140d0940e00700032069541110000003264032a075540480c04c507043c05441180d002e8103c12a694503070071314080d0008e2411981c0700c0d500d80d00390020030041138080c0c1c1d40152440e08079000d13507501c00c952400f440182c0080400740c2409402c1540c0004004015007103664100c00c4460459030148007103c0c10302c00400319403002030880c0081070010b0045c0304070360003000000e400e103100d981100c3c40d1504542d0b80c0920314441c0302c0c0a40c0035070f00100c0107200d0114407840c90b400003041000c0c2e00c44a0718051442004501c0f43c0c0c800a070045907501451141c02b04240c04031501036404010070b0001003420800c4e0810340080341c0c042d003556202110071100c04c4c5050150304600321381210055007002242d801051855000060795458400c840c040080c26460310040d2000e035080319111001c500343d482c04040e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 172778120 1250 172776870 172776889
    0x20d11010807050307020706031d0115050118050a09020304080403020604030606030524150622080c01030902090109050c090d05030c01061406070602030a0605150a02010c0e0603010e0a0f050c09 85
    0x2d0b000d0100070710400c264a5800904241200c0d001e01e00481c2c4482c020a88100100702103802040d15400d011000b02e05201300c4071004c0c12110b080ea00d05500c20044a41244801200e0107920791001d1010020003030844143c0103550400d0140703038103a04d007980c0e030740c0040e01e03a83c0310340d1040307500d15102c0390f00b0400e2142c1482039007203840303201c1c02000c4c4e00040d80b04484070820b0001d020121520b0701008050040e12048160780c41d0000da0703402ca00b0a00d428040c112418280f5120705007152040300b56210065200b809601001640a0014410340e403d04d10703ea000b0340360040032500c280c401031008085aa031403075003101c1860300038009150b5030400c042c045425510650801070a000145492000b240c90303902c12600c00d00e8000c0c03401038072500d031001d521010f000716034484c60340610030410b8a00344030010b4006004016290b0001c0140d504807040030390769010412a41f0b5070010041c0010000c2d02c81c9450400d40c40120542c0015144e00340c0102c1e1800c503581602c0c618080c1c040441d11080c60b0400c50f042 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 172779370 1250 172778120 172778131
    0x2d0512060405060c04030f0210020f010c0201060e160206070809030f040e15030a02090a0f021303120f0305190b131d010c080103050c0d0f0c12060605090402010905040e0703020d110108 81
    0x20b00e02e400d08688800194541030f10000f0700440a40d2126810074ac0f00303000352111401100d00a009081c0e2043c2d0081c060501406180351100f10040490081142c58020118a0440f500076000710750b240d503026501c13620300400d0920980070821141c01e4030822400108068180d21246580e41d00704290f102e00700310040220103011b580070705020005070b82ca00a100d588550740c0600810703c3d81c4100340303020290060030900310422080300008020400c61009071a61803280e41c0d031345811031010110480a8800035186143c8801d841c000c104001080d41d04a150030860180410100040c03c1554070200d5410a03846031ba030495600415142c90740078001c0c0d49181003035150413500e9504580390952515130352050135105942c3d081d8003204014941040090407500700480e41185540c3e0314000e882c0c1030b0002030441d00c09103401d6001c101031603c103d4850090760180e513060351090070441031000806c85480851198840d1b00400001a9100f99122071460b00c42c460f010000c0d40790030005481e100001d0007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 172780620 1250 172779370 172779391
    0x10e01080d080c16050601090b0108060a0e040b060d0b1003060b04060f0b161e02030c0409080909040303150902040e01080a02061e1e030417042d051206040506 70
    0x407480c85941c01840690020f0350b0715080c980d02d58151403441d5000d103400300d0080150007204c1c00080e8040c55540000c0c43e080003038031110201d80da440208080c50380640102030b190010140440c0110f40d1400ca080d80c841c00141680050400307645800030052001c441c0d104100901c070700240100b2085000e1042501c03001d90742071003c6820482c41c444d40088030f0141d40d4401c800401c4034006140c4010403102c9003038002c40c000c21243c180900d04001c3d049413240903802880b03010078021417801c280c07080302222a0003034800c600341451403040012225001c1d00503010185c54002401c80b042050344203400400d5110310069885107410303010011024141e100e0003858003d000c4000168488204640c080307152030081c040001c0e500b03c003880c3d443c054100c0c1700d078040d0746d0b840b0b41c0740c0000820001507005500a184082e000203840b01c0c40247e6202d103000d02903a000c0880700c2c0c54070111000c81c52154440c41c001503803510755281c0c0f011442a08448400041c1540310b04144803d0007014032042da0003030100e07034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 172781870 1250 172780620 172780633
    0x30f140105071403040c0b0a0507030305090607050901030c0908070f0e0a051012060204090c050318011a01030b1804060204150e180703021b06060a05090613051801060905010e0108 79
    0x82e0143c00d24910000761032061400200040802401e485100090501c01040a850f0203400c2e00052040d04084e000320080f030310b0040850049400010140d107c0c000c1580d8083ca4005114011409400d200c134202c02030001d003a801248030b400500c1020050000c1c0c800a2024910740f08000105038800340030300092030300d4581481000100c03541c1c000c0669081051280706841503150a0700280319503030100c2211403170010340b000031a03070150055004100c0290a4404844a904900d080301d2081c0c038902c20700a0326100c80c240c1c079402a0880c44a00d003009101c40c0c2e4441e030540c0b92921260f022035045508035070000c1c06011491074820f01004a911618000c8104084403021403107541161b901004004400d100207420a44a60101c400701e440070f020b003040088038001d440ba510042960105d11074000004042028281500f5441c030844000707140020108a410755040240b0000d401e40f0001d011100b491040c041c02402800002c0091030000a425850305001850b1481c060300405625003109 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 172783120 1250 172781870 172781881
    0x91206070224061002120f0d0b030619152102180106051c0e032b0c0c02040203040501090b0c040302030714012021030603010c1e050703050702040204030f140105 71
    0x40791a03e910800c1601c0c0310034507203800c65050b03117001541c04004070341880c0055040d500c64401c8020305800008060240540c0f8003d100705a2220411907100820450180303112802c2802500034418040442c00301c00400303521181d2051100402084200d40407a2a1402008600301925030740f1a861826001045d10b504200d0001c00f41d1080901c1c041401d02d4414440c2000c03005036020401030000310007241c2e9280c116003080400c80621400301101e00e18400507403400c11186003e5000c45500300c2d5100490500d030750342040001c0d003002d001a15150342c0c9200c03940004205500c000e010b8100ea40034a0b80303132032962040528016003034004624500c41101e8466450741c100b100a20355604242901d4a000240468103140c44a00d03400c15513100200e861045d030045069009501076082640248184014014292031021042d440950340d000034a5142c0e04070ba00c260044c0076135500c00d2800c41c4c98100c01c0d800060681e0003039003090b06c1e02d2428040080402003c0c010a2490103105402440300d072426 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 172784370 1250 172783120 172783183
    0x40c0207090b03010b0a15030606030c0504050d05070b0307050c0c010207030803130f15020a020f0606030d0f03060e010f1805090c10020a05071e090216060f020912060702 75
    0x100e00c2210782480d02d8200307a4540d643e080d00501d008050181c48404150780c7d90748000c5851100d05a100f004c6850110b02041680c400d015014030b044503a03d4013440d013031130301d07051211f8682040001e43e614002c401c00400e58014180085010380120741d2410784038010680e82504000c0d1214040b815035000d0034007000012003103010b880d841001c4a851078901407242c20720710f02280402c0001030014500e082a5130403207030940d015089461035039003280d20795000001103d0740d520054980c0c07607056000400300f901d03851103407020064450042c680440c00035902c03400c4c049110420303003090300b50100002041c0046d007d1040c1e441c0c0e07610010310702400345040101c0c0c22038651200d1042c89001c2d008002015001034020001001082d0b40301040b640d0b400c1d9296445400008202c20340c403100c180800f40010301280342d0095a0000b00021803c0c0301081c907503550740d002803004d01051041d854092001a0403541c6007844204a40c095401400c003034684004002d007400c015104a69203810007903803202c41e0200 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 172785620 1250 172784370 172784383
    0x702011e0f0507020f0301060308030702010f091109071101020c01090b07021603020f0a0302180108061605043b0406060b1e0307031b020f061003081206040f020a02031206040c02 78
    0xd203400d100d0356514860000c1040385d11808546601582003580001c10000c1c108015441908541e008002841d030340e80103503054641028010700216009485401300789864102c0c0c54114541c0d040c4107281d60035100240c1d0070780e002610400c4007070b59902400d0051165542ca41d5a0101c03580c070180100724449503092100403414040680501e044c1003000250b031b03d900440360061a0014a07088140000c468060300e229024003646006001b0380000c42c41c3c01c280910f41e445c0c0580c0c6625110304150a00d601401100c850000340d0081c00b00c3c1e005000d069020f199016143c4801d42d80281e1200d00e01802d0501c203460042c0d110b0413007808100302500c10060885020b183c0305419000e10b03542c9450350441100503091190341a40c1e0001c030000c44414449d00021000c00380382c401c800743c4580da03031410303210641c200a51101415816007080458103c4200b4020940d200c1c00c001c000042c903d44002c0800e003260001c401c01005640001401030200c0c020094140e400003080b10240185445070000070b40700c09 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 172786870 1250 172785620 172785647
    0x305100b030a0b010926100b0105030f1302060c010e1e030702040203040807080c10060504020a0503040f0c08240901090515150904030309030806090402030717030d05010b0702011e 79
    0x41d83e030680709211344c3c0702c0c000d010002c00202c1d0482015000c40b28811000c0800c00b5038410701489400400d02c501c0d0110b0140ba02c01e410161076280c210303075a8070b2441e407481c10001c10b00e481c55034074003000070016642e02c0c01070400d0054520001030841454258140303840c04448104d4502c15010b0240050750400008641d00140e0682d009600c0c0c0e2610325003290507004141c4002c0c140e2502090302107415000041043d1100c0703200f0400d0181385e590344188801c038030500e841580007400410009000c0394a400d29070f00824407030368400303009030303510b0b4002c43c20640c580c510b030100820521800208117141501094100ba901d01c001c0100900b90380e9641d98a5040051460b40c80c2c00e05000241001101050800500c80c06031405260b03103403601d0024014007003100c003100819151004070349a8108150254401ca81c0600100b040c14180341e009030040c4a04840590f02d40f00803c02081031401e280201402071400e082c402d40c4810b034510006d0144801e11503c0d003001e00803100d0120200703a01c044103482d80d2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 172788120 1250 172786870 172786891
    0xd050618060918030f0406020109170301030c0909140607020c0a0e0c030412020a1502250c0315090c09091412041a090904030906110d08040b090321070305100b03 71
    0x19030354402d45404d500805109809900003c90009005074040d00b104101a00c903510840040d900c02c00510128002800080d092003866001400a4071141e030010301054012040c5c144a6885000d01610b0030408a9074400141c00c000d18488550a1124a4401600d4000c8403850640f814602c04282c030b01000344044c01707490588a1000303049000b4001035400e55000310302400f4040c5404c60140295001c10201420700120800c0b0304003000803078020f0722849600c10f8110003110710316101c0d007a104410700d4a07050640d981e1020700d00010f149281100090540c480046010161030818044141c5142c1c42c151107500030031910350824000e00c0172101030341c104506909145110022640c2507019020721a03030050013000c280404e060300300682c541210140c1d540c0c032502c554043c0f07000c7d0f03c038512340c903c0001241c1a00042400918454000340c0d0011490003160f043c45200d8541e4080b400300020901c401c488801c06102580d503250040b50752007168800c4503183c00e481c25841232900e10004110940340e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 172789370 1250 172788120 172788151
    0x3170f070f0c0b191e0e010f050d0924091203090c030c060e09060406141507060501030309080f0a0209010506090a170304050109090b0f0112020c01020d0506180609 72
    0x401042c0404038020b00441c864090300e4640014040c09910064190703400032502c2c0100a864141e01d8039103030200c010f65541d8031460702d0030890043d02e58802412030300c424001c05004e40806000c2a1082443d028090540038040c0c0c01030a282e20b6440160012081c840c0d820200c0d00c6000c5034a0b4445003407524100c1c6400580c081c401d0420407036112103500000c0c5282c0c81001e00003502684502e030005031003411100c1d00115121441080b01302c40051165401584200a01082e20701d08892023090030000944843e280100030740e941c0381280c2098008802041802c0c20074440034004101012045803804000e000c00103054001403030ba50014451584a20b000141e00101d544440426100904c41009003c00a40346142d0603a140e820078007580303000640314000006d4895090051000032100640780d8204a00c1d00c9004444064446100020b4103800b0403a0b809001400d2008003c51011340380d0014160400800300040034001c41a941c4003641d074038090001607625800d1142d0400d0210804038107 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 172790620 1250 172789370 172789373
    0x316080c0a08030f0402010e010f1409041d0d140403050a0f0203011e05070e010201050f180322170f0d030e0a230717120d0b04021303170f070f 63
    0x5400d4103124001c0080b00080305104140b44502e90301da024501c02d88a1543c1040e01740e00441d181a55801050001010305800801c06042400180003526018102049401480500090f4100e564001401580c040c002004140d68000d42c14409482d0060180349040d266841c0c41d40c1d500d030407079009401503080501440466800754400c041148216010003521807064070704100900d0125200380c0410254810b08159600c180700c0e41313110f41502080f800080e11a0396480c40c00104d13000703040146110070049401c0c0309031448440080d0360241e884001401d42003032140004130805004a07441903000b1a0791420030040865150024240f40c80d00040041c0c1d010780d000c2c6400100b0310003400d806900c417041c84510342c501400d2401d0017412011100d1150f55076a40c0b44c00903500301d1032500d040d04800c2c28280040fa1b400b0041800c8001c020b00800c801c07a403640000c01300e9111524152400760a00e0b410810402c1401e0441c0124000e5000300b03040084e0000070411920491400a1221801c1c3d003d440 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 172791870 1250 172790620 172790623
    0x308040b03190f0507020607021f150315050901060605041d100909050601050405130f030806032b0e0901050a030b0406020706050711070f0609090c090504020c03090f030316080c 78
    0x1c0c207081c5107041400f00c4070028910b00000c040a0700c5c0d8030014050f090000d00f00c20300019054403203111812054441d200101803440c02170203142c0514141d40c04005c80080401c070703500e000035413003a01038400051b941480d025803803c5842541c000c009019040c03001b0080d28226180204044141e480b04400f2941c07800000f1624620542005c0c03105451b1490300800d120001030b11034140d030004d840c20030541e1922588290702c5d100707000004002c1c90404110b0000031784609290364000e0ba029048425184600103210503026102c4140d00b086110380704100d45040e800340005126071810b54101c00307554100b10126040ca2002c0c0809000307002440702050810250f40d0481e02510f8201c0005c100364108440001c01101135504c0e400440e02c0703240000305800e44600300100071244551145030140b80f4001120000d44483e0a6010034171000720000111034a803400182850704511000c0d5035100200820008000f800025071800303a0300620000d04484a0400d01200d110742005249403a0042c0740c1096 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 172793120 1250 172791870 172791901
    0x1080403030209030708070b0406030b04020903070626040b070237140a0503090909010213090b040b1002071706150f030a050a03170c0c0d08130803040503030702010b01090308040b03 80
    0x6c451203000310010303218500c980030704103540055605201034803464040000380e008500c2c80030b0745a004041d0410400340101c012144028031004bc0c81514600d5568441c8111012641035038069003000420110540c1401031401d0078001b000340450f144007036025201c58009541e020494031140020700d030140800341d0503220300c0100b00300031606420b615203840390f100d030017182c9114090030010340031449408040c025104030b4000c01c20050092440d05116101070010f0400382c64100c2d98800b03078403c4036240c0c8031004010703030015001041141d00d801c1e00c615a100300c0003d4a080e0750000d00030b1180c0c0001200250645900444d0310301c24144203040003034200015500010480e1040c013601c3e204054112843c000402c00c40e98000c0d2166480007001c800511403541c00e900c05030031104031001a18050210590404601a6401003150850fa20344102e0b80c8160f40a0350668000b00070051115424014030410020a10b40b09080500c1c60b40c86e0140c0d40940e002e0140014404800190b214900d801c0c00c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 172794370 1250 172793120 172793129
    0x90b06240304080904150e04060b0f030312010e06030a03140a11030a0c0c050904080703080907050301090615081f020a030b0a06050714240c070206190f0e010804030302090307 77
    0x21690700d0501d803800b40590b80c040080b860181d41405e52071008025010070820071204401a0030500340c0d80d65895000500c0510682688030301c201804449030f80f01040500252000041231624550411550041c181c500400030b505c60343c821013160000940c846800d801424111524035140c4c2c070303109420303980c1305500441805203103c0419810346680d841440b01003e83e000b405000d010030340b540309001c2e00d442c0840d0040d00b0144100000000a4414480c040e0b00001400c00d0302c0d619a01c410004e401d4030302d116825a0b103151107080303280121701d1528240004000c10300c01092880500100c2c00c0360b1001041d09002c4156011545800d000d00a4210b0316050000810000c0e00603140c1001401580041c842601c1e000d500092903454848001007002c070b0107451050214503251004a4035501141c001c00f4580840c40c144440d50050720741d10080c09003040f081e0068441c1290304280144216000c20310f00313007002102c0c20190b4446c2d8002d0a081c2c0c106130586805030740d5460b5080420f19049a0341d02 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 172795620 1250 172794370 172794439
    0x90405090706080c070305030121060e0106030c050405090706050d0b03190b160816030605040213170312070e0102010e06010806071106060a0905060a03060e03091003090b06 76
    0x300040d0800100e80388040d10b5103502c891280d61038032000381050b030103864002004078074100014441044c16948095041581c2c1030701d0308400c240340c0c0d10305007525241c88948040d691502d4040c0708000c0050744240140c58240c030104000e00d4110034066490080f072092800f441000151b400313030140282c2110b403034000060308403030122180540d80803a907003072030005075800b441d0071000c60040489001100e60360f9400d6a540d48098840d5408622482d6184910380c0c1415510f00380000e8584940c00a82028080118202042c0e4a010300340d140000c0b4000100e02190403c0210005040c06605159044112072070303c980d407070714a10b006078010304070b10180448501c51000000740c0080c00054851140090303a41707900c2e1120161300d44a554060a54803254865000384041c80a9511a4081c0e42e220130000c01c0c0c450020340c3d80e141e640031581d003050441c03290741000400c000d19091420068221005a140400c118080c645810040d5400a4607052080c1018002d8811403824080c0c6010030342800d00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 172796870 1250 172795620 172795631
    0x201090806040b04171810050d050c0406090f080a0b04080c0609010f150501080f151005070218011d07022503020a0501020f07030311031e09030c040b21030904 70
    0x3450030b28040111011190780c070317080700100031a40c0c3c02c205031341d5809140249820b20704201c80c10040e909aa068001007000018031840380046114041d039401204100c018680e0303641800030040003141150030510b81012101e4040100c078400282c001e84864012107580c5031f41d111450120100e11504111100f60301c40d140034043c003800c0c1035100c3e030010044039004100084030450041d24840851080d079000c211000c0005544441c0030029540c4050340501421010100100140180441c062800001140801d4031000c605201041c5542038401c8a030034502503150482d43c072000f29402c04420807400c001d0b008100d40500800013400070020164142d09034202c00f0315290780181c0c0a01c410b92046414500000b4654000305482c5038406445d0701a003074860444e02c007a074801890070001000b52104116000f07c4c00b0405c92083d00109182c820303e9912548041058a00a08c5072000d5204910744641c915a50351141e007001e018501d841200756030a854498494110701956103669001070400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 172798120 1250 172796870 172796873
    0x708040512070c03170a0e09090d0c050a050601060906080708011505071b180518060c18031002040303021506010504121104020f030117060408030f04151b0e040b0303040b0304020109080604 83
    0x4e0f0140906c40c12a50b2074210400300c05041100006041d1044440c0da04502000307400a4481c600c1200e40c079004400700c0d03010390364682e5a6071601400368000f50010b00d010b07030705200c2e060f444005c07660400d502c1d1410024550511514115203444600d21000b44200050407400704110207641c400109072004c4e86243c825030760060307030400c04c4001d0b6070701c1c0d0600c0c41c15001030225004881d1070440d0441003001058030760fa621030b48092681c80b00702c07404042c1c8100d0700325080965041151080103209080c0c0581c130383e4618900a4030300b009001440092002c0714041015030790348482541c080b1044018603504981c020b04203104140740d286022500a0b000146210901610100442c100c60800940c0e00a804440d10b07070b289c50380020340d0300034400d50040021502040ea80c00c130700e60b00640940030030b5031058444900c00040724501d138200c1c2c8440c50a50072540c5150b8209014420199058800b40300210804c40002d8070391196001d00d8488000100121b802d592042c014a0003411b507140403070b030150409 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 172799370 1250 172798120 172798163
    0x702010c0c181103010f0b0309030409050a1d0c10050d0e03040306060602150f0406051b0703121d0307061505060d020c0717060f07020f240708040512070c03 69
    0x50191942a240c100f030391600440000c030b01100d0485499542c0102164140034030603032540d0011f0100640362000380004500011a48100b9001e524000400542c901d0311149840c6021859004e00d0030030f8020b03000111842c1c40b00342d06c40405140910384659612044000400200b12076100c288480c88040703000301c02c216042d4881d00c143e41c038076000c0b1020314204041080012030122a89600d00c070440002c103000500940186821010000e81c42104000b20300040890b41c02c0803e060300000d003403d10b00f441d040c0040c80340c80c1a518030811040055031109082d10f64a00c10302100030402c80c0e440c468401440d1851010602506004200d65a03480d602e00c5004080d40140d5400c40245c060140000b60380c1c4c802010040c0000ea903c3c02400710b07513507001b03201484441300070101d4056001c2c0000020242c078062164080c1c0010703040d4400c001e602011a2040b45880081840e801d002c040c03818007001c508001262450310140d041d81650301d00070b5290190440301903a200902c869000c1c1070511001d00d0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 172800620 1250 172799370 172799399
    0xd0203070c0b2805161a010803040f0306020c0309131e02030c0a08150a0617070305041109090114011203091205061617340e060906040b0a020105010303021002070c0501050702010c0c 80
    0x25a0b0b44034024a03600c600103540c580c4a02e01c00c0d4484820307200820400070b1a53b40141c20760305011000d990402c1c003140080f4400c0740440c40c8004145956071044c42418910020561030031280103421400c601d00b03a0b031026003600c2941c602c80144003084001075007112050244440491003e000c00c40d8486c1d842c02c01600e02960b081b215034580000b0310001d0010352107440303003a200710380003d10444800010003d01040100240210025549036403161032175a0340040d9640c000c061490040c07207485110b04001f400904150050b09031144a031048002003040003582d0b540100f56a1080c007107015941e001a1200c1c010706c000c1d2702c02c0046c3c1c5002c0100203250744c0c0d5291412801c12644100c000804442e5105a99921544502040e106c1c1140082d508000018185d0b40e000500740d0351409407a00031654694208141d50300c0181c9d1a00014420076505002003150403178480d400794107003060340e41d4284803c03595028280c10040c0118005082d603110701040a04d481d0054230101e155900d1700d108540303984 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 172801870 1250 172800620 172800653
    0x403060902030d1115250203090102100203040206040b0f1621080f1b0903010603060c0f1407152705121305100c050d0203070c0b280516 60
    0x800e580302828030302030a20310f000e13810010094102c140044000300011900604211803200241d032108148110b1145024004940b83c0c0045d034580c01700000082c60044120030080313000740140140f10058684100341c40950326914111034681e60b401090000d24000c151402d0324070b545085007030f000c0c81030000211091480400b03a040010250000c00d070b620100648448010781e9074200000c1080c2c02d11441038800c00c071008041d52800c091000041c1c2518100d400039a0340c0ba9441d40c81c1c100142c4c100ca800e01d00d680c042e00f881c281d00c200000d4040c03c0c6009822000c0d1246889240e40601404280d00c00c051560540c8003965a100203203060754a84034404500f2250351041501141c800745103041961503a4aa510780248800d01740070074822080406108103050119005e880b0f03000a00512543c4080741c10350b80250340b2035030f5905160902c1c41c0194041d01d8940ea0070001401c0074198109404500031400a007461000b540c00c40440c0c591150429203101041045190401c00131483d40c10f88245 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 172803120 1250 172801870 172801873
    0x7030c05060604020307020c0f0a050a0b12090a021003020c03040e150a081204060e03071502030a08150a091e051e0610301119020d0e0105130308040306090203 70
    0x6589542c2032208034070090341c0c00e8000d030740300940c1c010042ca0b081030203c21030038004e89001903c0c0d03a18008948500082d8200c51040707100070414001d00c3d13070f40c845410761010162004150140050b0045030600c43e00300468000c150300018000e400b5101082150000d02d0360700c41801e5645094404080710b800b0030518207205040000b000640d1a8000845498080c009508503140602c0c06105544400c0c40103840707134060080030b40002d1f2000070854415680002a0041e640d6400d80d0f40008061500040c0b060600402030310110307a040d00c51110b020180e0b50084400200d00700c6503a6421030711403030806011555410501006030020a00d000040100169007400f036098a441c02003200e42c5c81d090b40b991000401c00d48440705103060100184d0a900e00d46031104245214131012141600c114010b40032400341c000034552007800904568101050040c03020380b0340b52003410705c014080307140071358200d0400002140200502d11640c101340011036001b0103069035107959140c00c102a001c1200c00ba4404d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 172804370 1250 172803120 172803133
    0x7030c0318020f0d020409061107121b141609150b070f060b0d0b13020f030d0e01080705120108010f06050d030206070503070c061503060e030901050712050c0307030c05 74
    0x32810100141d44a00350300922048940c6410b0090202071881680182d81c8580ca0f40c8905c40815524481c280e080e0f80c407240000d9451050f400c019030f0104000031240e0402281d00403d103080b0300c0411035000695485106440d4010106843c2c518110800712603c403409800d90001541c41c90507440300350715411006000c0b40342580d480f83c0100d140101c00b00a4020030844803c500050130075071111030843d400400c01801100036071030b4500c003214100c9522038020070b0303042d0080c254640000c8840c2c402c1030840c024011045100340c020300b501484415541884250300104441e11b01460556141c52540342d03e081c4030f503940300c08240c0038154100c1074454903440c1000c04103c5080c07048241d28800e400da00203000c5a21841c400700c80550009019104001c10742801d131340018614085d207000c1419600c0c40c0501903003582051012100d0003803444080b81d104016851090360050700340d038010358118241c6004000203046c15201072040510f0080d590200003507c80805070440320304580d25000d18112240d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 172805620 1250 172804370 172804391
    0xf08010204030c03020609031e030702031203040519020105040801110301050406080a050303160306030b18010b0604060f0c0503070605090d030605010203040b030105040207141c0e0d020a030f061407030c03 90
    0x8034840e0b40000380005041400a0000d0b00344080105802000501110303009168a00a03080c000400001d4491030380002400c5400e5190030014a40418042201280b031428107a8899603205480d030b004c0b00c038400ca1060070342d056a02940580c6c0c024560100280030440380d0740d01100f46035000f40a442d100b24138100c80401c03040d20014036081a142c0c0f0800951454071a946403514821014800701c00309612154088001000700c4002c50289100500d6540300d040070a0800f404d60b12a8901c29000e11000d000420801d44e10000e400c04404035400c2c240510711031410214294030680c14050240c5080000344169441c00003400c0b003640c00ea5a5040103929102d100490f1644290321605108a0040c0018051442c0a0340100f59861140440640e460700460040f4240310340506085095030111058480c6182c2040841003007420465030000540c48603030005401200f9400094030318041450b00c0d104201e5540d2012200c10070919002d00549070203c3c00034007800900803181c0029040000c0c000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 172806870 1250 172805620 172805623
    0x40b0f030f1612030507080c0102131202031510090b010e090f01030b0a060308091302071a07121401090c09030f080306100215150d0f151803020a06050403090b030f010f08 75
    0x20f08035410341d103042c5012481d4490180d43e4004460b01200c03550f0800003200e100d5041d001100040219900748610314520740101420480d6511040d07106d25003490030040d00d407008040d101e007036600c002d074005041c03641940103c4200c8070a850050304105034000b0303c1711841c1d020f11910304807803140031100d05030303940c00010400380c07031051000812019081c07005141600d00268582100e075400300005040500039124420103845041071001c1d890007002c1480b1649900c0400c1c03031490001c102042c8110391180c050006950014880c44030926034810114420901c00c8552100031a082080c030700309224a400c0c524442d500c255a554401c000140d000c101c91400898464007110031007800c0f420300c1d5584c3c0b2800c403415051455040d0301084548007440000c07000805207452130f01440c41c403400d1402d450b40c4001103c101c1c4800d08241d60043e61603c000a034006039040107254840c5c004206070b21285816120010160081e03041c025001c0100700403c134800108074129461909805041559000c03c903 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 172808120 1250 172806870 172806899
    0x5010b0a0e1005070203030712020606030a0b04080a110d051206042c01022101170109080a14040b03010605120604181b09020a090806090615040b0f030f16 68
    0x10601c01d25800289241001900740180154101685009082c1e40020b0440d4004101100c0703103405840d1800401c0e50420545500c800c080d8000c0c141c0600c1511400003001000300000c2c0200d10015440807010305c2001025100036007241103888140082d180030740203400421a001890000000140943c500390041c4910712855032144001e00d080725940924103401080c02c504103640802010110803d0030004041000110b0202948d65042c000210164010842942005c0e070400c0706040114074110115003041c1110304145942d09070030752000601e4012540008a1202e01000020340903801c000104454500138422040940d180030402044802d01e00d030b080c1ca61804a80304000140ca0140c0e003654440c610381990400a541d031310268180d034004034400000400c1d0190400401004101d01908040150080d0416250040e84040151031818071148100d40740e00d00c04441d51900700b62900c450101405070350b10340300c1c0c003901956584224074180001c6160010005152400c180c4075 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 172809370 1250 172808120 172808137
    0x305060c030c0d020904090c090608070803041a03071103030a020703111f0207020f030a03050703020d030b01051c0b0d08130b04030b0402060c070b0304050a030806090402030721060f02070605010b 86
    0x25508140900c03e000000390809040141c1041e564250700021031510403908004066248001c90b985080141803070802d61340381d10040c00c580c81444103001821402808050305c111104800f9229a12201c0031941500c1ca104100700d14040081406600013158004184150203611044074105082e910540e0f510444842d881e0025202120403155415a40007480fa1a000805061b030319001180020300704030350b000e0120041180000c030907040540520000901e0a001e0404214190051300041c2507449028200084c0805460031a9480003056000c1801c5900c0504070f2569699185004d140941c01440f442054103604940007403070200c1e81c012074064075484981da0b009500c44da428808284c1054041095a0040540c01300d034014490000c3c51195000300020f0244681904016000c504003509145c06000403008020160310300045c2c1e2012202000d1b891064480b035880208040e80317456100800319801d005183c02a19402d402908038540076540402443c0d9842800f00e0091181e10320 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 172810620 1250 172809370 172809391
    0xf01050903121c0221060a0e010303122304050723090907050d050309040f050402030c13020d0c0509040e010c14090604031217060a12060b0a0f060503010305060c03 72
    0x9502020004241c007611a007450303800350511074a83c0c54044410798001441c0205030f008103042c0f60700d48640410f038198000e84203541e072021007410920300c012043e80500015041c0100d90548007113075009a4030004a401c541c40070503000b81e501640b0b85800c0e039030903941038909200740a404542c1440d140c00d04480350054031543d50150010358140308020710000c1401e40e041c0601d010004641d106d85440c50300d04c80c851130185688000c12020403003101d600901c000801c7d0320b0b02003000700503200000c100581b86400c0710481c8804c0f09039110b240203807065240c000400d500b0204150f05440d0040c0c042c001901007102d00380b04510302c0c1d8600c1405c0301c060386103d00001d02c4003070000c1d1442003282c00914260501030303c418540381c1c890b240d043d2400412500320f80003038954008103248045d81c860103a0405000c44100561510f408210589055000740c040e00b05a0340f41080700072503540001c004020b02050160004180c0da511340904a900300740301c00c0c2c0b0361307026500008440d415030000b160f00c1007182e0315 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 172811870 1250 172810620 172810633
    0x40b10091e0e0a050f0a1b061b02031e030c071d06130905010903170702071a2506050106020f0319030c020109020d081b030c070905061f02010b0f01050903 68
    0x160a00054005804881603a000f03146050010030b00602403d085c0311042401402d0f00450361419080c024040020340b85241140c0b0014041e00f544110001d0241c207582d40014505189400000d0811030141c03414a8641080d030170740c04d030302003020000c0c2c842600c80303c09a0b10920380e2440c00003c01c0c0c8581d9102e21300c103219000001e40030701e0301040000d4040b8280400040810b4160340e26802c42d10790200550214211808030001c1d95403078201140c0c401c0407131001e000107628000c00a246401086006200401c000c1344031814003289c84880030b81500303995505485180342d070401000604081c0110401402010001401d2200000407690400300c41c0440041c07145881504500034a180240c02046548074282900943e40301c0d0070a0600300d0140e580130b40d489000e40380c0070a05060301501e200498200340040c80311880049000c5046842c0d011f4081741c660345a600240280400f00c040030303c0080014002e1651a1341540845c404d00f01c207030b40103040a6003010040d9401c6c0a00d40d016641a8800d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 172813120 1250 172811870 172811921
    0x220e010c020d110a1b0f230d020a09110c070311010f080c0406080703060b0a1d0301060501050d050a0905030708090a05151912140a050c04030213020a020a0b040b1009 73
    0x910b40c020b808413041040c08811074540c0c800311b510b1581c0d980041490102c110000d1100c8840503504102c5150803192007460080720303070100e4600c040700d114242042c0d659803d00bc20210400702251541c524040c10f846603162a490014010248207140b203000034188000c0c50001070013040060f001f103000070740c003070f04181c40c1600032620350364018050020580c80384c4000071840f82c42c502501078040183c8440a0001117500401e41c0059a24244d0b0321980c104181040242d802800b1204914401790b0042074555507640d00030050512010700612910002507590244005403000c1c0001e5401100d00c041f002c0d6681040294141c04901a1250090b003000741c0094074070b5200d2102080815801d01c030498002030000907048a140d0524080d01010400800c0020101407040a03808020200386a040900f50b40106009640da141020185a80001e000100e18000c0080d000c01c240d120f070011025240c10324000322081d40507200d081505143c0c84010550040300c0c01103103513001c00303001a0301d402c00701c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 172814370 1250 172813120 172813133
    0x3040c14030106170d080c0913022d0c060105060306011202070606050303040f09060509010f12110d0602040602010b040902030d0e130603030806030706020d020606220e010c020d110a 80
    0x5020382968559681d501c00076141284d2503240500400010180802408a80c1c01826154004203040815102080125015921202d1542c5407540403140140c903162540e00d0124039141c0c00090f0111f010500020030100e142c1c2000820040c0390460030760b4202e07683c8500340301203800165400c1e0701103020580400b640d10720650140113054021400030030b8540d42c66001c24159030254000c07503006006542c05010f4002d4500820f402040191036000e03680d071501095014002e400d01a50210781d8558501d641444081200c2c192011001407010080110907c0c00c00000c0d4803902c0f4841c095420255155403a16140c03084202e602d401030040e20100c21000f604451003403505110700ea12090f1500d18420410851064034007441c0310381c9400402e820124201441c1116641c0704500715030010003001d1416602094141e0042d030241c5d018603c00c0c410400c900410402030303461b004103034a0460040b01480301500110002e8215800340c0700c0075030b041d25048941509428040760725074040e10144c80002c82 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 172815620 1250 172814370 172814399
    0x30a02010e030c1f0f18051504080d0302040e0105190306050604020f07060b090903130e0622091b050312070201210504120f0f030b0319060f05060603040c 68
    0x800f0b035800700c1da41d10002404d072000d02c01c1c04a01d0341c440922078804550011181620714825081080b154406e121031002c10000314026203019138560084850b2a40a010699011340407a2068407604503030703900c1c0100203400c01e12445c008070f411507000003401d080107520f010842c850305c01c106a46a040d501e4000280001400a5030000d0782000307000c12a800d0540500300862103030b0000b003131000455082169145014009070110b80081181d550000128482d60044949030072a04845a0300c0c80c000503402200c0110100341110384500b062211003580e400340c151140b15581c21f0310b21004c600d540c628811010f020300b03a0990f100004410214018002a024940c8145800700c40b2203401800340e04c40c140e081c02000c0d05951110300340700c03c001065181c141040c16a240c4034003070014412008042c0b89000030031000349544c42c42c1a2185403014464828102d605075007a110b25031042c64203100803e0b00401c0d010f207213882c00000c1802c83c5840b9048900546d00003032104e10807070420003013005030308 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 172816870 1250 172815620 172815647
    0x90309130b240415110c0a060516020a26060114030309090406090807120221030402010f0e100f0806030c090606030a090b04030302071103070806180106030602160309060201050402030a0201 83
    0x340030024142d20b4103e504c007102400c95039461140b100c00c05c0844e1900c0303101d075170061103601c10304024015194003d082d07903c80010703200e6101c0641d0003800802d41518540d080706e100c5520380829510003000e400c080380d840320400e0040b24940d80e6565039600342101c501c650b090341900204828030251070700c2180d0640141c080c8030000703403882c110307070360059203a00001e4200c4820501034090240b69405001c9070030002141d07144050600e000056202c00ba100040c0024144290b9400170074106100d0406e500d559600540034405001000c503014000b116100394030b000140008001400600700800d2000e01d000000d003914a017502d45001b00710180e000108100d5580b0360b41c0c20f8000c041507003503401c40e000f640241c070016070341c03e0941080740e5556850148280a580070003000c00c03046200043e41540b01d80302c503400304c0d0343c0c0e0290200c0d2409400c90354005401c0900108048450030a41da81302e02d0030511a8030703041c2500d0755501040e400d0312000c0341c02035816001030202e6030142d401204a0310151 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 172818120 1250 172816870 172816939
    0x170d020c0901120501020408010f0b0a060302041410020c040510080c030a0c03060b011202190e0f130e03131e080d090e040206070f05062a0708070204060e090309130b 73
    0x651032348403490840328985c00412000303854020011481c02c1205080000d4038241c0303810b51a05007801401741c2d80c080c14a000078081c2081d40003a5500c00e00c00d112a4400300f100600501040c03c0280401e084511a8003489403036001e001010311591400194018034194007911441c0251303e50f407151002411f40000701414040301c3c041517100386845100514501c2054810790860056420b030040c1003440c007440460141e80300c0465030711180da50415040201c0d401900100d04c02e10700b42d91060450151070f44401442d00441c1c4080303002c00c0c2e42c1c848046010105170113848181d9a4020603985d44852241500200c0c0540c842840940e500f081c3c010303803181c009400d941c94411a6030308d1443d00040d295040d6216084202400700300c40a14150b21680302c4500a004000d0751400100d80061007160002002039100003036500440d141c2c0c0d000a80108400301140c20f40d8500b200ea2a0340300c1c0d01500e0700034494046440b845c512a03946204451a180c00a0000071038009106c4290319580907514404096 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 172819370 1250 172818120 172818127
    0x607060b041811091b0c060906070c02012c04020c0a020f09070504061409060c030c0607020d0909091a0405060103140123100b0a03060513020a081306060f170d020c090112050102 78
    0x140a0703000080043d606c3c668001e050a03d80785540d0b0b8201440506040d080000c003c0010025030b90240886142000005d1500800ca1700b004400310590074451580b90070500108481c0b103070070004038441070018000e4919414022161003000340e01c090440b20300011900a11092000c24441d0300000341451000c1c095500d0140072500041c560b130844101600f8640c4001901c0100319424001590024010300003025013070301100b00504090214000c4c400250355840c24001070100ca052901124202d00340d4014503401d20342001a21440700740000c1d680c600380c151029540500c148030701145400c040c0401481c0140021001c0c1d00d0745809013190f45510500140810b0010100c8014100151291070000b013030307454003091000c40340790b8159000c1c1c3c003031050146802294010305a20b5025482c0e01445a1070704961030035000418480c3c100f0784404610040101e0480c0c41d40c241d0842035100e24045a01a62480c5006c0b641c60f15462010754008410400400800c2800742055411906c00c100150a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 172820620 1250 172819370 172819411
    0x81b040306050a06080c030c10030b0402070c15020d0e030303070c05010902130501050f0603090706080c1303050c04052215090218270c1009050607060b04181109 71
    0x941d5010740710a2900d1343d035000c0411042d0f0080006010012054026000c4004c03040300064213500e418000c03100f4903454244201403a41c0700d90407580810361051300c8910050300c407a0000101041030703190741e016105503810b00070068091110b22110020040045107035580c0c400d0201d9140202e02d004807241d640310040a001a680d01100c200c40481d000310002e03803985000b042256814140700c6c8130340200010801c0c000e0100e0081020801d8130218108001d042d103941d20007035094843d49001c142069501c06010007044008260307034556610440d030900083d1581407043c07140031284c1100c2c10481c003000c080c1a000901c02404140000e410810004200340307145c0205a040d050200802d072061011820070825010080c0041006401e154203d009494801e4020b507581d129078002920580488144045051207490200007900014002c01d0b190003062520202400e441440244130b9401d1800b90b0300003080e4078092008003900210322800e800e410400380085000060700e00c040603c80c50401c0320 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 172821870 1250 172820620 172820633
    0x3020a030b13090201030614090f070203120f0114040c020307240e060f07051306080408071202010c110607050a0302030604020702061b1014010501030c200d03050c0a081b0403 77
    0x1591804124001c104070f039440c80014201c0d130780340d00b0900c800070b0128048000c1d5100d0030798403035002d070244812034000d440d01c44080e451030041144000c0c802c1c0542c03081140350948208d0b0380d41201c07110460b81c0018000001040107071105440c1d03002c0140e200780680000700d0140602000c0401c9603098507104400030581c0307241540c1d1950003c03085c9511003400d01003a45480001543c1c4049540703800760902502c0325480c800414140f28110402001e400800c090205480840302c0300c03603000c0601c502c0c0ca504900301034081e092003410280411142c104400c401c2d200841d84a01c40c11603652164035008010100390005e4001a080b01d4100354280300e180c0050b180c40e801004110720601d43c007142091047e480700e2810b0316000000e120107003000208400401100300f1a81590b400f402e020440186800c412145170980300d11031125000b0302c50700c2c14813402c4049032040d52008140d4051040340c1c0c030140103038210300c074001030080050701e28000108103071055034441166940e00d00001d40b80079525141d44 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 172823120 1250 172821870 172821889
    0x50f0a0c05010c020106060e0a05030c06030a021213120207080613030504050904240c1b150c0807031103010806013c0e010e06031b0f0d050312090f070603020a030b 72
    0x4005031b9500d81040c00615080b601080f01040e00b224400b2460f400c04000c00e40355101904070a0140e00d000c00850400c1582c1d405880d083c0ca0300110500841c5480d030849142500012030642c3d16002d402d44c40040e441c801706440054818800c010130b03050700e46001111303c0c90f144450640400c0f009201c0440c2c5a40e59003001800743d401492501e6001b064a042800c0004188040100491820750501034281d004507a00d039408c414640001404800c40c00c1a103980d038152808195098944a10b40d407405401c1824a07000701201d990030041c0d441c03e1340c01a91a444203000b400c0d1158400e40041013003402c42ca11100c2e03552500d02e07103a0010f00e00c5034044e0715000c00440d01207002c040aa081402511481121940104481100d520903401c06001103a11003040c6050501e03040190840c2510507140c854400c141c94001510340005400d01d4107019440340c100d998251041c00c00c40c0c001c0b8040704c20004500f040071152030080c00100703142040540080d17109a60110615848240020050b030302d0780c010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 172824370 1250 172823120 172823141
    0x71403070507051905220b01020f0a020f0f040c120b010c1a1e0703020a0e04050f13020f03030c01021206040912120f0c03020a02070801060f140a032301110406050f0a0c0501 76
    0x500402c40105041c1c07da42507003001d03034115403000c03000300040c02d0700050041c1103d80540e9098440b400d02808116007440114a4a40007400e201100ba0416880006200c2030403402a04118007410310004640328904080b02070b160100303c47c0e4090362190703560000c03504896811090035a0f410900018849884221251400f0039804668010466040140c009a01c00121010001490720b04a42c800c0302c94003030130740300f4a00084a110310840d114500c00c15070814008003140e807a040d251076068040e50018001d107800044900202e891400c1c18025000c4130b0343e0200e802d41e24078803540c0301141e034029503100c046601d03a1140110408442c051003001c0002d102c9a902580c3d41d00b407500042d03d04003180d805015130380e01d004010004000c50117015030079200712082400201500c074000620381c034a030b9000a80407050440902c2a9191400711101109480c4002130000c4503201e40030750707405d004900c152000b0135820001680c1c89451680103003072440b85030a048055031030b142c80e4942124281c100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 172825620 1250 172824370 172824409
    0x160312050606070b191b021002040e0c072321160312060e0c0403020321180a08070f050306090c09070806041506030c11010b15030603120c03071403070507051905 71
    0x40c48501d00d41c18081d40184d107901550035480d1038a0401544411040133003100720300100454840e08001030809040400f4400380a240e01c409100c00109454480d4401c1e120580d0780000401405c5552880c2907400744003d00c0d0700741014040c0341d102603c40320210f0440243e000e0340c4c0d00b40031400800113800c5c64040e078000c054050300c0b5810752050500c3c0203588041070030303001681202c0365400344040e400c8502d50448100035030340c1600d41c0408102c4d00c400e40c0c0c1107010b150080c1040420001c102c940040200d6034110b00300d40700f58441c505001c0d2680910b880031038100b284900051a0b4034080c021040c2c000102a000040400107400140c1b88440b0503040700001070b4a8036017016481d80d07c00000601c081040d0000c00c03001141c02d00282c10545680d1100344035450104c0010019501405064844428285640d6607912844d1006032242c0c4040c1c022140382c150201d240c0714881c000402d1b5003400d43c0c8200100a010305040402ca8081c5030480b07507048524980302c010a03648c0b1451802c800c26420304170b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 172826870 1250 172825620 172825661
    0x30507031b02090402150705010e0109020a0605040f052403070f020705150d11041a070c06050405010c0f0c050301020f0d240e100308160312050606070b19 68
    0x10300241048441420550841400200079015a80d4010215001507040f00c203c01c0c00041c2200410f03003030250704009003d5500e00b0078083e41040c07042d04200400b5100710341d0f030001551100c4040d00c10340102d00072220903d41900c0e06011b00d040203412481002007824100041012103d00b03030550303501c11201e4000007240316480a07134241c0c0412254000e04800c4502071500b541e4680036070103e01031403c04220940c0c844181440180d04141190080d0038029070a0aa081d07130382c14800020350051008407100c090007180001c0f42486841900c0907110140d40b1741c0c0700c401075519480e0b60081c019805640448283c48009080d5509100905925900992840e203c03001c0011101c00c0311040846018441c800d030b0190b4002c0c0b01c9507840d00741501c200081d480b00036251100151201c09858100412907070380010210407504a900207440f0140c031982c2c0348500c0c0c0440f01204000d4910640d00c0b41e40284040c040c03240000d60a8046650190380c401414001c4004035148905079101d94101d0540c045103035 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 172828120 1250 172826870 172826873
    0x509100905160503030f070305130509010303050406020d03060b0427020d0b090a060302060714160303110d0f1d031f050405060705030402010905010806030a05070906090f200322030507 81
    0xb807881c004010440146040160107021034005119200000701048000113038403800360b41c41040040680005401c0d084a9a120300c1d010b0103d6126021f0400507228500008200600c05d000c1c003400c0d03071000c9000606051901190480c01022500c50b540082083d20036090780e04041e102401032003418000205a0011450030301c181e100003d4642c0519a0401e002400541c9508080301c0b403c55109914800a41641c98210704108498400c5000604071000020505500c5592a003580c04003009031511b941c0c1041064603e01c3c02e1080c0100440c4800300315039403200380c1900b44070300c4803005000e0f15810500c41d1800740c2440d85c000d02d002c1801da500c009000a1050401589600080509055140d41003d07000030b0516803281c41100e04016942c030000c0c0003503e0034040000c103107074064201c5900580712004200601709600404000e940380c000650300d0715516000301c02c6407400c030491403511035201c1d90300b03131100d80d200415441e140300411001d2480c01d21011404600c1d076000340c0d240d42c8c407031509 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 172829370 1250 172828120 172828153
    0x6070216050f06181801030312230106050d020c030c0a140d0e0f0a12060507020d020c0a03081e04080703020f060c06181e07050901090606080a0509100905 68
    0x250019402070403142005842a01c603201103d4070380362101d0f05041c007250b400d4000b42d11102c405240c5da6400d5180c000010802d0b401502100440c6201441807085200341c030300c0007001942c2142280c06008a038001080030501a8006000040710031700094074200c003420030285942d00041da02d41940d40840c52080c01d10400314040381944500e04080c14802c1c0b40302800501480310724810070b02c6a102d5118154050f0b96420012005001a208181080c0301e141071400042a089440d140903000b007070343c01081c145c40030941825144000b00b061403064203588590b0559081036a000c00c0b00445d205a00c1a205481030150004001c1c2a005103211800c6105114040590034421801401c00384200f003842c59000c500d46030b00c020400c10202051200281d11481d00c8040101201d030b072040c20500200304d4002052b0712090740d00c207030b07510300d00c50366541007100c1201c0040c4105400112000c003c6903103000030f504119080350180c4c048071500b00b2048690030444140110488540e0301000c01c03845514003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 172830620 1250 172829370 172829413
    0x30c080120070321050f0604060e01050d08031e091b0a18020d200d05060904050a03200105240307030206030112020607060f050f090a030905010f11060702 68
    0x1603031003030402005644094860502414030b008051010090080410030342c6008410403101c041d64082c085403d00b171040a5a2440076100c0b0b60246041900205401e20040f02c024100d40e800f8044400075070032034441905603003020380036212001c54543c8840502541d0013005004204101c054002144241c8107411487c0075044002d0150541203000c0002d20080419070b0f4203250300c03800c0540e403841040d40c2e40d8020445000c811030507241901300442c50002082c0508260900c404c42044280c80704002c05c5460300c1d0071034009046502c040320060000e4450390345c501405040300b084c03240019480c000c0d0b900350b480031100d030700c1d0112080b03d107a10504050003c481c1c071040203034081c1000c0c40c191b40103c3c2c100d10050142c0405003011141031302c1107459030003c80b1000ea030000c1080028240105054018040964a96440540420118017015400f040726151198580c40343e00d029441c1000544040c0104065101884090075200c409142d0500080b481402180c1c040c1204001d00a0183c041c50b0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 172831870 1250 172830620 172830641
    0x216140f06040c090509030903010f0f0b01090e04060207050703140109030f05070506073203040203070515070201121e0b1f02060a0504060b03070306090b060f0d030e0a0f030c0801 79
    0x180a18180808070354110f444000303880031048041440c6d500e400c40710707140d445a03800c9590158039040c0381841100e1550300218500c00318020a100c0c0a844100440e10301070140a0a100c816044011a0000c0c440d40c2c014500345100d80150f402c207598a80702c40409000080b10306955035110341c190f008165000120a0403c803603820301500740f01c2e00d51101c0e55564001080d0034240040101002454086080703031002103400c050401c00380f40e82014402030320750004c4d60101d000f4403c0c030300d0200f40d81c0b900e00368201205294481d0241403003010b800465881c0d21141d41101040d540c0c0c1c0c10846c00c03404c1440d02402c1c0103520a4081100072541d400d00c4140d00190700c0300b407140101c500b140f03001c0907030109803035410200c108404100d0351500d0030044010204d0b1884140e1501c07a06800000300400f54016980311401114182e10035501c2005000441480228095001100d44150400a4010751241c4680c407009460010b0b9031752104030806d201d26047d002075826001480040104c401d090003410b8105 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 172833120 1250 172831870 172831873
    0x5070b01090905030702010807020c03101a0433030b0c0a02120307121109032a030c0d020103090c0e19110427150b0a031a010801180216140f 62
    0x2c40294a030184c032801008402410081c02401148049208000488000d800101903c07180c84501116030018011248000038450990b9050306191505218a0040030101c1c48004800303030310030303c0001070b090301d492807130900c0340080c0004400300f01c1d40c0035102c4c800c040b004c000541c0c5003031000001e49070030b0411840b0b41c1801c00070410402000c2d0300c42550604101c4484020600962502041801f4001c20b004543c0500c42c10510b4030b00d4101d000417080056100070410001e00021205240e20796210021040e00441130400784070040d4406c2e80448031441c01114040f04040e120a4490074101e070580e000401540c9541500d11550610301c07d85000d0080d0440c014a02031502800c0100007038502079204d41058145e032005580c0d4220340003640450120000f5040564442e0702151194100e40d245400107403600000400d41404c40c401059440f00507103403071002c0da2812468654103c2d5090152182907000d01810880010444001f40c1c964412800104c624000074201481e0039910002144103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 172834370 1250 172833120 172833131
    0xf060303050f0703030e01020a05130b07051506011206060203130611070b0702010c0b0a1a010c0b011502070803120105090f07051905090915101805040c09030203070605070b0109 78
    0x1c0c1c100040301d640d40c607180c41c060340300c81d01c0b820190000d0052000d00e4119500000350540310740d50003c000c0031260442840c45494a803200704c0c107851409081c00040c4640c0c040e407072542158040804071580302034145807101204004c8148041031f03510748e6010001582c4041201c001480011a0820191007240390464840c01007046550b981c4d802e52085000e503400c0001c982c02964400d4118080141d0400302900103820103c0c1c03000010200d19652200d40b242d0b09000100700d6201c1c0f5030350103910342c0200300c0701096420080d100000b021000c0c1042c055100b0f082001030040700900140c0810074000c0902d0481c2e6140100380840750b580100382c000481c400c08104603081c0e4019007545e000a0b491039055003031218200050700c0900c07519a455070b10030701c000100030000c80212610441d040042d9100c03001c1c120780500030340380e54021010007215004a95000c2c4182d0400368400c4910203202d181172041242e50f40c011030b050200d1902b10f400010350001d8044140140c0c80b00781c03030062a07039076810041d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 172835620 1250 172834370 172834373
    0x10602010501051014030a1103090a1511071202100c0e030c01020708030d1802090f061206061507020a030819020c0d02010801030305090310020a021e0609060127050a0b040f0603 78
    0x1e0400d07a0940c01c1a045c0c07000c0b002c10f60350f100740d0303004400c41c030011091300c0d950382441405940e660304c0c1c540f4101c41c0d0030704003440e41101c400c2c10301510f03000755840030209083c030016a480d003040c1c10381d00803094118460310354468401fa2076030003014080c5407140c0791108a80c2c500c406060601040c3c80106056500c003510400450030000225405c484a5083c0080e40f2604002010b08580700c030080694000d4807003042c84102c1b0b0030902c1680c01582e04480140702403d40204103911801c0464a503070b8400f21824403031821146190050189034801041100b4139a100d0750740f0312243d080304085900d0342020841c1d80400710b4042020402181080368604d001c042c1c43c0d80000c00030001400f00908201c0b01003402c2e6402d4404105514841d81c03030400035903d03662445402941d50b0201258480d40c0c1e45413001404d2040d4000c03884c40e00030040780014081503800c05100c0c1c0003440501030001d00c0300c0342c85c5d03150341c0185030340d8414507018198401000c159034180c0c0082206582e18141040440c0749009003c10 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 172836870 1250 172835620 172835627
    0x1416030515100f03060510050c10050402062d0a090303200601090207050102070210051305040213121a130201120c02060a0e011e1b08010803220810050106020105010510 74
    0x194002c0249001425800c01d450124094a0103a00460f0840d003080540c50784141c002010344003c1a81c0c40c2110750540c034426140c015503605683c041e401020402030700100e01264413514884031007004014106400d007102c405401c1c3e0161003003d000039150b07401401011f5011b03108240902d01d100c48030703040c4505403080c0c540303840040c03007a10811607001a1240c2004000c0d015503007440d400070080e850120350b40001820a0303024160041c0d07490343d100f002003154501442911a40702c114a0142c0d00c050910400960000354000700360340a100b46040c0c16824002c0c482200d110707a0351151441d4020340300e4070001d0201c10304094400c40b228180900b100403d0b030f0001d01a64410300e22200030690a48130840180188180300741032400144107501c001084003260018107008000003e4118000c00100c402c0313405a400703024901041d04200305c1e8812414403200300c0445442401c5000460a0703403616440d240c450b55076848602103440b50010402182c0a105480c0108401d6a100e00710000c64000207 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 172838120 1250 172836870 172836889
    0x3050c01020c01210929010801050610020a060506060705070b0c011d0d2001020c1f0b060414040b06041e0806060609090a140c190504030812040201031416030515 71
    0xc100c1542e44664480911081282d044e017007030120300342c0c0701c081e8200081c0d03006c0805090060303000b190b08280c00320315281852003819040c001d0326805440c41409540c0c4110190001a18480d4850300510000c00031603424451440144402944191b03500e403c00c04407820744400c511006e1480d1000d05d03642075030010220b62134003044d11030710f0254171418041d410724100040301400c0301120340c804982c0300152440000d55000301c2d190014642106110a40c910090750346d800079280d04260140000c101e000c0030500c9050002c403000f400480c4160409001c1000ba412543c003801800320078000003110401490441c50223010440003400a034a0302c5030100f03010388111340700340740240c4042d00001e062180310740c05a0004200c0c04408520b0342064644603840e900680284504c81c0b40a1081906c2a40070b44221012654406007030390416419945903480501c008000341d05041c4c40308a190010480030003403e00c502c4040020200700c041c00d01000302241d000811147c010351a841c01030810381d40c0d00405 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 172839370 1250 172838120 172838177
    0x60c0f0a05030603011407170108070324180303050f13110f0604050d03090602070b03150402070201022e0c02030903030906070c03140105070806270907030c03050c01020c01 76
    0x100342e403526020f0200c2e004000082142c004e468648042c004074651088220004141e46030250b4000d0743c81d041001d4403007075a440001c010b008460b815280000e254003031a810625142000030784010740701a040a0015002011400290b0b600c0c100607207400c41e0000c45070029100c0400064152050751800c0c00141c500389a11311030140407251300503642d03940701110301401e0007030000107007214986009041040540a46000740c0191100402c044a0031802e44e84504001c900440c424500d601c1071100a500005081c2d045014045803000c1c4e040c01c1d045440503440c0e140183d4103215100e544030348100c400316201a02190801c01c03401c40d507a60008195107405004507038040d42d805140c41c180300880e04541c40200100b0f84802d140c102c864065000b1880742e1450746401d41180d644404000000b210004030202e881d00c3c00d2600440d4030708851f40c01d070f409400c0304100c50301183c40b07444505040d2100e60003203e150b44042c0740890300c0e50b030601030000054000e082044600064000c2c4558000300c0002 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 172840620 1250 172839370 172839377
    0x1410140d08131e1a0304031d120f0a0309080d0203030a230f15010e060d2013030212030313110105040e0703090201020d0e030d0302032a0309060c0f0a 66
    0xa030400d2034403480b02c1503030040083c0d00a0320121450380a14400d824000c1c4100c50340f009141646140c00140d00c011039200310703819036681074504e0311100601c04500d61a000c16800101080041c0710003c810841540c02024200040011030124a0002c040b1500d40d000f0302041e41040e020b0f20303000c90700002500c0d000915100b0204512014041c200891466096045001d4102406100445c4410f005084c000d0600c210101d0b0850596001910810030b034039500b0343c01610400c113400c070070348a0341d00c007d40034452070020401064450b421300b1803035003095403043c0d040d1300308000030000c6141000d075440c003581d80ca901840c10342ca8450003070281c8240400d006811559081c0100b06035078030030400c98000d480318a203108080c1c103010000038010b0203400d800b01d0241c4603170202406040e000c0c8015840d4090018018070b051322492008030040e4001520040660145070762440c2c1c0c4194200f050b10509017002003294a902d0448035041c54600f019010304241c0e0010400b62681b0b1068804a80c0110340904 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 172841726 1106 172840620 172840627
    0xc021002091f0525020a122609041a0108040f03050d0c0801080d0c200114070b041a0702191506080c030106140f0d050307061410140d08 60
    0x1800658000f02e50700042104007681e11f900e9030090b106150412000a1042e02c44070469002441e0340d030340500100b46e240260400e40b1030f40070340d15100700c030610074a0030b004006070850b1405040940340d12a40c0e0f2210b03090600910440d82d044031240ca0410a4140e1400c2c0104285000e001d00180c0f4016007424000c01482000c0700079103943c01c1928614690300000d03510456404607000036060180c10b20720034204944402c09801f50382e02803034510301c2c02c1c582880c120010102c400e88061421050b0418000030710750014a049224403060424507122115090100c40d01898483c608081c5041800200d6079480100b0647c03040d01c0c0c1900280265501e5680d100f5800f582c020031950400000c094002c1189054042035550501441c1602c3c641100b0381c45c3ca07002d417510b182d803034661b0003641001e1040003040352140200030411140c4045420407840009111b8440c80000a0050000803 = true := by decide +kernel

theorem cover : BRFrame.Cov 172661870 172841726 := by
  have h0 := BRFrame.cov_init 172661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 172661870 ≤ n) (h2 : n < 172841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
