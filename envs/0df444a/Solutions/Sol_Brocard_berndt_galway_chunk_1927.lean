-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1927
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:10:54.228492+00:00
-- url     : https://prove2.me/submissions/db73d895-1e8f-4ade-8840-d69119304277

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 346402877 ≤ n < 346582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 346404127 1250 346402877 346402919
    0x14040c020d080907121a07090602032205060307050d050c03150f19080a03020d0806060904020c15130b0a020304050606010c0f06050f1504060609050f01111203070f02010507020601 79
    0xd000e42e9540c00c04860b9980403428140e4100060f01d48200b0705e90768220246d030304044c641c0360421486103072440094172801540c114403420340404218100b0506140402c501808004195a0380c2e030806c000c2c00350282d032010b02d564003054200700018918890307440689100d40c550400041099400b4010841090046401e06900c410040c2801304e100206403122006000020300a1682c0c0e2030506000c0d142c2203541e0b00c5001004460b508102442d21480c05540d03040d403040d00d015851b0340950030b0103030400000c140c0c0e0f5510780000c03030100242030a404a0542c40305010711061106a2100403654050703200846018141c2d610250100f083c80d403242c50700c020000d000380d100300590302640d0b4a00065400546100e0082c12601c002e103c00701104050301c0c14131100864003040704926081002d0b02303d0034580300d4540f140f20082c031544900d0340a40c4a030011007080d44182c1e00e035615921881c003000d40050300e100e00094010201214510300510905011300c1c2e0a40051116030700e446580019001400101 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 346405377 1250 346404127 346404133
    0xf020a0804030f021b040e0a05010204060e03070807050d03082503060504060506030c0910020712210c15050a0f06080102030403232506051302030f0a1a1b0f0414040c020d0809 77
    0x23070b4020980a1003e08042e0110365107550454000c81d04051600c0030303940003980150040e6100700880d0340c410815032070003945410101d4040e9940c020001703092200080440c88610829040f407015503140d80840140c1e00200c3d0208215030301c4038180b06042c04202e82415201c1000c206042c12443c1c8040c94150082851040301c00c207a0f00e9030310100081170441c01c101e40c0c81102d88001600c01b81000c2c2d01070040c82040c80c10240740080c945446004112072051030b48299940e501040100c0c003960405100040c846209200c0190303148002ca00070b520464040d03000442100030300403c13240c0300041c2954102ca2000d45800c0c00c0710481c0300c6180001c0c28680c4030b0201c090039090720004c2c40a0050780d2013001242401090b1282500505007008054410350546411440d0154001004505040100341115041c2501d655070407903480e030410785580882c0100d800c082029001c456540c1c1c0140180d0b0500728140103140364140501081e61a000d99100c0560081d0b46c101d841e440c82055040e40c0b180c00b100072 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 346406627 1250 346405377 346405393
    0x10311060c070b04140409050a0609050106080d02060a060608100306022115030f03030907060806030304051207060e1f05030402220c0e030a120c060f020a0804030f021b040e 76
    0x40b40740c04281d40c04000d00c0341c80031034200100c140c8042c80042c000c2040c0c6003400b80404558a603500c64094140050425641301c00c2c4505000b402d520810103081002c040703c000c1c10208400ae0340e2000100c40280c200b50030024003090040c481c140460050190302148100c035809e5664100203500080407011041400812040d00e001c0c4120300d0f14040c0d80c0c04025003024418010515041440050541800d03600400c1403107040c11000855508840c01458803000c20341710540081e0a40c492584400e0780401220808480c40c800440d041e07080b40d5907502d0b0034000c19541c2060209050b0f50f643c40d00d045818496644079071900a40c001d541c007d20003410140d0b0342e21a5003280350090006220728a6555940a240440c19044508003882020450040586900036540c0750301c40e10418445404000c5281000300400c07106400ca101100304080c0159110050754000405545c002c0b02c2c140c000806c1482015109030021403088464a044291861405030301020f1001400100300c0860040c0b081d418 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 346407877 1250 346406627 346406647
    0xd020612070327050c0a06080604090606081c0f020f0a12020f0f06060f191401050f03010e071412061507060e03130803040e150a0306090b01030308070504050901031106 74
    0xa40301402d80300c1c14400c0304143c269042840c40c0015007074240d030003251026403e0160726001881280d02c544121008181c0341030070b15145020708480d03802441c40384070710200c1a0f200c5030030b503080c101400c032140e903aa401d0a800c0d4604aa6590007442c051607260003140701c00340447c0b00340c0400c0e60042a00d00441e926400001500c42c0343c50702d1b90180842030b030401c10904c1814600003000030070700e040441e8004c41032102c03210346110700c1c00144140713218065081d00e0544140d010314190f894014241460644a40e590801c2c40a820350071502c0000003440c038022550340c55420030a84502950342c201c1061720356582c001b800350381411f1a080c03103280e034000d003c2c03040042c0080c0503881ca05001c0002442d200da41e904480280040d45811200d03c503001404240100039412028035404101000d0040e4807055210101e000c603041a040a000346040588d25018040d040020381d04a038820398421800e60388022003200d85014a004003507010095000420110303070b02140404066100916103172400480381 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 346409127 1250 346407877 346407911
    0x1a0a0e1507030615020705040515090408040f0e040b0f2a1801020d080a11070f0f020f1009030201080406241a0715150902040815060d0206120703 64
    0xc0c515865140c140003080031240d418050807008043c2c0714a034615502e40000003035100c45541c06414081c1da51000010038440d040d02900c40c001c40044c0054440382800c2c10840110745c031502400c5114000b280000031100141000684595048451042c0944907014440002400500800d8104003a100c0a0100302c502c10702c02d0002d1040d4150041d9244100c00b4088a00841000454155002401c900284540043c4002d03071042c0144000511591460444400c1d40035007a4080d0505900503501c01c100641442c1c100b80741c5008585889020810400304000d05070642c00c10300008000301002c00041d401103100d280c015208110119000311548030b03402d20130350001400d95202c1940072003040381d8980c0740c1140216a0a40826624210036911426919000b00310030302c0510741d8510280447e01303200780e800409000048815551035503258000c1e96034003071a181c00c41007107840c000800c07000e19043c0400c51455a01822071070030440d20544c1401d41482c0180007100b4541c4912008107403d003c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 346410377 1250 346409127 346409143
    0x3010e07060e030a170a092103030513020f04110f0c071a0f0306090703020705011e0e010506090c13120c030c0b2a0c04052a071a0a0e 59
    0x50002404200d1070058010b107108a40b00100d030081d00910b10600c0881e000c0819002881500004103598640c13600c07048401640315440b00c161020415058888004207104109809020b641d041c015a2100c812080d08141581d8009520000704035801c0e44609090b08040715084100030060b09040840006040a03800f9501c0f4030f500ba0416142403150f410321005203048544c80348021410f00181483c2c1c80c56911000c0c0c0030602c12154000000d0b95036210340c044511459000c8000c1c02540030a03640c603406c440d007500036102c503203050000c00f082c0c20005103d828800e00e001410b048080d00c641c2c3c030a98140d03000325003400f400d09801e08041045494805000c5110f0320502861b1501455802c0c0ba030189038081c2c000b44c91110042000e04600e103140c0801541914035010440b40e000c0002500515184421030780071380107400c2c14104880c1001103ea50a0016400c0c44a261240c290071401041d5100b140c1004000d800b40c0010b204a0000700c801c4c0d182d0004580d0b00000701c415003804540e1408400c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 346411627 1250 346410377 346410401
    0x4030b040605061807080103020409110409260f030103020613120c05010807050c2508100b190806040809061608030411040606091a040b0c030705011503110d0201030b0301 75
    0xd5900f0b0181c03900b0288602c4920500060b181030150030401e034002c0200f9418030001c4d10840d1280c0c0014140826406200c070403980003041040468814076015102d504811b95042e0b50640c0e14003940f05e485040300c1260010f0894440003407075603096900700010b5401c00690201d000b03090301c10215031500351050703141d0a1805002c00005184c41e02c000101040c40040500c070810105000020b00c03103c00184032110180011074a646003190070007049105c0c11942d22108d114070070491210301c0c2c9015540411200b400c01d464218504c2c50381d030102c91403203038180b185811a9106000160104400c0f00103407000100040c006403502c0d007150003140100555a0054840e50800400d00040040a6808400702c40040d07600340151881d20308040c01c00401e500c030700c0d480c0100380040204c03041040801c41340640384043e0850b45031f40159218a59a41000c40211455880d03c0540800c1c0c210301e814141c112a4808010881010b00905101c00e6280c0b0b2801241031649406061400b40e800303001c0d60301120f50b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 346412877 1250 346411627 346411631
    0x1f11160b0d05150d020906221d0f0613060b0402030703020405041b0e010507050a02120f070603050108070312021504030e1903050a0212070b0a03090b0105010518040c020304030b0406 80
    0x5404001d44088400141c50040d480c0b400603050203107600c0f22100c0d900c00d5501265100036603074851000c10480701c0c811020040d25100d1405643c4450b0090f405083c00f1400c02049500040307007140ca090ba94800d04064400c3c50b40b10800041000342082000005c8511646010855001715808203040e44c00a485640100382c001c202401281440d10401c01400c4180200200c062062400074095405181c009410400001036847c1800801c2200c42800799000d05141d03030700d1819140303040d00c4580451009407180608007001403940e1090041070705032240080900b03041883c5554007071203c00314003510001d5000b540b20100b508003201104910880c00380d00c80202c15441e01080201000d0052901c070480e900e1042e041c404a6000100003007115816071701000030244580901d0310f0206c0c0e42d8800000300e000068031135080c941c10781040307081c6449508016a50707604d0300010344050046112034107400840400d180c52519258201c0d48071000e41c1d00590b80b034503890b601c1c2c41107031442c00c95050720039035 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 346414127 1250 346412877 346412887
    0x1110f090d1a090309040c1707080a0207020612010e06060a0813020d0501051812180f0a030203060406092303090108151504030507060206010e010e0601030216030215061f11160b 78
    0x10a0a014000540f0130394980302041c0d0028845002300c03200041d00c640104450840040c1b1000c600c1c1c2d0407a0020340d0001c180c10745455210704400f20880d03090140000c41d003d0342e4045410f41c10070307809507980b980c4582c64200e402c2d543c503800e80c651082c40c00401e0740e00c02d8130021000045942841303000d004141184040302c500f070741d0b080000d240c1580050ba141c14100104207201a4125802a82c00d804104592000f0008603d00003d58607038030a03000654113005180501c02000207652241c3e4565102300d078030840c0c048600403c3c9002800c1c100e206607a40c0c1007005800090f610440100398445070403001d8881c00c840400120390382a22882c9032803c0c85000041c28428000108251001842da51008298039070515580072602c20043c0b2030880305103460804103109a01a40541d50f074641d8114000002100c1410025030728081c4014940c0340d81000e5000c10100c0c00c01c1600c02151003100401e1034009040c02da811980f000e0905080406030083c440005680c22040705400010f00300044031a0b250 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 346415377 1250 346414127 346414129
    0x181a030a300f140f180307032a080606060301030605180f0f2a01050c0109020301140f0709210c1703030f09070f0522090506070201110f090d1a090309 66
    0x82000c500d0401030254244404004d01c1c070b2950450310000100034880e8005003000000c6481c041c4640c000502e55984018880c25100c942c40803010700380601812403a44594520f01c0d1601c0e10002c6c0e9580e0b4004e03408000600105040b07030031550300f04810600e0152010102441e2a00b8440301200d074400b2500031a040d0b08105004010103203503503503099281180706d19448001601006464100317418400041140c1d00070030380030741c0824029600640244461039511600c4135005c034086441d58000c0109a01107032400f4800c1c00c03450103072548000c400007a03610a80312100345e81c0d4480d03011a504194680045810401100105001c084042c011516424940580f8007003207401005564581e22240c010402c030800001500c3c103c960940300700c40d0b07204080a0b00896401510040c0150b1810070300200c0802c0800a00e681c8254861790081042408400b00c460b0503215400760710b541e86005001e40c903035a1904444405403d482081d003084616000c4200030500d0705c003207500c1503c1e9000442c0d03002c2c071 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 346416627 1250 346415377 346415387
    0xe0a060f030b040e0a120210020a0e0111011b1416060209180403090302090c090d050d020c032a0d050d03020304030306120807030f0e0406181a030a300f 67
    0x40b0a40454042c40301500031551250741e5041c17244068003074130426142038003443c000d00c50200c01d011114801c0d07555150444c400340282c002c10080c00d0006880900b608210503061090b84080030805401c581681c484507811241c087d005801003801407002c00554850402c444811244507100d0400540c68540c00010001c5480c50181c21803585c4980f01c042000081c0d20403004400d80741c0c1228064900d480b5444d0862150159060454015202c07540101c140500003480049488080d0700711107528507803405158440034148080c50501002505c9200a82c40070030a1032410710001d003150418085540707600d031528220940000c007180e4004240b00a05600d40a9030b00648150020590f054880f42c0da0100c00784030302d61020702003000583c0040800d074450f0030040242c010040090149584412030515140d001c0d13068a41e03468a000b03820318444419400780805580700401a141e078403250b0315481c175404d841103030303550301d04891401d45400d480d000e9086042c03880c02030303032502000d085205000e40 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 346417877 1250 346416627 346416641
    0xf03020a12020307060309030201090209010602060a0606030209130f02090d08120108010b01081305120301080304140a21150f0b100c0206090d0804030c150f030605060a030c0e0a060f03 81
    0x981c50070703491000c1e01507140090400202ca8042c40e000441c41d8050908174010090a44000d51002c01180000360f00ca90004241e4040e1642c1c2c81d0030400207903601415000c81c814482c1054202503440d22051111900740e01c44006801e2580b8058680fa66241c00560f41c0040b0079012603903500e01003039401c03260704a00d078000e000d001404000c0108400c100006480700200074514074030090b40300c40c0002003200500428107070345100000c407600c03561181641501e0b50401d0041c0c540d500001c01040702d031440c100c52006d0880b1002110300030100350442c21144518234007003003641d05080c440c031224201d003400d02c40c1c201150001013000504960300001c0100ca111120120410494005030749030160395003c007112140b40013116642c0204620749011540d40c000e0303034000f51000421110001d000d100301c081d446001b0010baa1000100245800180c0442d100380c0a042d82181c024040203040f00e00a60040c90700008074185440180d40d10301c0001c000e012a41c02c2500003d00d03d04014400d141c160045007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 346419127 1250 346417877 346417889
    0x2190201172701050105030a080f07020d050c03010c0201090210030c0908030307030b0108150a09020319110903070e010602120a030204090c020d030c030b030a0f1718031c080613150f03020a 83
    0x8000f81d45006e000a42c1c802c0405d60140207420001050404004994116200eaa50103403403031801815a0a0840c0c84030b600e603810038041e5081a003801c01e1144184100301d26030341d005003541141c582400c81100204410602b40050000241000c00c0402d8104081c510800d0300b560003040c48100380000410810000e00b40004401e040e49a04034195a0400128107a4400d618016200d944004084014489000125000a103889a00c032140c1031910010f041486050b0202e50055035203a84001d0503100034410140103030000540300e0050740032440201413100b640e00e0058100b5032220226811500c9408030b0602503408440c000134100d0b01030140700796803091814100000e400800c08203403600340500c030040c0348a00310900c4008002041034054007201d049202c003034944d9102c00302c070360804c001440364520034444d49401485405d9411502820107146130ba07207044030b445010900c400c06881c54582071080b911031032400c00340d01a2a2a040080074880f503802240d61031401070100314591a000306c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 346420377 1250 346419127 346419131
    0xc0311030d09061d040b0d030801050306060102031c0f0603020a0e19060807180609020f120603030703090e06011e030f06051503130c1d06091602190201172701 70
    0x1000307850341200702d0340c503c0d031000c41c3d05108071340ea0040001c00401c02c0000d06503209000345e0184080c90351002155050b41c2d8250301303c45050f184c01c4016692402007490f1a20b841015240c459080d806070741050070b0724001800040303549a241d50014240c00629000190410002c40c1004150007441c20501d40485002d1801c00c030a0781040342c01d0351180018082c08003040e54813045100b1000c9158400001080701d08011501c600c02d500014a10383d20114401d01c07410025404a10780b03180100456800395070548903009150328103802d82000c00001400c1c5410300001e00e6151542e40b15050b03941d198030100c2e6800042da0001c0d40d503a88210354003130b0460703030050203200c040b0600e0080800807650403004204554040c550140f40070750882042d5048008240752808203c06842e10040015018140032a07920700641e030340020521805104c5610480140d0083c00c0d900c02c101c180b00350704410030b401171410480c201010f0350111003404081e1051b100018000458011b4000e9640f0310709020b01c103860007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 346421627 1250 346420377 346420379
    0x601080f0f01091d0106080703120305010b16140115090c17042a0f06080c0c0c060f0c070e01060f020a050c090a0b130903120b0d080304030504030c0311030d09 70
    0x181c480d02014021980740e159a0821a071100d02c3c021009520400c846000b80328050303d4100254a03402d09200494443d030300c2c080c070441c0f541d0003402042c1c10f9540703103146030b810051510682c9407001e0201c103003502c21100000c1031302000e540c00e003e24881c501c0c0072508144083e103400c040c0c5040380c0c07001ca90b200401180390150110402c900903055000ba81117042d4060800d004021460800c5034941300a034851045200000d0607c01c040d0b444003200c0264940c00c9003990ba18401c20550711074000d40120340d801c03c01400c0340a00d820070103402904080b0304001c0c2403885030310229190042580000801c880703444e0041103a1b07680007000c442c456030244060b000c85d88490392400d07590100852018403603600c40c1e00207241441d141d40f00304080c41e4010089400d00c8040c10784040102003100003074000a66603055004040320030f0040080c0e8860180140804507182e4542c8800d94001601c01c400b000360421000010644090048001e035004582010a0b200804101460407251003140c6c4144969440 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 346422877 1250 346421627 346421641
    0x6070614090d050c0a300305040515091009080d1109040501080a05030d20070b1017031e130b041806050a0512100f0f0612021c26030601080f 62
    0x11100205e50b4480c0d000c0c60381c0c4c40ba00c91000311949540c004041c0c0d00300f40075900b0181d01e42c15040380380154040c100f61070100d907840381c1402100d4000c9070031150340da01c10340480c50003504c1940142142400317160087e0170300041034520010344d400d500b0054907190020440300e11a2034144a9680180302440042000b40019500c0715264001c400c0326102c2142c1c1d42083c07440012944150624010340d42c00481c2e038a400c1071030140c268480945200303c0d0711004031800301c2c6041024004484d0459001c004604121030540084240720300c0e05d100054001046c07000700c0c9609961803900303000e40000118103031510304003414201c5800015a840f02c40314201803042041c1e8071030101010603107070140d680c0c089a02000f8005860070b02d0341d515080c0c0b0780740341840840c90000150f1000d0755a2080160601685980703004814038800c07403200281d0700c207107442c02c00d58103402da01c2400c2c0034441c07040784045424450302c9042c204020038090f01040305040082045803541c0d00400e450b5000e250511180d0180c10261 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 346424127 1250 346422877 346422883
    0x3060a051b13090c090305010c1809020a110304090c0206070c0c030f02031501090509210f090109120506070e060705060f090f06011203031b0e04020906070614090d050c 74
    0x1d040842a24030020301600411060401d607000350031034000600480a019900904c4503c85100a4407994a002c00c80c100d6030b44030700d980e0012010415081c081710b6040112082c021340c000791085040c032404000c440c07150300c0c061014000800c1d42c100000f61b0304140e004041c0c00d10780002c081004005032540c090740000c86c1c0e02405015a508510312500c100301c54030101e441d060500300d15980480c021000000d8001858201c24071503002902618444130380c25116010404074054140702e00f213414001c80c0300300301c401805410103001c1450715111171a0f5443d4201c083c041c3d131000a4505401420801410940040d00310403080d1055800901d880019180c2503200c0780094071423102d44030301d04003240505004101480307240d4450000e84d9901e503981c0c0001800007004d411b0440102e030428000d00d5030141e0301c1100c1044d00d401c1d52a001d0303846d00003201b080001d5100095590b409001808108041101403048400c4001850340e03200321810240c0c40240b03080784d403041c2d44007003202c00c0042c0001c2c00da000c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 346425377 1250 346424127 346424161
    0x60e0121030c150f150501030c020705280305030a1b03020309091008030c0a1a130f050a08181206060d030c020402040b0a05070312090f24150503060a05 67
    0x1440c01040c01c080e54039004100d0041d0388400f0f0368580c208078038000400c01079444481413055410704902021341e90700043d4240e40446002c8009038020001c108070a042100101c10340201444850240c91102c1c04c2c543c1040c8280c0d0420355066101085008815070418440024802002d01043c002c10a640e0000e43c1ca116100712503001c0c00040001c650780814020502c0090712600c81034a40b1040b40505003584c80c41d07400c03020781d280c2c100341d10042030300c0c00744020840c01141001c038284044103540d10348181c1284400805c81e200d10680032300101051030a40500808600c1e8100503600f03001d2202044007110702c00b100d41103960840018481c0d030f561581c003000e005039458141000d21030110300001c1c009025603070002a8118000031850701440c3c0c80b0000740303400da1098071200e05510011448508454800b07000030030b40f0f4440010715011a12403001d003440c1e1150220f801042540c904482c006490b807810600e03015080c600024091841d0500a055100000b624100403620700a10654582884 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 346426627 1250 346425377 346425383
    0x30f03150111010f0f0f020301080d0507050c0306010f0e2430011d030f07030809010e120c07080c0f04020c1006060509040f050f0f0a0618060e0121 65
    0xe042124216640160000c061460780748008002c0044900d110002038429580350200a915082e010f00748034003035100352170503280800010440851a5001680c0b00c3c0e1004030242c805201e03c01005625640400003503020f082080200c001300c2d40703402920310002c1c2000d00904001e162007854100303440080040080304402c21204040000c001c8011504084043d5482e07540c2c0190b030201c0c220402005402800c114000e980380e1450135160041a43c1e1280a0142950b00000041141d900400d1040c4207551304054443d0001429601402c46c0610b082542c1641500022011032580d4a109050004034000c00d1418050600000f0000020703004d420f20030005846542c4c045071020443e1810071514459140e40c000401106031113180280c286d4200061040c441c40c108092038000d000c03039000b003500800d0f0007408940d5a8482d01d2102a0511004203c00a0740d0340e1243d0000f2528400a20b1248080d00c84500042c0c1c14280241c041500314140c100c001154005404041c2c03150f10030810301d0417960 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 346427877 1250 346426627 346426651
    0x12060403140906070506010608101202100e04020307020f0c010f021f140901060305010609110306040e03160b0604050105010309170c030f040308092b14030f0a0c03020609030f03 78
    0x907107920501c01e00d02800d2015500a00c0100c0c0369001c10000042d00d034180c810380e881e6030a280e07454014002c180c840a0207102a4011025036400040c14502602459100c00d410899200d85030301020030201d03007003291760f42c0c016400720b418624002d8041c080198580000e19200f00c10a00d40078000c0d40d9409855412480e407411040c049815100e05d81c008000b4040840c88140c5606103544d8982c0a015280400e80309946083c0300060b0401ca9481140020600d0840890555442c4e4040000801818601c08150700040080078148281004a082107a1040069030881e0400384188801c483e016000307181454a44040c2d0004610009a16903079064a4410f00d640d91801d07034050383c2503001c0d24065121059005c00e0100c2003203c500c2c05415000307400e40d030035900c001503500b1801045c004004825404a415410180850900540c1010790700e0080c040f00c0c507000100302d04030300540c010315680300011401c4c18580101a41480103580103001d8000450810b08940c221b8007003403002038030700c1c0781c44c01d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 346429127 1250 346427877 346427897
    0x9090708061c061d0d18060807180b0a05070b1b0913020d0c0c06140f07051e120613020c0303220c180b06040803090111030715140612060403 62
    0x32915820075840c0418104c02080041130000f0403564411031018181e0104811049044448200f00641000c44003030765202c240703e480b40c4505a88815501515888418044a012803070000350001801a51620360320306a403480641000952944064034580c01d200480112001c440010301c02d880c110b00086801121500c081d00c9040001e1048003e24069a8101240388030001d030040b13448103904c3e0081e0014042a0441d00201480200880e000c180828134080411a1244030b20061305041d96078150302c00d42c018000c0400c1c1d1458000c842c400f22144020010807225061090010312000b030b4052066003405943c00326039440c0e0100910203000c41005640c17001d2030b103501324200f00c6480c1d00800724942407500c5a0b110309200d00c00c542e008031550f0500104071100d08201d011102150701e150040c1d410807620800440785d00403600b00420440c03109200142c08116448600302d851402211700003801c481540d0010310f0080000d2940744104420301a001071903101268450380594507107020000c80c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 346430377 1250 346429127 346429133
    0xc03070201150e04111206010807050405062706040207080409020c0717071a07021c050105070f02030d050a1508030702031b09060f1507031715010c330209090708061c 73
    0x91a810b100c001d1141f1503180001001900454404280c88040d1402d01080e60b841080c011004400c0481000d100c500f050007440c01c50310b020380160400c1b001807016161a0541e101c400c4a90810b421040c2300541c00102a038140c50f013040b0641c000c0004000802c040141280c6e15915205684100000c002d80d407650f40201803c841c00701d03034200d54002c10f91a5008400d0751904003038581d003002120300307603c0c0c50080b40321940a404680416103d0390b000b189000305030b92141010f070a020300100380ea183c4526000d410400c04001e5600905000c00c01544c440b071190041502c2d10075902403000301034a082c00c80440c2c507140c085072158407003416101c000002c2120004980c0718011050203503007449001c43c0000400da4082c0c185402020780081c1d001960f219481058545e0025035280ea01081060b1b80280004542c4010150383c0407030031080900f443d04905854400c00c0780f030040c4401965000614069501d0200401d680080103881c1401c90b502d010030216420381045191054006c480301c45071010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 346431627 1250 346430377 346430389
    0x50a1202120c07030e060c0309010c06090501111905030c04060c151d060109060509042a060f08090c010207230a0e060a08010207020d1106120c03070201150e0411 71
    0x601156440100e12464032444603501900074503012400540702170200942031400d103064071021320315200510700d480c0f030100040d25080c3e0002c000312a41c1c1e454400c4240811420300c41c02d840b80921004803641e842c100d1010100c400740f6952107105021084c014001300750300c0301c000d44003500c0e42420003100e03462a07401c246201c078aa0b114003031400c40c02c0408042021420700071101051000d001141e0150742c0300e6601c2001d60340a802626040785d0750343c0016012546c0801400c141d40d5020b41846850403100c0308150051606030071050200c4c3c0ca00000d500b11903400081c02e640145210040c108125a42d00001c0d01d501040c0310300580c5a5070685140d4030021040c07007000f00401d0040103041341e5a0b9034648038885d414200d903000e124825032580024441410f0086a00340340e4024440c0c03002010540c0d0307050082c0d0110001903001101070229044109410610b0340c050303079801044079220f141050f00282510340b24504883c081e28030340c8040100e43c5543d241f4a801603407100c40e00415203540008200 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 346432877 1250 346431627 346431637
    0x4020d031106101e14060304141b01110c01300e0109021005030403090b0304060e1006051f050f16020307030b06010f080c09040903020c030102070b15030607050a1202 73
    0xcaa40038050074845600c1408200d035003100c20f0310111103152500031341080034120040c0300b03844804108403a4089240741c00f2005580c454801c10388a404043d0701035005191420b100b034045507004030f11b001880c071903821240d241008a5554000e03c4050004000240162142c40d10510340e5800b00555090030f20382004040141c6c55203800c00c1000b85445203115020300917102041c1d00401c19070303207255503040c8580b04480c4a1a095121180c580b03180204084c1658002081550301070350300d8100c608070a50074040c0540b4900640000300b101401c2100300703c9512030308241c00044100400c80d084120303070001d041e90844240c0c10101c07a01d07224100703c10b2044d10800d4070f0080d41402070401c04802c1000c3d000300c05000381c5080e0385410000c403003004140d8141406039141004c201301440f061a191625401007030409100b441902d00141800e000700e82a60003694048a00084102c10412569116810310200f018220010080c2d400c054902410505c1216000010440481404110780000d501215 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 346434127 1250 346432877 346432907
    0x30405190c051002030306091f0b0a0302070f14010e030a120b040612050313090603030c0b040c0509090106080c0f060403140a0c15020609010b1f031103070203070b070201060e04020d03 81
    0xb0a03010310003e0700035103030344c002c9a41512a015980224906050710212854094000049001482c0c00e02040c0040c5400002c441720404d0780800c40000001c00c03c3c01e01c282101d00c55400c0b0244c07040e1b0f00401c6829a0f40c2040311400315032061060481459000d5190301e85540c4001001074491a210007041c041e040302e8110520070511005800e01b0060004000c0020300c5001030007402c0c6070340704c8640c4410745d0300d1840060009078400e8040c0f004560503803100341d0400d10500400c0d021649c0c501c003080e50101e0480d00d8801c00d96450078200040102072107080640e5108851826008146034001800b6002c5d0307000140510940c041c44908a5004002a40c400c98000302420f030380940c0d8542c0d04500e84e141642c0c85005008540100303561640c14000d81c100b420000f072502800341c001000f04908c522940d101c00c000c15880b08205281100c11301d004500607903035540a5561140103041c840340c512005084501168903000042143c4007015203000c1d040356040b100500c0e0580035080c21070b00000807007620 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 346435377 1250 346434127 346434139
    0x70f031a2416120c02030c1201150602070609060e18060102120c0304090c050c120c1002070c09050609090a060504081207030b0a05100509061e0f0306090a02030405190c05 75
    0xc04038a4030030301103a0480d540708024000c01e00054280840c0d444844150086d050350050392106e403203103048a0189414a0810000280d910140101441d10f0714254841d00140c1c200b2181446a0b981c0420650054104c9082c010513001c030303100200e2a10900c640380c0e80c1181c010100810301c568400d0000e000a85196842c2c20f84405869107050b03120740c003e200b002034803803510080c07404c242d001d407082c0d0307d00d050314401404206091002c40c81555202c4884030503607005030158081d00c01020700c003501249000c0d0011050141c24403003424211900a81031521420111003005183c40c80003030514040d42d0f0050010038a61180d14000e00c1a004044070580480329420400c2480d0354554415030144e5811103000c086180d48105100404100c40050000120308009111f02420900c000f00ba01041c90b502c480342c1e50744203401800440e00120411030210b1400014044a40742c0446680d410410b29601107180d81080d5807002d980e400011282180030304048882c0c3c1c10f0003c045800c0004140c05025 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 346436627 1250 346435377 346435387
    0x515070503030c090a090507171512060f01050d0804150309080f130b090307061b0602070b0702060c160204090c090509010905160312210c0503070f031a24 68
    0x28058240c0c001c41c41141c0601c0c0b021800040c0a06c42d8041c6d5401110580c850005161081c4004103206030010500070110800d1000340245448480c10303d880c284c8403070050180e906003800e031008003540681c044c621a8944000c03c00214040d8000c4a084400d000c0c0340c00e4000307081d07a40a030041e01d0070480c003904064000c500420f0884102e00208050840050005031150b2140c2250341240101812241c1617402060b0912089016a01ca402d007075034a40e21801348c0710481d0340c41d48140d03841014221640c1222100744105d0b0794040202e180c000c0c040c4541d0900706410080f6880d00300780740410181c072480c0c40d51801e0342070107404e030001b00107854080c0702440f4500d80055a10b0203060800300840311482500da070b40006004c0008640d00341c07030788010548920094507030121a00403030003089244010428070a00c0500901d4401c6031480c0041e522041e480780f802c4000a8214140c50030700d88180f40c1440e1045000c00820300c5000e09026048dd601c40b030200c504000300c4510506007505281e07880d40051 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 346437877 1250 346436627 346436641
    0x3031b0f03040b04140406060e040b0f041107020910052d130606020c060301050d030c15090303090c080a05060a1a030a0507030224030c250b090105100f051507050303 73
    0x100030f000f0303145c40c003120440c542908410b000850f4464418680040c101201c0022a480d03c1d80054001d290010189008038140600190444a6031741120b000390000041390303411800d1080a0503484114101441e906a24080c0030882c0358010006600d28003000846031031600c40c5158009040d00d00190441c043c0041054520000341810b0103410003620528511040790301c1c0501c03c490503900701134114160701031a56000d8584e2124014101c0f9940b0307460513149407a503001d20400c0c030841c2c000d41e00480c10721401e0805009800640d007010000d900300e5602d0070089140001c94507009400f0744400103800d005001c0e0603421103182020380350305020781e088510611000103071324000d590080360180c070808401995080a40d81044c855980c128040c00054200d241c4000500603003510100c0380e580c1e2001060311982e8451340400c0803070b080004042440062038091240980c003000089802e100503040421a10030110584a920300c86ca42805001d0981070801003944c044507480411a034880c00c20030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 346439127 1250 346437877 346437899
    0x6050a0302071415091c170c0f070b07121b1805060d02030a050903040819030e09090a06050916030215040906081c170114120607110f060603031b0f0304 67
    0x5da44529907110300c0014442240c128001030504002a40f2944864100c49003030b0400b032603005042c1d030030124050000401c0300c00c15000802c0400e2091564005500e08404085e0125440030429050076103010b50120000c00b030f20b0303002255000f031401c2c04046a05082d90b50b601210782900503580126000c102e02c1140101500a903000f004086000e0109659140a140d600e0141d07119036407480c5e1184c020400d60038030540c20082d8180c000c0c9041d0b10741101180c04075003840c0080c0c801c0c22881c0c1c0aa080f080501000b4450650494407070005000e00c0740301d448017010703c510f5501029105080440b0b03c2410045503200b254000d04010f007051090b250744440740c6446500390004000c0f00d06001d0010340710b040c880c24420030001e03031500c207416090342881d80400078a00c1d20034016400144103000c2107002c802c2084070f030380310384070903503554240002143c1d003e07080000d54003001006a10040502034255004010b0306c00404218402901c080480801c082c5400c0011035043e0f02804002000f18401c0da10b8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 346440377 1250 346439127 346439131
    0x30406060321030e0a08031b0708040605030103050d0c021003020a0c050a030809060a090b0a020d0b030a1b1211190306060e04141506040b010e06030a09060c0906050a0302071415 78
    0x29201041188551385019499150300c1c40d0081520004000141c0c0101483c904104203030f003c4010705007410101d075110242e81d846130b00b02c5008201c1c0880108100302c01000074851105e4240340c032503020941079011034211940380056000349074000c500e09140e2031080182120a80d008002c0318001456401d0241c0114402c2c0d40c81403060080c1d40000c0d0750940d0368014030200590009921a199440600000080d003120703d00c1400c0d5a2628103c0c02a594200040142a07000e00c09046015280901d14044400c550f4400d201500c15641003201140030400c1c2500710b600161800004c0c2200d16031480d545011541000b0981d030b10706000030403001ca407425440c0c4150320075500c9080143c80e840140d641c604414812600d00146080041c13900e06058004944030101810902001c8900b6000641182c004072140010350742d0341c0c00b07034400340b0040780500240da41e01ca003003642c1c030301d0708141e00100b1500c070300307101c01f01850340010300201001008840025054214402d039000d68100c0418100f0071141 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 346441627 1250 346440377 346440443
    0x203120f04030f2610030f0b01241b02120601080c1504151101110a0c150b0109060309080f0a08060301050603010509030a08040809030f1005071706060304060603 71
    0x608800001c00750080000b4011245540c5210702e0b52180b6044200c1c4c08000204880c207004400c803c000000b0320081c1707031100c02510030101a0082d6051000c24400c0b55605010428114400380601c6481134006c0d4075034030724890006002c0041001030001c904d10008241d0360f000030340b1400c3c000286030600418082d81c00d04003100c0c1d00c1103141c2e0300e280248041c01940541c0100e080ca4440320540c0fa40600c1130103019106200010440f10f82c4401d4a94058200e240c003c00810f00c000008010000c0d000401040c0c2100220304000c0d00041c00002480441c0d9409003006150f914541c101c03c2c0010841616003848199079407650f112241d030001407800800307458a602942c02d000101d000c0d807a040c010320384611040802907041c00b0541d00100c0702450058400d445480041101c00700a03281400310309486000100100070070650440780c0403c89400511890070010051944039081e11250403498010b101120410740313036103950800f10f00070315565000405888200004001110103029280c0090790 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 346442877 1250 346441627 346441637
    0x15111b010f090c050603070309080a11100e030f0714060a290105220f0b03091b0310091e0c0801140c030609040507030804030f0b01080d1e0203120f0403 67
    0x600303808900650b4140c42c0d000300880e2100c00140510f0801070065584560a403502180711402501c41030640d0f03000980c50400591000000a1071200c01c00001c000f0386050714041200202004166403603019a40c54003006150004154050020300290504044080c0e010360301e960500740c00c0c0e5401402401c1c10301481080001034121744004003241c0309401281030715005c1c80d0403000c0111600c182d0032910340d6201d0044131103002c12109140112000030705003030500d5540e2401d00000c02841c0022101a020303103010340c20076800c1141c4001c03403e2840b02c04522404619155649012451404405081207aa6122103241d20502c40c0c40c51482c030446c1d00d603100030001c0d00451041e83e648500112015000c41000b0400f00700c00c2e090043c84240d1090041c6d05817a15180c4035501c5a0381035016502c1603900d08a4940200180040d03620704030b0041422030001d100b406401034002d00703031280c0726041e40e05050300d002104011a00a004454012112002440003840c00c503080c4000140c09944c194000f130 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 346444127 1250 346442877 346442891
    0xf01050f011a090d03080a0609020403060614060a020706200d020106140109030b01180209090702030c0705040e0604030804150c0314071803110a0909050307020411030c0715111b01 79
    0x80300c642e04a90031014043c0601e41007828035181628216000f8003000c00d0f065a4510001e00d0b0540d40c80603102030b610034000452941e140100303102c4921018903000e48211802c010901e561900028014100c5419052014160f111a903c1c0e020300300d844107507111a80a6032641d4054181d0641c004001d613910324809000f940e42c00c000454040744540801401e94004400520880300200c54205810641180251030010f20741d0200f500c1210580d04d07100507078404a076048503030b00c00b40600409880e007a0703810003450040c10003242d520203003c0c0002e0148031500000c0750a0041480c001c91081c20b10500034051120b8609004000300716100d0000000740110700822400c910400b13071601c0910350f10440c0fa032038508684600d0501c8209035811684a0ba244000284c40743c124000c070794041e130107031000e9030300d810480c01840103880e141040b03022110000c204000d400525103065913178540d00b0000320100151240c0d04200141440700c0c511401c0040070406000d0420507406140506184500900900b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 346445377 1250 346444127 346444169
    0x9091e01080319050306060c160314032503020a021e120c1f09120c090c020604171803160612061a070206070c0305010506040e15010608090f01050f01 66
    0xd00034452001000081d07981c00410580c491005140c210310000c0081d0328191111006600c0c0040e6002701151107540458100b003800030550400c441c05d500325018515008003c141c0e101480000000c03500c4040003044142d09241c800c1182c030360841c0e80503000000414004001d003070407504045910b4072500e101141020400c002160150800801400c5004541c074620200c001c08944010340381c2c10801c411200085c20100c00340c20804a80c001d684c4032212504002d6060140c074205010801998444010301c030016988160a104007410032905980303480110729160300d40c00102c1c3e00310703905101e5243d0540901ca4100840001c581040d00d44000c10610822420151505441404080e181207000c54840700d0b410030040c07200d98402000c880c40c0c08901d5489400401040d001030b90240c1d07646041020b2810a0310a030513141c441000107140e44141862035400c4864140506400c2200d26804210701074005c0081d4002942450b0081c85680340c01c91070408290000d219992207e03c03151141c3e03a0f0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 346446627 1250 346445377 346445383
    0x50315010314011a0c03041e0512061902130810060509040302101505030a150507091a0d090b1306200d0c120e0102030f010501031b120209091e0108 65
    0x2800140a5070000f607190941c00044181190382a9011140070005461544000d00040000c1d1481c2c03002103c03036415421100700403911340d0700325a015901c1a400d0465034480080d40a0340484942c0750311800c002e49650000c06401000c0007510380e03054032103011074405004600c42c1c121401040080084a0780c40342005210181528080c0c0560803104010b801c1c40d00d41c2e04001000c081c400d05000000b90740782d011370320f080382400040c3c4903080c8103402d2030707001e00c0140181c90b004122413810003e164101040c1e00d500080d884c070703902d0304941c001550940050060f0040f034012500031036030310070500d400104001c2d500a034440c21544249820388503414000705903400000e160115502c1d0b070a11078080c2d6620020f10000c05c000d400e000c080304140074202c080d40100e842203090a00090380700e040203036074881c4a038410b800443c141400c1c10b000800e0740001404550a40c403440c6003007540030104001010080c03207600030040e000700b890020084000031600007098450144c8080f0010b9a90303500010352 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 346447877 1250 346446627 346446641
    0xc09090115090507091a07140610061b0813090e1f0b03120a020a033f090803011403211e040807140109082b0e030604030503150103 58
    0x91409641d00140118615544043d43c81032203402c18240b55070b102c51603910300c021801074401203024009000010030880c10601400d01c029800146461b040a413007192601c105409107000300418015203042036140404078804150304000650345d5101080e0b18a0069100b90082e03031105400e012001002940c0050000c0c500e000d202e07940100c000d000c00e20040139000c0101c155034107110b00d4507400464200400105017010058008000f1600c5a14020b00400a10030700d5045848000740f001080182c00005010b1141a00d03044000c0c0d026441c51b540d00805103031a0181030640003100220b840c035404c820801800310f080f0b007190125800c41c01001441d8005040d50314010701c0c180311840c01070750700d2003210100194205c4003d040c00d031503a40c91032030806541e00c1311a2a05201e0640f205550304400c401010b081110060491000c1940340c0070440220f1010207242d41c00340308160000e29105000100c1d40300002401d17900c007801e15085c000c1180e0400c2c1d43d440e407849042100441c1d01e60007071090700d03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 346449127 1250 346447877 346447901
    0x607080c0309210a0b0406090b010602010219020715080423100b0f0a0308090d05060f0a0e0628060504020c0604111212031b12010810060303051206030316050c090901 73
    0x1c0840045517031213494800021308211211074030307885c01c0d0001401d8043c1650203800268001a04d032a40700343d8981011044400d8142075402240d018007000780e40600700910f504035400c0104c01e40d1a68540400c1c80e8603100210700a89114002c40141010045401da03024113001d4414041c11011304100310140c4c00d00840c0a41c00660311a0406c001290207000d804000c0b0000c00c8d0500040d0940c0b112428100c0440f00c80c020141580d08111012020380f08a00b000c14052004140381d14118600007022003101003e0700342ea00f904008402c0450070781c1c00c41d0003c0c110191041d5101c004804c08150b680906441c00c5540702121113100e140390a01301e9800469802d0680101500d9881c480460001e520103444e0844030000e2200d076401031400d520050040c0585c0440450040d0b242403260bd0030b101e182900001c0c0182080f4082010136409829260748060740072410b14152644400a403075481100f0082603207241541c0c59105108000c1030380b001002066466550315600c909600d4200d4583c0c604034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 346450377 1250 346449127 346449133
    0x30a090f060804140c030304030803090601120305250f051c02011a0402030a0b04051603050105060a0509120c091e01050a06090b18090c03012d050d020607080c030921 73
    0x1801301d03940b8442d58403440c0000050301c0a5040d1040400d007143d00030b40003901c0c000f40000c1403110404042280b076004015400c03a01306888503d41d4014050b00c20013091004600d50115014060b420301c0700c10344800f552046054401804c140781541d1110704e041060100d0105080c40000214018001e40107042d45c001a010b00201940d170800c0000d4001401c46481c999450103440c4290701c83d4450607024010340d06012086082c00080101030342d0050b007083c3d002d810240510b041560704031060311075100046030400700d03c2d204c92054614021003256070642c0032220b041070291071105c3ca4128103410b0b90100c1b00510aa80300d0b018003031420346500c00d9400050342d03103004020300300c0c41340c001e8030507103003501c040b00d10031485400000c403455030540700150300d2800000100305460307810a0011003610001c092108042201000103400c5003684030389030281c4803110700003045640e04012140400c0e404003150b500d0f00e5154004a0707403608403506580c082c0c0b80e500e0360402d016a02c0744007510948440002 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 346451627 1250 346450377 346450381
    0x10080711010e012a14070b06130f0606030c140a0806030a081909061b0209093406080907120201050f03040b040b150310050403020a020d05030a090f0608 67
    0x204940c00c0c5580311000940307550702c4840c40078501c020b005015100200980d907020039504090f0701c00e84d61200c00307280028400d03448540a0300c0c44030441030740c5403241c100f045030078a55254004980700c1c1140c241c2d00b800d400d181001200710400c0701d501c00015180950740402011161700c0c01916400030000000106102c14040242003d21800c90f19910802c05010380e04000007503694050320307811409110b10030080c401c54481c1c1469000b00680001d000354030744080194a0030b8802600c21130030000290084554100140b20580c08010360741f0140f1510381c0b20307043c1c00034206070304401034200c0012080c2c000000d440050901d101c0d062050040c140341c4091702105141c0a680c9669206a21080b0305200c13007400f0742c0002c00e13540c5010b14401d030700800d101449031a003032920742c020300802011018103111001a0b007800762000600303000a04618030002941e600d46003000e030724101c9001c40081d44484101c842c1e004010b000303c0944165a0b86407a03450481e40c8480407040e40e100c0c80c0c0600790001c1c000b480 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 346452877 1250 346451627 346451641
    0x105070b091903030c030c0c081c02090a0f140103140a05060f0904140105061f0e040b03071d0703062d0b03071115060306040305030915130b061008 65
    0x11a410808580c200c071500100c800b48910032082c030040030742c042684c8281d91209103405000d8007004990510b8807850740b0f240e507526170885000710340c40340140c2640400c490802c0107450707045603c50400102800b164541d60001c090418460340100103658045070258041d5500038091aa900d82e038514841400e03650300040b1030b00422004001a500c00c1016224030015100d4050050055000301080c5000c00c0240ca051800e40301d000d01b034140240c4c018070442c00401d18001101d0240000d03840d050444003501e80c0020080c0c01c5144905515004001c0c001034402505601102c8008901c00e0720100ca584626098080b14032a203c0e100707010071000201c285140340080d8807403180c0307500303021244071648401110640381c000f19610004601590200c1c11134074810042842011600d1484443e146841004030b42c854002410040034080040041000c03488180440c681d104403000170080c45103044102d0011400324000c00340d0344a402040403447d5810a202e1a05e04490613441e01c240a07100c0d40 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 346454127 1250 346452877 346452893
    0xf071a100b0a0e0d111c022206030206161506051e01050c0604110f1e120a080c160806070f0809010902030a0503040e0c19210c03090605010f0302010507 67
    0x214128200000c2040407840c035520b5000c201d241c9030052004400101451040c086d81186801c00c10482c0149141d9000060b030350402e0070300b140c040075a030640c607061409034004040e002c03682000358415004909480e03002616500c20441501807810f040c0518551407072310086910324041c1c240c002040400d07040c40244481042090310360f06140c1140b4060f000c2c100c1f141408425241152140741c1c201e121009880e0034040d400c4050002c69150007501043e0324210500820302c80e030039000e03190032503104d0f40c40701d010b10502d00003941204080d951594881407158503440c1c440d111a42690316280080b03182d40700010361b98400d4a15440b00b494210780000d05030358204009000c2e020940d01c560391000161010722900001d113200300c00071625207003443c0e0090341610008000f050118001c2c829608825402031340c800401d410344c242240360760300742544001c4400314012071b82000380c200800030300f12703e6140d80600b51440c0981410005030b41c84800c41d0030031311018031010340000c409200190208001c5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 346455377 1250 346454127 346454137
    0x9030209060d0b13060501090c0512180a03050406030507031802090402130e031b2107021314060f040b011d06040905010b0307170402060d0e0708030f071a100b 70
    0x20040d072071101640e0f64444880c0000c443c03000707a11914492407400c01c81d49000da0b82c0900b41c1284144040c041c407200040444c003988040340300440002010030f2280400c1101410341c0d00608092b9120440c040c01d000d8850b501902c9110300082c54500014203c80c440d100e2660144101104031021251315000c10400f0311003d003090b80c0c81804248082008030300b5101c1c2c9454110395001654840c0c50040e403103000440d8498030800e83c1e07040030480c8032000c81c07040d495a03c0c1e406220b203d90313200d46290010961480181104d001818948207040b5541c5821200e918443d02d422102d400104c1d11040a020680740c2d41c00601340407940901011519021440690b152900d010b0a01d505140d940e400e01425a042a480002046400070500103829480169407000501e0401000030908165000c200c11b84602c400054501d55035540e592704004c41403000340000c00d2550122070f124803010740d0810044d800500c00701d480886094040c01303000c0c900044075100c0c540c002c4484280c2e900c0c3c2140b04a543d400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 346456627 1250 346455377 346455379
    0x50915040e031605010f0b0904021e10080103021014030711011401091e020307021506030c090114181302060703050d0501180507020f0a12030b0d050102070c050a060903020906 77
    0x89074080d18030781408001501c201120200740d0401c000c0142002421181035030491440c0350304088000e840c41d282d8000c09034100341d055488030348403002c01302c54079a40d54020038115803103480301c15150502eaa20010040c180c2c0d0003201d50f03900c0c5d5526144190b0300700c41da1000c103e1250500307000081c0124000d910092290714400004150840c0e030110f0050801e100342c0003114526504e446000740d410500c51100d802c942d10035001c501d58109610301035521a00c000f02d400840405500060150700c0c2401182035040c0043d203400c0d50755840e19040701e0307049500e880d214065240c0034241c5040192203140107001e01c960b40341c600420071580e028440340344e0000c00280c3c1442010811455075200c3c41c440c0900a00888070b200150307400d03072021081a0b41d07000e84403000319806a240e40c41200030100307108014a5000c0001c04500c040c0c200e040c0c000c1c2181e1884150320200c40d810070000d0040c1900200031032846004200551a118070401030707201524015880081c50381c8030f040c0010706296100d103400001c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 346457877 1250 346456627 346456631
    0x9020904061d010e0f010510030308010b1305030d02010b10020106060c1b0803030106020105071707050904050a060b310303080711030f0408210f0d0906180c0e0c030105091504 77
    0x21151902e50964554031504d4030264454402c50003c10028407815070004145425000903d00c0d50b01c004000240602a041041c140041c4001850200c0600c5038020000139050307640030440000064020704c1c1c070601350340c01041840c00248802d0701c107100702015039146486d10081c40106850300c03920402500c8044681300c00f461008949800104069070080905074000710b10707454058001061100d540c040c220b12003000c101884800f980040540b080b42500361400030f00344d511001481c02510b02640802403030080002c0d40c07000304c0d580c0800f038800f041c8200d00c01890314903400c0c503000030148503100140006040c00b011515041c820403400c0c000c400c007442100d04141e054040c40c0e6031a0320039400000e40c0d07030281d507400d52000e242d4043e00750405141400a41060a4030655038502e200d1703907040d9400b41d6a00c0c0c4100d01001029402002c1444400d1001d03030b45000c8034a0b201480140c01e010300c080300d421a40014451a00715000c403030580740e014181c803819441e400108100303414007001c601d900907 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 346459127 1250 346457877 346457921
    0x2070b0726090313030c0609060810090203070c0804060e04060506030f06010507140d080109050f010612020a0c23060a02030402030c012d03151e0b090d0615180902090406 75
    0x40c40c00081c4401550144d4115406c884c54000f000d0300c164542c1e80114240100f0070100300300e03d10100b115504a603410314016aa0341d9808030308944140315200024a400300204000c10419400340003240b0b01c0d02c06807020444030303846408000c1b450000701c0e211242c01c0c00032070000d00c155104d074000e40101481900300050510000320103e041440c01a50800010131780001000302140038010242c108204012400d240c2d410032000419030301c665800d502c0e400740c00141c1c00700f01d94491180303c1400b94100540b50901c841d80081469000d210032a0480d051062801141041e00305100b00c80c02168010010700162091200640e00307000d1002160b0b109600350306008d1944404210504288800d40c1c0e40022020311500340102403641d60b810501c00d8060000b0b010707480022540d00f41081d925000a0191105208000a4804140d1a0000f840682003e1044c144030b21400402400d458205000343c0686040c2c00300b441c211048000041d6201c0c0803000424080f4442d0b611281814550282d034090300 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 346460377 1250 346459127 346459147
    0x50a1d0a021309020403081e1810090b0c06090f120403021909020c15090a0503030109051503071d0708061e0102010e0d110d0f020601030b2802070b07260903 69
    0xd1700715038016500c8400000f10800c40c4e03807444401f1315280d00c40340c01c00d41c10400700140d80300c0d04181842201d4081e039092035500c1c4085006101c1d200042402041c410b80c0c42c40401105a1503003001c1d200c02c0d50034880c0035584960040c0100d550010034030048041c0d07003001d103035800300207071910258841300f208c900391500815440818001420380114800042c806a486d40c1c0240c100e14100500748841608450302c07020000d6004001c50b4110340007001d0224894071440094185c513085921180c0d0316100b01800002c0c284e03140300d880d6141039400c0718071780b07580d82c0c0315101030b00c46040c00c0341c5840d03200c9860f4031a54462010802d1200a5810600c000288101c1495041e46000c0d4000380180204124082181c100f201c00c01100120b02a5841c3c21b426a0790058006581c80030b040c00b00601c1e0303e03051400101e41c130910440c1c03c03070407180740740050b019910b14805c1da00003584600b605840111442c000105c0c0503000384840241c00c43d844100d5901c1945020030700e620010080d11441081c0000c011000032 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 346461627 1250 346460377 346460381
    0x5070605070503060906092a0c070602150c0f0d0914061504060807080303060108070c050d0c120c0809040c0c150b101d280f050a1d0a021309 62
    0x200312096250b4540c1ea042c450100038514600604507841004004100a02c1a00c482d4101da074410352030506400c4000b0020029403980240c0c50941d859108a440c00143e240e030014140725060180c00803114651140811101d00d4491903012814091042041d043c03030f407540e036010580d118020801c05070259001700d5600c2c14503505503014010300c00c2c3c0c101c84341480d00c2d0502ca11002070030300100a01c9070302c1c0f40c100340ca41c5030b0000030210741c1440606030001e00124080e40c1040f115a50001c1030321941c0c643c80402500c003042c1c200c0b00342d0f41c000300c120110005030300980c01240001d401901e61401c0a19190800c0f01403c0801c44140421410402e800c0001e043c101014408002e11180418014044024000544130580b009d20070006001000395040d00c4a81b0f0711600d000083e2400785602c210304090040c500c104040740b80c20f8002030f58000824894640c4c4420a680048807040b0308c4540e27030b10100003040d00d104aa02108041a4049096001d1650090262041074240b040d8035540d1803c5201c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 346462877 1250 346461627 346461631
    0x20f010c030e010c030204140909030c03040902030a05010e0709170f19260d02130803070303141803030a0c0e1201051603090f030309060216230a0b0c090105070605 72
    0x3007a11052404030ba440c0c00e0181010703080e95480c0443c180761500014620051050100c24003500c0440e0205480602c20b10840d407200c0514402c403035860341c1d0303000a00c000f9482251150b9906203804000301e8404960000b4a0245491380d9908119070700304181c0d0360101051410440152080724070582d1080d1090003102200031201a50500b02112403c085040520b501203200c4400c04508000041031540c40565048001002c00113854501450303d81d20049265000030316240f1003c9000c3d0209a810303041840c00100d80c841094031901d40f6015800a400d4041100700c50b60010300004410288950104241039441c1ca069a1028919004913003e6119813910140d01c4c0d44803810802e0100d44c1203001c05100c180ca1408001480b0261500c4006011005008003010344a0036080144419a010341d08038202c0d1580c131095040641c58041070305081c0682c0340b0034050314020011200f48020800780101e58000c185460181d4a4000ca81101d030321440d00c03d0b052000c2031040c5c01c04924a403007854 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 346464127 1250 346462877 346462901
    0x60f060e040c08091e0a02090f04061d0d05090a0b040b03070201061a070b0402030703080315130b030d110a08070614100b0a0f171005120303090c06070201020f01 71
    0x2600c20300c110144015544400301c2c0c5020711040300203208040100181c58070b90803581d8940c603458141c10a100314100141074002035801070300001442000c0050b07106081c01148140010000e10003401c8032201a04100b0600c0c1c0e2040c3c114101028000e030083e001442d41c00030042c045040142c94540b0380c2c140b60401d0300314a6030200c010041100780c5409105101c054040060110031100c010b68007010644150031008040700171410100d402c54408009035009954030203d80c03134a82c070300040403584281040320314a228403084940c4d0040500d030341c425465034a0011713002d0117262060450643d6001090340342a2807a1007084008000b0441d4500500303038031886200007103003040e2040303000f04500b4005406101c8001e09040100710071180c14088410050513402d000508404224003610014064070051005241c0d103010401c151904500c1e00040c0e410031106c104043c007007181880d9507404201d43c580c90985c00200c0340317149407504402911444e44144112586144d61800d11030944030042818 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 346465377 1250 346464127 346464137
    0x209010303050a0225030311031303050c240403020d0203030f0706051b03070f140c030d02040e25230c0f2a06090607080a0801050a09050108060613060f06 68
    0x40343c0926410301440030446031102d03050102c2c2502103c1e220902005100c01024001440c040b050715040c04d005035420b25003c403044c0412541d03a418015246c6007250101441303142c03c2a0618082280b0004402107420042840c3d41042c2c00c503424010000410402642c1c584410b0001c45041d0342580b000749991846a032002c14036007085100e200300c2035100001603503080f03401c0c8100070486500003601c05154256290543c3c800e8510346484a01e03126006455446000010f60044c0c21505500100101c54441c00c1e400f805a40e51907503100b444014180040480d0141850201106c0c0314881002c14000002d80b8460318420a600210107070307105015201540d00301401700080d021042c046c04001c814107051190030110100740342c2c07205669042540303201d0364010895000d16201c010540301400d5005c102996200d04540003d08109003d101e07482c0726000b0080042030484050058504031465007009109a484010030030442c0003030701c40120781c09607984000298440b006613200c0300519040e220 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 346466627 1250 346465377 346465387
    0x204050a240e0d0605102105060f010f0605070501060e040b040201020607020c030c150d1e050a0b010504060309141f0e010c08010515130635010b09030a020901030305 73
    0x24610040103112a141c1072140e0a80c4407186a00c9062007040034aa02103070000d2036603200040521071070780941101c807000b9214444040807400408090500502480856010707555121004207001d100340641403007842c060380301700700d1540100d001c0c3c00c010f4800e00010841c951202c400070703100c1000322000e454086038801803209552b0180240b541202c01803001c0c0c5440c00d80d200c007207a60364407402d040d28020000d4445c3c08140c0d280740800d41c1c605440300141808140c01206031030096501c5449200130f182e00c0e120103d80c03404464403c4440c40c2c0c0341a10303220f0600703107814815001032803180800e540600e44800048000c41d81409450751f40305c580100104001008105017007100c0d010f642c00d520982c5806a5428500e40010960313044a00c2202c0e01610780c4440700301310009014514010101e11445100400c4081e00451068dc410b18100084801840301c114a004c411446213200c040500ca1032006000b00704802e0000c0c041e07404003804a231180000744d80032483e1400240d20a0b0002003000c24 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 346467877 1250 346466627 346466669
    0x2070f030f08060105090d0f0b040c1d01030b0c030606071401020409060f081209010c060507030c0f17060f010327060e0a0809060310170c1203040f1403010204050a 72
    0x1406070000d41c054604520740d4070b4154006011361085841e0603110781040302c56101004000483c4846459000f28111468141890304001c60401400384803100031030b008485911b4402415124100c82d0070000500150f140c50616680641c8054031103504214100601008516100030030359682240d01c00060380c0c0c40c035181d559022245150040c2503007842d10081000484800220250444404000140e8506940e40180c03025010444010400f0b0304110130080160341540c00003030200006c0d10b510380b102c544075104540c000cc11036092441c0000c40000306906040c19074992028002c10b04000640011840c4114500c00b5107130900c14440b22607010741010009107001e22000155a00300400d1100c0f10341d607500f40c0c0c43c011011654081c03a0013100081d05041081d0202006025180103040006070900d5a581c0b100c1b000c1010342e02540c1020b001d46808030001085908880c6416144080c02c1c0c04c08041215a14074048160342c150740071310020606a40d0406202c0013000038070311042d050b451000c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 346469127 1250 346467877 346467887
    0x3060108041a042409020a300c0302010e15120c0c070f0521060c03040609080301060804120905030a0f05010603060c080a060915050d060e0f030702120a02061e090402070f03 76
    0x1400c0341d44e041d410700100c0e4005891b5052207801366041d400c441004840706035900c90243d149598000720400b50b04000350188144d00451000f0303a4000e0780c940b01407550031002c0c44400340b240d1070280c1070004100800540c480320301781ca0380d03040b100c17814405203000c2d0a01c000c50714040c41c540040301c0b40700034034904212611380007130300407218103001d000c1000756140814503903200d080041411380304503c0000083d04001140d400320172160340c000c2d601c9440b541c4514009001d007204031422142d00812040c82da02e03080c06030443e10300700c450080091046200c155a889402c076001007040701c0c29902e480012000442c01e020343c40b00b500e202e90742e504041c035040a0700810348500c3d60040c0c0305507203413a0081e007902c511131a100341651001d5900c02d06d405140d10b070040c001e0041001400300703801810902c6d24044000300090820038000c5800e41e041c1c509610690342c850f245a400290301040400002cae92808280c04544d1100305010903c40c01d004d12500441c4c240e030300109040343c4a02c40d24442408140e00302c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 346470377 1250 346469127 346469183
    0x60c1106090706110c2d0612010303121103010909020105070b04030c05150702030a081503011a01140405090a1107050a0308040303060b090f190b0409050f06030d0503060108041a04 79
    0xc078000c01c00d1203080e00204035241052071803c1084200d0000010641b10701003002c1100c5640604015034032a001c01c1103003610761003030200f140003c042d0b60050038181024001c06011310707002501e9624692078201013a0040000320740480c1801001c1c401000812400034900e44210700980710810740362024a4030506022901032040740b208010010720201c198008180c441310310304c0c0e013002c13402da0f100c03007050410741c0c48500402d640c55803c0c40201000109001c0c0004407464003a00c5a608045190b40d0400d0140110f020b102c0d000000b804c0015910718080c3c22041d50080d035464030525000d041d4440c1811700407518001e80c040384080040c4820150b243c401e90340104240c0710110300b058407042c00105c461240c0120310f44980030900c1904122101c00071844028045c0f581c4540e6250744c0c400488000c2c240031660b102c200200300d80018501e00b000300389041d2170306165440526680d6490015240c8110140c01912036281c08643c518100c82041c212a020b24055080f0f203242e092015800031404c040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 346471627 1250 346470377 346470407
    0x1210050c0a090b210402210c030d050f190c0506091c080f0f1803180f090105090109020c07030213020d0545060705180402070f060c1106090706 63
    0x30400032881e40c40f841c2e8004c065103040c80190782c04103403540d00001c2c1602145007040e211421680034001031610700041d1107980241c0540c1510702e04101103105071103d00505240480c552410010407148003452854900d000f01242000505480580c84143c54410201c8111600d60300c10504018048160f43d9014400070203442c05003010f140c01c0c1318200005102a201004080003200403a05c080d80d208064407209480c04110381d11078003c90b0440b00184610040903000d800e62f1110140300d8103202c100c45042c2c030006010203803e079107800c0c0a04000d41c4000b841140d0390080380c0001c001030b078985e0840209107840d5600980ca445c10751201104455014003016550400c02e940840107640c4c011140308214441d0340722200c5505a5808030990550019250505000303000030851501d0300a0040c0c6100038116200944000300d000500049109140300940213204105c90180094a50b40210785040950304c2d01c91800500525203d10f07004090710214140c0d001080c0a0000c0369104004000c3c02003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 346472877 1250 346471627 346471649
    0x8060f01050d0c030803271506030708120c030f040f060809070510050924070c061418040b0d0605090d0302090f010305061903060f05090303060a051210050c0a09 71
    0x10386070340c03041e10050080c8002040c0c000c5c0400042c00c9415030003400d40f8103d00c03820300e0702c20200590102a80300e84184003200c0695411502080242c240040d2420948041074020030184400c0c04c00c003813842d00b000d000c1e8000e611041001c80c1c400d20300100038000070165105641040c03400c008014011900003000310105a100e80010000fa99a000b880c1c0400d8009080944d03445480d01c02041c084103a07100741d89042108800c81401801040b0b0084c040503001c0c01c80c040525031524401c03980d074280088900d800749014406911111241e200031440090018030000b102011200410301802c1140425980d00750b8540400001650070712184048000c14079003140340030031050003c0c1e20700a06484541c10190380e0f030006461034a8188076074881407810300040c0d40c841d43c0d0346072403030262000004080140e820000801d41021000040c1ca000b903d006103405203080c244001e001d80c00c5111007060603039201c0e0b580044045443d0b4442c05010321100e540d9559500d1940d0710140c12500264440000d40b2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 346474127 1250 346472877 346472899
    0x6090803120103031d12030c1501060c0b0622050a0c050705102409050601030f0504080d05040302070f08030c16031505130b07020f0106080606010f140c0708060f0105 73
    0x81d0308100050550b40e00d401d2151010b402d041c8800362079403002040319000801d60b0300240f0042c000201400300c2c004003208803a0881c101840071000e420080c460940819140450b160000301042012984244081d09030a02e004601040c0018940b0714a05500c01598880c14041c000b44e5a00a54007101c0a505029107041b0b0a076440f80e40c0c034407100300818080c1c0d69070003111513041c2d540e4280070414007106c0c150209054881005038002c210685985011030b2904d404410720f20a01e01034a446140c015840a00b001c0840c1c1040000d00002042201140607200000c00d803c21058040c0c4042c00d0000015034903a46610030040c40e061100c4040300455200c41c208200007000050090740e500703003110300824103480d43c0d81954503c86071540014019608141000302e003d500244d518280c80c3c5050003072200c2c61759074600c552940c8041c0c42d80c500107404800c1d1040024000d41110018400030640d1502d04401a032400f410a00c19030005c03403098000c40c040c0488d000011a82c6405040110340c012168 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 346475377 1250 346474127 346474147
    0x303200d0e0904110603090d0813020609130e0601060203070201030f022a0307050706080603010b01090501020c0f0d050304030f12050307020304030f0f06050c0c070902190309050f0d030606090803 86
    0x41940003607000d00ca50302980018080080450b01c8030041c0342c01900d035640300c0c141031904907101d41c0c5035a440c000203002d060010b8040000c007850060455009040d01d882c100c041c80a012002c1d440311010190b80d911802c1c5681165000c00200b03000b0f0003281d02464130340c80244001011745100c0c50741103141e1401844a511145407030f050469064072035418041a02001d04104c904501403070002820500800e0400210942c0007034040344070307041c11030081026695503001540e10704a00d00540340183e1008120552908046000d1a41e000008050741403001ca0b66070703060f00e1903000d03030011100b400d00d2a49410401c00c00c0500e0b01d00800040c20480e0841c44c0149000350342c1d014911001d440c418014040c030080c03000c11070140340b5094120b0f00501c000e00d08034680540344c0d03001c08003a4140d4840c0640004c1c1d4400c071071081d20060420700c5c5007180d43d403009550880107007401c10390980d2503001d2000f030030749560001c00c0b52070304001c1e841e00d0100b28940ba00c48003a254102c5580055210f8104101500710 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 346476627 1250 346475377 346475387
    0x10e030c0f100c0c0e010f06031a0105030910060b0c06070c080a120f1503050609010218042304060c0206071103071b0906170105070905090115020c09010303200d 71
    0x1510060301e00e042c80c0c03015160112038109600d403010b840d2084410000c5003809044070745034181c40c8450420101c0d00d603aa01c007107086920181c11308000506182003000103600c980011604183e191302224440e111420490301111080c0d403060000341c1001032811102d03682032214541c4000c50f4288250b58281c0c42c0c546032510310525a000040044000310705403c840c0c0c59003c007030490f40b42d01d010429040380744582000c0b1812400281d0f0148140000548440014000c0701c14850b4008c042c0030140200d14107020251980b0b8000c1014003070a01680042e00044104180c802c3d8055100800c0050300208080d0610402a00301d82c10020301c1e50000b80d2142d000821115142d501c4403858201d0520707051004031680c0030f07401401d400d0f0705108000684001e05041e00d907070740304c440d002000b05858600c03041c0e039407000c03c0c452503401c00d05100c0104011004076580c110f41e9a1103005941c81411100002104114241c00c1140814802004541005408407400d207500f00980002c0003495201500541 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 346477877 1250 346476627 346476649
    0x3201c0b040603061a120c0307060c080702030111190f0f0c051507020a140a1e060902090a020a030e06040203190213060e160512010608041a0103060209010e030c 71
    0x420585401812009481c0c581c088002140c10607030070044a0180c4401901c86544076040301e00c50181d012600d5890303440411100b2694130002c0003424210b19150041d0341211020f00b082d12030b00400c0c401e41c009a182802400440d045050540f40e4130842c03580202c1c0712620510b210000c000b0107400d0805644e030412008144da0410b4107061080006034a4001d14010303c41c994400e0440751a02404400344d00041c604264603c501c4a5100c03082a0280711507440300e100301c0141146003605001d004055207140366102c242d00035580843c10384400d4020803124182524689903407075000400d822034580c54425010801010000780c045802c10b42c000a41e40c1c545903071036510b6100540200d000315a95145180744000c882c90051020355500c01028840507412605501d00115008030403510030b10a40846180c3e0882c01803d108990034508101d80c840f000420858041c1c10b0a040d9990160140400a0003144101e41c0540e8440480d00010f02540c0585c00e050301903031203c4107801055403540c05a40d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 346479127 1250 346477877 346477927
    0x70e06010e060702131a040609140402060705160308090103050601080f0118230a060b030c030c0f091809011109060d0e01021b070f0e04030e100e060a0320 68
    0x182c5505107400000c000705c00040e040303600c56207802540c1c001208a2403c0c07241c040c03800c590403c01c041d0b640040e40180c4a500c07401e8640348001c20006001840c00802810701d1900810444450340c5603680d815104189a070015503182e400421034542d6981e06001d0a030303014100307103001f52081c01c2a446032500380d030341030040c10282c810503000580c0000360707907102c61001902442e007101c22125045108143c003800b030314044011403c200e004501c980c03003807044034010f4040da41c0781459503407402c003445040d07003194040301840801000020650b41d08c4410041a00c090200190f58509081d9200c5084412140f140300d0894004d2042455a41c3c0312000d441503c02000004221b03c004801c0c00d41c028403426a04a054003413200d820000a0300c005014001e46400343e000407207a54507840001001e40080350000e0000d220581c1450881c20700d00460300d611903041c2040c64a100d412000261142c00c24821400026541c1180715068010741c0454001c8000d00420f103494484855020401d40246014070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 346480377 1250 346479127 346479139
    0x50d0912141002040b031801090b0c0915070623010b070206161b17060f0a230a020d052a0307050c01050a020a1d01020c0f01090308030711070e06010e 66
    0x40a060414442d2003202c00b00240c04550b101d03254003c000706034000703440b82c0354030706004000c9510060051040544c4550024103910a0b55107158a4511990049030040e030894406d0380d86500750032111018198143c800c080200d400e00401801c078800c8400300701e10f1414002c08400401034000a50f080395070307540d0103480d080e40e50502a9010040e0320b00c03084009000e412700c041c8185220481e503034000259400c0481d082c2c41c8280300c1c6562030b41c883d415100700344400c9440d0081000108154001d0200350a1648029484c04103102422030000048030025290f070f0300019200c0881f102840795581c0480e8071811100c0800440b00e890f940c0304e60004078000070240010100d400f0901039000e507000411010001d014034601001060040d400038132034900407440b0500d04241d04a201c501c0c03980301e098107038000d03c2810b079040100144200020607450600c8290302000c00441c081d0001140306050a460b510602548990220310b0141c5a0b0b005ea0802504c0c5c00a0040980e031265524506e03034021620 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 346481627 1250 346480377 346480403
    0x9040e161e080f030c06090109080d090201030905120c070f0e01380d050c03060904061a03150714030403051215030a110901120507030803091e0703050d0912 69
    0x49101e01103202d400034070b640e20850103102e10400c40003000b0500e84000740107580c29920703508030300e9003695004680180031581c00c0c410071000178404ea20040c06140140740101e41782c28280c440504104505805c0034090400150407040e0800070482000181428150208000d19103000a100d1031418058803a075074503410140700741400c5071400300c1c03c9030440c055129002411000110b40a50100d102c0030342c45400d00d8002118800c890702520f109210144c060355040d52103580720720091504100b10382081ca0040c5911580f80c80400a292031202c107103156a125050102c80500000c00c54441d07407040038410000c0100180d440342c2621103000804081515980707680011260407420000d080340c051013900f504800f13101450400740745104d810303100c00d6550390b2180040c0d0508680c001001d8001d40c405281080091a0800110703808543c0d0303803d4500c2682c015000041990b03a0070414035142e03110701000d00134000d051182000c04000d500b44509414030f000d40009000c2c0c808500600030408c170b406 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 346482877 1250 346481627 346481669
    0xc0a0e030d080a0606030c0c03030902032a0301110c19020f1f080a0606051e040806010b030411010507020117071202040602030406120e060414071a09040e16 69
    0x11061548000101500c003140d82444004084030340c210f511124003402e02c41c0c002001c130b00034450795156920b04e80d168103981105032003d4016280c0810126010700c2102c00700d41c80103402e0112020040581840c580c401c45140701050b0039241c803000180c422140c208641c059540c0700249420410804030b281098103005800011b65560341d03003140e6500407441c080000c0720003003c4802d0307118500386525918000d0322a100c511085811501800d004200100b00e010138070700c0000b04020725150009a29494962100022801d166081c6c0c05075900007000710a0004100d0f5081d102a0800000c0ca0540d04080c100e0700001d00d1450700800c80002199071001041c00c052188903120108060104195500c44e0350348002503413036005e84035078000076120b100c510344e02d03911f68041e2000c2d031502c1c030f0020826070b122901c403070300070204550782107803540f290143c005050b07250405050b94090032100c20300e46035800002030106860380303ca06610351383c000240001341ca6082811000503160041200400c1c04200340d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 346484127 1250 346482877 346482887
    0x1060b2209020304140105070905011202090d080712080a110a1407050706110d0801080d03150e0103050703113c0904050303012607050f13091406100305060c0a 70
    0x1070030100d08540000100000d01686091414060f45007400800280c1c0c4d40b03240840d0000b02c9801810b000034000985440000540e8001d0104210002c4c11030b110944140c1da6103881d40d0180004840401f060040c4c10070380d6070081036441d48040390380b805010342055009103500e9885078007503c030306101c4049000c810b41c100f004244d0b03078450383c090200d0780100d0305c841010340480542d156143c0c16110b40281d40310b156100301500c41c101c411040060a034546d0b82d0900f44d0143c15603000500041008032400034050000129082c029402000940595815810442440350540000d1b90003a0905580c01a400780c04c90762090789080d584000e0324034981043c4278211040080b10340075a20040b00340c184018000080006c40c100c0d540003045014045402c065003011507420b40c1c800d03c894005c140100180d091448850060800007407006003452072030040e04044440070071044c2c500031045051801c10309810030040d44c000c4110010401c0341d524641e1941d644041c000d043c01c0d030541d00401c001401c0c0c5d01403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 346485377 1250 346484127 346484129
    0x1809080904051014040b0109140612010f08060604060506030601080a0f02070818090603060714190309050c0102030c03040306020d0905030c0604030f0f14132705010801060b22 77
    0x28030910503400c160300c007101d400485000b00450702002103100011031906101b0044441c8060710303110851407800e2040c3c8040580c142c80709400c8013041052222191086840a011b0800f60000200190410740c2c0180f0740340c0b0003410f40d4090b84c03a0034010301031951010280c076032040c8240ba11040c00d5030f4440b0f200001e04002e04078804500d0010507010104503005000e8200024641701c6030100030003a104016a8440a072450703501034220202049180f03100c1d40300c0041040c07465903903d244c100c011182c400034691070b04d0054000390f81ca45080c41005420312049040f600248029810445080540e680700d100e075101c02007003240d00052140c81d85c51150131500c80e041d085820380b0384441400880c9526040f0884040780061020f0311900101d50142260043c1000c80340c1d81c020950305c82c0d4401b0f28041d408410790f2462072141c084000380c1e0741c03102d14150003202c4030049510305524100c01c181c0c0c2510f0041e009044c2c90390411005214810b0306c6401c1d6054603605013012403240c0042c0b0070341d015030340c12 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 346486627 1250 346485377 346485379
    0xa0501020d1a0a0f0b0315060d05010302090a050c0a0c020f0d0c0608090604030f0804060f0504050f1506030c0f190b1b24071701080607020d020718090809 68
    0x30455026044840d44004648110102802ca0002c0c8a42c20080d0181e00c5004010741c0e4800c040c400c3c41036140d00e001450388000e0300e40d08002000035007000140c40c0c2c1c0044000c5400584c560006004504008541941000392800188900d08103410700c280b8a0141061400400418010390720540d80c0e0a00460001080942040c4040480342008d681c412070074024407000c6410500070a034044000211184a80d030555541d140c0c4640c405000c50b142c9801510aa0324140c481144046880b8940b28660007a403068004200c480181b2001034144a0000350721080303860814100310300b948010414039030b01002150303070340240c200c9040050b01018050034451001c40040e1008550780c08000004e25404045078040300c1407544490a15a441300e12000e041d903280d5090160703003da20080d504158000c003060420801e00004c4d0340b010080781400f603001c0c1031607a101d0702c14440c102b50103004070600502c3c24800780040d02d04103400b0f59031800e20420f20396001035480b03415100707001070002a11140e02c8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 346487877 1250 346486627 346486631
    0xc03030c09090f0b03010b06040b0d0903091e140f180c070c0b070c0b090f01080a1d0127030c0b071e050a020d02030306010e09040501090f080417150412020a0501 71
    0x7181c035800014134078030f200c80e40650f180611914107072410b00162401c1b20300309401c261400015101181c05800b81c91021810f10145141c046004824058800e009012851a100d01103103488041c85000b0369100b5501e0003030b0b0b05c00c2c400c0e101d1616003c0c0007101000301a410761055482d480015000c2d031041c800c015120417200039020500c0004180105400713405801075020b07150f2140c5d9415002d10400c3c840d594040c0c44100600751550040d2100e591015603a1000100c82050b1901c4030903d54025030030b0300f416513440141880d010481030b010080c000102c8002ca440d84210ba8024000100c07070b40c809003440c8200c50004049500c100e50b01c1000d0b0000e65403000c00c3c0b054000c0054400e81100c10400051b00400044519651001060340d1103404141d4036016660020742c02c0c030014080c0600141d9840d52249190300203d6030b508007034091035102d550540c1d611407500c00400c0d2079561100851180390090f4841c0050f640003020115040b90300004c2c0a030700008540c1c026031810121a00c018440c1d4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 346489127 1250 346487877 346487891
    0x8100509101a0d1b2303070f02250509091b06070f021512070815120f03031e0a0504050d0e03010912091403030309030708030702031c0605040e0c010c03030c0909 71
    0x1184105481140b01501e881700c0381e42210112401d1407100280b90b07140e46036002170001a803010b200d005007104030a59801941d00704245220f401400380900078000302d5040d00840100058101009000d82c401035603c05081c03c02c01e0b0314510000015000360091141c02c01040a0003403000100780380d00002c0c0c0c002c104540d482c0c0c041c0000300c419048000c0401c40790750074100003045107004e100d0242c810800b40090304191303040e410800c103062003a0140905188102d9210202047c0100002c50160510702031a00d49900d030250b14035416400140080401802c20041c08002903000403001030b8810b1504203c516030354514003090040c5002100a044da041301d055407500d83c2c0d086040d190590b5241505540c0c918004820305a6a21054540d04003035881000490040703852080955004052841075038509095180354044425440c55181070540c1d54201c01c000c180340a104080c000942c0c000a07002c1142c540c80007814200403484050117154454410298017445070314508081c160340b601c104054 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 346490377 1250 346489127 346489151
    0x12050c01030b041a240f191403130807050303070e0405070905130903090503030409020d052410031803020102090306100f09151508100509101a0d 64
    0x105400640140420301d40005054241407500600c0b449420001c9800c00010503401404503182d010034812001600c3d2603900d0090380c00400061158800b031191031510380040105903010f800d5006940f80074044040f120040f07144c1100180c03030744807001c0c0480031401d04c0301c0d081400f400d12510130000c040d40000010001120b4010060740150301060f2400c000c3c0b40e0b5001401c1d19448510b0045940c4900641c3c822200d540c1c0c0754024404440c468908040001d54680c0424510341040c2c104504a54002c0741d111800c5242e41300e4164010351481c05003941414640c075044030b486a109509015050103560070040c40e02942000d0305400648521842c80403041c10001d000303401211003103209014090114503040c034070310045000c0d1940039680c10441031070300c002c010080845c0400496071000210000441001d9101c1d0440f0f0412281c0710f6921614000d402c0c210703a40340640180384901040d0041c04601d02025220707801749d070344001c0007403100b0b000b40041001501801c0014aaa5801c00c500700d251 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 346491627 1250 346490377 346490383
    0x3062a07170a0f03061e0b030604061e03050f0c1309060605090709030b060a05010f08041b0e0702061b09041113080f070605071e1104050106030209030d03060302100305101205 77
    0xc514007030744d010844280ca4803507601041390002c6c08411a001c0c402c400340500d110b540d000310b4012800820015500ea9902c1c15440e0000d20066000900380010078100705002d800e20a86070984070f18005088449098800035050308655240c1c80c00c0300d55600c012008010543d4801e40117040300802c2c1d0882c52900401c002c10200e4580011581c2d640068080781d4203090420400d415554161190328400340784000c1120f01100042c02503e2455201300c0c2200098104c40085010b046016040260380c9401100a0314000000e03100020903440c8210810484006806590200f24216008500240c00d203007000d200d4000d070440e04128101d04c00000404070783c00904903444100c1740c4155661036542da90159101d00583c0e4000e84048042114203101c14042c0079a00400c0d4450001901c1004215000c00c04440090704240e000c203500017000c1030300340344c2044607180e111020b103414040c00d800c50780814010315080c0f04503000d043c0c50342e020030321001500141501a148800f231b49140404a8146569 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 346492877 1250 346491627 346491647
    0x1d06190e0117030306060f131505120105011b0b09010e06090114090604080f0a050f1908090a030914060c0f0c090112050c0906130204090b03062a07170a 67
    0x381d1407849801003001c09002000744e070301c16140100400d0030310548410540b0b145c0d020040c200c40c441e543c4000824000c4c180c01000300919804d58031552a411448010700a0302010b0b003069040c402c8644082620b91100320784110b030913078440b004a44039120300c0c0d042405000440d004e25054060381d410004a410158003c615841c071407d008105521080c0350b09445000a503005018400c08114100b40d181c28240145044c2d807131032510500d02441d494141e03c06070440c6644903c000703103058030000766580c08807400c0e801200b0311003e00340001c80d03540d000e061440c46104c0d0301c062030145480500107607910b409a480d034141050036110084d2560081940345c00740e811610f84182501c10000c1280e1320000da030113022a0b03005000300303c0850110200885100014082c036448100c41c000114544030f40c2c009000200070140021840da40d00c001054200310000b050340064040c850300c1445e0940f554104400180d000c030054582d103802c1400c1412035505861403004003c040020000702240c0d00c00d03d008 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 346494127 1250 346492877 346492889
    0xf020405070302121315021b07060207060e012609031b0c01090506090d15140c070b01032405040804150903020603011e03020a15021005011d06190e01 66
    0x140e6035026002e90803409031401000c400ca180c00c0001e0403200b120b6280381070030b502480c1004500081a06041c003642d21145502e91142203040031801071040400c15600038200c80e001500e169400c0c0b030001844850406c12003030402142030080c9140c2400c0140008400c0400040d6041614001942c96a607a002d800104410340340d01c1c0b4550140c80002c2105104850b050f03450400c210310303060400c001e0313400c0a0390b9558080891018280002e1031401c0b02c0c0310720040c41a001c00c02c1e12000c20310b2524540020f080140e00241042208001880840c289064a070b019044a10440050b4403a8007200c0f00e0254107060546000c05000611a40b500a0001c0700d9061442481d800701c010340481d00500507210081d0000001c1c0010f0040000c0905004280040c06403000c40056480c2c0018808102940c44012810301c04503050f500b00350705101803903181a510805011951400408041107050010a0700031605010302050869032005078050780041032030407140c2036030348405100741c80e14003e10543c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 346495377 1250 346494127 346494131
    0x1807050702191e150903060905010b10020f0c04020f03011e09050403080604110702011d1306031115070506010302040f0f094205101203080406050a1a0f0a080a0f0204 73
    0xc141141a61440700042da591702c01403102d2035a521200640b071003030022641035484209890341e41d15881d80c034044001050b4000d00c80602d0316803c140c01c1c01146401680600d0040100801c2011907004807411180c110003051201042480c0410b0b80030002d402c80da11450034031003484103141d4490480c82c001d41080b03804000070340014861701510310603030740000e0100320540442c2200140b0074004001000d405488000f00100c0d440d0b4a0045820a410882d5841c1003601c9100880c200b61780510b100e400c010400c1032800040d901e54a40c1c500052000921680c0c454500c801080c0254011604582c000f040620642c403c0d440d0150002c2c001d2002004094080c08500d155014117039600d00c002105240c0f801405814034242d0000780c0002803040d00001804e1000161001c0c03440d0508103014045d50f5030140604040c0f502c5002c1c2d58001d40000358a90808040d900f14848205020b845003200300c0340c9080c0c05400c030010481c480c1d255031000c0068080d201818003846844039000d09001d04c200c0741 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 346496627 1250 346495377 346495379
    0xa0606030b030a0209062419090b190504030f0807150c050909271b0105040f050f04090501060801060e0a020406020a0201200616020c1807050702191e 66
    0x411401c94075a140341903415400500c910026040c40d40e46280c2060f0003030040208000b8203400d030032554101d0608180014800110036680591104c000310900741503240c100711407881d244e181d80d09030040950038103122503a403000701300c2c0d05d0080742218021641b02503220304410281c209125190009141a10f00751000038403841800308511a9a9081e2815180e150030b01c9000f005100c02c00398010f0150000861307407400510381c030700715800507100804030500034030354442d0f145402c050110024808906214051006116480f1103500307440513140d003503414100d13505032800010094261200050440e5280ca0000f0880f151f0640004040c0d80a05001d09c02c96290110031070103e1140e40300303070401604240d4071840198451000300400104503118401036501c03503035803203080c00000c2e51503400108444201000d03854043c82110244802240c2e2030100030444c0281d4045848000c04072420048000340500841d9603010186d40d400c0680002d038291702d9103580d0b0903540d1519403191884c2d80d007001c082c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 346497877 1250 346496627 346496639
    0x9090f0318030b0c0c0a02040905011d0a02030607050d02160615050105071110020a0b090a0b06010809070b16150f0506090c09040c0e0d12080114030307021002010902180a06 76
    0x7120101c036407183d485035080d52090b8298131160030103000c80c0e100d401203401780000b50380c541c0281e81c0c80030300640c0000f8002008203507041d1409014030f40c200d415007010348000c025076408607019900404900701240e130f85842803080d0000780315000000707034038a41c4504140309001d81c5038080807050700d825140c041080d440d4001510b083c0944e190052030300612140000d41070401741c079190700740c080c607004441020120380e4400c5042c0d24110341031106a0702200c00c07102841040340704160400c50038204920241041d600d00c0791580a103025000d150100050114912003004100c1c0c500c09800450550a402040700d6800142c02e1a400c60480c071410840820002c1c0740100308940034004810b0540c0c90b00d44a82c09100c00b50070002150b409000a40c80c11641644030b800c2c81004140c80b03a010074104440300400a0546a070603004200f102c001d075030034100c90391400400c8074001c64044801c1c81d5a1460404128090a0150b5009400c10501c0c0c40b510a00000b1116440c050480d00d1018828251105 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 346499127 1250 346497877 346497917
    0x90b04060311100309080f0a02070608070203030a1119110705040c02280206030f040212010c170912040611012f0903011515020c0d0b011e09090f03 65
    0x3000c090314a00310904000014900030f510100d611059040104120340d0350b40f500c10682e0482400c4141d00c030720015034840b04a038107214001c042c00d094180003e160030240402581d03808000e1104586642e00d15401e0312402082054401c8940c03070301180b010480403414018090041002100130900c50558042114545401182101c10160340100382007200480c1d500e00d50341c2040c0d181c0b2100c0602c2c40941000d603c80d58021071160707510f0300d034200c903030300301031042c4034400d0200d40703200507540d25102007000d0f100c0d4008102c00075910943c000c64025160241e48034240032103141e90b000800400500010b995400401c0307484441248002001081c85da14800e00318200540c4c42c1c0c0305c0b0051107045008000e07c440f0702401402101600000d4200c0d00300e0a00d00d0622400d402c030280d400392003224200d1007541009661402042660f41d155645c40f6690703640100a0f041c01044100c0031806250755519441e60044801000c100c41d00303000000b210305029590012262041d00081c00940c1824403400000f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 346500377 1250 346499127 346499129
    0xd0206010e0405151b0f21010803030c1b0703050c100903050c040509030c0a0c2115050c070b010e070906020c030a0204020c030c1501240503040201030c090302100306090b0406 77
    0x2003c00762106030520388150422000c0281403a0100c101c4404d14000c0c03034482006800106580030101c2d950310213175180600100c00d61441d6156000f50074006000c803903c0402580e80041d0420f40c1280c94844450900003041c405c0544110b10b0b01c12a5000001d20a00040c2c040c0320786002d66210004030801d40040b50350180c0c40c0805001540920f401000078245903101c0b070b41c00180c41c8156410711810700c01e00c604003107030500251120304440105005c48000e0b480c039841691042c17881746031480b80d2603a641d1081c0c00f40490b40b44a1559070310000715519040e500325505594000c2c6050340c01e686449502c103180d9016070310030780015070301c41e00482c02e18000600c0d00c201403401401003a0110b62642000065030218590404074081402a001c03034050411111b0482c0c0ca00c00054a1039605088844040043e513580302e1440c00d1441a102d042c40d5000401c9a07082070f020319020401142100c010340c0c0fa040160300094203c1c0504d84a941d065506500010079a1032004052100e01014001c01c03040d1421 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 346501627 1250 346500377 346500383
    0x306180a0603440702180601080c07110f0613060309120f02060f04240b030c03031218030f040605090f0a061b0c0e01060c0501060902071e02041d0d0206010e04 70
    0xc0101c0c6142c82d6030400c45100080e03c801c803001441c2044a03800b14500c035203e0441c507031410003200c042c40f0703496030403140c070684c400c24000e409410300c040d6445191008400741c00790f50050740c000d0b441141e50f41b240402c598210b881e050f014000706a07216001401020b80c2d4600360340fa4880d40743e5503140c2d0744c07142d15a40c18204241d8010402e60b20395100850034000003a1044441046625401c4240644075601c1c03540084880800a0a40c030390a0506003401c01010441d4441d820420a880502c00b80c004000c0d0881c0c030750041c070002000c030300501514510a40d400a00c5c036080114001800503402401008a1107003602c210101d050442c0034000148058012000801c2d082510061280c0c45921100c4805000e651819413040d680c0c01c0071850f0002c2a080200050101d20740036007845000d004007401840321400441c034040031a102d40381084007034003000180740303480c40120081d9940e9030048800a40d0407400001d4101014a0300d503070303030380082450a01500a0100000ea004540704055101b550 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 346502877 1250 346501627 346501703
    0x10603150f1502010b03010f0c0e061207050708130f05011d0102250e0412021506060d0f0e0d03060f0512030f09180901020d180c0501050306180a0603 66
    0xb0402084009032031222544904540d43d80d420344a8a940900a03643c640c031000a002a00c400c1c1c00200400c09407958480c0b5003c0c0c0010403074445000c10050503240d1210017860200c2e01d800035480e28400354032801c55414201044594080303001c040740c039806c6040b594240c17610302c3e000c10710b21340c5030482a05441c4880c0c0580c00802c40642030b18907002288000040d10100c000c1e034640c4865610f0a0060f084c0c0701038680c03c82060701000515010480000744c00c0c0d50341300000e424a0310400144407441905030705043d841d00d506000801414079041008002c8021055491154580c40000c004021600c5003003000c00041800043d50700301051400b00c40100c2e440a10714201202d02c03c404076030b00c40903103950003c0c0c40c100c1c81031056400154103800f5000d86000541c0e030b006135605240030f0383c1e0b42c080f035006650410b01c4020000707050898880e0442d0000e0820a40300e03515030001403005c11107401070f0781400e9540810000943c54a51000c426203219441040190041c000d000c21b03860304400a50401103 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 346504127 1250 346502877 346502879
    0x20414100f0807030f09290108121303120206060f060405030304140607020d03020604051507050306120c0a060905190509130f02040e010b042d110d020c06010603150f 73
    0x7911821190354061a40e041c0810b090400715184401c8a110f8002503c4040285218480d8401d004914107001c08042d143c92801c0d50601070b2454070740e064100310040314030000450182140e82020301600450b040146070902c1c1214950103511070700c08884451040100007401039842c82c0c40f2081d1400d80340c016000314101420001c4000e04118001c42c601c0d8006400d2243c9801a50f400c04020380710b51080e800780400d42410b1609615040c86180c5105003140d03168104000c46038000196507020001b160700e580701044110445040c070000042c50754004101041c0800c010740c0040740c0d10100c034010342c0c1482c90000120801142c000c1c0354020513520045a1340480c480b464948142c80495004842030400200c00b41d0001c1d013200d042100554a0380d44407501c01100e40b070144103a81c014601707048a0b4924115040105513030403003041d101c0142e0342d5203c110343d688100201c142c070790114031030304215030f41c1044140140e80c072142445600002801d19101031241680040c00500302c0b011104020181 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 346505377 1250 346504127 346504157
    0x905010309060e16030326061306050a0b0a0831050c03060a0504020f0306090d0c0501140f04140309060703031e1b020d140a080601021009030302041410 67
    0x81c1c05811002e849154a03000318001d5280284100302140440b982640c01c440c0ca5854007501038107022040c4089003940360701d15410a1181c00c1b0490b409141150b603d00c0103608115580c0c000c0815400203600910303409004203440300500c000b01005480b984600965540b500c540303240b4a141c00841240d00703040b603c0514140d6000d200b512070154864029030325042c110310007007850210100d51901c000d5480c3c0080c0802d50801400781c07515500c094002d401e052500b03521640e50307001c400641078100314000e14120148030080d841085501414011122107040280c41d41c0f90400b020385064486440396080e400ba0b000c0000111007c1c3c840207040c06080030911b440c1640200041c41035086980310565400380a0032091180c1e0010010301201004111b9660200034a811030584035003051191044120b68501d03010700940d40008001d01e0f00d10750076501d82d00100e0400d5a101e08141145003000025000c00d5015000780084d02d588548044103221a2400c002c191656203040c8000b2400d410905c840f8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 346506627 1250 346505377 346505381
    0x9080d182001170a021b0a0308150a0806090c12070e070c0303110c010609050109020f071104060312020703050d0e0d030806151209191502030a0b090a0c09050306010609050103 77
    0x10041c1410300b43e042c030680414408910758100c03603148607a070780055100b944000d400c684001401404004066610082d60050605900076210710080d50b007002d1210081c1d03a45800703480c0078041130001d94009042443c1c04035584e28444104520403015850319001070180010850200c0e0030f42041d00d01ca070b40394810284c40d00c00c0b560344260201354442104081003650f560091051010140000038524644070891040340d42c180c20079100c0c540108030030f0b4080d400030313810340e19555004a00c0c81c2401c1014000140240103d41c001400c4100d0700300300c1c80580342c010440904803805502030768624030064100325003011215850380c1e800078004d41d004010a04c035035491070340f210001e4074030107407d140159801c030346400085c050095079a800c0b040200180c2e0134000320302002510604144040c0b0155141411100d40e61340190034035a0201c0001d038040c40941180c031500303102800342049800c0c0310300024040c0456884d10404074884240018003400c00080c021b04849280d81e828119604082c01100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 346507877 1250 346506627 346506683
    0x10518030316050c030d0305060f1c02180f0c0a05030f040c0308030a0e1b01170703090819020d08040c090c0507050d170703091709010c0609080d18 65
    0x203010320041c0030103904566803000000c0c0d2079004900030300084540208061902c0076412000b02010f00304420b00600d0340703491425181c1c4402c04c8070b0038141202d03006000c058016a004010750311450a1007425440010315a4450050301058031090a907664034010b0100384c41030b80f5025000903003c000007610300315039118080d002403203501e107040b4540e901d484000d5260410782c4d803141019903607000c54861140401c0288003043e090542503002c2a2a000060510343c0000c0b0111101ea2981e00080d281c14880da2080c4481b5a0002c0101c0c1c80e00b000145001507400da042040c0d015101c4c1c2c07038200009500405840348115030021410070070034202080d14014040c044031840a101c4c0a0240c01d00080b01440000c811701d080d503880315041543d4200c07001c4c0e002e4003d0b044100b414a42081e00780480d0802d4010728642c00d800c100c0907a202803030300c0102c07204240380030003400f01d0b850f02c0310320400c02001100400d842c10f6100e030140495800c0b007a85544a0705580c100501a50850b1070081c55001c8003820a4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 346509127 1250 346507877 346507879
    0x20f010603020f060f090405090309030c0d020a0e04052107030e030a0b0a0c020705130504020102060c0c0d0305061215010504050703060e0406050c0f03070c0b070518130213030320010b010518 84
    0x41c5c205001b0b40e0118085c3c82c42030302c1c01a00c90b040840c0d8201c59040401450481d03540840b00007000b0007941c1c01250b41c0d030016024801c900c0c01001c00003028410100201f11050003211f5000380801080e604540741ca4015a00450000f11003c2100300d0740d142c00100885510f40090b810410b54030b60710035420040070040e040d21b0a60048800000365940e5041c400316041401c840040307034034a4031744002428800e00800c2c141c540d010900080b40f03801000507203040480300c181000611a12403600107007440400004258140c42802000302111900300340440c1260001d4506100f02d49a01c1d100340c050316990700403100d000c440c0000090129100f034200c3d5400c01080045145440d0503a07800c06400d5004881a401046203001040d00300907041d00c00a60092061810b1810403100e03440d002c503940c0e0020400c92190054610784810f0040d02d03411030364494105104410403e83d40e00e0003402c2c050f421401003a200314a919105070240040c020350400c10350580d61a0302c0c0c001040300082c6440d0410601d2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 346510377 1250 346509127 346509157
    0x280f0f09090609050a0f050403020a0807031808011d0102030c0d1a0409080a080a1a040b121b03010b0a1a0f04030f0b040b2406070203031c02040303020f010603020f06 73
    0x140290051040c0b00c0584000da1010869107010290301c4262250402904031107483c2400b080040f0b5404900c0e40040c07540548221768468032810110307040c015000da014800c05d03c90b18001900201580310f885940d03403580e000d541007109100054200c0c0821285400000020840e880d00d808071544080c42e8503840c5425070b45500f0341840031030103c5034413890842e0100300002e0000c16403508840059440001040140016580003401545244c1c4e44004180074645460702d09401d980c401110401c41564102201c41414554000301105225444054003035440d14100c4010380c00c0c4954090240e03480140621104920150008204e0744903181c081f068110034040840045e40038002d5050381401010b000c20b4034207150034070460781d030713409007480755000640b41c1c0d010848207203140a540002411651b0540741c552900200c0c0c118890b030f511030f024000000844940e010f0007035001c0c000788c034069821111803100340300380c060894031070b030002960040400d0502c01c410303d802030007010b58001101781 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 346511627 1250 346510377 346510379
    0x15050a090e01030302011d160302090703090609060f061e0608060102100207030206010603060b031501120e03030f0f0106020706050301090902010908010e01061e0e0f070509030d05280f0f09 83
    0x100e0a0400083c0c0040340140d44410f000c0800d02120510a80c0b0130881134017070b154018407501000b00484103484001d00400880c000650b41e60f010350302050031140c00a0081c80380039134614009009000c95801c000ea0039150040100b40d4506601c004030304000762007a05210f003802c20000b982c000c0300081c44203046119400c0c0fa801c0300140d90000d0841c05129400811b1154100207002c0c0684010340c101a030030300428420803401601c10751900c01c007500c081c00d02150a06040100c2c0f0301400d0300c0002c4040a20001061240c0f00703a00302c2c070051080c8500d80d1001c10070390b00c9050803a00c455171840740100041062006105800c065845103c14501c141443d500e09030381c640d070b02401d40f0303601030800d0403a0750b50321001c01c90400c3c00100106458103548901c0305050a2003805910318201801d0014008501c000186016026100f2a041c03c000181211000d400d134410090050388480029800c0c0038450744a43d5004a000d00700c2c880e1b0300d00c580c4a4044581c4408001c9070050030110b656010070501c410 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 346512877 1250 346511627 346511639
    0x4120f0b07052104050f0d09241b06110c0708010c020307050601061b02040e0f10061206090f02181f0311010f0c0c080c0321041a070c17061015050a09 66
    0x8407c4043d4502c0361580011585030040e01d004010705400110f4041e010b00200709405548840c090b0b440202d010044003c0d0b001c6400c004008051585d59040340d1000002c8440c1152000203884088a0014000780117103041c0100c201d84030f010f1400b0042030f551002c00140400380c0030f4443c142c0503040084204402d54500e80004081d202c51140c1050240c10810a0700a149410300840c0820400c1070411701c48503282003d80c4813061448840581040e030b9400c03102c000c0040124544110396002440804411400051929680c200791441075250a20004401044900c140d02604494000b01c030950007580000042d10344064480b01c0400300281044030030005030745003c10750050702d114001050042c0040091614048150840e1541c0707448a12650700d4034050441200c094a004203540003410340041c090f0300703640c010084028031402c40c5800200350280e4550300110307024258011544103454080207100e80e0112400390030074910b65020a100a9406000204000c0c0041d2070260702050b9114 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 346514127 1250 346512877 346512883
    0x40b0d0e06150f010806010f0e0105040803070605011d060a030303090206120f18010207080406030e070e1f050415090515030111040602060f13061104120f0b07052104050f 75
    0x950103255840440d52444903410903c103080f0a40c035082c03c1c1020b072401c00c180042d1140000b08808402c22050105d14481e40c0d20600076203004050420860361209005e11301823020704000d00606d049403050000120300c0384005a2a90301800300078028010071811614210060810346100b0303600b007442080303410b0640041103403d03441803482038404d520070300786035000001d2180b038201000040e030b0050194201085586c02110300301c2d02d250800050007821551128182080c581c44074054440c0d2508024110208a42a200d01d80c012030107403040c1600d8408210403114400954011134241000502901c000c5901568020701000b80c6100c2000c0400c000a0130740f2907001e40c50031041d01c042810482542c0410038250440d2003009201e1580c03600d03005c0904070b4032450001408050712000c200c8844400c20086034090324076804246401038160800343e22071000c0400445007440100c3c0019112071048041c0c4540e0104c2e100241c0080640c0003202c050070340b0217881501c4900801040070140c41d410 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 346515377 1250 346514127 346514131
    0x207060f0e0a170a060617030306190b0a0503090715020d0309020406080316060c1106150a0b0408030a120e0703030507020a0503011b080915040f3e0f06040b0d0e06 72
    0x510014520440c0c41e107070000c10f46e003455004800e40452500c4480740424080190b07640a0821380c0d4252141c200d00c04400c80040051b40880c0f141140020b50354480c59018005500c0b4660342c100700c030b41c06662105118200014807542030300582003540f0f0310000030322a030410380c00d00740002c2c0041841502e68841c5070465000d010309d04003000d02c03202038004100030342c040c18010329504e041450701005a0034000703442e58001480d00110305001801140545d54010103a000703401c114904a884a8807800400c0e80c940c0a54081070100789042c2145800c0c3c1c002d409040381d5a90000e0141840710714565042d034694100ea00d04991099015001280c103460901c660459507244165507461074001d4140940f0514014041d07100d2074018583c50803d094440c1d010940196000d200000280342c2c608001842d004c80014004104100b41124401404004100014060181c024806403200d4104101e4502d0410390019000301060004002103010724003d04100204142c0100310254007640c0c0343d050000c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 346516627 1250 346515377 346515419
    0x215190915090609170c10110114060a03020108070c20030f07030519031b0506041a13030e06070b04050606040e010209150903100c080103140d0e0609010c0b04050d0f0207060f0e0a 79
    0x2010883c02342d01c040900403000300e0700003040c40d1041c6040c00404200a8140350002170306121020003c90040c034403400c4200720031a000302000c141408001c0e101580104405155486481303141d0410050f8640032410304100ca03440070041070000b07100c441d846102132000c0700a80503c030004000711140381b00100030401d030381d100340003402c810700d864541199089420080c071004042a441048501328002e800d402400e901410141d075035104640004c0c0552141242c01804980f54005003c20005c0000781e07980294803c480c2401441843e5602c5401c13070182c1c0e01a44d074400100b019001909401d08020104100c014003511400c2a5040206099070b00744c2c4681000620610010003e01c06030414810301c0c202d06d1005481c240e551508000e0003000910031180c4100000118503405a00486040d590781e0703070107100f0300d000b490141000e03502d80c4e021445401c081004140e130315003600e102061980030388a0b643c07201c050401090000311405040241c245820014148000c03540d504840c084600c4d85031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 346517877 1250 346516627 346516637
    0x909020301080f241b04050303120a0b0d02030c060901030603050712020a0b04060e041d01060603091b03020a0314010f1805070506030c070215190915090609170c10 72
    0x4418000d40b811404440041c0e42a11040b0850042c039141c4c42c6150308002d4605140c011034149002c0c60825100b00e0340180e40c10301c00001c001d100038044d010b64a11400d40030108005100076035090010765440000c0c029495000241042c0305480c001c03010702000315049c5000140c0c2620303644c903a458191241c00c5030040d031982c042c44a0440ca403644550001e031402407111410b0901e01070340680340f021007030903140c881c41d02c03080320303444d0211006001d40482e07072008001c0c007006503942000340c024021701c04180d401456a82da030040400c0c101c04074508072640900131418207450b40d00e41020701030741214000703055503d802070030341440e01901550310320004c1e8441e1004400c00524126203404401d6000318041c0c2c0c070900801010b2402101558000f580582d20620300c01c0d50b1100c1c01000d4855400d00e03140f40300d201c2c1c1700255096440303602207050790250040c5085282c01031000b0b60f185012881690000307000e80b002401b03409143e4201c1c0380c81d83e00880c1298210000c0313500048030700e00805041c0c00010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 346519127 1250 346517877 346517893
    0x519051b2503110c180105010e043c0e03070210020f1e0f0609060601051809041103120c062202030616030f0603050d0f021009200301181101090902030108 68
    0x48004d102c801d000c048102c0e45441c2e4510a110300040b80c400510400341881455503150f407090300e980e0860403406200f00500740c0340c24460340c6101c400d00383d2000e81c500004a120006218041e46106032440251004025414052702d5820880d80035403c000a00460007035000c0402115020041e000c400416002d401c0b51a04400041c1d509d0b01510f541801400c1d071100061205400002c228a90420001e00c0c0866490007200010700c00034401c0d808143d001410301040209000d104410382a4600040317040d070302008020300408840340100d00d81603003180c01203808940350295003207448c400100c00f074176004030020494002a0400c8002c68048d104004d8451041840a605100390b66034482d038080d04001207815034035402c0c1d4a07402039040f10103028806000824090003041040048180401e062000c54600d2411020846250016010b00c85800042503090314040c060805003801c80c0d10031030740d0610341d0340310103407a0039042034114184001c0d00004140c00c4a41e000440c043c10107000240309074 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 346520377 1250 346519127 346519157
    0xb0d020d14060d080d110408060703110f1c0e03030f060f041505060a0e090a0f293105010e010b12010b0309011e0519051b2503 56
    0x5560300341400c401d514641d0082152558801c014151207580000005071110064400074004200d042c6d09140358081c0450b000400702000609280304031903699092041101540030202c03071b801a00c10001000c070382880181c0c804101884204040e40f00c2c1c0e00c2c003151a2460b001120300303540c000e440e840e4120300e40344100009030410070901d88400c00140c0c0d003007004880300a0003094803143e500806120305000145100708a00c0743d000300e03000e014000d098100605190295400401d501c0103000440d600b001540e0621201000480541100c8004640c000340020b1040105013860001041b800c01403403540e40903003441e5151802c13440c0900d41000101541401c03400c10344580140c1c0820340b41c1d1000c01c000c0007025100303e401d03811a2022010240c907038840300d4016000d00451802c0801c010003150301c41075540b150750401030041d06880c0000c0444420b45041009450b000c0314103100c0d011403540e4500f400400c800040000c40515103004400d070740014204002c13007070140402d60000396882d01714101 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 346521627 1250 346520377 346520381
    0x90a0b12040615320901241806030917040605040807050603011d040c050310020a180302031b060d020d02040e070305100306090f0210030501080d02070b0706020a090b0d020d 76
    0x10a00080c4550380805252000341c40513050564408609000442c00d0340c4030003c150b040e002e081050041005606684a0242c910104121842440c921401d1070f001e01400380200c503070b01c8450030040107456445003083c2040d40640550b010440b00151002e1023049459400c402510203000ea0341d030740710b5446103040c0d0524901107503500510f10801c0200010004640c00340407642c040300f9145403800b115905c3c0c2c10035400440c2164012509401080c0d81401c01031004d60042c00800895210480341001809010b9002c0401e0300000707416a1114039070050741c0216400c040c0c0c107030000a002c503140070b84512008083e078000c1c6642085181e0082000d06c1107074034565020394450014942049589401c1a9070018a15030380f10103413002d5680e107448802d010341038451844003900030b03051154171310799104000e00520303007403003078440900480649c0c0c01400d102003115801c482001c941203044c21032039200d04001358002c1e1202c000780310001c04001103400c1810b000d1305100b4501d100050310380070300aa103401 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 346522877 1250 346521627 346521641
    0xc17030105041d03120916090219031b0302360102060912030f0c0403050d09140d02062205120303090c040908030a09230106170f060c090a0b120406 65
    0x1040c01c0440040a03400f0004240d605404a407505801d00c1d8580c0740703a190500f00c00342190040807880c1d039404a48035506400a02c1181d0890440f10002c0841c40b40c111f084401030b481c0540100105c50303c40c2e10562094001d01240d4130301c0c0045420013607085039008a201840c203080d00b054540c11914511035038044c40a19031161418000c1c1000b064050351900191000414a4080c00f1202021903507001981050b034020710f0b4810112480302c80e00b0b039000341c10032100e44207041c01041e00b818062180d0030681c0c180c00456501030803890400700142944641c0080442d050300c258480c800c0c001070f240e904c0400156040c02404040d40c2c1c0d03824840701246c01d010301880e44a00650410395110000740401088a610580e00030b0001200b082c1c900d00481e07508401d14481500404a446141140c0010f50060b001c4078440d11100d64003420364450300da120035800c407015a01c0d4100c8000a50401c0f615402800000300013070962045540741c8020300c80c0c6401550114805100c030204000812051344a003907 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 346524127 1250 346522877 346522901
    0x63016060206130f030203040b070819111222060f080601030213030206030603070513020c0616020a141c050c0f15160e040f020c060f010f03030806010c1703010504 72
    0xb014602c2d14048500708035015140081445030f4890004d41170510078801e480240c0342c40d07400c5640d00e80721814040d1194001c240d034580310781e900345081507149008410f040308001c80702024014410400d4504042504403a483d40c3c1c02d4a0303803282112a905d0000516000b4100c66124080e1800d119440185000d10040029041c5403040041607101000c1d55125022694120b44066882c0d450380b0101f81803440e6544001d030000c242c00c1007514a407080750003038040b040c8048111601a901c2144024150580c81400c1c00942c101e0708030400840c400109200f113147e03181040303810318201c01b0a210010782d5072404490000390007246200680b601841000400d030079000081c800100d00e00081001c0c0038001e0841d800182000c0d000143c030314010360f8044120b40e4024010800b03c5404610040a0f5104e1002c45003a4054480061500580310070309034143e6014844503021141180c1e829101c005000e0015410700c9210541350b000503888802035507486050140143c1c495142400388425103136413104070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 346525377 1250 346524127 346524133
    0x20f010908070210033909030b0402040504170309030403060c0c02130f09020312070b01052e2007030308010807270209090c04140d0305030630160602 66
    0x2801007004031041d40d0b04250101c440c032005580810064001b4268154002e01c04264484010100d00d24200302c88800c0c00306c10346800300d40d0042c03a404c07902c00d4902c1c003004000c0041800420090309056114640c0540f00d0514401e40e202480744141d02d5800c1110030b81200da0000038280100082c0d405540785030211414480840c5c8810303400141002c589401c088021076907500c00f0014642541c000a03800c64028050b103445211001b09108254041141555500450000041e15003800307080a582901559032a5469041c2d90181c04100040c44040c1d408114840b040a030003807510f49141c04c03005483c00300820307a00d07103140750242251105074803123041c070381080100b006540802001c544015002d441c000401444d12210785000f4000c415806400000490411800141d240c000784195004008080d04d0f041d00301003001503d048600c00203001400910108105040480208228140751440034505100940306050319200b122504102035205010a40f46522400314640203000a8806 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 346526627 1250 346525377 346525391
    0xf18010503011401030f110a0f0603060801060501050c0304030303020306010e130504030e06090f0f130c0818010b01050904050a061a22050a1208041e030510090302070b0c030702030a0303020a020f01 87
    0x3801906e4602d044c0e000d007410090326400b0340b0b41d0741c54240740c1e0064200080b407459001d44445c030040040c9150701900e01258071300140403230380b58003560603034a468811000440c5000d0451343c00720017940014016606205194001c180596282d08490703032101b103031540005070b900c0c260074014a94045242e01c0ca000d881c04000920307d070388900c0c00000194105640c2404001d0350200865807201100850100d40c0b80390444c00d85a41e90f011515602446064000190701c950364220107003200c403a601c480e404a601000541040e044c143c014039440510071400158240e038a298042c00011009500d03503408000298070000300e45101c00c10b005d030031030011880001c1030508011174242c05450242c5000e9008010803102042481300032180030380356511203a50f0090031404003807195480c40c00304880300e0284201c2001150150b21600541d190107500078121689004c0d4032540315440500e82046a000401c07010700562020048842c0381c0e8403c3e0340050350791700380000081c104607003070098050070303410044 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 346527877 1250 346526627 346526633
    0x150e120c0c0103092a15030903140405030a120c02041104081b06030403050304140d020a020109170c0103050a060b0730050906090a080d020a050f15040807020f1801050301140103 78
    0x581e1076120b61018800c0030741c0c0a01d111806170690000d80c8060321409200001c61081541174100c8010a4800e85905561059840703460100c0e016500420390158020040040492a02102d401c0f1030603c0d801e000248150b150003207406e54491035042d41e424030f000034041102e42404c01aa107a80440b000420007040600380c0003e03803e2002a00190401002002240920104005d0314500c14448811100c00f8040000041d49070308610800f84e010403116880010340400e500e0080215030001000f50080082400c015402020042c001400081d5240c1010075080b403100f00400110f070240522000380704003901c080103001c00d20b01445c1030842c1c4050500341d0781c03500001601c8560303030304a410b81d031600030030b00103c0d884a141d90b200310301c144506800e0107000c54010a102c444280200282c0b2010314603800c00c543d9030050920821700c2c440300b407400503012444c0403001e02040d0744001c164032409124500020b2285440c84040d00181d454800100b1140c9801d1149940001c401801d0014540c0b41d03807 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 346529127 1250 346527877 346527893
    0x5041214070209040c0b030a060e0a020a05031618090b0a0b07050a171303030c0201020d0e0a4506150503040f05010603170909180703150e120c0c010309 67
    0x68024040c41d907483c0490108184504039201920f100036030f168603842d05503209006840980700c2d10149000390404180342881500842c3c140002903110b030361540e283c1c0020741e83c420760089c5140082009282240c907035202c4040940004103003001000c11400300d040c040043d481072a42c80500d810f641080444005100800d50318051034110900082c40082e0100e0788140d84580e0311002c0013a080da0341e001c0105034001d0406a03616000b80d080701c06c20694504281d030101c86202c80e050b4403031003000d020041e4001400616150441040030b541030000e4580305a038150030580b021280703c9910b8001c205904c807a900c00e070001400602c2110241d90505100500349200c040c0000d44a02c80388204541400001d4000100640d400340440310350742429002034640b43c002c090440c0c49610205c002c0f80680d00881080f03054510042c0140c405507203140d941600003d034803c142c00200d500d6400081c1841070a000ba4581e003004803507020741e1a070031000105c2c03c040a101ca000d0502d071a044e5000c003c1500b02c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 346530377 1250 346529127 346529137
    0x100c08060d03172a07051b0f04021c0f1b0305040b010b030705210a140408031f03240524010f0207081209090f13020913020303030a05041214 62
    0x9141d40e840c00b5103c030b015140400ea50141135410295542c4c050001264085009000c028000c41c10b854a040c10604203e5034402c02411099012452a003001c0c01842d082d801440440c0224410b0001f062003d0801000e840c50801024407103a51900344034400482c454070764002a03914901004a464166920f0841b120180500707800002e000c0002640b58bc0180100d9003c0d00f801101d06000000c9640b4030b485140d42103502000c035030300740307420608004600070019015030340c8200304500b181e64844600e410101a82101e400f158400c0314001301007081503010cc2e408424205880709808070447d940415100b0160203507080408600c4000d2110b648207000084000d02481d102140000d1b20300e00f245070a095030440380e0b20303010b00c00305030307c0d0b030a503000c000d004503e001d5850503507581e10880c168145038800c43c0c4070641c4a800800010051401c0c140c0300750310070518105c01003c0625038000c81d1031504129010403a00b6641c0c0141300c10b11003d40d901c0f03080c2030203a1a0544540c038640e180d80405000d5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 346531627 1250 346530377 346530407
    0x90d0e01050325090302130515010c020603061c020603040b041a0f070c0203120f0712030e0303070309020414010303020d02150601020705060f040801091a0609011d04050c03100c08060d03 82
    0x8440041d03c0d1a40c880c148040c025038000300030611034070044200ca0014601540c0740b000700c808180b0303888080e5020f100d0000c486a00209554150380c1c41505208001514030715420340c4e008240e0840c801a61480042d500990080c0c0c003082c46c13481d0500c0d00a240002c0c0c80d410850f0b10700c1002c20428030060301b01d09a80d1021240c540b02100900e1440802e04d00a14542503503140c002c041000e5800e01d03480c0d0068600503000f651080401100d0900690848040440000c4150130070000a07002c0790007604a2290f051001c0d0000528120043c001c4541c0c0800386c0080380180c12080803052903e90400081207590021480c1d0302ca54180800013030b5507084e032032007094018140400d0140740b400460040e03400401e1000000c1c0310030b000030300d01800d032171100400a5600c2052200451072074100f111030241629405074480850705503405c048100c1410050080783e0903ca065941103075a101804a40000800000d0102e41000d102401429103000242000d0052440500c6540801c0d8840d4500492a00c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 346532877 1250 346531627 346531681
    0x5010b0a0c030e040203072102031b1e040b0904152102030c0909031209070501120902130c0306140108041119080f06160e0d080f070b090d0e010503 65
    0x107a203181c1542c1e82c03030b070318101654018404001c002c110f54006001848a02c00141c0301c502e400d1940c80c254040b8042070350020031184e0540103807000d001c188801080e9034507200c000c203025500c0b10007040c00e013079001b40c000b0603c104000c00d62a02ca400e042c000c0031a60042c0c0011400480c0c1001c007102103c52032000d50241c1f04000b0120b000070345d181405581b040c41c4000d810403255203008140d965403507003d48025a04d046000001620383d940100300d640585034140d403035211010f02c020102c030142c51028001d90b071080703251580b007031502e10034401c440344030a45407008610986400c50a60405094601031414009241c040000058200000c0060300b202124502d400c03040161400c20707070740c036144c00040c82c92084000303055468900141c0e2a108105c2416500d07030344400b1881c01c48416021b06980d42e0040411103100002030403490140c200c01283c10100c40c2000c41035280c02400034030903100042036400c014a9810b9060b8003150041d0415802e08225103507040440709a422281c00c20794108800d6 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 346534127 1250 346532877 346532897
    0x9030a03050d1811150c0a0803180d0c0201030e0127051905010203090c0109080618030d0603031e051e03040204021204050c0108100f03110607050a030903030905010305010b0a 77
    0x1c111584044141003030b251001080d080f440c84d0200088415001140c0b00e0301003034200c05111980d40040b00c442140c000c0103455a50304a03903403601607400c0030309030b1420000031102000804400f00518030407120a5030f5840b69001450001600300c58140c03010b030403943d05003061220a040340e100140302c070304c0d200c08110040b4045414501d00344116030740150907405440048400340700f0150051406110100c00351511401110010f445945183c403440e0301c41d03003180000940c00c4080d80360721030704003000400707a915183d070030401c0304101c40890700120003294440000d10440d100616040039a0b01d0542403040c90440c11121401441c140044048480d860010008046440e2034066031003440740303d0f016402a050a01e4440d03124010303404168001211100000c18000004030203200700c5504c8030301070340e9150558a905084c3c8100e400320a802200401c00c3d00e0018104200b0070308110300903030300c1d0b41c190b500713600c4c0c020920b103030075070140b4101410000140010f0103842c0403a0030304103090410304204 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 346535377 1250 346534127 346534147
    0x60318010207150b06120103080a17100e0a02040e04021210020f0405031005250306030f0615090c021002030a150e09070e040b0a1107060207110405060609030a0305 72
    0x6148010a106a500104400c01080b203000c54480c0f0000714110300348042c1e006402803114034082c6541c2c2c2c48841501783d00400101d181c0d1b07070091000c0f020710314140400c0e001c0f082d402c9410b40c500760342031074218001000402038100c180786620781201c020794065240920341802051218000b0744041d1041194411501210204001c11000a04840c03800d644403151100b000903190014411a40030b4000c2d0680600344484600c1254801c52007105110120400d03401000a10b031503149545081c1950b44074044045864415144d013950303c00c601c081407507103400031890111038095005c00c014034244100c046c041d603004182d80d11121004400140c5941d40e0106a002800211102d9080d004140310b010034600c0c00d003030b812446208400308480c03145944244401482c00c04540c09428031321000c002c81e400070081d40003090126014102c280c149184c507101c840481c1c0c0840700031594842155991603260815000b1036074401c504980450602c00400701003503c441c801c4500a0810600041d208a0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 346536627 1250 346535377 346535401
    0x11416090317030403090e090601090b030f01110306030c090c0a03020703031805070801061a070b070e030d0302070203010501060e03100c0302220315060b0a0804030c0803070c0b01060503070e0603 86
    0x1c5400003603903900c0300040c20320041164015a01500003a4030b034003000ca113680c080c42d500b9009602d51070042002d6844c1420f03440003440070450156060069046100890307600740101c501240300f034180141c1c1c9003840400c0510300080740d800540621040f0781040008000c036029110181500d0801581e116200d207000c800400d40d0261044001609010000074440009060019241540000c001640d207030305a08204050080d510108003d0070081d1500207589541d070150042101d09008010310004c10009013020984d840780000658003180207420351409011340380c01040f950400c0c0209200200109844030f01503158551129100c120384e282c0c880c440e504560400150445c0901820300030030056240d01e90380e00c03050303030792569010980008002c1841030700121540303c10309a2400311642c0d0306844140b40140300303809004501107000c001c100c0034001103100c3d0710203603580c050b032183c185000804c100040e0002d070108181170007002000741d040b00c11506000e104803100740d16681ca41c15480b90b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 346537877 1250 346536627 346536629
    0xc17150703050408160b1008060603250803160b010b090114070f02090703020a02010614101809061508131e080415110f15040201031112091e01141609 66
    0x180d05507542c3d00d10010b06c00b08180042c00340183c03900e1410080c4da00ca00751660740c1c0d0152106a41500a070352158510b0400016410a485c03100010100503559030310001e0954103c41a098488508240d191040200c0302c3d80c02d6001d000d182482505003030820300020a900e0000c00000c80c0000300050ba80140710401081e980141e83c01008040d180c608054010003035040b050640300558201240459121441c1c10384402c01880607040b0200a2002001101c0c480c010200b8008103206140000c41d0b030030303450300a00d00031303010070325103150783c03110550001f015003400900b0111013032202d0b2507840001e500840d40c44682c0c00c00c800040100703131603401c1242c51482164046000d8101d5084002c6656801c40f14400034640714000f030b00c403160401243c050b02c400e108040ca00908007000d00050044d800782d844813988a101010641c02c0828410022210070f0003030f5036100303890b03010900e02c001c1c0c4194601406180e420480082c40014031400c1360640250000c0c001d007003540c0350400c01c00e06441c4a600120 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 346539127 1250 346537877 346537897
    0x51b0c0306041103150615031b040b091206040b190e100f0b060406080127090c0e1008100203130507060e03100c020d1d030a0c17150703050408 63
    0x8080b81007602c3c090400a40c90f0103030901a0041c0c10000242c0b036407542d07080d4400c1101401420004412000070b0314150f000814905030070740007003144950b850113200980080c00750b00b10b21340d90b0b4200d400200042182400c2000390198461400c00c4002500e42e403802e40c00c1448038003241425122070081c10301804000c85a68458070440c218107000103501d0f0001c0b098000703208010051891140c043c44801d00c146d005480c00f08000e10700401c81c04160851000d100176805071502206a060341841d01aa02d0b0707110291000701290000b031203c031410103910750b04290013000e0207a62600c2c00f00c1064585081020308095140e01000164400d9140128101f11710b81c800c0c140d540403511500060206100e14540c907019210340c6182e42d026000d54450000c40304101d800404111005050032900901c1e4036510414100300f070b0a5640e070a440400020300300c02d00c81c00c00c141c1e032030341441250103804119082c1e400241e80003a203103040d0507000100701c580012403803070b0208041d522820089050b1044000c0a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 346540377 1250 346539127 346539133
    0x9060714120a030b042f0c1c020d020d0201060f0b030903120103050601090b06030c041e0302060a0f18030809010c0f12080a1d1c12020307020a02120706051b0c03 71
    0x4420b006505521100420008030f4042065400d00710100d12121070701c0a4140c003480c0e4014584a070038030260040e0036807081c41c500700d4849040e02100403201c0a2005000c20140c0d0044a556000740d406100d40000d1480038402080103514081c041000c1c404248074603030103244000f010131030412040c4115500c1461010f03000e100c550752490303c0c6a50f08024411496160700c0c01003002c01a1901c1011070b0f008042a4044505140c2403104049a0306110082c00c40000d0800f000000180c8511018090400450302d40c2d0003001e88100029080c00d102520310800d050140f00c00340300103207581064845860702807800b000325004d00e1604c2540c03810840d001621246490340c4100810ba40903003200d201d00030000d001e0004030030050301e0800300e17035819011104030b810051a0000100c3d942c4000b01481e15a4603141c0440800c08031064204c0e4000d842c00c00041e008907540d08158140021000b40007100d11008107103084c50800000d02c2c500884e03400408054001c0070010b40e0340c204200703410b0444001425 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 346541627 1250 346540377 346540387
    0x30e01050f07022a09010f030308091b04020c2e0c090f0902130902120714070b0103080d020d0e0c0a24080a0b04180c0b1206060f1905041a0906071412 66
    0x1151840c7d4a05200490000d04400c1c000340c0c110720b0103e0001c541015400c1d0105d0f07100c4035a401c00019402c00d00e07802d200c91060548144d140d8045880e01e0300310031004e91a100c1c0d03641d88514400207503005084201c0500800100810075071102440d03042c100d4220200c0141c030f80d50300815500d01c020003540201d07201400410052240d04484643c14003c850070748400c0d90020350019054100e0268010140c034085584004101141c0310100401c1400e801440049c038040d09034606d002246c0c100c04900c4240c1e07000c03d22009086c01d10705508001f400d050112012900c03080b0882c01c00c628203081c0c5410400c0400b10120b14804000e0b0041410100020003e11040261030385180d1038001c00c0e181610804440b00f8006990851041190a414501c44900074160307203c42c1801425448000014580700c400c000c2000e20f10028a800910070045035503240d510f61034040e601400c02c201e0110302c540a038003040f20942c40c0d9038010840312110303401403030f81101071000c0700307101d0400c0c0c401103032040d0103200095 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 346542877 1250 346541627 346541639
    0x16060f090812190b03151f030803011503051611160e061e01141e0309031b0d0f180b0a02010c091e03080d0615030e01050f07022a0901 59
    0xb640501c035000c0c21a6041c107050b01c51094809494201103040e4040d0400c5400c41d1001024006030342d4800c0f0320103508111b4105000300d9414aa01961080ea0303101008001440b100e05030100c0c143c00c0228900d020703c00750030a47c01841d1201c05a016000501000f01200c4081c0c5105010130710341440000d01e1011140d60381c003818240c1ca00c4c00c950030780c8100c07c0c0440c10764860300003200380b40e080a0180e4603140380c4140c2008000b51940030103400128500c1c0346416041c501c0a003801544a90311000103592a00d42d4a00580c0c0e460141410015941d0400f40e00f2030000d170340c040c4520322a190180b074034030f01c4a82ca010552242c08a036400541c0c440000241001900d50150481070000005070f0b20000384075980c22407201c20780340e45510050900707503484003080880c42d00c0001e05140da00352140028660381d12820035603084064404200426207520b440101b680084c4030301035100034002c01c154040c1c070780400000d458210b14010400c440324251145480d050b40300b40c03840c2d844078018100d0702095071900 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 346544127 1250 346542877 346542907
    0x60203010302010e0d03020303011404060506040602030909010f150302160b070305011d0f010605070c080a06060e01050904030806040c0917030415110304060e04090203010f0f0506040216060f0908 86
    0x4001640403802840b588a25410085e100c1000d45400d5405107056909100f884412040c1c4c4041296019899403000301d002d07615000140010070300f076001940c0c0c40460105101e490581680000d0000c020b424041180080103004110602510b25005030f030303000591078403a03800c1c42d5138101402c1d0080b0b2000b0484400c0d00740e80014140c914961f125102800c0c0c42c0b05208441038100c8143c01e426841c98010464a4002c0010309038882c030a56103840e040c0c1d1521700183c681018000d081d039045484220410001d00c4004515000d000252144181407601c5c0e2400f0703104000240c6454011780d40c86030300c40003170b0f8030655500005e403071510801340c440c49007980f505540b03821038020142c0494440f0300000c10700b4001d4020103c82c0c031030540514100351800900b07484070b07504069642e401ca82c0700d000d030100582c0c0a209161084d1700180f4001f44041180c0c510000b01d032001000c1c24050b500c10403207040303592006101806440d034040c1010a21816003a1802e0144c4100400100300b642c000c500d03c6003c00d080 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 346545377 1250 346544127 346544129
    0x4050a06091a01090b0a05180105090306070201051501030b06030f10050406060903060c05040333060b0a030b0a1214030705070b0c010b0d1101052b0c030f06030b0c0c150406020301 79
    0x266130701014961901e6840040d44200b1610b900400c0b070410031402c03002100e0a5150410790141800b44c240802680401c1c01c00408903031840c0103035540c004010f000c02c9240a1032102d2a402e180c1003021211140c0801e13881d1001a085881151014001900b1100c0303261604010f00302c0a0320074002155a008043e041500c58042182c5040c00d080791000e070584a441902c040f01d4001d4982030174180c03101c03500c01d0351949104020702100c5050014200721403d900801006050301500542c1d604491000101203c0744c0c0d00590344648a24101000baa014080741003008581141020141ca2203043c03e051851107000c1008090340508840003c015507004064030309020908002c0c0080c54150040150364020040000d0100c00b00c2400560554480d8000d003101180840350722215000900c0d0b410300517011100b1081000751280f80d117010040d41402042440300085a00344580d9080d60303204018114010844441407602003501d4070000000c2002c40102c8041c800c12540505084c207050000c0e60007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 346546627 1250 346545377 346545379
    0x2d18200c01050a090b0c07030309060c09150c050601061b0210080106110a03120902010329040e011a010509010519030603232a1801030501060f0b040504050a06091a 72
    0x6041c0028008a109000e92211680c5c4114a560703250365000310481d868204010136801c040d511b0b0324140c0007032030380c0c4100b4841c440a03441c1d82c03c0f01850218855100c803000b139004000c0101c040003a10000b10000380040c1034400900b012500e111a05920481c1e0100035400070303500c69a82c140340051550004512816920a80c0c2c1d8514a604800a581c3e0307074a04480c0c001b000a410b40544840d0f50040341d00100f2070901c149000b04e5401c00b500388208a403051124007030440d5042c0c0b48501e205192904c510f225004500d00248851001d40300703040071030390105c0301d800d0602100143d200308a81c07050741114108402a41100d600c0c0c010004001d000708001d01089440700c05211101000c44010f15480102031025030003003030107440c0310709500c4100078020400e444d20104a140d080582e501c0c000d03405082008400c4c10091903245003005400e41340c00b540140000e4114002c00e00048010808036003e13a00b007510041015115a074020009003416440202007a1800c141e00b196070340200303586004414 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 346547877 1250 346546627 346546631
    0x1612020a1a0105090c07030f3c0318051902031e1c0507200a0b0f07110a06020304230402030903070b060907090306051911042d18200c01 60
    0x145d000501540c81c400c002028010900e20303050054920700c5241510f0394821070041c0b00c503000b02600c2141c01ca200c41c2082460810240001001c6415454410094003248460032440b1140c1c2641b21a0b445100503022408e030440c60400740429900d041001100204480c19840c8012151000403034070b0354024403c42102e40d640310715001d0098441c0040e103178031a0708075403910130892014403800d039406c0c070b400c0c0c0d040c0c0c0060207042c00044003000f002c040d200e50080c00280d165039140034a050082042000c003040c2c41640303004000e00440f5800010b40e0141c41c50010100401d21125819011155540300420380c0700303000000f007081c1c2410210141525030b11a01036a2841c0c0c482c0000c01100d080102c503a41d000404e0031100704085042504016000f4006c15500c51412030340b2942c22050381d042195100040200040400100e410098582c0000000da007015881101e06260b100b60a1803034817401e0004c042d240c1d2070b5843c2c401c103a480000001003000219420160030300041c2e2a6410021807810694 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 346549127 1250 346547877 346547881
    0x30f0f0305150402090a05030d05070b100e042307030f03030e010b0303090103150e070e0901081b0f010e18221122050103061d01021612020a1a010509 66
    0x50003400350724081d144000308014150030060521000350400c106450b0302c1001c4580000b0643c806100300841d80c041e80d41c80d15900c612908043d00006400380c80703410b207001107c800300304da40c10400783e407a0801e03485400401034903840762559210841d80030200500d402050000005c0040303600c4400d038102d2203500c050207030781243c1e05c032542280e68031001a03806400800c104400c640c403d03800302004070201d000e050000c03a1034174500e0300f981d1011140400487c407000300c452941e00e0100c0c8680e00426403503000b80b03840001085952105e018504005018600d80f41c80d0b648580e0241c0305da1403001e08040d00c026001c9800c0070010481000c10b4130819150340c40f00c80c140300410380000d0500c1002d500400480a05040003051069400024500384491000040000000f05140c06a50700840c0030780404034a00c642c0050b001002170a84050341240c3c0c0c810040d0780990f4075182013611031103400200054180060740700a0b4140741081c50000d08641052284041d24010003010394140c80c000e0f43c10310165 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 346550377 1250 346549127 346549157
    0xd0c030209011b02011d010212040803130506040305030702041a0904120e030f06010b0a03020c07150f0e0d02040c09080f060a0c020703020901140604030c23040219030e010902030307030f 82
    0x544481440a40041e0b100c2a446012925841b1415825403040c4115141d0130004251401d440d0000d0700110303100d410004501442106031001c400103400100d80042c82c00e40f030b580e207140e42ea11854600a0080d5101c04d03204000800c1a01c460300c101c64081c0c1001c0c414a014030349000e1074100064500301080114604103060700300002e00200a40411004011a03400c103540c5d110260004044141050b400300866003400c4024040c5d2030091914480442180000b044043e00307100c140e1034071a04102c442c04405040b0f0f600e02d4055903001390180d40010780000c00010440c0c00741601c0d0454012407060f100c48110100f00000c1080c80365000c0c10003042130202e102e00803a2145180d00c0003a600080000c014803032100c6810804c0c111a84c0100140e140c981d41e603455440480c2c0c1584081010000500c2e240101c00d0005081856504d044a00314a00400c5000d48401d50340541300104c01c0541d00c82c03407000c1d0102d00350f102d042c5603500101125240d592a01c1c00411011020f01c200c1e0000b02d46000340580 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 346551627 1250 346550377 346550417
    0xd061e0b061204020d232806090f051f110412020108090705091320010504150201060b07050304051e090406090503090d03032903070b0f0d0c03020901 66
    0x402000100524940b1841c01d040d0010004050401d90b40456500c030f5040005540022402480c1408030819000444451000782404a000100809441c0701c19a44108400c02d124484080750f102c440003e15180fa03040099054400f074000405a101e12400d0b080b00d01d0449103906c0342052030303203818062b20f0b41000a40e0700d030380a10f104508820422011081c0158000c200c5642d10040c40c508444101d81d03280001012160140c959002e402c22590125042c04885c5c440040e607a12083e00d240b030110005000240684200d2050113414200c0314405c0784d007076100390440d00041481c10111500c6401030304083ea2264881d00c50307644103a100d50814400454005844c52042c1c4006091860507615522a80058036417481c048440380002c00800140b941c03015502d0b80c3d044e001381d1300007c981380b03070882c40c844241c00002c18074480708030014550f042e42d400280b11000d4a40ba0214151108080e00e00301485004110302101c0c02c03230610641c136075031550513406131400e0a0300740e8403041e10004080311803031 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 346552877 1250 346551627 346551641
    0xc07060512010e040f0f030f121503060e2b030608070b070f0f02031b03010c140316050f0a03050a050a0203090a0b06030c0402040602011406030609100c02010207020d061e 75
    0x3030301003100e001003003c001042e41659006000b4107401c04440d40c5903a51008060208408901240a04c2100c801360303a4001450207040d0180c00040080409941035070246210911004004949920100402840034040e018043c3d542c3d280c01282c50b5040054803120070380c820403480c0080d03d002000528200b000841008842c0c0c5007058528000407911040c801d41500402070360a01513402c19000141c500b005288207114070852010303d08400c2c00200f50940320240c5181c000c0151a840720310068000c14101c0f9000301c40500e01664041c0340003801d071401c3c021a605030310384000114441940380e4060b081144500d50a0740c2c200456510b40300110b040340400c0c0c4040010350302070005c00d00020381340e610310340e0800402001c0b140d41014190018050b03034410381108006035101c45414240307158600425421280440c050070079441c0c484025a65035540754040158a5181d80d00400014000c2d81141c0c2010b0300500f4041c3c20540d2400d1020107000c0708148080c074a00d90b0096020301c1d800e40d01c9401 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 346554127 1250 346552877 346552897
    0xe0c030114060607080f040b0f0306090106081b030a0b0312070308010605030403090b03071404140310020f16030504240f020c0906150c2b021606050c1608030c070605 73
    0x2e8282042c030740300c85c0c0507038009469041844204000205001c644100500f101d5109803c07880c2e035078035024043c0120074a042e80700e4002c4c030000300113020b4150034000d41e01d49064a541142e9849956680c5014060f1418101d41c030b41600070030480104040240000301007484c020b440347d40076039a03580030480e03035840f00303c82c040e0005550020901140c5021001540c100e009440c3c20b003120500a80700c160181c0c01640b241ca281d948014a8903100c1c10140b2091f0124421a1401c40c05d00f00b0604071810719202c1d071a000c01c0985e000d10103420030140a4000d680c00f811032911074581e240c2c0c1200030144008402d20707081010885a07041070916500c00201120404405007440131140c40b038030207206c041115419181d44c4110b052042c0f80000e88100320403201c00403504280320081440303541e42010303680c0482045045421990b005011260320181400031103020f4a001a03540c600c29000742d00344241c0c035090810f41c190354000020916000000b40c010540e50b517094401180e6a80800e492a2242100748 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 346555377 1250 346554127 346554139
    0x90d0e01080402090414100f150e06040507020f12090f060c25091b1715090a0f020705160b040320010216321c14010e0c03011406 57
    0x142c014184101c105400a1050742e10019019400420714105006030b0440000f203a500c980d9821402200e0255100907201c2c0e41d48100c00b01c2c02c101ca0780d5100703800203180b0340c025a12a070104400303920801141c800800c030001961980c501c000384000144d1f00200c5894400c680c60400000b552034820304032038102400340e009264800b401c104090041d103005240b90704440c10b80d40c1c0050204054011400602e0012061405250340040094401e440d0713a203e481c0040611001c00006686040b4101c2c41300204803101003990b03440c03c1c0c018000d4441d4000914007203002042e08020001e00040560b448901030100180140d280d00c105100740c00f030392001402001c001440c50f600000300011000c003481043c8141d0720f2101000c1c01703082c0d101201c1d602003028400802d000c0b01801c030304030b10041c81260803ca1110001d850250000701d104500203c0c0994030162509048100700910318108a00c0c16204001d0202c480200c2500d5211702c42c41811320702039420b204000300380b10581c0408610480f401098 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 346556627 1250 346555377 346555381
    0x909040b01181e090302120d020403050f0606030718020405120a030809010e0c010806180405030a030608030a1d01030e061503100219050c0a1a0603010b030c011407022106090d0e0108 80
    0x20f0140503180030042501540100c514a0b4803030140c7e14010300e590600c0060140e41c5900e145455480c060b0b500b810a41690060410b120312036801290207030450ba003240c2a80f006010725403001c4c00902c80d55105591021018564079410000460b441840741d00a840f0001655200c3c14100e00b0384c3c0303c0112680254000da10040199030260a850f0b8000e0b40203010050304540306c070304c20000c001d8181c6050380e95034008154038070520b92600490700a8082000a10708013910080050200c07113428106400200400c031032103249074031952255080f0302541003118128140607072150380c0c40002d288600d00a00402c96144141c0c0c000e4000c82d00c502c001c183c4540b005420000b021159a002003c036030415010b105011800708601003400030a440c1c62603e401010b00701042014212148021001e000360482002d03690583e0300000141000c159180300e003595901d16100040414070030500508126003c40040f8600100c001031543c4511080405c03910f240a0958007074810708920818240001d40d5640 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 346557877 1250 346556627 346556681
    0x3030206090c060f070303020415020312070c02030303010603020c1603150c09080606091305060108160602010911040b011b08030103032c0d301206050102030316050909040b0118 78
    0x1004104e983e0082c1f40060602d6211030407050350728404a103e0006a0021920258100f1008802d58100a440c1801550196140e000c41d8984c00148100ae0074544c0c04140880d00c5a0305202d00380119800c00d042805e504d86034509030b00c018030024070340c06480d403810780e1903c0483e000303403c1f000c182c8a0a2006040c6a954541000090303600180303503081540c40c4488d0080064000c00c151400381c582c07080940000f00503c4800454001c05501c16006c580c1020380c82004216401c961901200060720040748620304a4016101e50911102c40c1191040b8a40c4040a04c0100c40181d4103170f80c880e99400398914000c10056a0000498080146079042511954200d181118000c0d030303054456409031100803035541d252040c0038401010341c1c10b400d000000303120345103500050a041e000000c030020070401d420200000c1d030f24000104810b01d42ea1042d0307810390403940544243e034940003008021507114a054030300100303006402e11490441c0e40807040c0f4100043c2040c0182c4285101c4810b0300101c800030b40c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 346559127 1250 346557877 346557907
    0x7060504182007020405160c0204110f070c090605030d050d020315040903050a030c03051012081e0406140901143403180503070501050d1b030603030206090c06 70
    0x280480d401c85644000c592485100c0c501c0c0701401c41d00c049150358031400c0ea80184002c0c1c2c0d00090103101848861407070f00001642003074038081c429406940024540410000a802c0313072150300407010440c200464020104807428011800781c5040040c01d1292503611030525540d44208c00129011407000d00c0300c140d0322001540596441604000384008112404003c10102c446000d000e90004a002403200e0659806008004081c03c0318070301007100c0c3c503280c140c12407a09010f0154011215203c0d1109080c0f000b150705076048503044000c550710b510302940d04a04254405c0c810800401c5410180c004514007010541c2c8010206860340a03440940710342e29841340d8400c44007069840e90f200c107002c51103003050441d0000e2400310060400c2c842c0e52802d01a124160160703003100800207046061086032008201d00c400c0b21800e092060310340016058440260072000500c6d4581480c68010500c040e9158100c2e00c1203074040d800303580380b54481c203825640764001c038051103800ca00d040203110403c05200b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 346560377 1250 346559127 346559159
    0xe091e010f0f06030b1803390106060801060914100215070306051e0307030204050618130b0a1407050a09031b030605070206040506041112190c060207060504 69
    0x4000001203018503000d084040314a0582c08010507541c0e90414400c00c588418820b4120401c510603940d40c48400d4040340d501c0c4103402d40407410340724410342c0400c40c046849404032407211038024901c034072034050a80d500030415840350100180352080000340c010b020340c00c100e0540b5503242d01540c80c0380c0d070340c0280240581c0c032050001c110f03c2400c62410000491f81c2d0300500686040e07501085552804080000708107040b5a00300c0708043c50504001180c1d00001c81d01d04995040d0b501003803541e80d4100164030610f4420058a808483c0e80401c6142c8007071084121306c0c144640035a40c2c80d91502503070401150031504805110b818450041502c80340100058a520701292a1842c1815101e545048140d10310110030107070388168070360a0040200354058685e201d5503d10044c02185000d0f10383ca0355459001d040500b029138048139681803a19102c50010b4814041c40895144100300c991404010070303500c7c0b0070b071006000075402054082c07021800104460b016039034203040c60f05161000c080300c00c2d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 346561627 1250 346560377 346560433
    0x1201020a034b090c0503060a0b060301090903110706050706050f011d060324010f151b060b06030c09100806030c040f0b030118030e0402030c1b120316090e09 69
    0x1d030a0359440d111030b00d4058140040d10441152007114070384814540f4048019190080c841d040c5899500107031500d20a50b41103c40400700455142003506042d204412414182c401d107005180011070856040801001d45a04c1103408014940d112101919011802c2c007882c2074841b80c4050180070748420f06e10003900f1860040030707a2160f03e08402c104001c2d6078036441c82c0214088400040116000c4242c19400414005004c2c0c0c1002402c07c03c0140418000d03e20503550709071004400c1c05000c040e512101160720b010b007041d0341c2d0341003d50b0022119000103180300c1c441c0f0140d205503c48a4401c00d07401d030140c40085c00400f2070f5401d41c800c120150264441e84210590b840c070b800185035409001c2d100744d100c00303240b107071040301c1c442c3c2801002d11000002c0e00340118010020301c56060204002c88007908030f1312060205018003040c0e60703801c282614080031110710021013480b00c113486035680d00407a500343c1d440d084e03000c642d50201030480c0030b41220101e0154100c2c1c083e0720001104c42d4103584503070103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 346562877 1250 346561627 346561751
    0x120403020f0607110c030102040b1903061d180a12030b0402310803120103240606081005040501180c18030501051806062209021201020a03 61
    0x901c0d4000d140b0b4818101d800c01c00140c65416412403182080c441c442c401070040c0c000b0351500b0305210310300c0380034840c00780d80c086082e48040384628601c3c4654402409000c5c04002080051002c400c2e005145605039000005801c21141341c544000d000600b03403a905900200b484c166081040b800e400070318107410080c2c0c1198003000903c1c1e41c805401030301680266030090042c02010b0842c0e0000c44400c3c503401084460b4000c02005844212001049044940c0300c1c2d41600f40c800c4017a1400345680700d490910300d15030305056000c1000c1d0b03006102144244c0988000d0000c180d55041044140d980a206152105211114400404126421500f0580c01c036003402e4064600e00b10715408545095401622a03966603030a000f0f029000c3c2000b130503502441802000c1c207040c407900090a00381c04980600000c620701000100140c8650007152100c3d030010640e090700f00e03c038002a8044c0d40a0001200001d1411107200015410b010300e0104480c0034024005098401c0943c658442c1d049840390481c0c22 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 346564127 1250 346562877 346562893
    0x6010f050d05010e0108060603070e1b0f03090c0f010c021e0613180b0d050c040e011803120c0206010e1602030409020a050c150105062505031204050d080c12040302 72
    0x1c00c0c42d0041034000c00442c1c2e5103880320340c54601e81d20f05164025003805e119401500081094036180201d85421042d0100d020340300b01da510070f15203410301c00da803038049001501101b0810b04c4080418100c000080540b8248070f003500c8a00115107101604e8802503100720038400100c04001e0604981e0610200a4145031810401104080c0c0c4225030364054140c0c410303210307a922648800381c0252a00a2801e440c07100c4a800d0b40d94490341c03101808812540155612103445181d030409402c85140d11200001401e0072208034207009060464602d4600301c02c50034500c00310441d80c8000b851504860251000300407a0f103c041514044101c84089401188014800840c291255100400d050b0f942521003507960f103c12100c8508084141045007150000c080041226880b0002102c1e10100412001c03444807690030380341c900e0500e18140150440c030010076817004036a116100780740901e0045085a05001c112407045450038411548807448050912000c2241103040602c0c0b5041842401035407100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 346565377 1250 346564127 346564147
    0x30c07020d120306080705010504090c0c060c020a20030307020d060e100605190302060d0b12030301030b18120906070302010b1e1e0306062701061e0f0806010f05 71
    0xd0090320382c0310382c004800340426094402c06004002c20b1000d0500725262100103091805680324040c00c2e140c5940130102c60364800c140c0360758035941c0032104015203800400020340c0d03024616000c503006e66898080c008480b901308401d0003101c41c010015031a00195070300f40311310080301c007504403646600c030f4511700d1690800303000d1340c0050700d00743c034001513094030700307010082a001d02c1e03510f824088042e00003d00c096159074084400803541c101e40842e0000e20701d40400d0003017030380d07151a00e49404080001710800c500800f070700b80110b2070006017404600e080e01005413510491411100010403c101041880c100030010f0000e041c003900000a41c0b410840100d000062400303a501145105200010b8040c42d00750942d00703d448901ca030281c48100103202007551168050329051141180101c2c0e00c121000031210389502c05640c4180a0b12940d440c40b02a14005e100300080b03c40ca45d003500c24050051048100281d40c800683e148a204c0c2c46510041d030300c0203c908003e40801100300102c1c549 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 346566627 1250 346565377 346565389
    0x2091f1103190f170103021207050916021519110d02180108100e06060d200304020f10270803070308010e010b03010305030406030506010c15050405062505030c0702 72
    0x40e40020b0011182d005004107000f800c00c88140d98610a000c1144440715070480900c0805044d0396044d1102000c020000080c01d1510034190302c0300c0e510003070103010402222800d80c02014402c0041d02101d02040042100c40c920700c10840703140c3d81024001503001074185054200a00c01e6406190380713843d2000400c0d03590180c0c0e100742002802e900381041c150301d103544e001c200186c1c04400700005202c91804c224101c3e48281d8050030b040d102d40c0d00070844c6050141154040f4041018440212030500d80c07200070b5001e41d8200711403da00c28002050041400c2c28901d008440d00b88484e41d031a0b12070003007440030090581c6201010718110120b000085a0350130104000d00c6681c1c001d4072000300d558581403030390444a805070024181140e080c4010400913000006aa00792440382c10b02050071b60b0b810b4012a0320b40308158010380f0764001c84041d00d2101c840ca90003140264001e0003a104140e03a4102c80011446d03074501c100e0400c1801d00040025a03211780055a005000d0105281c5420155000103032 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 346567877 1250 346566627 346566637
    0x11061b03030603100608120d0209060301030c03150212241221070201020c1c0213050403020d020f030a0e0a051305010501200318061e0a1202091f1103 66
    0x59600000c10b1080c0d52401304000c000d1408004014000e060070500e00588560301c0c04881700c0f4420021540700342014080d0103488980d24060310041c0c0300e6a490403c41c0494149101c180ea20801605040d07602c840713140212242c81c1e6106040448503244c0482c600141d044555603882c040800107903c100360760f11405001e4021440400030300d00315588000c00700c04081c5070556491010300030400c200050740c0102d604041820110b4070340d40000d445009500950000d02c10095006501a80181e55110b0651249003d24007d600301c039000307411030f0410390390341010601317100c001c1d40180420a50030381315000e0404a42000352079607141700d5494002c5804003040408071003625488074014041c41d40d122015802007040d5004110030414040b142d1605d070310a404220b04019881c1c04030750310b00d13150f07601114161004450b0081c4c184440480c99200c2d0b030000e11503200019035481120f00c0114150095850300c1000800520700400d40c2c1c1c00301000400d44445c56401c1c0003440b01002040c4c0d4061020704 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 346569127 1250 346567877 346567927
    0x130c08060f031507030c1701050306010b130f0b19050703120b04110c0105072303160504170c09181b0d02060d0e150c19021c0309020f0612041106 64
    0x300d4040006c40d0044c0007042c0d0503001e4210468220010012590001122811661003000060740c1d2010025507881c07404503030f0040c401c240c0d40e040300003403a0040c42006004100c011900300822082400d8100c4461040e50300c0580020151080385159450383d51001811160046c0000380368482d4000303401050f040140016141d035035130070802166540107000c0d007000000e03032550701484004490100c2c1301e40c0405801a80740302c241481c4440d649001d06c08072006010700048500c82007290300f010703583e514030114803a401000140b0105140b20700b8041e141d0645d01e00d103c040e2030000400c1e000b400380210400805075001c40595411409a01d920009141c00802d286020510b6941c400d0020720301030540d5419200800c006041265003400c170002d58601000c01d943c0b503100d000c1c118001701e140407031020010f03c0c4803002c6458080035a4155100c4045144256040f100700820345007000f0b85405040e25800e4050007e0300040d001405000d110900e0500080800e82824804041c058410080000c02 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 346570377 1250 346569127 346569131
    0x70e0109050a140307060e030a032a063c090501020f040b0406030c0f051812061f1e030f080c15060f0a03030905060705100c03050402130c08060f03150703 68
    0x4401113003018801403000c1d00160a00010016101010a56030004407401600b001204240402c400701c1d180510150b4807803101903404890b0b014213214004005109010140032482c0c0300301d411002e036040c03030220001c1c6e00075280c251084c407c01c0c050000d0080e00c070044034155401c0000320b10408400c406400500b24800026803142d0401d0703000742c101d0340e000e22400c0502861400e00c2c40904c1e0b005040320840c2500405298446589001150700c0040c0048503a040d401944100b190b400245008200c510180d03106d995141941d40000301c0107240c03e54506482c40d81d81030710a00100f102d047d00d44c070300284140103039840d1100280c00107003099100b01d91160b85241c5071041c4501481d0110040d0351600d0f0440c0c01680c0320746940c1e07028000c1c2006218142c0900004078801042c03050030300c4540140780d4030340c400740503c01e8182001030040504071400c074813030301c061512650300c4415485400c1c103c081680b10380310780c0d4888400308211100c0744005c4551600c80c2040030720004500107035542c01001c1079280 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 346571627 1250 346570377 346570409
    0x290309010c17010308091509030a030f030b0d02030d0305070c0c030b0a0b01030203060907211802091006020601090902120d02060106030501051c0f0f170a090902040806070e0109050a 80
    0x34080194194107007500020b802c01400801c83d08811914000c100300c2e094154480107503820340e5540101c0f81000e81c940143c0344210140340c1c000c001102ca50502f81e504100c1801c01108214010039001000b9426602084c81221514000c0e481a81c00c20f0071410705101105007591409030448068004440031b510000c20b100060352a0b024039404070100f400d00390305501d00600429502d0000800590801000c40b85107451036005400400d100f0820600510030b100038a802c030300458810100c00c82c0a45050780024a910b80c26035015001d50f1aa6400b41c4410791812841c00044d000014003664841020300e0440b100040400ca502c490703540a80141402e07601d0481d001e011941d0591050b030103000032082400241540c0d07541d8080c480d600c0106d0003055509400c125240f100200c00040c076059140c0c080207004054140504158800f99482c0b120903512620340c0010b9000c0c51040f46140c1c0e000c00c2c042481c940c020200701d668101d061409103070807540c800000c5c9654499510602c00711000144d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 346572877 1250 346571627 346571651
    0x30a0f050102040f09091115210f0c09010c0609050331050102070803091c0c0b0408061608070f0210021b010b0a06170901020702060301060503061306030c29030901 72
    0x10500071701d00d01404206091071900c4844035481c5140b240c0d4491101e60800c40d003003981001c20785208900111012008029a0071003021145086e1071601481030130030000b03407802c0703502d40440729400e4040e0760f0700802c08610b50341d240c09000c05120858240c0414801c60f1100302c14100030b024180000c2c0354080040804210036071950649070003150441d040b5442c1409850000002c98003420001da61940010401c4041403603070341d4042e000140300e00e09900c800552000f0b01c80c080e00540780441e0986010b61605c00703000c03501c072225450110200d69100c0025a0044c0500d040b0b450503100c0d070064480400c03030107010708200d07440038121401c00c0792441070010911500f4808d80f4101181603419039256410008051300c8000c100c2211520b003004100040c50400d020b4058425256019086903180d50310741340094025001161014061a60308100c0c5c050504140030744012aa04059080105803c01e881c400f226403500291311a4a40c0c0110111000ca030400700440c030810441000190f654a449 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 346574127 1250 346572877 346572899
    0x80f030f0615030c090f0406060e100318110409020d0b011802030405060c03071202131703070c050603060316080a05010501061713060e010504031d0a060c0f02030a0f05010204 77
    0x341c41e00340078020000b240744400160004894000e41d080c40083d88032180440050400c4095010880d0040d06040001840c0354100c0a10383c200c0c141200c010100c81540359048085440100c000306410308101d44001c02300f03a05106a404032000a08003146100c3d1907008103902510383c0004541a10500d030040001c2080c6220b200380c0450201015450760030952a01a5100406480a1440080000881c0026009a807242000c1300d007030f041551a16642c544540d080c100b18400e41203042007e80050345040310110486071400d911581c44080241403e0500143d40c2000b041d454040c0309010b90300f14078181c000d0002c00144481c4004013200025460141c1c25100180d010b0f2003807101c02c10046800c54144c007005944800186c06282e002c180506044010300884201c44510b546003074113200625610007010041c194141400c440c1599440342406134035501c0c1e02c105400603160b0000500014a0f03e051348916900080c01c9440b1a049603c40380000c810850040f501c0d46c0d070008041201000d00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 346575377 1250 346574127 346574131
    0x4030222051f170717031804020906072d050307061505031203070c080307020d030e1b150408120d14190e070801020f04030615030c21080f030f 63
    0xd00046600c28410b0307850000c07890030314003d100201000010001280300c0c03c10901d0024503070304d61140003c120040e44a0b460b6403000d0b292041c8200a080d0b40169410940211a170444000e44514a0300340180c40307240750141d80d02c4c020100c0504980c0e03680100802d003083c5110b91130140c0003955845506150090403902c1b21a0f80e00084011500104070a680c04143c03400795003025868255a541c4000e8111800148058010040c0c100071040c082000c2e0b000070388121640450b20100040e02e140181256511140c500d04201060000082070351403c16103404512441c0361601c03079040945a00e16541082c0525038150f010b18800710740004003100c1c0d4054840b140352010941c048a040403241a0b42c40c603042e10309416510b4440c00840b03992602040700100421842008644405803502c0c61112984984001d03204c490070b085104643c20349050006080f60340c04224070a28524040106181c2441410151540307051011240d000c640302a0040201c10f00c0300d0700c826070700d01e402c02c0b5a0b1002240 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 346576627 1250 346575377 346575391
    0x12030a0302180a35100507020c010305090c0d03120c03091a0105210c0a17070b040b0a14070b04030503040b011401021203150a090f0b0d0507090207080403022205 71
    0x102e0141044131400c000260b04070480300060b07042a9000620690f0448070400c4001c4c0c0315840360b42c12205100c00242e110f64010a040d40c2503070701a00907040118107071030040c0d62007070254000860820003450540e603c44d01e442c0c402e08005841c08180407a02049a09414514001c00d4407100b8000070401000030803108043d004400a40c1035040401180c03004034070200200b41140220085020040c0130442c880742c0100041480070811b4855100d8607003064800c010360759034410410046034645a000959081d5201401d480e81007940c001002c03102080b0004d070382c4200d020104686c4010850043c109407255000303031601941ca0610b481c003c040040c059020000c0c08504034041001c90b80d0100d10a8152660649400c1d200d86500940c68181184490070750fa10050749400015860b00c0358000b040d100c0035908042148000364814401001d4103500c0c001c00c5a0403400c41805010010b03406084000e0050400340e042649079404100c103080b05110b80305801c891001c09400c04402c50264540c0114 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 346577877 1250 346576627 346576639
    0xe0a0506060c03030f18010c020703140102040311060f07170702010e010f02060f040c23090714030103080703050405130b0a0b130308030405120f18010203070f030e12030a030218 78
    0x681c40303926070002511903041d0200c44804140748260a00c0541b189058801c000c1080ca1040031003c2e54485140c401180e51028070f42d01584d00c004180300350f40460b600b0449041040d07a0040401c8040da100746a280305016003880b044003c246101100800e1065148400d9900d007036500003d0200101103d0f0a410011048410030f580d40d4080b84064010040d40c000c290b4036101d80c980300620506070742104940c4990204054003140c403085103e0303500081034401c1c1280f92540728007103989558640c447e2042c140100010000075005400074808075010f45800c40c18039840b1400511514001510446c0494a400d01c4855512700f05884000901101c0700080ca08003ea40d0584100115031101911080c4040b000406010050103e0301c2850a004151030341c41c0603440d00e482c1c482d009110507401c0340f50542d2584069500010032a60180d400940d00200001b46030307400c56940c00f980003442c0d00024050400518408108043d02c6a45e001c0c0c0c40141c1c8840609060410140707052981a206031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 346579127 1250 346577877 346577887
    0x20a110406180b0a0e0a270c0b03071101110c150708150a082b03050118090501150b0a030e01021e09011b11121f0c090f0e0a050606 58
    0x124101e0081150b0000300b100200b1485800c000081844100e5408a02c0c1041c5170b1003000b903141200c0c0c3c800600110f2036030003040e0b00e004802c0a810749a4206100508165041c60b003030112400201c0515802500317403070454505a82d80309905d0945800507a403000b1641c0204066018641c14400205403907042d4290150a2400420003012440c020741b54131484224000040044d4070303492000f6001d0a4a001200d01c070024080345038114420184448800c0039204912001091081c041c0a0480d401d681031610140112643d84004100800b4125520341d1380e944800a0468880e0320361000384000151030351102c41c04540078040e52142464601c1c5030744104031813925440751040c0700d4500f4240340b5003d62200203c000584000d0a80b140c480880f0322215001c40810030111a6841e1943e000e80b51284045010100340f03685980e10052003080181031000750300c2c020000d40c00328401901c90314240b400555102c0c245105034480340c012810680d805010000c9a00c958011f82d500403a007500c88034501 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 346580377 1250 346579127 346579139
    0x151f12030e011d01140f1305030f210f04050d03020d09150215041a040507031101030603020d1b090905150c0702010504030b0702030403060c051914090f1807020a110406 74
    0x82c1d081420400d0510101120a503c5e41e442241501d0010094500250741c0340c0c20b41412403202e01e0b052081a220f48910410b0013a0f40c90086620501d000c10100d1000d4440506200403889800180110852201c140800100c5030345498081400a002380c0142c081840001d600604014a917000b9089445402100c64000c03940002d542d03003000c0021a9110207074940f85004454080900000780f02c15501e8001c2c04140500450540100c1e40b240e6118410300008400560540e20750b03200195000c940843c0a0001c1041d07100781c0303e1500e00c10b00c2101c85a94940b034042e030494030030110a840c91b500480c0c12450384140c0c4042140c0007014129542c1c2092038a6000034460b10407400700074407014108001c03030180e90080040d5806586e0106083c006d84920704401415500030300c1ea00030000300315401615000380162041404d080104c01c00c40c2c50581000c09000e01c24130300800303c54000050103d42550002c03d001c585001d102e07164040c010040d118180340000c4010400c59511403403400c0b01c00c00030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 346581627 1250 346580377 346580417
    0x20409050718060c1e0b0f0a0c091412071802070c05030114130f0203030301231207140d0c0f030b0115020c100c0b0709061808151f12030e01 62
    0x181381c0d000c5040c88001c110707240316480001c1d00400061002c40240c050003181c00d090300b400b52103409400340802c907a001d214001c03201840c41d44900080c1c05104821902d40d414031b214000e4542c00603034119481c07075a48003410748a02e010f429200700080e0340418181c0401c100e00da4050024501107000340038040010081000174000038121481003100078900c0003c00c048802e0071003c02fa0008e09407512580e4586c1c002d00042c0030341118860490300d00e040c0306158074150300301c1035031030500d50010030006040c019411859080c4184060388400c1071031341c810014034081e4080e03001d405e0070f40703248010704d1441c64004000181a040000c58914540004210f2940050301500d1083d0480364990f0418081406844e80c3e0304d107840c00303404181c0e000704105180760018400700807203000e0750754666044454100f20140304030b6805041c5294201340b070040324070030f40208856040f64015084146c0e4042d0042d070081d21081640c8185840003070910200107242c2c0144002d80d034000c0a081110000c4580400c24039 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 346582733 1106 346581627 346581647
    0x4060b010318021201021c0c020609061b0a0c021305060306090703080d0c1e02010902040f0203010305060a0903020f010222050d0b070807030f02040905071806 70
    0x10554071034800c9211454461101ea40603140c00d03801c0040041c04805560203d640900c410301c84501000000900250000400103c1e811214406410405d00030f1404829030800e201b0018555601c041807414540c40e01c48542c1c1da000200c1007959800320a10340690004105440469146c2503a0b03c01d6000304c0b0f0481c1150669501c60032644d5036000c0300d020007041c15034280b020418090b03580e08032040d007094900704141228860698400c08074080054500103070b4580341480203508080c0304041d291844840700b94503560650b160307150ba40001030a2074941550b81c40013401854070901a0740918210701d8000c1d555079945c480541c41780088541820441201200d0014140c07034568400c401e41580020802040d64401c10140d540003401080481410780702c1c000740c202071000d403000300090100704400042c281081d40b40100100059001502480d061100c10b00206801804100e = true := by decide +kernel

theorem cover : BRFrame.Cov 346402877 346582733 := by
  have h0 := BRFrame.cov_init 346402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 346402877 ≤ n) (h2 : n < 346582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
