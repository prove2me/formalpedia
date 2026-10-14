-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2968
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:16:18.547995+00:00
-- url     : https://prove2.me/submissions/6a7608ad-ceb6-46a0-84a7-9bde6db19bab

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 533633093 ≤ n < 533812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 533634343 1250 533633093 533633117
    0x1030215090f09180a08090a060915030207060f0c11010b0a0506120a1d07080c03190605091606030603020102010f0204050604030311030d06030b012d050f01030e03160201 75
    0x5060340501d400c0c41c0d5001c808103419120030b0070501c94299110a5010800f006841880740e403a00340301d0007080a42e0b61450000e0f42034420708091081d0002010031345460300c80103140c864100400d80003034400c08201500026004180425500300b0300031051070450402211b12203000182c0109206046d9400035401c004c0681d42030303d041540f40b011540040c00036460021400075804281100a001d50307515541d40420200900268403801c2a000c1d0450044c800c0c10304100f4614504007180114a2095000d00c00e01700303030100510483c032011944180040f41e03075203c509169061200d030b0032800361042d020100000c2c021754103801c0070301264000c1c0c000704204501c010088003648107501900b81c102030100f0041000a1080100d0607290b600a0152030400c41c0c0c2c50b1400c020380e509036000b541c0600048006008021a00b50720030400110a65480c41419480c1c036004071a450900c241880782c90048140f03002640680c10420341105403805880c1c2d01c01c0d2451400e142900d40040a900040e00d110100d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 533635593 1250 533634343 533634379
    0x190504090f0e0616030905030d06031506120206071a1f0e04110d0201170903030105100e0d03030b12032106010f05040902031e0403020f06130f1b0803030f010302 71
    0x10340c02c4800d020340074210715903691550541c40b2907a40f00e503104142e518901c41021600500140031042c400d0074000c1081c916504210f0b18001c9002d040100c29881c0110800a0b6055910442a0706a0585045072110007a0500b445000c140c070bc3c003a00315090600411250000c02052356403841d001c0c0e070b80c00a96586400940401140032100100f4240c030520454415180030026000c2d65031051502100801080d2000c011025068880d01d40070f51020006101070302e04840201c41e248000c0c031f0182030900f050300018a1241341400050185540d6002815050720380b4200c0c156000d1964048035178074000c0d113014012900f071284c06901a000d614001c21030940c41221400360300c0c2c446a0380c4e40e00b82400e24980e0230003035001030140044d40417038003090182074810307100e15403085010303401803c08040e024403400d041100060050212103164990040000d42c40343e420b40c0c02d0f07030b00001d051852140000090340300321000d4208090600c4040200074542c19461034143c1664820345410110750110800 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 533636843 1250 533635593 533635601
    0x7030614060405121f060303020d0c0206031b19260f01030602031512030919050307030f050a02042a020102030708062e030b01031d03090d08190504090f 67
    0x1a2940c041001c101c02c005515140501380c101200c003500b5144080341c050060017544042400b039011582c2c98840c10004c5c990140203a000d03031041410501d2030003483c0d85c000f0b82c072848000c1c81c0c2c000440d0501c00813445810060280d034070301c400c1444217180b41d100402018005c1009002c00c40195520004085c41000351810083c0c06041d03107030b43d110441d908507a0344001a41004014200c0003503510144241a81d4131000d24008000d2500030b1541c850a02d800e0080461244691140400042104101e5500c0015014003101c0c1c03c10104d400c0d100b03462810600300301c8281c8010b036226081001e545801040c104003400304951f000e095001d250b4240d14140d00b44d010850b852070100b000300d00040c03c2814184d4400c03214034241d13402c10300d518003503a910344c4581500700b1403e00002d03650039002c141c55070076101da144141e174035200202800700c00e800000c3c1e0381d1003400b2440b4081c2c4003988080041000c5841541e031114084c020440201e50000002841600715210f610031181c10034010381c48181d801e02c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 533638093 1250 533636843 533636879
    0xf0f150f060914060603090f070b0a030509060105060d0902210c030d0806090114060702030604140c03030405060a03110f210a0e070302060a050d0e0601141203030114180f070306 78
    0x8007260f0760b54850041200740e810040442c00030b40107007a09444218000d01c904800b4001ea0111319850350212400141190b40017881c0020503401039006001d265a03a10a0720405030301c0300c1000c641d905080c400310369001103500052044040311201280408008556103d02c0c1c1026002c90701d000c0a40c0c007007111080d50a9415982101e0100018825000040b0303000240000142c0f10300e15000c016804a031400d075085900b510b03030102e10005940008000e01c560320040c1400c03001103081ca400c2c000061001c1c85024210000d01d580c4010000c0e6200841c01078500d01d200d40c90460351500c041700e6204640c04044803130310400c44441d0f400105101d0f018480c50454000110040204504642c20f00000c4c1c2e02403145d08043c41400d00c0300603c604820b004050007012544007802c541d501d41400d541d01804401e02c103e01c165a41c0e000042d42c030038000182c904403a0101490617817048040040b4412116003030f25010700004e400300b0030001d141b084c20310034016881030b07070100801c81e62035500d8400f60740120 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 533639343 1250 533638093 533638121
    0x2041d010e0a020a0c0b040b07080c0c030f03310219080a0201120e010c020a170a05031f150503071103092d0a1e060206070504030f0f150f0609 63
    0x1d404220000040e82c081e182e1000d00b0304004410000941780c040b1071781400c6900b22403000301c44d410040c94a40c40000c103504011900e4600c2e0501029400d119120302490f40c100c5800c840100c009a92141c19034592411035801c5015110081c404214010101d82120816402009008424000e03100901d82000c115840c800241240d8102640116205404406503110305034403a002410303115020310416055020a4000f81140c1c502c0345011030b404001c5012080341501c05010b96042c0e9608503084a501400100d44d14092003003401701c208044056400c011008032040e19a03a01290300100214003070005c644030b000805146581691741c0e0b108508a003908020701503414010781a04588505401c44680f4600184100759000718400600713a03402080c0d0b8041e40300084040c240b8440200000e4491440a0034441ca03000d180a0141c0c0300e0781c031005141d44120115001030050f15550142d0550b072082445800c1c200080803980900311220f480301100d032a2030400240e080c1c1d244240350f0303c10790344 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 533640593 1250 533639343 533639369
    0x61f030b04060f0b2709010e091501140102060604090822050306040f1707020d030806120706120e0a0f14070b03041b060206040f02090709170102041d01 67
    0x4544114003406003a402690442c1d00c414000c28503800c00044a40544415000c65890310b04442d82129031011016500d044000940c6081a550b1105801e850550310400c10b609010784902114a00d4625100680c80b4a200716000110718030540d1900002e002030260708866035500c80b07804100441d1303820f81006060440030005924002c01140c0b40200088241d19140109076940010908040701101e00b2102013004043d02d804101d1702082c04036220000380c200f142030041581c0400c148086141016051010010010f8850350b1940c0180e030740d41110409482c2d01941c3c503c1d01608c0245e406074507420340340c02e0818103201c0d1b500002e205104160480b09d10b8242e6003941d107070110101a0822150000e000305d00f4003091200700d40c0f005600035481340b44040821040801c000c10039212603003040c0c085401c035009010210f0318080d010015140c045501250300c3c0c450078026949500c0c80d0f88810540350103401c254402c0007042d40036000322071462214280c41505416100500703102402060049044 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 533641843 1250 533640593 533640649
    0x150f010e0d0b060406030c0311270103061d0a06060501020d0c030512070e0a1d011d15010e10020601031502090607200d060f060b04060e041a090c04080606 68
    0x500d050140c0c00800181c000a125a141d440c1c504420107d50000c2d110640e40844144803814030340c0b400300d038075003200c102006074040745000040b40e50010700c0094202d0b034a6000c0c6a20424659040b04a14810001255100d01040c034000b409012203120b4540903006070500f00710018040c221010a450f45580c3d05440d100c5400510021000f0180c018010400d1840300d0052a0f25020940406003010725a1079200b800000c039510440407050308208a072401c141100c440a00b00d00403850740003076446421607002d01511004844106146003010f5001f0002e0351020704242c3c000c903a5605a81c01413041c2410440c9141003201079101d07184400b904050100500f002003403a40c811140d5a1a40110603960f00c8071403c005096103e06400c00e0340c441daa1000d0440224800c0d1051200501c0c6802c1140c0c1000d241c840054607001000e03034060700454a403904981400d0540c00401d448180041004d017241c1000c5071102451313040b44c002d5005500c1140081403841c50101c180300c2d40c02c41070984004842a03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 533643093 1250 533641843 533641853
    0x9060605031209271008010606020d05092202040f030b0a06051503070306030804090c032a050f070501020f07030f1b3e01020106060c11040c0512150f010e0d 69
    0x4040921031300c01100750034050805180611030325008400e051003007684c1508240d0401e0840302c160f8031460940d03004400c088246a000425a240698116038603107600c69200001c40400d1160010701508903c002030200f540c150b0440a0416640100e580a50b56a82c03c0e804902316030072800b9880d0b01801034000a81d43c45480300c010743d8400d0040c070f40440c10542c0c940d640e59042c1c002d03801c0158841c1d100d00d290019145d25100d42c240d401d90070900e03a5110401c2a080004441511a01200700320700020160003068010080b10507655001008668402104411034900e400159088001660340c43c00c0025051003103005400d42031440c030005080300d070781d50b031040005090246082e00656550300300f101e0807950048000805000d036003003002502d031400002400c441c000e4002000740200010000007092260791003d061400c01d490018410320014800d40c0c2d280109007514281134100b0701081140c4081c40c0c11480401000d943c12802c46480b80015074200302030f40d038103d8105000381a048003141d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 533644343 1250 533643093 533643109
    0x140c0910050d030c2001080a093513050405010b132c0403020717070803031f0506070c0302210607080403090b041d0109050402100c1a04050109060605031209 69
    0x9200b802d00c0c0c4100c044507551260150702c4030034a00c1c0c07820041c0a00b60506c1d43c1103680c00794002c1841d0343c00c102110710740d51103c0c881020302281e44002c50721361a01c0000c07003007010490340405114803c3c0c6901d0310034104900000030324034020240907a0804000040d4044881c064502c002e1080d0700c1c0380441401c00b80d07003410b10a4400214140c001c00540c13040076085c401c1d1360f41ca008078081d90107405614180003d0b04440d009400c07076101594010703841002840d00c0841980d0708a40203039401c0150b05440a450022500d26421065000f40001215000c000d01000484200e0744250f820344868038504100c241a0780d201c000d04e885a8000a0009840e1446260780c50350003442401c120100e00e444030002c5c1510b03080354129182040079076140c040502d2201074038a0040c03521680a00c010314140d0f011034100e412030711b44c40c001d10030303da01004100300490a40c1ea501d80d030320441c458410300e45400e0050181c250400180c5200d890072802148509010030051013082d0b02c2400c4518005284041c42059 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 533645593 1250 533644343 533644369
    0x307020a090b040b130209030d081605091216060215060a06050705011415010207090c090b1305061c05070807141b030c3f160203010603140c091005 65
    0x105544180d850400e039a070781044a03440d1a085d0006807103d103a101030500d8080c03030104503014405076104002035005800b584040714111445d000d61a0f2000c03001041d000ca5040c3c0c00700806001e000d0698240c456500024004c0703a115500311007130b08460745202420200103903071032600700b50245000e000041c00b904c0100340759445200000381c40b044515551000a50503191582d584d085e0500d0b0150341e41e8100900805054403020070040340c101514094007040403803140d02c12040000caa41007000c0c4c08005190700a000c00381003595205c0c1543c0201c0c540e00c42c0c140312042d540b0b00d080c02250203603204502d0780d841441c498039000c60610003050500f515401c000c400d400c43c9009000300b0608404180040d201080981e40248130210700718540800d282c00c4140300300701e10b00d00d080c20000840d40711680410700c0442000e00c0d0f6591001c039116000616400d01020f0f4041d030800c00000300704140c0e000035848044262094900c01c403403c50410841d40001d4981952544411006000c245810382a25442e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 533646843 1250 533645593 533645599
    0x506030610080c0f030c100e120f0a0f020d050a03091505030609010911040902181f050319090f0506040330180b010b070606051c120909090b01080705030307020a090b 73
    0x4022030040010002142d4400c0400091900234141d50f50382001034440c8072400c24000a460a120700c0303104542d0f1010b00100207000009d113541202c2c1503440d044020b0001da074024098601003100d50901500c0f54407144a90b803002034596034025182446102900d009000080c00684141d2a101d0001d000d016401085035001c40704010008881800703200800b40414840110081c80c1080010000c108910762a05015181000080400581c1c040100c9900c2107480301000c20400760000d0071801403141e4080100f20403120300b22401030000001c0c01341e10981c4aa56002400511100041c80c52104580850060040380d803000b850082c10b604810b0380341401c009a40400c00300350300c1d40c00c2900390a0340044094140020340400740b001d24083c8030060705c410380b08190890f140c000800c1c00e075801301d900a80107201814140043d03d00c6142010700400101c1402d110188281c146603d08280a1207800020b124445001801d81404416501c0c2c0603002030016504500d0040d00501a244c1748100740e038 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 533648093 1250 533646843 533646853
    0xe040209090f090322030c060c030203040e090307060903320d050a1404031101050601030218130e060c04050a0503060c0304080a02160b030a140f06010e0402090406090506030610080c0f03 82
    0xc07491345a00d417403408009072840074403451940c10400c20320030082d0807a808100e8603002d0035000ca03400104840840c3c203081c0c140c05850340c1b00d14605041d03000e210300060400c1d00b802540014542e20a144041402e11a000d0983e922140845180d110340d07540c0403010840000d102d100705201456111651100e42c0d681c022810300300c0b00c500903204410413034003240803882c0103c141d00c4400c824454a40c0c00102800c00710f140c250381c000b40c0c42c5503030465075034984140c0400d00e01c24541d01564104086403102041201d6190800c4500345107650414050b0782c0c01103c01e2200000c040c500018014014a10140300501c6c58030f594484e481c4690010740058254803030040c40407200034854400c6402020702c04a120303180d00300030711560305503a0b0004840d28000c07007a1082c01a5a50065541c54110809090603024000f0107000b28001e401100c80c0c036540189460400210780c80b0a4114511802c02141611050340e80c006010341c0c001114051790b00180e0201d0a11185130502c520654550300004040b22 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 533649343 1250 533648093 533648107
    0x1157030d09050d170108061504021926060618010c080c0601030303140411040f09170307030501120305190509030f0f1207020d0209071404060c030e040209090f0903 72
    0x4015035014074011078040d8060641480004d60001111801e00505600958254505440140e8071100548450f5416124281502e02651590304031040c4046e0320480501c40350744400d025102c80d56080102c0148014506042c041088002205124138402081c150401215400300103090080e1b41c002030602841d11041400705520a014002003807600c402040e0544c19440c0c0142a9161070766003c1050003120240000aa0340314441c0c400c401007550002411028010326001070844a200a404540a040391104000c4540011441002991814455039a030b400844004040b440f4010b400103c0c1070107424070009440d05940006842454880e043c40080c000090901014100c04803007940f000c4a4a403414005022403941442124507690408100d50045000641d07941c000074881c40b0218000b03000640559008e00494000d011004d41350340c0c8410f0003410030f41342c00c18150081810b40d2942c01c0c2c9032070180201d64119001410320320301d0740c5854041d1101c0340700280c103014050005101d16 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 533650593 1250 533649343 533649367
    0x506010305060907060804030804150f1107050d020c01080a021602060309030a031a1003110d060b031509010308090409060b191a0a020d12115703 64
    0x55018601a0340034080714100f1115a9240086940c001014820710100700804203800c01c4645030700c282c1140b8804030f80010100c61200400700080c125a009181c5021014500c18040c0038243c6207228000303c070341400e0f01000503692030010080d51800607008800058014180d034010340b1850050010324090b1810070317800506141c00031a0002d90a500105804844a915001c0d06103501c41c204600721109824001148181000e0f20800c13080c513854a220304401c030010021101c1110629001f080060744494450030706920644010f89010b021840300010340c85e101d11a14101e0b80d00003052443c1064240500c0f002c0c0c03601050546000390717901000e80d160780b91020040030300f214454000b0002420403811400035031022080b046400010301104004035000642c01000c0381c107900b0000007c2d9030b81c001d0880605820401a0a01d00002c181016010f0110b081a82c40290300c2e52606d003669880341555010300c15401c04600700880704046403d21034903501e10860850038080a40c0d10f0300c1c54070700e50 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 533651843 1250 533650593 533650603
    0x90a02130f0f090b0f0105280312030204080609010513020d03051c0f2a0804020303040902040f09060914072007030c0518090a150e0d12180803011a0705 67
    0x9002d0301e5a1a054003030100003c0400b03041e0300c40300314100707610301c0d5050001007400010b44001013070140d01c0814403681d13040c10140d00ca0005640c00074680300da900e13425600501941151090440c64403074500880e0031510107000300e621030200d410142d008a41c540c1c00f08448884404000d074144401003085002c1d4a40e0b6002070b4030911000d15012400d4960f04101008950242d0303903c06c110300b04107207000c08005142c10000820741641c83c200860344c445000103030651117107501070740e0110b20001e40000d01c00a81e00304c85045a54180080103802e9882d9800000d4484100124041c000c0f84c400203080f240c001c40031204003040d051050520301d02c03410b030380c40c0c9000101d0f04103407011000004104403503d03083d40e002c0b600003529684803601b407c001a100d42d0700c8040b803200604804207680c01c8030010407982d01c100850b05d020000c503000202c0c81400604110784480785a046281095010303500c0d602907050085141f0b07401080103195070301e44003041d48440709a03803481d1a0072404000d00710100714100f007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 533653093 1250 533651843 533651861
    0x12031b0904020a0914030a2114070506060901140907140409090501060504060504060e2e0e070f080705041a040302190f0504050103110111010b190e0c03090a02130f 72
    0x1244c004440c107009001d680118814040c0e40f00f9401203645071f000406d040b0300c100860f10a600b20800c481003c050035a00074a104181c54062400811100248040058903d003e8042030300e860180740d0b22307800b03100d1a24448045030307600800c0c0c0b140469403541c85800704a5245107034140c86401c05440d14004030603640c1d11803013940c1c1a9141c00c001d0016144c40d100e1000101811507040040503c3c0034003981e6049002403070044800102a4074101703c802030b140400c0c00900e8040343c0d400b025120201020b452005440c080d00180c1e2445401c0c5065000c1d61560f4000d00c843e440e0241401c0c540303003141d501c1880a40010343d05000500c030000050f02c5a001d104080e440c080000308003e0704003800c111403041141d00c42d520a0303042400402c0403503807925002046120070f1034020441500100003d01410fa10100140c12034054140210740c090008402419583c558501102946503880c01c00c1045c001a103400034580c01605107000103162600140f203000c2c0c4800c40108001e0703440c001040440310100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 533654343 1250 533653093 533653097
    0x1b021908120d1b09120302070504050f07030513022110020a08070f050a09150e030703080405010e0105041d0403020f0d0c0213140a0e12031501030e12031b0904020a 72
    0x11582da40d0b0903a650280c1480541c0741001d19542e090981001880707800c03188546184510a0b413201c00500d4400d200c220017625000c0c00901260801c0710120f4004a0201c0f80c0100181c585404608091103100c24180666001003001079140300b5448601030703821f01006500f8240c0724484002ca41510903001030040100c10352160740c140e151001024250f4056042d6803000c002080042052080d0842c0c14403040e610050f03410146220064800d44451042080d200d905100c0c18100000300304410000308107942c4281e80d03003040009803600558013400707540260048400c1044e074201101c25180340c0c3c0755210f8043d204580a640124007a2130800041c82c0e1210300192480c42c1ca40706505000f0b0b0000d1070042991001c010f981d2131104414040c103000782000c145180c407241095016501088034003501d8082d000302d00d549042a00c595a880701c4003100003408642012a9154001004144a042032007008041e07840d5a45246000da0748503003010360340c180c02e2810320030000380ba1114405403680707030275903 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 533655593 1250 533654343 533654347
    0x40627020a2705090c040312050f070203010f0506031b060702040207050307140c010f0503041e11041107110f15031003140a02130608100f02070b070507121b02190812 73
    0x2290070b101300008000d020703401402c8200001c0000500041c2c010781060411314105455540c000040c2e551882303464000f950540c20320100300306407600c0d40d000a0141600320121041c100302400c264041d101d03900c1c2c1a82d8082c009212110260038945c00400620f440740e0160781c1b802d0800d980362404107010302d0050005601041a420b02d039600900b07010402509800d1150440c54035079a000d021030340701c0000d88884014104040100004000c8400b245d40d001081403004108440050b2240d411030700c0191806042040714420344c0c2030220701072219480151868400d0925455801883e610141c04d1080d0b24500a00c0040403401c4d001410440c01000805000c01e43c07040d00400c024109015266410b05103800e204014903c0c0000712051080540803021884824051003107000740501000940314945403810801401d80c054000c2c8a190300c5807204641204038117a04503600401048482044121041e10802614000c2d100741d500d04001c1200c3c10903c1d4030b80d80c07a43c1c117002040c010315a441c040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 533656843 1250 533655593 533655599
    0x613020301261207032001110c07090204030503030714090411030a0c03050123040f150f08030c0a170c0d020d090e0c031315060303050702040627020a27 67
    0x214030b03460070004404010802035601121626440c0300d0460001e0500034080403050035006642120014155072030005c200008496802c14000c0e4031100141400e1b0045800210f101c0245100360390030303250800000e50071940c6042003aa54844600d41d101c5054005001d08583d6640c0c5005050020130049507054882c1403401200b02607550100301c1c40181403c20300140b0814005603c00740144441c1540000c140e0189008140140310490400454608006200d84902d8035000040f0032940b03003010007081e40f0355038070701d05803a405010408202d58203c00319070709c0420300301100004c108100d03042c038034608815010080d00d040c1540c115100540c00c24000c841d40507402c040c0010003010300c003070740380220316183e6003560107031100a26082c403d50a119483e0705005000c0a800d941590341c40040190036201e0402034040d030030a41e8124815414030001180ca0200c2e02d030701d101d2990304060002d2595551503c0100607401030403640d4100848403820400c610b86036050b00c03e80201c2040d10307079141c80c2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 533658093 1250 533656843 533656889
    0x20705010c0f0804020907080c0f070507140109140904020a1203030606080c070b0f04111c050d0f1b020f0a091a09090d0f0201150e07030606030506030309090613020301 74
    0x30b0541030042032001160411003d40c440140c4554042c0742841e007503605a45109418801d0f016941d65102e5441020803220100500041c000058034907021514800c128010011079044100d8020711800d0850041c0503201400d00c6a0702d41d4115100a184070030f0107890f031100901d00346100009a0000c0e4071800c0400042ea0000d4403c0d4100601d02c0c4114580151074482c0c0d0b00f070680150102a00c0000b503070005061145140c00c42d04c03541c4008000e081240c040403201582d03007004407020b88407805441c43c1e64106601800b21031104060a4880d4070942c107d21a8000b12421a030341c081c3e13003143c400e465400c40d960b15000d0b00310141020050005080c900d00d1a80f51500d4140c0b1065405490b4420070300560100000305000c80441910744410782c00c1c82c80004070302619140d5207008035100b1000340030070a01a0800c440d880350b0010f40c2e007040120349e200012401d6400c00d4610f0703034043d0030400900055007810810194001e402402404000c51440c11100880e4800da02158030010b0030081c0e054108 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 533659343 1250 533658093 533658107
    0x1106030f0a0b03010b0303120402040f050103150e031e1e0409020d0615091a07021806042a0f180b07031407020117040510050a05100b12041113020705010c 68
    0x2c400b40c001308489000030b00465908c7c400d1194a100c2850010001000c40d40c441d0405c41700c19005d44000e002c19690307403070200c4c40180c1441055000300d0600e114041340000c00016204907a1410055244046840061003502e50145110249060900e651400401039841c0184000d0404002c0140d541c22000e03030010454010745c1207071000501800c45074000c0c031350004480060b210310640b0785250b81402c4075001000d100303e11009400c404481850985401d5400e912880b0300c4082d07a00b0f10141045000d83c1d0b11040700714810030008094040002002032107081400310444003800c040e605200c0050021542001c2648910340440c0300280f034034201a4050b1001656242a402203420300e401603001900d0b200b51a450000c040e10184006824030130100800d10618151203020411410701041030b00c0a41011944809280159100014000d54800c110350001c00c0f005002041d40d202caa40c1c2c1e0096903110501e00707178050503c808001220200388004c0c110075103e0300c0000b0700c0074600d180103410300d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 533660593 1250 533659343 533659361
    0x30a0b1009060b0f0307020a050601031203060503061b130305120318060f0105040f181a22060902030a080a03020703080a1e0e03130e0604240603091106030f0a 70
    0x215090640400c4101c030702c3c5003501c1a844004034056101c3e030781c50780e04030f160102c0104068040d1113402c0001050020719620000300c40d480c0d5405100d450380b200e0074142d841c141900d503400c1c0741100701c0b285000d500340240540102c1700b01034580700c1d4890340c036200c151034004462a000e403174002c00814000200d0b80015000d055014090290040d460218083d40864038140b150602580d101c0312801181d0b01c40340e000e00203601d10144900150800c07800e00000c001000300720305680110f82000315100b040074003102c100c0507082c0500d0718403130f500680e0f07108068558404220b8061048400410000321080d02400c645100360350016251100d90030003d00000000d4000002c05180c010504135204403403400280700080c85001164204000c0200340c5107210b00d2805100c600e11204001c07a0341140304801a00400c800c42e01409220440201080c0c582210415080da00f191890300b0004c9600036000300d01010b0040c0d4012042e06523030408540e855008541c0901e690b08a4001c10a442605110309840 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 533661843 1250 533660593 533660609
    0x1703040e0a140c090406030606061d19091e09080d15053d0201060806090102040609031217040b04030305070212040b1303061407020d0c0507051002010b030a0b10 71
    0x8902c804010703003100c00c1070150559600c880300040016aa48039074200d08021a801001005401d54921004201c00c0341c4e060090b4040a0b09600080b8520b0010030018040400c2da0079450305502d03200c10a03004180d41429a01008016000311141c080948141c1b40750a018400c6036a80d1a0a024130b03004a43d688000b01c2e42c00340000d4018040f949451900c101c440301900078445040780e440045030002d50005142400801e01b071012580f0756641034010740120340c0b070001212101c0d1641804682030303000707600800e800074550120800224141e0526802c00112900b001c5040804920101c03813450003c0385d042c3c40300c9034a04103110401d54103110b0349610111901c080d210080e02d1040843e1548510300c10690142004503155188a045440700340040d0b5000c4020010818003200c150403e0f041291030901500a0040020a041c01549440d241d0b84e880300203001241c6c184402c014081003801003500440d0360300c1012518a40f0f0410014a000340074500380c0312103151032540e0300d644244030340111035 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 533663093 1250 533661843 533661851
    0x1060809010513020907020109052517121b01050f1608070c0209090c0316031a040312050403051c06031101030e0601140f030a200f030d0c0602041703040e0a 69
    0xd00100381c0380c0d080c400350304075044070340380c6c58640c012409801301c00d00140850107200e0a208416083c440091400c440c404100c1102d1540c3e0b030511120400b541d8005142030b0000d825182480c0804001003003107400080c44041c0c26030410100a00710b80b4100c51100021010f4818400205c0e218030312032203d04603600d4403414510303100304014102c42035000f009018000c20804100c1c1d012083c0030114005001904548a162943e00c0c0447e2a0f0079a1000742c9083c549000004012007015600303030301c40c6416445410301030060000c0c020050000600c25010081d087c4a0b8040002400e84200201c0010850120b80282581402c51123003204982d00350625242000d0b40d20721000c00311b0490b044409405c00707070030f2003c00a4085202c2c0c112151004d40e0501608102400300b242882c101440d01e6801e000a0603840c44003004d20440c00020050300c4d60541c07202d9040c251a900c5410040112441071a025017803d40d00c00e0100382091006901c031100303400206090024541d40036840ea8840380400c03044c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 533664343 1250 533663093 533663101
    0xe090d12050132030109030215060103050103080318071802070b01082e140c04170c0105070605070c0215040306050a021303020d1a10080c03060702030a1b021008010608090105 77
    0xb00007010090f840f12403c0d0062545a0141c2c0c400c09a44036202002900038002d00a0600d0001d444a000e00d554280d184c0100c0301060040d4803070712030302d41642e0303101000030320315217030f102e440b041810803541e415200344542d890100d5607208019055500c0c0811240143e1078131090b180c401c01101c0142c0003105203901240000325000700040e280d0b010a201d51000051010490a9074806460000403000c100d6200d4828401e1505980d80100212041160005586888113118170b0320f13a80701072000e500285080c0202000f051490b8400d40e040003407401c1c5074040410a074046401c101035900841c070301c22404601001408881c0c0500c95004c905440d0441c40c0400c841610f814041c0300c1e00000c0c0c00b480d80921902d08001916a010311031010f0381040c0b5409103410820010000d0942c000c140c414010201c41003482c2c20300242041c060314145c0c000e1070811108a004846100340d0740001400041e142d006840540c65200c003030000d202c80c036a1180c820b581451405800190007408032803541e1700d0b004c104 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 533665593 1250 533664343 533664359
    0x9090c0c0a12300e0a0803011d0a0b01050f210103080309070909080406030b0117010b07150c0f0e0a03060203040803010f0f0e01050d14190209070f1b0c0e090d120501 73
    0x1400884203d070005142030000207203600d0300b0300c50796000300064000000440c24241c1e41e414a80b41481100130340c0150350342c0465035410341c1c07601c492103800300d5000c1c0480300b00444203001411135036049410510b00c1200803503181e8808138080c1c0c426180e4220000034400d1194044c41094050400c004060080d020503036614442c0d480789110b5041007568901c0788443c268030801103034040f41580c22411807996180d04911201d03502400e0121150040d10040344d809101034000c44602c0e0200da01c40081001031303441c05403110b0340310740d8146130301000c1071001000203803941c806540100c1c000c842c0c8640765070410100f03151042180d04207000080403540c0c02c10410b081091114152503040d00d071700750f0361041441c1514040d1402c500d12989806001c00c000c001c030762105202944680210b4410360305403a11403055070b51500d0010101d00040c008450300c2204a4010181d26803d8070803d10a8141940c840c0c420b00c40520545400005400c6014000016640180c00c11400c66107154200700301c1d45000c0e00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 533666843 1250 533665593 533665667
    0x6081e070c020a0f1d090c0306010303120f09020916090803120a1406030d051e12060a0b0903070b0304050f06100617010605040620010614130504050309090c0c0a12 72
    0x346041845d031100020080d00c002c0c007001c00d909401031b0071a100b550f140d24000d414003010001c5910715600c3c1070700080404c0d0940c040c0c40c0c0d140d0340140501e000e41d00c80047d00030312603a20305144024004101e00000b501d0b14100300030030b03206000c0d104050450404006038002d440c00c04c1010f074070780701a980900a0a50380030440c1c400c14070709801d0255072101e074044913220303142040703c6010f810440070441e405c086200402451082c5811034600320300d6500d40c0030070f250901400681c150507602c0503105102c0c3c6040e40c1c0043d50003c2c0288204c50440c01a89041441c00b003044800c0e0607005441c1034100320258114040d440b25518250009601d581051342c01030290080d80320b040c04101c500d0341c1c03510354500b80e4411442e00991b610001d100150322540e043c000e003000030b035205018030042800020412807510456002c0d40d48000a58548400d50741000389440018101c00003a4000700842e5400d15410444040d8040c8154030743d200810914202034080d4003c40301824001881e43c003031101801406034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 533668093 1250 533666843 533666879
    0xe0a050d0203030f0304061e02180a0f090c0201021210051201020a0e0103050c16050304150509030712170a02060403110a02030607181e030c06090b0406081e070c020a0f 74
    0xa00c850300e1b80c1c3d0f1420604041d20003001c0c3c0c850000400e040c0c0054015039500141580c05103031000440d080300601c00c2c0850300109103e200303204816494207112420f01d0340c0010090842620015082c001d54540502c15000d084d503650300390319070040c0208050f040101c00c4a04000d01000210b041950004024080040c94004030703041660354000903414030b0381d001c19190a05c524017035074a1200c841c1d140c446e40d0703a44180600e00c110340d05401c6c0c1c050068459021a502c08078041c2c007904507680340003161a541c0710045402c84007d101d541001207402d480c08041c010203036081d8014189400c25040c00350840c0b007038a2100040350088040c02c030140c1c500007505074200050740350282c261114192055100b03122034102e111824150302d4401c1c803510342d03808408252030080889071400390b554101034503020399074880d0000c111000c4c00200314060056403002c0e4481c42c01b01c108110300311411101c5002c0c010031102200860710301035203034081d810140e51a202030418071041000c0282044102c00b0003d031911 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 533669343 1250 533668093 533668117
    0x702010f080124050d0c0306060e0f0a14150a05040e150303091530010807060807030905070314300405130b0d081209070506091c02030d0e0a050d020303 67
    0x26414000f05104404481c1d0340b020307010040080181d006d0b4000c3c0500340f580b0170a800500c4200c2c0701c40803032a040c8103a4680007402841c50243c01c1c0f40540c49000b6080c40c100751684000f0b020f01c40b03803180601100619110000d903903203564417400e1414030424080c01504401c4003903c100d550059a4500204858411104640885200420b48101803c6110300301e8010003810514454009004038200f501c400c07060180d45403081030b07807640031183c0d88041511921000624407804540c40a020f94014210a07000d4800c1c2c401c01a1a41c840d03003508000c1a80d0030f41c003584030390500c501907108046400103440842820307882d260003124004005019502a483c130405002407090403032502ca030311101164101030001c82302c460150808601c15002007610341c40c60000f140001e420400041400030584030f0040c1071034240021902071112801100c04084014982d014894001d1381d801c01060001d442103540d807100707114400060004118013540214091840500704c100103a4000c0182c441c407800c04 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 533670593 1250 533669343 533669399
    0x30c0b0304060b130903090b1303031b0b0403320d020912010c0c0209070c02011709100608030c07050105070b040204050402060d2c0c090712021e0702010f0801 70
    0x1d42030a50080c0341c502821684202c088610003407110036a0000180107010b5150401c0aa6035140b8100745489090b0f0090000408840f003400040e010301201980b00141e400c48541d05229940c4810307244c841910107a0100e0122103d032a404d801ca482480c02c03c0718180c0b00da0646400c40300c5102100d02580b644017004940204290802c1d0f111b42140f03145031502d4000a00980c0024007010b0411083c23101c042c0c0c00307817920400080c10a030103444407468144d4180c1d650b00c0300301a1540c1c0c0e6022070501800c41d002c1801042e00c400000c0d10755006d074001402005000e143d8500840c603089180040503448075061107418010b1a01140080f075080340d00c01e40603500032505a40b680300107841e40c89603d081d604000e152070419440706000001300c411920b80401c03698106103540d01510380d60007541d5259988400341c03800080c0f50b40d100b060900900c4166803005803e2035915800382c1502c40803002c002a44c030001045040c155a4440d40e00850104a4200501079504240320f000c0d5a101c481e039200307000a81 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 533671843 1250 533670593 533670601
    0x100e0307150311040b09090f09030702090417031f050a0b0d0f090516090b0a0b1803030d180b01060813110105120109090606092309010905030c0f06070504030c0b03 72
    0x80e04111500511400f9066459403141386030151038020940581c011400000004c81410303210242500807002480158101030b031603800c01c98a41d1000b002151501e1a00489030501c0d01c0510145d40100c18800c2c810403c540b03140d48210300132a465104910035810140c007003201e600f004e400c40d00717061010200450a107522507442c102404082d20700a003a84520381c42a07004030b2400c00080107980800c0400d0080344102d400308503802026020724084240c080001d048440140a0a56811600903060303e0030a010f0301c40a0307048030b5080f07080c8502e00034a41e5002080124116559025080034203010020303092a00b0824061051945e00400c5c081d001d0182003010782c050300c29229599802042c424441d0b8507500300310080c2000c0d42c4225429810080c0109000d5000c0c00780b4100c0c0d400078100442020271031030268040000141c00c0343d800b55030360001c102c007140c8144024a030b04c00c0c8040042c19030b8140d0b80c6c41c09281000043c00041009400d12041c800151844120720440f8032091549440341c031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 533673093 1250 533671843 533671847
    0x40203060f210307080a0e04110405300c04231924080d0c11010e0a03050607050a080a0c08340e2704020405040f06090809100e030715 59
    0xb40c03079480461900c0701261804c1004080c03401028000f070300755102e030701101400c000d000a44040c2c0301c071086108011700003400281011b00c4808225030791041c091440420540105620307110495030250203030000311841107942000d000d650504504803541141d4400300742c82d00d030350b14400500300000344200305c05090110941d5800196844c280c0103804070076110080e25807110344266108a00040c0902505108210300035401c100d00c00f03401000101c282c210607001101c8444003003507041d42c06508004080042803080080d00e10510068940d255120f24000000c0d20f000c1e001009080c65070b040c0341404000702e90007642c0d140c04c2280702c40701d54418025287c1000340740030482102031701039484810210055034801e0140c10900801d84442c2c001d50195141154030900c21000705005403015400300d001814035030300c02648113002e0030061180d01101d6072100300752121000241e1341d2002c04501481c0381d2030103414a10307540405080ca1301d5000c143c003000c691030300850f114460402a4090454212034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 533674343 1250 533673093 533673139
    0x70e0114040921020706090905150103150305060903040306200712050705150601081b030105241c15080a030806221506110a0b1f0311030606040203060f 67
    0x69012442810190f442d0025550f10f0139100741c10000f08210400145802d442c802d060150b1303444080c0741194401072005501500c4079141e166000c041c0008000b0104005000c1140220300b00c4000d0f640e42e070702d103041040c141c0d07040d0788011003903411504100c944508000100c5074010351107403503035030901d035812010b0701e55008030705014100c1d02800c9100400c4041d009a420701c02c038000d0301e80884030749684c20340040d0307034044080100440f181003005020030b240c031140e0440650b5200643c9801c0762020084d40089400400e1003d032402c2d1a651040c03817111a5000f5541110705405841c1c2c1414900803410f680e800034a45c01806001c10340b008540c40e5150801020846000c070314510390410300710090a070080c410b01250460b1004003000c0811720300c0c0304030b850b0a40340c7c0d00d6900900050f001c0e42c9910860640262081040301580d00401c540c540c80e54006d440114091044446102045010716052900c001d02c002d2003031380b04008109440d0381e0000307000a8114107032944a0b07049503035a903000a00c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 533675593 1250 533674343 533674373
    0x1061214010e0906070813020f031002040605030712050402090a1e18030e0a032105090d03200729040512010615020c0102101e11040602070e01140409 66
    0xd030600600100d4440d800a1440b4003560290049548a58034900100c0d900c003030603154100121380a000350005880c051030040540100241a074815100801d000e004a03032055000802103000031080002c41608442048911a0000414071080c6002e80c001601580c000b020000c1656a914031010343e003d01da602403122114920081001044d40310b4900210850000e04600041380c0c0c4086095034100144070104076a849031195103050303c205200c0001585071100c8800f04070080c88109080c1d51003900681c5450700a0702c58680034400c0101c0c000d45504440402c4095a1041c0801c225070f441d8000b54250311002c810a400d80002201c038410983c3c800c640c00740d58050a880100c0c0c1c410101940b10030115040c40302c8021032a0541c4509a80310b04c0c1d212107840c0541c20a46801c000000b95070045021481a0306460607109104400f030cc04880006070010042607000c00c0612210341c0400588014000708601d001d019854181c001e03680b201141e0b2100d00031078881103200304106042c4410110 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 533676843 1250 533675593 533675621
    0x30e06070c02030d02060f070309230705130216060c050c071d0a0c0e0f03030408100b090f01030b06041a06070c03050607090b0d0f021b03090901060c020f0d110d0b190e0303010612 79
    0x189402a607010b53349040f6030048511400c29421500501c480c00e2081f50720354483c00d512800d502e40103071110340040c5250035640041c840c0070004001002c80521042002d071045010b4020507900ca0326030710707520303800042822451526044031002c07030a030007000c46084207104441e181a200c802e1004203080d4000c55221016910400d403001c2980e5400c1e40250000c000c09988803a0366a95141c283c65104c402880081c00c170420340001f144040c145500121904084889901084140c0d98081240c40e40162070503584032100301c1081c020080705005580d00071049141c400007007800c00320342040600c10308007140702240c0c0d51030020034441c55a8043d10900c0c48020a611400910030142580781d9001c481c060348145140b10003c17036004d0242d044003001a0f00641008010360086090003d00c2c0c180d11000c0e5a00c940c6000f40848550383d030300103451542d2042540d4082d50074201c0c40440103504003070345500c8480c104021000c40003400429281100e03603501c0c104c0b24a0b80c0a80c08000285140b10074020 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 533678093 1250 533676843 533676893
    0x8040f051e03031501030615110109080a0509041a0a0b0711031204091b140c0f030d140105060f1e070804060f02101506050901030e06070c02030d02060f070309 70
    0x1596840202c040d5205107407104c0280440070410b00118100c40040c007408801c0c5114906010605d4403a00c1e84942c5030441d03000004620849480708007490700900050000508000f800b4845410680529940060590800080300200708005040b2020750300a0ba0810031001c02d0100c02e01458128031584802c0240a441000ca49050360407041c0e4030602600c0b01c100c0c2050340034540d55a0a40c412100450165100d02d448002402244a20303400700c1000d15152098100c840c0030010b0902c0107100d1506072140000f5211806d131605150020b05070702c2030f4450b4034107004600c1d802e40c940c000c8071984c8042c00a040081c40c144244c5400074041c584000c6e100603408503000c65804c0e042140a031500500b90201c4800c11030001603402aa07503010140c90801031400410045140514042e2030800014140410f00460030349000b460310340c0440310540024543c400200c15803c0c240400e000c1e81c030030340c40507044c10314041c04103201c2c0380e801034510b004069a42211800340032591605044401d24010010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 533679343 1250 533678093 533678143
    0x80403120c021e100309060b18010503070602070b0708071b06030510080c03070509060a0b120117060906060907050702030a0c1a040e0f0403050c0703050a03030b060301050108040f05 80
    0x20409418050101c1c040c012050003812800c5803c40444aa0310b00240842401541c90038101d000d011090801c41d4600e8440241c42c01c183c6e0390487d2a00210103021a09030b45609d00400c151500f06182d1114003590003c803420f00a9103210030803510501c0d0403041141e07031070045140c12064010310096012155915101c0031a26550641007103002e4030401e41c0b0440305946991100c1d03100d520a914995055004400c1000a81080c0e011031b076200a00030015074185944610104841c0d1003801c0f4102c080d51000018400da0207058003807514021100000d040074038200088039a00c0c0d00281c81e60380b01381410701c00500d615201c3c1080341d600f03a0317024060300c40b02900380c5410a040c20340341c080d00341e11500d40700c03155010b403212805650448140034a10320741070f00c2c0c7d020015203083d0054401d0b82086000c0113845017010007040310000462090001700742000302824018102c0b070018100301e20a803010001080107a91003006281c009070486040340742c034101882c000c0e1800c0a1000c4803012200c1c51341206c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 533680593 1250 533679343 533679347
    0x1507050f120a08180616030e010609020d0e0102030f152709070b131e030c0f0e060109030b1537050d0507060f0201020c06040b190908090d08040312 65
    0x19040e02019a1500e0b00c00d6100c810113100d04401030212030f80710780d00c81d00c00140481c03040b0700d140500c02a18240080d07030160181d0003509644064005651042c1c0010360300b005441035102d0740c00700c00c0c0c140000b1825400c240380741c020070040103045042e2200b015000c440c0c0c55038400b440104642805600d840c0801c0d408503110000032811034520246029403000000d4001070740044801075010003c0000342641070000c6000c500030544440c01d503074001403402000180c144110b40c0090022411090aa0303072030070800c1001d941e13004104038100180c0550410014100200c2250800414148208041c18107004201142003000300c4040c0750f06c403c0c0044102000150f008040d080403581150165034842c4140b00f20f158003000300806036841201d08100c124070030036a88034510410320001d840c050039581100e01c0c00100f40e03016038801c6154010300001800c0c1908180108030524018400300000f80c030f13006090301602550074080c2400750210780070003c1c0c1d00101c5024680c40608118402028900 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 533681843 1250 533680593 533680597
    0x11070f0210020105070806060c07050a09060810020403150b010c0f0b07030e0a0803010920030403020c010e0f0d0615080f010912051201060c06020c1902150403021507050f12 76
    0x280e0280c0740d103200e0396260520600460344507038030750f44078000070343c41d5503040c00002e034040c1d24103003282c1c0525000070649a40b4264120001d0249075800700c0c1817403c1035202802c1a503004070000241c0e104110030000541d0410148a00101e07480000459009020050303401c0036650000400100055544804008201c0c503002d01602142d6010814051320300ca00d00c1e43c0398011403000d40405d00130b00c0100b00c00e0a0301d400100c21803401d852544445018480c141c030464005450444c0036803c016000c402d5940e03c40310510074003401720b48004540813540b01003070b20b15450640c041c16050303e402d01841e1a1140740d44610003801180112103140001c1701450340200130140085410219100040d00c0f80d0b803055064414010482d003024000307900c0c0030402c3c0d449400e44201150403640910041220388070620032038082003103c00c2c0c0207599488510420910700300242c440303c801d890510041c00940ca41c0c210040c0440310491140c0d9540c1000e05050b8541102d00c603546003540309440a140700301d422400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 533683093 1250 533681843 533681873
    0x6040f020f0c1e010603030e06030406090f1a131a070513030311060a02030103080a0e0112021207110334060207081e2803060302041803080a0204050f0607061107 71
    0x11030810710105206003403c5e101c10344000b90014900b00000156840e101c1c0c011074000d486020b0000e07070240d25540e0f405107002089402c0da002084c2c805d0401c0d00340b80a90728181c1c4040541c03003c011300d81140c4c0d01c4140089003c00e031842d030038001400040030749004108942107100e41783e440300e200301e035603240c010b041d00b070b00301ea6005060003040d000c2156041c40c1c6c002c0e02d0590b0b6000440c1c1e4281540707400300321541490a2006410441075040c17400c1641410310003041c4686d911403a80d00d01e850111009400c040d0000d10214582e4810030441d4030180301c04001001078200d100c41c440c0008a0300142031004410800c020346414400650b01041003541c10040c00120707540e00038004072944a01d8064081d020b0b0b0015140359280720030340074150351132804441c0e0703c07206c0e103050028031607443e074001c6004c0b5014a0743c2400f00341d109031a00030a040d042560290701515510055280c1800e14020901c2c11a00c095414082d4002040d40340400480390407841d1203000007400c450301c800030303814290711442140e2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 533684343 1250 533683093 533683123
    0x405071a070c0e0c0f0a020118060504020f010e2103090a0f1e030b01030b0a02160501050114040203100506070c180515030c03120c010f0f14130b06040f020f0c 70
    0x20340c0000e418407000b02c80c80c402c0c542d58000a041070b10b4a0b040b017441d6030041802c4000c5558440c5410110b00c0c1810320301d28014050200042c251130188180031103944c400ba50681444042c4490134900e560742c0107103600100000c2c0c11407840020314560309141d402101c10895200c4242c0034085000c0c0324104d15541181c141d44584445880c400c40c03005030715442c900014040c00954001440030920102c03100b0b800c41ca085600515210b2054450500104581d2045442e40d448000402c0520b0002a01001b80342e0304507021461350410382c601110f140a03911509005280110b9610180207024141c0c2001344420020703a9034135a51488460f009100032103a031a00721401904070002406c001440f07001e1080084c00502564030040c801e50800d80080c100780394030750340b92400b40c96180d4031800f500020900d4018042903c06030241050f0301c0c4c03a801030036000307181d00c010402c001145c0d180311000d401890658000030070035040300680e40a446088c0d09240400070015040907038000004050700715001d40 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 533685593 1250 533684343 533684363
    0x414070e0105031e070e1315050103060e04060e0309060a032a0807210906050406110c030a03090f0f0302031216020a031d0d1407050303210405071a07 66
    0x100054640e07000603100d160090600c52401c103913054a0319211508010300d4103044440f0112a000074006a54a10805031000d4440b941d8040c50109141c91030041c0030242000d104490501850045906004101810042e01c1e80822080820184100d451040c1c3c00740c11590f4441c01024045c0150192515a1164a444503000600f4909d01e00c02e10540700d600782ea03080d16680740c03035038226107030300c05500294802050a1402074030407156200300310308588503400120b140d26003402e2a504403000c11f51b86d0390a581003085040181d00e0048103c0340ca0003001c0c100003410b180340d0700b0000783d90410004000c1c070180100c45460f081c190000060a0b040f2603180c01740d60165030b0038000c01c107090007075188000543c1c40308000c080024020200035811360b030b40d10460155907102038001810550304a0b410b60b12404039000c1c00800c0041401840b01404003a80114a049804034180c0101c1002c200504800c1e94094049820010144034120050406408401440c40b50440407241030b40000c0d03040b04e60700f0403 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 533686843 1250 533685593 533685617
    0xb0603010902060a08090f1e160503070302010c06060504050403050d05070c0c210516080f030f1206210105090d0c020303071205040e10031505040c090c05040302041407 74
    0x14020507021a030b0140440b401c00360000703c1602ca440c0081d0a06002c1d0003120b80170f9291040c00c0040c080d0101e00f25911100058001c2c840300d081600803800c0c00ca6000c0c2c819401d01a80d01c00280500840e54280f81c1761419a00c2401c012009213050307042194402c0c10b200c180403d01d5805005407051003a504001c2095854092056030191142800280313070040e8800200a464200d56030850f00c100c0581e14810310311405d540c2c0034104000700c486104c14401e035001c00e000c4010100212805000c01d0b80c01145130001410070080540144400300780340358082d400199960b103c491084294060801c005802c4954082c407540c06010211001c01151045020300d602140c440e5a060510580140140d413030610a40c44090b0001d00341c089070303018480204800200e00244e0b015003407255011555842e2050f045140541d15050751440d40c0b00304a041c401031101241c1034070000700c100c5c2d1407842d0000340b504001005682d01c3c0650f41c03001c1e6019103000c0300c0350030ba0184006420b120b903119554201b11115 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 533688093 1250 533686843 533686849
    0xa030804020f0103140403030e0c030319112a06090613090e150406180c17070b091f140a0503010f0524070318180e03190e0d0605090a0b06 61
    0x11a800c170290055415a0129000c03a0080e880441d0000016040d52031a000d0600400c2c40c4d0f0b840030218103d41d039500c00502c07684a5105c86d005000702e13035500c01340c0f01100003454044503d2210000d0301c4a07103016440c1202840d0380751070445444038405407501d9200c00f031b65111482c1190710351045880c25424852140d0102c07002150312680302044401752801c2d034031280c0b900c8c0c0003003031052400c10b55220b418210b0303000304c1c010340c0c04030000340701201035054040390240f030341c40c00c1c41c84651047c0343c55081841107251903a00d0041e500458601000e1280c00320007190001c83e092000544c3c401c052510014141d02e04aa000c80250f05884041c0c50741d540980d0340b0400e00250649065400703003032200c840c0100c420301d44800001c0100c0c5000b85019443d41c1c0d8035104104402620ba8880000068640c6070714036400d0003801181c001200002c061030420300c0300350110424482c1005180104207206248000540d1040d8a01194581005007040b180c42c0c03440b21300780c3ea45150030081c0c0f805a80305000415610b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 533689343 1250 533688093 533688101
    0x5280510060e060a140d110301031109010e16170c04050114030c040302010c15060603021c0507051e0c0f010b0102060c04032f0306071d090609270a030804020f0103 72
    0x11400307403c2500d0910092000c403200c0303001c0725150545103010440002400d805004411140c0000501c982d0b80e940b4510380001ea108810240174010051880100032840d141d900550b80042c0208003140794110410701101c00e0541a40700320840341000e010301c9016404c64001c2e000342d940a07241c1c2220751640380078446850104030390511503814104004c0c00103500c01c904201400b4420303204c54644018405211090300c03555007041300081e5003c650b002c105030a85120307100001122900f0091800c3c81c0100410342d10440402e40239100c5001c40007628900040102d03001c0c90340f130740d040d180c001420b40340b014003810924040c2070041c81104017240c0400e4001045500300ca6001001d4814988549821524403000d072060442001951403200740d6034406218244c8070f241c0301d030348482c1c94840c1d0000c080280c544e00b1a102d0301901f040010000c3ca41c9036150a5030300500d085c0503450a1014540502082e41e1500480585038012004030030100340c1c05c8028a400340d0701c21100071344544141c400440880f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 533690593 1250 533689343 533689367
    0x50a060c0e041e020708130b07062906160f120f09060f0f1e1701090608030f090d0807050312010b180f0307050a180c0206190528051006 60
    0x50085044200d00f0011039005280040c42600444d090001004141c0b01e07600250780110a45100010198200202c6101d20140c02d0201502400c41019129000700901300744030010303000d07a0b00091400301100b541d03520007066903800107101035680d41a10b001e00040143c0c540b6400440c1d03175804482e130b03a28080d02180c41a503400c0d40c2d80380211108601c0454409440d0b4198600340910301501207100f141c12900b10910690315220b0600141804c00102e04002050b841b00e9016841c2101c00c0c00703002804001c5a01882490000c161500d03d6000010580c014032140100000d1001900200708480800904a40c40b5080c022611680ea510f01e60b80241c80362a0342408400b07850200e4a01d54030b003080c940c4492403006411618001e0310303007021031030042441d005200c5840030aa0003403c941c81c0d900410800058500c00b5140904141c0c0d589418040c00712408610551140d000403480c0c01001d02c1030984040c2840c4000950304c0703c202200040c4410340d0700c03604010f04107a01091a501a01e214a81c1c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 533691843 1250 533690593 533690621
    0x1b152a0302180a08211c0b010f03020c15101511070503011802040c0e0402030702010b040501121a0a090605070503090f120417070302040c0915140a0e0d050a060c0e04 73
    0x30342c5c0c035905004806509103640f00071502e442070108009142440840e84e00d0003c011100003400c03480303030002600c2c09080a01d44000c250041080b0341030140049822120b10700d5034250701060b9201c5012140540f89160080303c96064a00d0440c54030551140e95028010000700a07a000645c5400c20316080e40c0c6401100c41c105d2840b012008014109035015900b030802500c0c002100c00903900000381640c2c0f00740e1b03007900142c1d140c1c070000d2078a140a1041d83e0040c00291000076071803034244d44403040c0091000480e01504803181c0090301054164000c055056440750003003145142014ac00380c65600269800a020f114001c85100400400605203030744080d482000b07402d0070300c0c0c8110400043d2400011900e0350098200c0080143c4803030040440326222510350b14500c608003844018030025044410b03040203c030745580d819040c00300341111107192413803624050301c0c0c3c06140400c0000c2c885901c014158804c4141c014103000c280da10585a00b011580e6100404001004010aa44401c0042d040c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 533693093 1250 533691843 533691853
    0x501020723071404020d060f0602070b120601140d05041505090604030804080c070509010909060b0303070c0b070201050912011e0923070302150a1b152a0302180a08 72
    0x201c60818501c00d100e0f5200800240c03411000c040700c0d0080e00c0c00d55200b42543c01a2480500007690180130490191144108003800c4c518440103400144a000d08110705000c6a2601c07d016501c030300c0c04a0f2081c2007049018000d0b400c15103404102001ca00c2c108040446c0340c44081810404082042c40c01140c141d0740b158940c2c2c0b104d48941495030b00c80c0c0038619440c8035040c00010340d82c4030310018038000c00d891040011450400c0c00c0c410305948440c3da069100350401c20120000030b459409610507600011442516022548016180c5220342541c484d03102581140b4500c10384015005001401c180c11200d40108908900005c2a1181e25000401d0428803508048030500440002100c4c2400403048031101c560b80e03008614294880202d080540b040000c10f05907070354004946003904600e509140e4110000c17511032548101041109110054440300340c80e001022100d100c01001044469051007541c1301e00d006002540a0001682018460607030402c091400111060885100c60701600b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 533694343 1250 533693093 533693099
    0x10602060a0510090f2313141e010c020d2f01060b0c0d021b010816030603150b03011104030506060909011b0801050108090f1903020c030a050102072307 67
    0x4020b07140090420680900c1c0d10f1000480f14214000d03220000300b441c0b0006150101e020766060300301586581c0429003034a01e001e2101c00c03112000b41e40c00381c94000b607441641c4000b00800a09100040058040c200b0003004100e60f000c8040d40b001c3d84504403902156a00ca000c0340040d248541c03842c0380c07550b20b4070030911440004e0031500c07664807103540048000204140c07106103400712500560044141548074203043d0f51036580400282929070020b030800c980582d407060008220300e00080081d0340410b0040c17103c036116402908800c02031030703000c03001c019450380d00300e940001000c43d07030742d00c074401d6003420860328021008404403400c1e80d40142c080e150a680d9002400306100001e0040c42040d17503104a06240380c00c9c03100341c44015113855598081030f945403e00042a070403010304220102c0c0c020341000180544002150b402d82c2303094101ca80c000900c6414184c0c20602c8002a503030b01402800c14203810002e040d0300400066100d808480718a9200d1750311502000c03040f00300005a03920070b039014 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 533695593 1250 533694343 533694361
    0x130e01110928090908040302060f070c080c030d1b02090703051929010513030c0f06050c0a0b0c0f03010326070c031e1b050f030d0e060d02070812041a01060206 70
    0x32000c4117028107201440d103690b81c4c0c04900194020099a0040e41000c5406003c01c2034103100c0e10010100e60000300004055a0b00007500c420091601c00c05005500540081c01507040c40c520305a0382e00100316030003925100b00c0140240c042181c0d0705e030507900d503008450010704061041c4050100654000300008150381c4859510b40c80300340010b07040c0901400004850800655800069403003400303c030210901d401c4061040b89480e4004d030042c00b200384560544c41a000652030ac80c65045080d40540340c40300f05240415200b0324032562140a4004004818825407100c001d92a42000c0e08450400f15602d81c0d02c6043d000e4000000c02090310b558041010a507043e807081303110000084400035441e000ea5850545201c48014401088046a8100083d02d84010540c02080e010340281030300006c4154020309803414040e00a00c0382c2004a01a00000d01c0c0758155800f483d8822070036a541c1d030544000d0517001c44119001c651440d2640b090300c582c1d41036501c1c1d00c0c0c1225119001401c0035140c0c0000307 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 533696843 1250 533695593 533695601
    0xf05070f030e03071b1208070c0608010b03060f061c09020f06090907030c0302092d01050f0a110f060108070e060a0e0a021b030f070605060a1202130e0111092809 71
    0xf03041d1280f484030010444080c9000749070740c6c0070b126212803a5501468038080582041d16070040042c007004030300421040f4041d204980d800003089814580100300c490001c0c00d60702404220351088416011201e078045103030f41c032011440f4001c0350005850307108076081100511446502617006480007010400d03442c065000010702801c18240541004418404a002c00c2e00601c4112a075001d04200103140181413544465031180a281c040c0c90703e0807094261040784900c2d1506820001c100310701100c0d1643c01d02141000c8a406010340f041541d46000865907415a4020000211842004104030385800d61620044a1004040344001d139288001c00c002034100c0032071890311120b1202207645401d01030000b003000e0303130065404c0354031180d40b0705000040304e800400700c40c083c0c0c509131401c0c440d40c041290440b0240752304030f03404240c1e40a0107030700f04058000c1d040c21501944c00c00444c03059141c0840e000e0318900e40e0076500311880d443c3e0203061200503201245180242da601610a025240301900 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 533698093 1250 533696843 533696873
    0xb070f0606081005150a3f0c06080a05040b06120a0624090b1320070f15050601080103260c030d060f080d0e0f040f05070f030e0307 58
    0x2000101260b9840405081c11410720705184038691301c0f001c000219002581d4807114100540d101110f45044c08000f1056041100e8444266204c000c020b4900c89080140c00303150701d040060f2060f544105203401c5040c560540980c0010504507000581480c541c5e100390b92043ea04010b00341d0321a00d40c44280b181c040552656400c1d02d015102c84040820010300038140b0f102d6002c04802002c2480810b00005075442e0b41040307070780074241500202c00781d950303423000d4814443c8001d001420903c0e061000d141524071404484007c180802c0380c400b8004041d94612105000b5071500d00151002005001110310403200580490900c90051010403d440c0c5005010651420041e1880801030050740c40e9800440134035115600020b2414410007040c003c1c48001c0208000301c00031f043c03c02d5141c42c0c8805e16036066504000c494030b00007905030307588082c00c03009241c0580100044866181c0c004042c202c1188c0e45004036009a0200003854424821a10a90325074006541030000320b40ea80d0703c2070740b0055 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 533699343 1250 533698093 533698103
    0x120105040f1407020f1608030d0203250e010327030f020f030409150801050714090103020d0903080a0b0307053f0607080f060d0609030215150a0b040b070f 68
    0x10401c1d4042190400068040d0f10960001e01c3d01145080c0030f1454a01030112003103e211581000700075803280001611740c1031903041009a241c1ea9908804144071440780404848682803039030005d80c054104000d900494000c0c1e074180070502c1c0101e515010070300d1724010300100c03482c05041c00b40420322540d1030b000b040e03565205840c01059928407043c070f55000350308130240c00340c0c1e1040302031000241d0004603001058010004c0c0a07520307143c8000ba001c0c8041d0030401881e00c500084030000c6a00c41c4c0d04440c80c04011110400030f8500500b00204030050403100100e85c45d1810208074040d26001801d0801c8400003020100307601140d140c1e4040c03030040e0110f0a0003440e00c60320208840021100c007090742c4650000149100c2c60102c1c0020a80340003c0c0000010401c0d8005101142d103c20a00d0080103800c00804510000c00d403504034600074610060482840c4120280b0026000310a54041014412640f015505440350341000282c130aa100700c5241400800801001030070031922070411074015 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 533700593 1250 533699343 533699351
    0xd0203030a0801180207081b100509100501150503011e180507110c09061003060f0306051b090f210f0d0e0f060a0c05120c06040c170a061a0a0f060801050303120105040f 74
    0x3080c809d106480c42645c0c0108242c020032011919400d140c880d450042220800240e1000704512000d860b520040c02a034450f0312091031504051381d120b0a014005008400c240b079a43d22548010b07000502c4185d400e03000144840e5070590740e01030005140281d480d0020303d40421034407800200103078200780300a0501850b0b01d60200041443d420710320030380111702500000c54545010814000c08035041060548100d10a21043e0026240c1c410341004c000c90594609094242c4d084040c1d254211070010035020b441a090800d11110010465958280303840e21810700d00701e2000204803000d541c2a0065811101c00d10009002174400c2800d0404130b4024815240700940e42e20002c2c9c600c0d41b250001e03885981c840c005010400021801ca50010462490209806a030343c01c0c0c05c0352100440040035203004d0b01e5004074280601c0807000540100c070000e1104c428039544d890203c0a44a4903ca240c011580d2140005913608000c01120b1042544200c901001d81c203000802006080f00c00303184c0d80302591 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 533701843 1250 533700593 533700613
    0x51b01061701050f010321030209040e1c020109051921080118060806070c0507090c0e031b010c0311070b27041a06090d0203030a0801180207081b 64
    0x400c0c8540005004040c003540d400c4407901203018251140500840845107107080100301041c004114568120291040020b2890414604801900645850701c1c1d00a00e03002015445010002d020f483c4183d42c030355501890401c0f8001a800c9401901014105400411070210315403010b504504441d4400c81c0e805000d10540980980c00090056107000480d484500500c0141c0b003840500369101c0a100041c0101d90400c0600e640701c10000c0d03e036005101841079070100b0800203000103806005512000c0180e6200107100404200010340390324002e018440c03400b07445480e890f031b41c1e020925040e1120300d2400c005a80498400c80c001044a44038041c120b00410328201041c01491070403802c41ea0b0380603000e9803603100740043c50218012445503281c201144028a0300b0b490160700440104d5a0544607010400410414880c55000a6160000280030a26550232480300b0703040e00c0050301d241c55074100c2d40001d42c04030700c607203940509641000e01600445500640300311801c540f00ba01a5000892 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 533703093 1250 533701843 533701897
    0xa140403060c120612031719050c0d0506030105060a03080d090b10090b0f0306070c021f021516090302090703020c16080d090f030f031407030507020a1203020d05 71
    0x6030302c0c1100e5000031029000d85507625981d0194038041c149114043e582c800c4542e4000d0f051407551404060300300c150358005144500c07240052070788442d00000c18400c3d498030101c1071a013644410a10300d040f03854003000c5a46070605100c3c0511070000a040c0b03149950654568003c980c0003148051101c5d0f40b204540000508203594082c0079852550700d0610290403c040c220a031210b80007460300590b80c403171035112103907400510160403261b05e09025a00308110300205000d140304802c07009400351070790001e1070015800100180440c5101c40302c1c64407070b03c4440144400c4d0007031464120010341c0400003413007d4030700141659040a03a5050062a04441024a60800c0480003104035003818020082260800c2849180e41c0d02c0400e24266000d24207003000303407481c4240c6001c00b41ca840201c4002c8810503000d0300303180621909001c0e00a48820640c03074002c10b10741c04560100c0c011500c40c030b0000b51011041142120b400e6041d0041d00b8560060407040f20030b41c000300b03c0c12a0012440400e48142c170 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 533704343 1250 533703093 533703101
    0x510050702030f0a0b1519050402030a0921110304060e010e2d01020f070e15011413150504080c0909011b200a080d0e0a062307140a14040306 62
    0x18410608170030185006204181804000d600c164050501c640500f40b01050038844401514021240161691901c8021000a00c07294100900c103481c601050500925540804c40c441c910583e5081c0081c0d05c122086602c1b4042c511662010408200d24040700c2d42c01f601001c0094070300542021114410381c0e03134008181c0700108400079242110841d000c0076590502c01c541244c2611401441e40c145801090f14408030f00801c5400c05006030002c04480360b2003110480e2201100c00c00850301d802d02400c18a81d00a01c52040d036590f144042c0e4a01c008501450580742216a120094030032440980140080b000c4002d00340b52180d580d406918000a16058440e1a20a080d50741c02040340501032030005074030000003846030158040300c08500001c49180440b64000082d007408541c5004500203149445800e02d0004c0000d03050286c00600c80001c503805c1d1a07038882845440e0025241c0005c02d0f0f030440c018454280c1d03601000c00000351032601480103191100c4e45111142c0c901036590700d4050882d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 533705593 1250 533704343 533704363
    0xf070f0e04030e0a03081e1603050c0f0d2703031704050703061a0a0e011202060703110105070c02011b0b060d2607031d030a060c1206030b1f0510050702030f 69
    0x144404070b00f02101c4e90407c0d066001c21040d8070303d11842c0c1070500d02088500c41004030024100900000d803288454018000d02c14a03002e100c0440d0096003417031a0140c0100d044603246110407801000000800b040a6100c81c1120b0b0107840704c40c4014a00b03e14805040701c014820b840314443d1000000011718140b083d07c1d20000c80540c940b02419200040000c02000c990042c00c0c0703144594018081c1079101d4241d14001c582c125015640c03401700c2d19061b00c4c0007010004055555180c282000700d000c1d00150103070f00e003d100341d030b6041c120014802d100d41030301c11131100509009038642c0001d101d421718800301c0050a0040441e60b00c00240c0004004018242800000d514000814030030300309904180b0858028107540441c90b0304850000100b40d60f44501000030b8400f43c5c40d0101500480d00a94120f03c1940d5144020b00c0055101e04100c0b040300300540c2e1240b1401480f001c0b00c00039030160800201559001820120303038610908046805801269060307070b00d4001e5900d07000c2a88801c00c441c1e014 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 533706843 1250 533705593 533705603
    0x90209040821041121010606021522020411090415080d020a080a0305060a1205071811070b100e0a0608061602060a09080c07170f070f0e04030e0a03 65
    0x18807001005034070b0b24600180300d0752600510030030501000589040d6092540c03002644c501e1504132640d41003400040042c0001000380d442d204020545642c081170301d04000c5d004910106580d00e4601c8103040b07010110341610150940380c980d44c0018074081d000800ea0b445825002800d1112400003e4221502501e1580780c04000c05000c01c0749140501101038584164000390041401c03a0322440050b1042c003003100c4c101030342c62000803443d070b41d26600803004e000320840e030300c0b9210741030f00d4007599881050290048038488517400341d103e40014040c400610300710558550501030507503a10700c12240050440c00c0140820752000c50b11071400060b05100f84401c2a011030b00310b18111515081c8036024003071b003003189011225410301640000b00070750002c451005c00200c41040e828030f41803901600c401c1c84031340d009185000941d0f9580c002d201099200000c00e03034180081d0610115602c114910a08181c440101d10400070f41811103001c40d4460f00a0420003034140f1050001941c8150703540007165 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 533708093 1250 533706843 533706847
    0x60d11240a0e0a1e12020a0f0803072604050904060e030a020d0908010504020901030f38060f0328020301110c100608120d0f020c0706080703060b0315040902090408 72
    0xb0302c1c0d00e041c0384003600510340c50301c100d54196448078910811101074043d50390341d014100039040454645114400040c102d001004445c80c4d103445010351280d002035015111000006e1302076484030b0304c2071411600441c9500c0320a02d810302e4075007440030b0104028001c3c1c90701c42d80c030101c446070090b06000801000040303502170184100039881c0600080190707081402d041c1e240c50100700050301c174241d9690542c0d0700b05460a11541d02440c144140440120004800b4039181c4005a82c414070104003100c07071010485010000e41e00c900500c40307144400d03010a903140c0c2c8003921822104040115500180c20f03081c003800f001da1a560080303030070742d20088480b00c080e00c00014410340d4244281f08040e00300040d2101407000e6498810050b681c1c07101d40304038000c0611300241c11000c0c1c201b1680040d444580c58203041d5203420a40c1190b07030b1240c90341e2003801e012032860800104000e109126030381c192401c15000c2c074159240c100600c3d012001c2c1003543d582150f916621600585d0341d9030200f51083e4400c031085a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 533709343 1250 533708093 533708117
    0x20409060b1201060f0c030309050f1203060f0f09060f120303041b05030109020d02060913060807030b01060816140705060a06140301150504020706021306020102030609060d11240a 79
    0x1d0868144d1080c400c0007095100300c80101d91041c944400c1a4140c600890310305a24101281016544110061180305142c2e440005984031030103103100b040c00700c81242c0c001c2180300c240666240012000c5030300000d41c0c40005c050307180c41c2c1400140e2110203031401901c0e0701d412307580c146154020703074003550031010740881c440340c11907038100e8800682000d4000740801c0c130341a4081990801083c10003485500040303805030342c03500c0700305240058203c07100003030085560750f100c10340e101e1655002c20ba07100d0080ea80041041400346443c2401000d0b00c4c24007070a007101c113020032113120a1070510015106000c000240200741c08000d6a805080341ca000018007030f1901210021140d0180c052500030303414040b000003001c0c81d1400041c2280c0003941c0140ea1500c3c01c0ca41440213100c0c65000001c84510f048010915550540c00b0350300c06e041c107132800700050700e038070003080169441d8140060080940301d03e85402401d0041e030701240702e400b11085060909c0d410110070002d402160321f101c0001c00701e280700 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 533710593 1250 533709343 533709367
    0xf02070209090f060610120903030f02040b21040b0109020c01020d0c080a0c020c10030e191415131412041e090213260313092301051003020409060b 65
    0x1300b0b4000030304582803000c800b070f8410007030039550003160b00090b0075684001a0701490f010360041100290320300c07011981c40c5d40321100d442e06900803406042e02e110101c004030b1300a0280803080d40c05283c010341e0344519a8a002002c2c0d0182d405440700140d9550240b00081c0c000c0d0302801210401c00d880c0d2284a80e9180c440d074a074048030403030036005045601800d6048000d4540740031001203582c8a20340862a84180b00d4110318050380026080c0f11100031000d020240074010200c2d86480c07580400751400700140406ca22440d09041d548903e006151503070510008060103071200103274818805a0f01201c030007000040ca650807950009880181d011007000014009075444000b40c220b43c032086003040031112800d030314405039004508d06299500354050341c415804c101101e0304940c030390480b551110745011070f0010081e248a4040e186040c1300302d841d03503441c28000208650348c028800b414a0ba180004115441450140c0c2d1307400e1550030000494100c0650258401900444640300d587c1e580707003244 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 533711843 1250 533710593 533710603
    0x10b061803010b0a060f031d030c0312011a0a030e1f020c10091a0702100204080d030e010911010e0d08030126030c070e04020109090f0515031209040f02070209090f 72
    0xb2151060040301c9040c410f15070040d403008120421b6280006d00c0c80f5425444582d000304e0060324010710322010a41e01180c4000100510360320050480441599030b8840c00c0c900d4901c11002c20002c1402c0030f0180034826031181c1d100c241c3d48030390207040b503009580100d0302c1201c094164411054050700050b25802034001000400b0000c280c010080080c088551641c90b5030054031404001901d4160003c0703540c0718030821103a220001c1d0301e802103548a54071043d15580300c1e41c070040403010a09281901c140500103202d40444250040e002628084a41d00110303983c05416444075404a40006a1004503c0e0075014602921114601020118038004400300d110840304080c81103a00421080301000c1c40403c2c01011034040c1388051502da100c0f0720050b43d04407801d411400019140c44c80d045000300f1150042130054a0000011035104203102c28140c076440360b1000781c0d0b0400d00c02c1183c01c100c0c1c20b169000c107103880a0920014105400c590006000100684001800d64840d10810280000500c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 533713093 1250 533711843 533711861
    0x50c1c0614240c070e150102010c0c0203151b160b15100c0305090d0b0601090f06050f03090a0c08061008070311011110050c0a020f03031017010b06180301 68
    0x5a80c0c00c2a0701c00c81c07000900c1c80d001e529002c03200742c000c22460071140040110744098403180700401700c24a041d4400d200300c1d14500650900640c24407100181c014054418038841540140c080e109108041212121482002d0071480642d0074100d0750200c4200d50001038080c100600c20380d940050b919040a890f2800003038070b5059403586243c0c01564a0791144900000b61407581403644056002e03040558203401040880c0d504411001d45680810442c80d031001c1c401d1100341c07500d4591603200c41c0c0d00e01d5003010a001d00c50104108002c07202c0012842c4014680c8011490200c13003030380001c2c3c0e4400225150f503034040803450384000305111403007042c0041c04000e8a0340b10018504545140c50b0584090781401107a41881a15182d041d04e5503024400400300e030704103076024045400d00401e091501d90003501410018003900304600c601440c0442268012030351703e80403110345420302e00800c000e0030310103032280701d00d640e80e0740100004d40b2014081c00080d45e460b6201d9901100520034507080d103c00e40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 533714343 1250 533713093 533713099
    0x15100309110907090536160e01020c01180308070b06130e03030a020901031401180e0f061609170106090c02010e100b0402090303070f050d110a06050c1c0614 69
    0x8003c000425611644500031540c4c00c94801e003403034001d04100c1c044040680b0b0240868081c3c481100704032003882e59510300402e000c03d0030011104082a0841e08007100816a038010f0700000040c880d11340c030612520001e40001004001240d40c4c03030f502c0850f6540401c00072105c020541b8108030003441c0480304a1401c018910b0280310070981c8120144d00d900c4002c0640d11529804601c041e00399210b9402130701003001000006905507140d0a281143d61138003c3e0f4107e001c0d041c4001e940c021040400c10b420194800d500a04650b140c403450703013901ca902c89142e0400c224865400185038403035223048e003000d0700c072207000022402e041622000c142e4007104490429a03051080407008440001001410f841ca491000039201c041d070750015019210308900141d0500c00458404240150282d982821502c07401c03c94000041c1d8280c04d070b81055114645d141560848005080840c04a41202e94010459080381e45414100a0f0b6000c40040d00044150f0b1640c4d41c41041c4104000505605695a422 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 533715593 1250 533714343 533714359
    0x61b060518011802101403011a0f070b040611180f010c05030a0f080714031501090909060b0f090108031b16061e08010b071b05030307151401030f02091510030911 71
    0x6404c0001b190711044c4100e40700a41ca4004c400102c401507800d0310703403135801d0f04220b550b180800c0c140916a203c00707a406680180c60084031698000d13503901201d41c1000881c82c0709400c0b0700040e0801c801000403c1c502414403900c047c0580008600703100a00c008103c903160000d801590481c01000350800902d0781c011b014240320680302100b80031069950140c0c3c500c46c1c003200405050012291141e9a0b804a40b0307007030404a6000030003c6035003220001c10000e0318400d02d41c0c0003480401140070400c0c818211030b03820400103900e010f0946c09840700903026a8003190190450b214075440c001c90943c1c007000c0011140c020090380041048032050303002016160130a507030350501e802029980310f8908010206c002c00d2800e000840d00d081c0d040002841e00400382c0340c4403d8581060900c14100304843e0312018941b1484c03004a1404030300346410382c2c0e08207079070820b0316145034240b20740c10102070110102c14413410312707141c0c2d40d42d0703400501e44030f03100b084e40c3c08903a02c1014a481c00c250203442d80c00511940304 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 533716843 1250 533715593 533715617
    0xe0108070611062e0302061305011214040f0318030c050102010b0d0c050d02271024050c15091b03010933150e01061b06051801180210 59
    0x205007102100c226003440c2658000d04c0c507050070380c2500020b9000070b400083c08291851100c500e200b146003124400c0c6c8601e15400007801d02032040700d0102074441c141640720404540030a031004e80c011485031107800c0050032141c134110508101314143d4411640003440c1e00f41400207590a025020101d5419503284403010303010750714140310392140d0045c2070140c01c0e0100c091096594030500d14480c00b0100c0c3c2c2d00d000c00d19034407200c094680c90444414801c408001c000181d0383c0c10101c1241c10000c0c10803014044800d07107a400311503d500002850200e03104800302612030443e00940c1c28061247d91004046810201c644a1101e12180c01d125200364034003c41c3d00042406040b01440143d00c0c0501300150b144003242c0811b503c2c00e49000703210050728042c00803c98205200c18002a0b940c0d9025005003603913505000c84040078440308070101e0119004200c4005004e503000706400000501162800300349250040d03017110b5010b0341d490042500100010b0950070104e0350503581440c14076004401c0fa01c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 533718093 1250 533716843 533716861
    0x20f0a170f04020603060d0236040c0b0a110f0c1903050a020402030a0e0a080d0f181502042c090c490312051308130e010807061106 58
    0x14000f900940c0000002000b40c3d0703442131020703019036008051448990170f042000e424845403003010450b044414030b1252100c42e4010b5424803440e4001010302120341800040704c5560000d070045414405002112000941d040c0501510514005d0062076400006420850300c408a80c1c9030440700e04018000784086071010400c0341c3c045070181c50241ea01c3d01c4404100005116142d407a854a00443c03061004100c6984021b12800154500a01011444042020480e0505406a003e901c0003104000000d481c85203407208075200001c005080c140d450f25038001000324008000010004800c2c0300405085071100b242d000855040141030350080c02020036401d620114550b001c4502000414200260800d2004032175140580d0035801d001309192441102c1070418411401b0903d1095035542e00e007154429184642200b01420b038444400b41c84604003030f4001c00024208058080000c244140745040050080c200140245001032400000602d07882002052040c0f075080700f020301690300c2d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 533719343 1250 533718093 533718121
    0xa081002031e0106020303040b0609060f01080a0f0c0e0a0f03030807050c03160803060f040903091509090203011202090a020901140f1c0e0f060f0106050913020f0a17 73
    0x244004401a52615403074107012071a00450a080c2d00c41e20094004110103a01001031030099202d24a44485501da170810004440c10450382c0e0340d040071141c407520f0200d40c403e01c44643c011080e20000030703441002c0b0704000151904005c1d118003140303212001d21100e04040352100700a12410218004c05400c60340e0041c0840300140c80e120130410b02107071241d04c2590034030445032030249024100d00b20b07207240d280260b242d4004441c0e0070b1155a500f1112041c9003801e000c0c091050f981b50352900c250b182402c16608542154240a00030424907000200e0a0300c0c4500c001e601811000c3c01c0b000c0380790034500c100030042d50300604807a81c80380103006034429640c01150b01c0620103410755400d92945601c81340c2000c107006082c29411481e603072082210002c103a036801140703000d0701d40081d81c0b852980780745415502e003016102d10040c21180d4004214007403141024000c000b400400071f000034114040300701c060343c0000c84e120001c044002034080f501034018070218281040818603000314a0301056229640d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 533720593 1250 533719343 533719363
    0xb0d05010e120f0405091909050703140d02070e0c04031a060901060f050901120f0f05040b0105010c08090f1f0207060215070f0e041112040b0105030102070f030f09050a03080c06060a08 81
    0x85000802048401803605c0040c0b804600318801004285800e043c550743d510081c0c4000d42c1c4601d03360041005644010031001c951900c02c0e0010400384d07292500404460714003c00d1500516820f000c040002800c1d03041821320058902c0610409080240030031881d4030069100c5001d100444010170811608101900d01e00c4109080402081c402548094090076104521807481840e0014000044110364002400380707004140c280081d030388850064650790865030024042500605c4006080e00c4e0030840001440c0000d8002c001d814002d0b10200400300d8004020745c0903806c170340d6080c400180e0412814122200c4101d00440c5401c104030041c042400404160040040030180c8400c203490300d400a00c46d0f1801000e1543d1303182036412150704a2031041c0d50481d8800c1448000040702d01e0140240c07001e02e0b401102c2c4010005059505403105446803001406000343d4100c005290355070351070581e00850042503240e0f91410b001020508110004004600c28400400140481c10700082c0c16284 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 533721843 1250 533720593 533720599
    0x5090f0f0708040c0306022a010605012a05070305061909031e11070f060305090c1813060f05040209090f100e0f010c020106060f1b060506040b0d05010e120f0405 71
    0x40e502c1d9410001c91200c0310b0b1708041c00081c00024007040c1c09048410041540702c003412041c80202035182c0403030984407148582d6001034490201c640240f580f0100021146610841031a2200581d641d03080c1018042e600070747d034541003c0100302c500c08450280b06480c000d43d200800c600b000e1642c001e880c912000d0741b0440d8160070240d1440c4030b00d0103860340c4c00395032124104980f012a42d0305046001200240203404c0002d0034000864040700000031000175580b0018210715040081c40c006802c2110001c017034a038554102d00e01d181c0800c21a104111a40e0109000810703039103094018002e441c2d1000e80215000c0d07000e20000000c0c003c01042c0441d403280322000100b5040300060f1184e103491030b291010045946051090002c49405500c1082110150f48075040310012840702560001002c100411000c2e2130045800c000403d15440281e00040c0140001109500140403030800c0030240800c840581d901d021079010300c841007020000360788003c042d507881c240e06214001010f01480c414140 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 533723093 1250 533721843 533721857
    0x1c060e090718050c09041103090120040b0f1201030602181212160b18160602030a232a0d0215040807020316050f151602011b080405090f0f07 62
    0x40132804d4904842e401c07200100300b40284072561a81c54143e074410340d4242c0340f6620b0700240d0254580b0803e00422000d040c0901141094075200f0300f8485a448a0b032900582c0500f0000da003078150746003d1003800303940211001070711204030725a6151544503454042d0b03ca80441d0042a001e120002141408480b0a01c0e40d82e440301e8103001508030800300880000c0c031050400d400c20101151000c0d81000864014040b181c01402503012626101c2680c0240070058008020042c0414000c400c81c0c45940024101308084002148603007059402c102c0e103200110040b04091140009008907160b000040300014020301c02e18600f000e51385840140d40c0f1401480e090001505105108099414803900601625403244014a180c05c1003c09805214860081c01021100509224080803e003004101809140018100d03d9030f4541002980880c10040d44035940311400810010001c4111311482c1d000d500c03a800c10080005070740005106943c010349400c1001035203d030582e04641c100d0744504042d0303 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 533724343 1250 533723093 533723101
    0x3160903050d110304090e01091203060b0304120912050a05120a17040f020910030314030c0301090b040b060d02180409111002010b0913020117011512021c060e09071805 74
    0x41c2c10350180d54003a07840329180c404a101001c1042d040011403500c12403001c600c074220340b0300035412338845c0d01072444454018000030303001851186d20700c40d01011600f03008414a0399000e03612442041c00c94119991b070072080341c1204100c03041004003006d8040d00b03202800c1c40e4500b04000c00c40b400c10141c0741c0312110a60f021400703000c0342c83e41ca284c080d6000303880c603c100c0c50251344000d4059082e1104400103034021355140000c00304c10040c0c03401460040040c43c55a46480c1000018200c8606c501e0307401a500d0301c0e42200d641c1d81c10300421400e0082c4074007585a40e080607844624024000c11a07024609282c0811700007941c40c1d42080501c01c1c00ca038960036010130410103d0040c03295051241e00403503608140a001d2210360902080940301340d0702d03d00c0780e108009071155900c03003e1060000200010242e20704071409409030910b030307044842005050454a084205c4001d00d10704c00940c91955a03407080c400042d42c403400640c002d2585008003c0b80d03207044903c1c0300ca24203030483c1d0b4212550301c1c408a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 533725593 1250 533724343 533724377
    0x90604021803030a0e150301030201020c0f030115171203131209030b0c180f0916270e1803070f02010c050105160f0c02090c090604030c090203160903050d 68
    0x105041c12809012681c030b4400a80700a800c0c003c0c00034910744207145c10041081c400705180c044a040c5ca0381a80600080c4e91081d003880300c241b05811502ea4155201c8950503544a8052007850052983c40701c04030100c0a262280790814081c01e003282078114082040040032544203864000c450380c0080b0b01c6e8981100e04804541c11201900014058807841e020f002d160b0905070040c0c02100b011070108c41003c03405400300030100d9006408103801860503000241c01d5501b030003025010f41c06900707102103817000e04c0d4412441003004940c0112040d01658080c03010b203807006045a4400319074100c100b0540103030030940342c1c0c3c3c1c01400c03001010b010400c0120011644249a542800b65010000348042d05225607241003000c411112540003e000c4120300031a03d00c504407244210350098101c4925417920302e06042c80c1da00c01e608107500110208030000006085486c240010b02c070304080140c9a0400290307018540304400084010451018818000b2070b4021441315034800f01c906040904049030b0881d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 533726843 1250 533725593 533725627
    0x2070f23150408100209181b12040b07091805070e22050c03060d03080a0b060c06040c05041e0506030a120c0b010e09060c160b0711160509060402 64
    0x246420125081c502101c1201010140066903980829500c460440c00c1152049010b01c11060360300c0300c106030760034210420007542140c0142c04428100e00201105086c1481644100014006082004200400d0040014a260304003041b032a10b880d0440c900780281201c1f440c040e5810842d036588801069141d07005503c885031100010305104100f95610302001c2070002c51f12a103615060801001610320344469045a100e0b0f80024000d400091454404445540d0000e0000394501c3c0d0307a0030305c180d01c4e43d21034010308009640000105103600c0c043c9410a400b200c142c0c07000b801681441245e5542850280d03413585044060140003d5669805000a2624081d408090712413000c40b241c140390164041c558a1380f0a0181080c411143d91340c07042c0e4002100d040343d030310281e608954041610400006c1c002c1010b16440d24034071b802207101d034a0f9020108016150b10002c644400301c1c6120380341c418000100150742076000d040290f071510000c07a12030400200854801d40c0c2c0010009121780003158 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 533728093 1250 533726843 533726909
    0x207030c0902030412030e0723130e071703070308070e040e010209011d0a090908120a051902090f060306030304180509010b0a08120702060d09060902010e0102070f 72
    0x4801940a581d901a4400a6005507800d8805010404000c4c803010702902500d602c1e4164070f4010308810f860701e0b498689269a40d4111580c24040f08242841ca030344902c2070300318008240701d0005200c8022000e035850002c05038484208014400c15000340e280e4040280e1ba049505070a14880a0744d0384581125181248011103520a181440b1900c0380340c0c055015000d0304d1020f0b02c885c550250200038021012500301c80c543d0b807001d484602488614115080030604c6481400c03c02e050680d6416107801c0840e0071103420684954403000c100204007000008180800400e000b1440d0010602c003080c540707660880c082d1302581c80000802c0360746d102001160014420307014a5140090b500308468003421069410b410b06601b000c1c2c81c180c441c82c0041000c0220742e00c0000400d00d40d0368000701180d258020fa40b0917139002c002800184500c003454010031070079501c103840001d40c00c0154800505200c40a81019045500890041c07041a60061210050b00e0014088140c801d058699406c40ea00b2504 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 533729343 1250 533728093 533728103
    0x405060609060a23070b0103110105040302030a050606030709052202012a0506010b03090624040908130902030106050d0905030d18060615121503051b12070b030412020703 75
    0x5256107006501080d003120f40010011001c81340241e9503d5130710b25014071a4080d04035581900100000b41c1d220700d220000b142c0604245003081c0c1c3d20b0300042e0401c520118103030365903041300e020403d05107418064000a4403031003504000d2801e040ca404a880740340c403103185c41141100300c541ea007560302030312100d14000c2216136551185090250002c440341c0146200310340c10b205400002c02c40510313400980e8801d50040307004011641d61550650303a00d5400e070384414038041c03204958a4903500c840c001c000005000b100d01c01ea840964601680c4980b1040d03001c000d10b80c0c410f02c010b100d03050340902105c4810144038804188240a4100242188181c0416600c0207251660540c0d40400350704184000a0090004200e001d59a40c100c15180181c684040c0c001104065000c10400d01c680c8500b04055200000304040b5490341da03220b1420110100c960400c251000f200c04162525074a400000c2c0b6900020307114181c98640060501c0c040604014000020182e01080551003004090010741d001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 533730593 1250 533729343 533729347
    0x306090203130212032107050c0106090c110a020a0b0a0e041b0215100b0c1c02010614010e060d090f12050306040e010e06010b0307050c010608010204082802040506060906 75
    0x301c07180341000e02c03110604a010b2503070014040c90311031010080e05c07101000d505403142e195140c0160b00180b4000202294180034040c003d16625590034801d080217005a07030f07800a121181c0070006019082e08410703600e02c80e442404c0c00c03001600c0d9640300c00c00715a2000c9059490b03000783d84040d01c0c1000c9060b119600903140041c0100c01001c0e1b081400007040c1a40c0aa65011282420005654034200c0b4540c14140c0800003c0006892840081c000c02c0104415541450304043c01c00e2503140c0c0c42000b140040c2e4441e2024403000c00c41740c000c003641820900f04005a84031a50101d00a401503c07420005680d0340c40110301401891824560596800804000316408000707014200d600b00303030303000380c042c901d40b4071800844d0005124800e00302c808100200320036860030940f465968401000c1c1d500701b14050003001c041078030900800c0050300c0c1d90800561078a040800d82850058407128942502e0200e50020323a11101400803111503d0301520301144c0b0360f45000110f0741d1031007110012a000400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 533731843 1250 533730593 533730601
    0x40b04090f0201090f2102040f2f0703091211030607090e1e0f0c0405030111041508010605031605040e130b0a0e0c011b0f080414030307120f0306090203 67
    0xd10300c007030000074400d0b2a030030006500c91508220b08400c0d401440091440b04011304c1518441a005601c400e100070170105122401400940c00e4558103a48011104950310308014a02030410300c081d80c0c5503403010362904203c0c06071402010820b6600c9102c20710790380748024000b0300c1460102400001c401508507206420600c078001c012800720f12035510350b181e264020071031070800880001203400000328004900c1c1c840a0401c60506005401d03107440c403104200c000f40545081c003c1e443c0c590101340d078058403145004d00c0d09a403001c0c4030349540304110070200103000403070b000030a80e500201e103134280084450a00c1025505445180c106940d00001d07241044030b464030103241d0203103185c0f2601110403152904074200d0283c564950030001e041e0000c1d5040d1005500c51003074620710441804083e4440d500c80c0d12400424014118103030740d281c1c40010b003482600b80c825101c4820000590046280c8062601c0e0441501d9402c1c4440381007111b002401e401691007900420064901001d045541e424 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 533733093 1250 533731843 533731853
    0xf070905090f2401090b01080103080d0e100e01050a0213060503040f08040e0106030f0b0102030a0509030a0b090c100e011224080d020c040207020f0d080403051c081501021b040b0409 80
    0x500304243c1d006010800119041d0a01d00890b00503110685884003da421999400c80d240c0100d00c00d482c10300d1f0b0381c6420301e101c81c000b0401c0100c0003a030321900181441a610b5282e094820040048000a00400c141c80d03c40c10b11940c02800c4668510b44203880c2c1c1c83d1b0740b50180a0b06050b10340900200ca0104000c24004101110356040b00c1540e10100042521143c0707160a948004d0185800351b0414090350401500604c01059286030040a6810307034401d03641e42900c003903400c0e07450440c3ca921600319041c1c075040507954600519100d0a04c1081023445a0000b08100480b801014802c0d072201c141100310a19401401240b001c40403050441c00c0d1281e01071603503018a09900c50051050140710141800c1a00c02c0700e40554014103001000d80d00c640501180c20102c0380300725540d07042040004003040d0b0074040c0d106401c0b502201e45484054440004040300b002400048080480585100050b80c0020713031042c0700596280800e00741d164650000c0e0045c0030310451550458102003844003081 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 533734343 1250 533733093 533733133
    0x103051803031f0509090d080604020f0409021b0610030206070f06091104050a020a050301090216050d0e03010c0302040e0a2d020309010507020115030807020f0618090601020f070905090f 82
    0x1695580007001400d940c1e81c100600d4217001e9510300311b01d4003c61300e02c410452203000d00982c401c4000c1d0001d494910b04c0d42d20550a42d1296001c24403082d400f151021404180c64001a4403070011001040507062480f030009103c20300c0d1100a00caa0700004d8040c00300001000d0340f908050b08403c0402c0100d81500700421080c01e01c2d0055403056142c203000071481c03200c910a4606902d159501c881c196803c2007a90300080d0300c84107403629102c07034403640c581c0050f804102c0c0d48007180c007942d203c8000441c071100703142c20354511540082c01d00d4010720080c0040d080e040441c1d9800401510081078164245c004540541e046500e000c0c1c0d010700d2124440311180440d00194007591218008005550301d5081c00c03802c9a600c445441212008a101007001c16400005451005d0005100c40c61700340d001000514194080c814001c81c440701e8029000540c6009682c2c00e0703110b20207001802e40140d00f0800b07244c407800c190103040551640c80e004203003009420441e007140d802e1004c003111240407184001407075030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 533735593 1250 533734343 533734381
    0x3c3207060b0405010614030414071e05011403150f040f14090d1707030f02030a091a01032a05030607020705030d1b1203020c0d0f030b0f030705010305180303 69
    0x2560429901d161142018400c0c58100d0344150707034001140c41d81c00820880b03030340003500540301e5507150102c1d5010b400050120034010000d20044000b800c0c02030030a0010002c041e40554180a41c4144101d40c501101c1d0450b80d02c4000300d01c108403c903503000d00080c05400004040380c0c00c1450301079030b01076110040e40f16098600514500d1790f03036603980032030a50382d4407145061400000c1480451804944480c820a500010745040109403115a40c07003000407604110341008140743c590406000b070180d030401c0d040d0203161310f400c50345841d815500c8596581888100300301b0305000c54100d45d0300c0400310504d03980c06000c1c024142c0e5a030b8280700100039036078070460040e24070901801d9000c1c0d060900034060302e402c03030800d1b0000d03c140490b1501c41aa005d110600f20405154003006001c200031418400100c190358107071103585008210078801000c032441105002d01410844c0c0a03000240e030000380032422900309180102d4242d560b4500c8180080c10600412000c0c40044184611010325405c0303100c40f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 533736843 1250 533735593 533735603
    0x3060d1505010f2d09020f074701180b090a02040302040b10020c1306080a0615090204120b040302120705031e0a0507061d030a3c3207 59
    0x5010318106a084031420080803696513940301c5410802d00c003258014284540032050352604110702500c40c0140c0b600d4482070805407032500c43e0390070030b80b0030b03018480410101c0424404030b8000ca03030550a202607030107020310805441c2074880450030b04165000310344010800350440398941000d5444001a40041c00120300c11810300b18840200d0900ca150b04020704915401094450b1140044c429403c1c1301c400307038468054a401c3d01042059042001d2509a4440c020015014210040141601140390010200c40740100020822000740c003003444012a000040900141c48520b020fa142800b10340b164640d54a001ca400414024044060448803407583c10b50741f010508152004040d12800c40b5a10100d0802d0094201107030050384603c3c0107000040c10460036592051640c1e1864016507224000140d201c0e8503080400c440541e1800c00843c0c501451084141e10320742444083c00ca180007100700041d400c008072012050001d03952080104210450b654414aa0310540c103900c0b0710300030744d2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 533738093 1250 533736843 533736869
    0x3041410080910021e0a0809100608070308250c0f050a2303120c1e1603200406120201020114040b0a0902210f2103060d1505010f 57
    0x4010700429240b0311400c0881d010703004440700c00c3c00001c003d400951720081d41c80e242000300d80c24018280002c1ca002403941e242d421081c17419205d49441c00400b0781121641504000003009550b80021722107007500d601070442c80e1103030040b00f05500c00b5207828680d0511048081c1d010001d03c17480e0014942500d040c8a085d0544544413014800c00100742c0c40b030700400111010200c0b440c0b009070300c4182400d500003801d03510022809070388000070307410044983c422600b120110b045900c1a418034200c80109110240600c0c15046111281c400e0242c40060144240ba10114002c000d001e66410341d58003004001704502c80e190b0a0b261030303829020900300d002d036107802c0c3c808160401011446100d00e07445002135000707039200c21901d4094101840d04a0300074613280c08506e10b000c0d45028010104002c50018040c4424130f0111a107040c40312240c2c4404645840c0b1689445140c0b02c003100e500200070ba4802180110724a010300d404071115400c4014180380000109513106035680700c108840107040d110f0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 533739343 1250 533738093 533738119
    0x112180c1e0b0309120c150c0d06060318030e01090b0301031a0604091101050d06031a100e0408040501030b0609091501030b15090f0a171c0e03190c08030414 69
    0xc3c03005a030342c0c103030301d50064403410b030311740c00880013004010702d200280d48240400e416800e007290015070b0715800d1414081070a01400009201c1d5030010611072600380318140018400c3c1501c2c91034084090204403020140440c540d02420b0980d00802d980140c882c0d481d03941e420110031441000032400d480341ca20401090745072500b4082c0b1010a50094401d040383d90103000195520f40c0301800e100051512094000080b9510201d038540c0082804523110326031400a0103500744520a8101c6503480741d00c80c0520001c01c0d01070b0140c60903202c0070b003400035003500808001001030184003001640062401c0c204505154550802d842c01d279030070703201440404c0000c4104598440040c28041307a1000502c00e503000d40c9043c400745076100d01c010302014030350358899804000b0402d1075003071041c841d0720034440803500010356000c0f5115082140781180002140800094940c0d045810304402d810002c0401800e01c414184580010459442101e40d41c0d50340f20001828071059000c007034480c200c0300c4841 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 533740593 1250 533739343 533739359
    0xb090a06140906180c0a0807140102070b030114010c06091b050f10051303050a0b090d05030402060301060507230c01120207080a110f03030103060504200112180c1e 72
    0x4140240030b1a00034040d107a80b9007140d0000000c2a070208411807040d00104034458940d214628003a042d8031000e0140c0c00d05003856003000c0400d0221250446d4040c0e60108505101202074905462440001c2d0440c0040900101d1300c50000e035002405913451318000008121034400880e03030b07500d8081d04020342265940100b0405511288500e42c110802c407054402e194403403801810031800f0106680c803083c2d280e445113450441800421101c00c506041884152a410001800902c0315442e21324518503242c0d010031010701040c030845040c000040340140030001100e00c100c1c0510040300000c0400a9003892141d0740b07405540c0e586000c42d00d00c00103480083c026008654000e600401f0a0345016040542210344240202014000340074041104851501c203100550003035005c2e03480814039041a04208400340c0c1d42e25040394179400b40100224050741c2001c0c880414040b003040001d0002c81c95440140d1500c10200004d01c0100700102c041030303c240081030503050849a00d04448519190116 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 533741843 1250 533740593 533740631
    0x30a0f1b0219020406080f0f1b03070302060c01290f06180108100e040c05040e030a0207090c05090d05030a02061f031721011406120604180b090a06 65
    0x88005821400b000850303004580341c4455024070140c00002c010b40c0e01e0f80710754249881d50b0301c0411150851a0600b11010080080c007a100d071410010003a844803030f1000990720f030b2052100a00035a00840c110303e910200f980030002102c445a0b8900584848100303c54405180342080c51081002000007040750500c0000d88090750031489030100d110b95440010346030010018080d0207281e010301404111581010b0b031310342c025880b440100e00c41508000c10041a1800f840310030010b60f000f40603001ca20380d1700281c1c000072604107440008003481c03540340440c8c49115219289410610000100c410800004028103c400b0540c2c29103121341c031084190f80786088402d9000e41c90385283e042c280080344040c1e0346810310001600102c4d241c9100740d14081c00b03804000303280c2c1000c1e001c0040104606104002d501003c010100c1d050b1349400e64480c542460b0b1400a003805000d10750328011a074603000211001c0e0b0398260401c81481c083d2074014140ca5945c0c4c2c032100101c5602c0c0c28101210014100341d02e0b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 533743093 1250 533741843 533741891
    0x7110f0c090f0a20180d0819020c030312010e010b040b0a080a1811010806040213090b04060b0f0301031b0302010816030b04050c04050109080c03070b0a0c0503030a0f 73
    0x101c10745a82d2110324000200d9040540901040380e640d2034100403031603845043d001002a18614142c54281105042818502e46511035000e411080c0540700000c1c00c030001c55141c00030320b4046010b400f10140c0128a40303884803030300c80c3c3c05200000f040c405601013030840604135600f0b80da2524080c1c0e04c030f03038020000340901d00c1810a64503003800000c1d0450b01400712654401441c50000560010554520304a495500c100359418a06072405000650f4000045a13200d2030584041d440d0480c41290140c411203940702d480712059980c043c03c92540e9070754004c080103103848403d4503124000c00344501c0c0a43e0081c40b080f10404445000041e80245a440c402c1c2120780503181e4001039035800398210f181070b003841041c038105691240101e455980e184955070117402a4130310552124208000517040301040c0e0411502c5a0103c080c10080d41c1e00041c210701075810f10388029417100100d0b00c007a00c03400c800f0b0500600038080803082126150069100c4410b0a00300c0b20300780010304808442c0821004c00d00c0c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 533744343 1250 533743093 533743099
    0x8010e060108030708040b0f0d0906020a030b040903050d090206070212010b0109060e010801091d0604030207180501030b070c03050f0309010f0c030c0c06050c0403020603041407080f06072607110f0c 87
    0x1006c10002d9000d0070000e81504100500301601d4046050324420840d107584104031120b560109900e031825500d0310546001c030f801901d040045100f207450160042c00b91501c40d40c1c41e251030705405000c54540c40c1c160b526441d805805a042d0600c0860540d001e0807855510f5400034142120000b01c10f131003000d031500307843e4068498802c680d00701900c10300a81500c020250345040324000c1507100d010704115080c03045009a000d000001d0800c0300500303180402020b0303401410709041c01070010078250051a508906c0034200701c0001c140318030382a41c040c081c0c0d42d100e80d0041c80200c00c001070020306420030740c42c010760319000f00004103090070250120f4004c91000400154007604000014110307501c0710ba0070410000040c0c0c105503823a0300240540d84112002c40c4c180c2101c01641320941c2d810004207001d00004000341c01003512030000d16640e41d030003c00030410055607040384a2441c1120300d682d4058001d148885040e40381010020b0f203000840e41140b09103110b0030701c000c940400007092000e2002401 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 533745593 1250 533744343 533744347
    0x41401050418020a0e100306060e010302121909150515220507110102040306240b0d0906020405041d07060806030703060b0616031709060705250c08010e060108030708 73
    0x400042d60013034012a04290174440401c9410007980e4401080c0744540929a501059060600400405c0f2480c0003010381d05250052100703100128480704900c1d03100c403411500d58407243c9200224809405455406000050030f809030fa0041000da0b08000d11840d0034107059a001050002070000c16030320094072700c9010164940704074100700b007500150b400c6030292804215440048942c2801ca03801039204031011070382ca250812083c04402035485001c008285503404051804428600d04c0c0f080780303103660409948641480801c903042e130646010b004013a00030003035018813545850310b503582020307141414801c154001130103074130a46505108480c080c01402405280da5940d0015181401d80d0662110f424442d02002d00e40c1d424001c018036000b640c4000c4c4411130b0b4401e624410a016143d0a6260880420003a6998016003183d5174102d9004016040307044428102c170408002c070000a2641c8035141000448100542140040032000001d80b002640d0700c1000503034900c68054014006201 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 533746843 1250 533745593 533745629
    0x31b0a030c020f120f1b040b01021507031107061d0601080d0f0203070b0702031e040806040201121404080d0b030105010509010510020f0d0507120f09140d0b09030414010504 76
    0x1003ca6800034140002d020458800c1c0980e030410306114013034000c0e040e0f65201d90b9184c0b4014155004001038008183d034104040000e03400002d448804003128840341529401c0441c0e1601d1007039118900050040d140107840d202c00e840c00f00301a0411308400c00c05003081c1d0030600304201c1c0116003035040b140c42c000145101c0409050075640f20005541d800c0541c0010312a03000407a4407203107083c0c03081d00d15034040e42da01c00c2d01030121880049030609103003481005010034170103000002078943d049a024200001c0c2e80f42550b0300300d0081e01414071144080c1c081ca0b800d0208002a00c8041c00e0b40c0d001100c001c0c0036020400701407500300c0c1c50901c1515841060080104200c0c140070b103190f400704106206445102c0b401441c880d00d0901161101700c001000002c03203800f440808a40d1000d008900d00e008041c20b50100002460790115006c0c00a0050369040c05101e075039070f00d001e108110382e0302404450b01442c18070040d507103a40052049400351a0090904543e56110351f080750141e03081c5003030f540041c00c5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 533748093 1250 533746843 533746849
    0x4060605270604111305030f0601060801120c170a060f02070b040b060303070b01080c0406060e061b0f0d0e1306030206032e0810060905190b031e031b0a030c02 70
    0x81c000d40000e40080c0e0721100d59005000000052424030010580c1c445100d01d00028075144c9150781010f02c1c466089040180b0481d544a411a4110b504d07501d003600804566091018812119034041c0c40603140d090102100390710045424a5403d018240800c049400f08155406070704c1008030080a4004643c0007900003405c0414003500b1042c0501201d041000503520003110f81001c1e08a031003103030b00408088a9606c2c090041e07501134106450700d40400d0843d01c2c04030f11309004002c02e200074081ba00c0d007200500c51080042412281e0100100d420301c10b000c0c40007a2110103448640c40c0140500200300c815003200740a94806c5030350141440340786595400fa40001068403070070345031071405202d46050403000c1c44018200a8110380020348503034a85101c2c0d0b141140c5c2d040d401010700d60f00b800d0800107914042041c809400c1c0055038003003403c00304100002d0600a50a0004410440984440c0716202c0004040c0000d001c402c1107450141d10b001d0781050792210b82030b000800007200032018400600f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 533749343 1250 533748093 533748169
    0x41203120906050408030103200901060f110105010f050f090112080c0f06160813050304060f05130303090303020d020102091507060b150901030606210c02190b04060605 74
    0x41a4600c00156612681d85420554000392000e80340da9401100501c01d1002d4201c000310710a0b00880e1144a4800e0500420110501441690103000d180307a0f24034900703409860340d0040041054020000b070b41c1c40b400c991888001034060309000f080026802c3d1300a09042900ba8140d842420207003450b42d8150b641c02040b0f40c042d82d000b40e498040c08d540390078100e004001c944c0c00360301089000320f03407003400b514010401c0c000103050040308927440c00b080c0003080d0040115000e8452030324050000300211041030301c441c032842c040384418150007140001416807200c1c0308425213100c5d500b40c03800d105c20020300f28240d028139a006e07680300003185145035110200d00010006544160b2001c1411180789001031204149069000740031800014070038019230745840785c000030303000e1030604062000c80c40704080c8042e40d40790302c0200215a03650b030669445000f0011050385040f4858140400c0c00149002c05002c0001da0307080301c07094241034010540d4079086d00809101c2584051004e0b1054412002184113 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 533750593 1250 533749343 533749367
    0x25051e040b0307080a060f051e0c0901020c03070e0403020706050307021015090c03051602010e2d0a0f06060f050f010e011404030b0f06010c030527060a02010e060c041203 75
    0x342c03040800001301c0410500501c1050b5000d501d0001f2905441c0b144002518001000b64914941000340301d030140c43e08003200341d0050280c2c0f540ca80c0710001040180e107402c0524041d580c0c0762180102c000340e04c0360a201040e04c0343c0c0c0b180d400d032500580e69400503070f01804166000c4001d60040511400406125400805c0c0080c0c2c3d44082100345942d8420242240c410b4014000007a4490042024941c4484030109840d1501c3c402001030142805172561a00e210990107a81c10f8403c407000030310f50110b6020480c5042d003c0c03064980301e0103c2c5c80c005202410b652000c44600d4142000001c04500c8920400122540038241c10b481c844500c004581504c040c23244203042c0144100c030404e01c6119200076002640c41000c0303c0d40c003030500444e604803452004100790304100343d040243d000070398400243c48614104542c86030109031a086988214880c01a020741c01030320101d45400c801e681500500780301a50304003a2a400d4840902d509228419402001c0d042c1c2c41001c02100003030b100b20024a20 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 533751843 1250 533750593 533750599
    0xe0c090301090606150201111305040509030c0316031707090306020c071e0905090705060403020915101d030a03232802070603050f0103080c010207020325051e040b 72
    0x4190a54803c021a00c143c2c201a541582040b43c030312429409215a040004600028030708205404080c180c0008182c01401c1c090340e100c00c045020550208141c5080315080d106072600c401440301c1204003040d400c2001e40019000c45481c2844a403580d414a002e900250307940c0c480541151541e0020394030180b103081c69480703140d00001742000381017100341404a404281680141c1303400ba044044c2d400117000000c0d84d4000d503008000b540d4039101200d04683c0d0590710740e400c83d030b11201c410419828400c0540d800000d44060b02c11040d40c001690100c2585200052406152a10070325590304000c03e4000c005c1800c03240315034007040210044078003c00500440320310300022218940d600d010303003400c0310901d0820001174039400e075014490500039003c03500d81008140b03815a2143c8000b201848040c08843c2c0009800d112040290121186030350040e080f502d04480d1145008039040052080d00000002200086241c2c540a0445e0503024010440214803540000822000703100300c030b1030a58 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 533753093 1250 533751843 533751851
    0xe03040603090f1a07170c0301050409022206090621020405130c090c02070e090a1502040506190809150a1508060a05071e0f03090c050a08250e0c090301 67
    0x20000320402d4080001d01c140c0c0001c10a14103003074030701601b61a05400440321407003842c81007190541c1c44100b03aa044620488004c1040700c070500200708000d1002044811460051845401e103814035003040c001c80300000380402c15543c0c0c800c884041e44503400a10710030071265440c0300000d807615810682c0c002119035442c00c1c40d201c040c1e44070318511071540d01948110b034881d03000c210069010700030301c002030918100711946468034194440e228480350000801c0040c400d81c000100c40300da40c1c140e6020381400342515076580b050358900b1100144442c9000002040100000e49400004c10405c1403406c0c00740410300c03a620703100310b404050240303542c8040601da0740f4000001c0d0b8a8003000f06a0154549501c0040d450800d841c000b000703485610b03410070b510a2441c01ca891002e502c840d00c00c0d520f02143c03800180303000092525104078100c5510243e408034030a680482d43c16008035420101c0f07038840541c0708504501c41d9100d5040d0401d0b00c074041541c00850002001034010400400085000400000d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 533754343 1250 533753093 533753123
    0x40911100c110a05030319140309010209040606050a05250204051305061003170a0c050706052a0c100210150512060411040207030e0619120e0304060309 67
    0x1899406240c51080c00954080c1940c020300c4403042d5000c038141e00070b8803000007050a10300826070313034400e1007400040400300c0c190310341d8035030f110795000000300e0b24a100d01580da040040b02c0764040c0d040780790712758403840c41c040c0000b6107240601c0c1143c15140241d2035290030502e04040c40f220341116203068603140b0304001e08130300041c0e8403440340901c10f101e50040c84000c1000c0c0d0500c5071910701c0041c01d44c44035a07040c060038030214085a880206400c8082401a540c44c684501200d0344042144010000d2091070004140076800001801c3c160544001180c400000c1c245412000d9045070343c0721034690040301800005050140e41602c0e00c80031401100e01c43e03002e60540804560034008244a10212003c060015103011941c00446402c1c2e60001c1051341401d4481d0960704a290840301d12450340005c400c010075000380302e074020400c00101256195101d0040b660b680f865040500c000141400300042c02805061144801e56604100194202030406000b0f0f001001e07251816150810410100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 533755593 1250 533754343 533754349
    0xf09100c0314040b01031a010e060603090f060c0d110304021807090f080703020109081c1d04060308091c0c0e060414130b07030c0e1302040803040e041104050411040911 74
    0xb50065125a0001c031840d859420448080c805241300281c03034101240042280405c80486a07400c64400c680383c42d50382c0c5554140902c1d109102d203080d4118047c4404000c6818a4000a0700300b4803540002400314032410402801c5d18481298000c0d4000390103940150480310980c9403982c01b4259040c08110076071515901d800c00394055200d070b001a4440c002c01d10455034070401882c01084154003e1000e044c4958145004e00c0712410b4520030003100d00b218210700740c1091302c141d013400300c0500304004160b1682003034400d5501c0049814024440100c01c92582c0c882d151441c405a504118096040c3e0704040f0102a03031000a0411740d80240c842c501540072420103011607014400070810301c07030312a40d1450110111300000300301000745441e000c113442145401101c4000e051800701c0c0c00440c06040d0007003d030001c2c01a5080302c46035110114001c940c1501102015000714010483d1250708103280b000c00090310002c94004010400c02140804a81040d41020316118410440090032555281c08 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 533756843 1250 533755593 533755631
    0x6020703090f09090c1211040f061701020304051213090c020109150c090902130b0d090c06110f03270f0306090d17070503010605070501090506130303050f09100c03 72
    0x1c8111003540d03505100007040345c130354500c40091900c0710070302c03420b60713001d07166005125120400c45018588030342d001450220603074400b401626110704501c0c1c03448030700c440860007900121821640c0d07104405003620401c800c8070503034115140d810021400e141c140848240a041c20706041419907484041c0040015000c03407407e03820320200800001d500e104541c1c02059100c076988500c4000d0310410143c00c00c80000c1c5444c0c015241c0404e000c5030307544504480d1100500c0055000707072881c1030b04400424625401031a04003000e100d403003200d420040d40040c50380c1b00e100315030308410050242da4020f4441940420041034a401c0184200a11400c2e03401180c20514102c8152006822441c80241100d400c0404140c290600c81d1100b030a80c0f400650241440c4818002d500c00e1100100d0300404011094001000f00c40e03001040d01d420381050b05008608035400e681c1103000c03034140030010301501d070101c10b07040c4100440002400ca80382a04c040e01c00034071030b8034922030801d900d4404081c001162820 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 533758093 1250 533756843 533756849
    0x30b180a15020c0d09080304120c0504050c0715021201050904020112091103010e010204030507032301020a02060604110a02060c0a09030503031311090705121909050d0801050d0f06020703090f 84
    0x207800743c1c0c1c03124407100d0395013410a040012014030411860170f2106180003c1503406403400b00540300541051420b0120b40c810f4a9440f0542c090706050030008044001400340c02c81c94401c1d4010380f80f510600d1100001c0c2d0240303044101000c0458001048140307800402d868015006050100303032403500d1401c8400383c0301d05a205030341001007002d2001d5039090900c2103c0a80d0b08140017142414219075440d0346403007440c440603000d20780b49456030f05580c02d81c12000c900760184000855131080040e1000c0c1d114801290001e100d24503041c0340050380c0700c00504580400c1c1c0e56034054410340c0c2c0d404000f05034a42000c50b0310000c03c452202c0c044001041040114042c02c41c9a10402a0495510303062030713a80141c1800a02400c1d042080c007141540020039152018020680e0582680da04205011407105100313001030250305000e0420709203d0040f40c22074514045d0b50b22109aa0b80742c20a100c1c03040b01c0000300070407001001509002003481d690203404050b11920786600641d50300c1014042044c2190 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 533759343 1250 533758093 533758133
    0x310050d030306080f0c0303040b0a021204080d0216050306240d0b040203070506070b01290a0825050901110c0a0609061116090f0b060a050409060807030b180a 70
    0x40241303c0d070541044048860040c60004141ca00d114002094481c0250321441081d1100410010103150080c07095030420b10801440d6900c86a854004030398600d01a8107581c0035005440080103075032a2000f40e0313010b40e00090020180e540301c00381c03040d5100b20a000c5620074100e00030749003003082d03481050300c9205074020981c1791014103080c010582070010307980c0014807070fa008010160024501c1c040040c11186055081c8003440100c40c0b140b5503111403042e02901455000601d03050094000200c94019040c0702071018017003244101d011940503000c2c070080040380d018044221250301c100441d0810310851000c0d110a0143d41010544a06d502d40140c2d001c51003203282440840c0d4800d802c4544003c0800013003003a40d86000c19850420090b00851711403a8413400380c0403890042c1c4c0c1060407001d07400b40515680e0345650200034803a81003030003051011424990001400c3e40001504801d80f84c10014041d01c5890700d004100d00b104101c02d07044402d000e002800d030003103565041d00103040c001c11 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 533760593 1250 533759343 533759351
    0x90a09020a15080c03070c02011b0f060c0e010e06180a0e01080a172701020a140d09050315010b0c0a060e100f1b08070e0d060906111c020310050d0303 66
    0x10500203060500018410030f03548130301340b040090072030740101e04918184d020300b0a51126001c2010803070509850000107800003001d4100401005001c0d444800e1180641e03a40800c1000c10100468a027005405210341c03000b07050000c03400c0580889030740d6030100030040080d28004d5030340c0f040c49100002603026006c1c90b045880408180207488075055a07a06401d02c0180c43d000c03542d0300c92142e4044050b05d20803070380095902140580d00070058030720460303001240d41c45800041c00d1401d83d100400e0039a0710000700c2040d000500390400090a403502500c041640001d6800c1402c18105508802c1e5044100d208100720100450658405ca00d0203001da88064007404c951200e20a06603910b04803110314031807602c0c02d8507a50658600d000e500540d43c0d4903010f282602c41c0e0000f191401204042240e216000305820002c0140035404401c815119036003c1c84000f00c000300c00071041c000c1c2c2890f000710b02c7d0b00c504080030700b034081da00943c1e02204020001d21166180d40210f41c612031003500841c0400e0351 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 533761843 1250 533760593 533760629
    0x408032a0414010903050307031b050313030311010606080f0703060b0f0915160f031115010f0b0301050a03030c02010c2013020309100f0605060c07032f090a09020a 72
    0x10b04240c5000e440001c1c00d240c240145580e80d0550341340f103500340284c104500c50140341d0340a110111300581d16600b040c110f9485100f140068800d404182c0700071804502c41d070710304640403070060141a085880355240c0404139918031011105d407100042281c801c040da80c040100c0c0101003c00600400351800c6e40b600e440d18040b0050110380c9070380240c0034041107020b00070750440c0482104444200d5a00c00c00089102142c1e281c141c40880743c2c044140220302508204a03c0074080d13503c8107040340e500e82070a80485903148000e2446102c280649030700410b00040500c040303801058280d0b2084d2041c5003440304401c41d91604080b0001c9041145944280043c0840151400302010600240007000c00c62850034044102e070340d10200000c4071400a41c0b0340824803c64265070740040c005141c0507060f541d03912002c0818544890042c0404c481c092452b940c1d03050f0900c0c03002d1402c5003240e111141c1c1c02c0010074407000c2200c10300e8010040101d468486021100680b0b80d895210010558104400c4070040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 533763093 1250 533761843 533761859
    0xf0d090603061410030b0d0b010b07060f0c020d051e030106030504140714120a0501020a080f0a09020f0112020c1002130501020a0c0302090405030412030c06230408032a04 75
    0x1016500500c0405107038401034074944c0e41d20002032814000f5041c00500d0801940100e450b4441902c4090600c850b0b060001604103d10001001000d100e00320030800340102507000c800f1144400703240c000590151000441d1a4006c00007400012a42e010b41382894082d0f9035103022580c000d8100c0300c002038039401804100701441403244840e00020020f04490350514170810320400003101c91920500d10001c3c500b0b00e9507018048005040d801000030340d0384440840c0301620b10f0300c3c207460040c881d000c044001380061202c2d10540d080940c0c02005040025840703401141c4045000f2801c0ca00d840d0308000801e00008100b10480300d101e04060003507110b8138913280d1500141d0705640030f1415500255101000a403e051007a010340342d045410500c603031074508119155001e1a003000701c0303500f10040303c1414543c01c040d4040d500c2d4070651080c0705c8070000b46102043c0e01d881807500490180003202240009080b18061a8000014407103012403801030110030718548420039071914503800001741031000c0b00c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 533764343 1250 533763093 533763101
    0x21908161e231b090c25030806030d050703081e150108010603060b0426121c020a0c12140d090b0603010605130e030f0706020a020d02010b0d030c050f0d090603 70
    0x40315400343c5003468410020402002095901a10460681c0f000440c44c8444005035205505030740300040e05c485015007501c03000003001c10181c02180503a000030321280740002d03c50a1040c13a40d80d695042030744541d03040d540340c0d00240100c0c829140c80902000914400d856043c0310705000c11000744c2e0240f40f0000500400011f804c210200350800c8070a000c880c1c0781c0000c0f10115240d00d580040c52540c00001c400b421101ca290040040c000d82200400000046010780348040c459042a0188904451714100301c1c0300e0302141c2400300317000003a9040840e10301c0b800a4440075141c1031088003180746010a03200c41d032180038040c41580c3d48410f100d0034081d800c0e0f1403d078003250981c001c003e00c0d800c04000601802c82002c010940e162146c510304040c4c2014000d56001800c0480300c80d85401480c038000020b0340082c000140144242c83c1e4074a10184140105240074101601480c7c4164075610b08443c020741c40402034a141c0314210a625080004019035006000791780d55220187e400d252009081e1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 533765593 1250 533764343 533764403
    0x31806110d0f1503020d02042c010f06050904290106050c060a200a05090d080c011a061603211b020a080414041806020307021908161e 59
    0x51038403d02512160110640708156501141c803443e000c61240f0000700505450780801540d00d0180205111400416808080c0601814024003d010203100d0900c2200c17018441c159000c1b52120101c2c0c00300c0d1890445805040081e1a55011000c05114040090743c00b0781c4100001080016032200d901c60500c0040e400c00010b9409000c0c00203081310024107030503114464921347c4000120181c88074040d00454100a002405900c54a0103a040c0b1302c80e90b8201844661440d42000d08400d001c0b01581010301a02500904940c10003407940e2602c46a49a0814220203000f620883c0740c03030000030000c0603c030f0303036940c007201060201520543c0d204d483d1031180d07074405540c0465418800518007505a07021f461821050340b004041540005010b07040300508044c480150300081070038041140c0003184101d40c25002c0f14100c246422100100445502c4081c000e40f2090200350b0000409404041019000c0e184007500c500000c1650020440901d00860f05030861600c03811204031407034800c4e030030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 533766843 1250 533765593 533765621
    0x919150e090129190c0605090303060102250509040c032f040f0b090406050a05010b1612031508072301080a0b120a1406010902040b0703031806110d 65
    0x1e0b514081070a004180d0702c1002002d20306a02650b2540980b5410558241c0303410f01e403052540d10f000c44009400c03484410f00543c0e0240c10200012560003000080300d00645045e40107100c0c0c5000307141c0084050412444c442c41502741410000742c20358030513403242e0060340120100b101903440d520303080030481c1c0c5c2e10b4410f00803941245402315a038070760025190302549041d18040780310740d603446d003600080600315140d41d4440c1104041c00103100465005a108260800d01000180d88401c40752120717000741d008075520a00d01c28103100c000f1300500002c3d034031980e45060103c1d403624003c808814220094003e400c195000c5442040782811120700401d4031020302d001d00c0b865004120008001050041c100b584031130300d5400140e85034649805078910070351036605681c03400c409031805c050181c030740705c504009502ca13000010642038010300c00c030b50407a086034008501d01580c0e954141d0182c02038060030b200d0310348940815400300f012402184580c03501d02101c16600c00400011001b112422844040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 533768093 1250 533766843 533766859
    0xf1b0f04060f0e1504050405011a01020c0a0b0d0b040207080a0305010f060503060d02010c1718060412031b380105130b0402071a10060201050c0a050919150e 69
    0x12421060080110035689401031080711a603a075400c2004134984101c00c260007503d08020007003800410f42c4040f01c90140718214040080c801e400490340c131100341c0b030620b034804003018040182c071202100178417500b00c06900200311100c09400003401c0ba04200403d0310b00000028000d102c165040c851107000d40003810300c44907018200782e002401400020010381c0101c20014071f43d07042d0783c0140c140b210b01c02d03408940a50511140226102c841e006030f030008501d200d00135aa8010b600e4083c0590301500d10400301100e020740140c5045510800703a18100012012040051011440000354a24002c2403810481c40c49142c400c1c0f80e510100c0400040018101c800b001484559a5a00ca083d02e034022000c002c2029402c00001230024072404038024500144200d81880510900d00101c1c03251441410108809a6600c030590036034030f00706c0340d0384909402080712444c090700480280001b031a01601c26800f10402800343e128010403500411211000c002045030a1a44091140340d03118050700d942e4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 533769343 1250 533768093 533768099
    0x6080c030907120f06090c150908030708160f030504060e120706030209060d0e070302100215130312050a0506150a12110c0307080405010810150c050f1b0f0406 70
    0x2946801c40e50040b26104102d103d226001d200c0d0760a10351607040d030400c0c410880e1600a2520300314200d214400c241f194000c07100c1c00d042c0180605030301802c0314800b801840c41c0c1066a80c901080b603120f0320050000c0e02c40c00c1d01401c040f48482002544403482500ca455489040c858007a000002c900d131303514440d24004200c028560804200c19049401506015840e1050b000020b1014082d0b0400b00e95503515000b10401c0140c130004030302088a000361103038644400000b404a88070091401004066184000807c200c000c400e403608210f94000d00d0320b01c40003100715010200b550402c1d6001168603851f070050080900d80819440703450808800e80b01e01e4603801d800068038120200038082145503036405884051200503044840c15900d0758156648c0c1d075141d00d06a61075821901a081c0001e0403e400103c2070541003042005890610000c0710040d041298120f49a5102d40011a094091151480d595150820141141240a4490034140050740e410b016541c1032412079075110320708102c020 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 533770593 1250 533769343 533769361
    0x1b0c0901050f0310050c0d020a120f140c0705011803020d1103090a0303030b03100c0c030e011812050c030316030e0604030b060d06090803040b01050910050a09020a03090611030106080c03 82
    0x51031072800c4105003c200b59545000b020024001d401c8880141030002076000320702c0707034010098098620302b01030400c44944812500c8048038103501d0302980701c04009000c10070400ca000003500d0114803079400800d0700341d0705031041641c05942c4a8118090780c001c024030485039401c1041e086104a1110040d82040540c0d0002112140f00e440050141540d5581c4400745440600412106e1711070382809018210007110003c214200e110030a40c006016a04078402d07540c0315002e80e0030800000607961004508000241d20740150b400002c803a944a460180110b98030b0600141c80502442d1500c8505034a450501900d4200514510f522502003040b041c400521707407092898200d81e041d120110450010310f00400100216a03001c0d21602c0048200002c0050500c07500e8107a401c180c1d55606036440710800b41140f000c0364050300307030b01040601003032010b55419809020030300414500804d01035501d0700da1908451443d4869904580c0003c0140f01181d000004c1e550405108a1058618a400404 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 533771843 1250 533770593 533770603
    0x70f0f080c190201200a1e0308070c0f021512011509090207120c0f1a0709080a1a06010e06121e0f0c090a0312021605060c070e0c1b0c0901050f03 64
    0x360607840100c070303000440b6403800c108202c4402c0d40690001c000d847c160a4000b160700000c901100003035400b10000c6c1c0306510507072510101c2ea5102d0070007a032a004541c01c00881d00c1001d045031804c0c10040c450b01800402c002a058000c02751900a40502c01002100400e081060340080c8022801000301000150310341c0c0c101c0c07074074880e80d07c1d10250681403803600e501003407071904001d0841e0304503140e000d02c070081d1025030034010071850310381d042c4041e174541c131941d00c480d4481e10180898041c07120b201d41d01052156003175480070051401000c506840800601c582d0400001ca030742c07100c0100208241e0380e50306400000302c1d580031200c001c030310301d0f04045411030340800030f00b0400d01c264040b814885586481e00c0d0381c0050355000503000c0314441c0301c0c1d000a58503c1c2c4d9885072004004019800941810b200e000c0310b91034208074014100503410545800210301024100d418264000c010400d080280c1d00e4a14800b604820090100190000104440e890060300304611035104032100aa80da940010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 533773093 1250 533771843 533771867
    0x31a010c0803040201050c0a0605071709030a0e01300b010c0c21080c060601020607050a022e09081206030106150305071101062d0b0708070f0f080c190201 68
    0x1403030960b01d40c1c582c13004880ca405034109444103403081c0180e900070450141c100c1c034800c2d50307a0341d540d413102c603441d82c01c5910500702a1400410b5420422200b8641e510910701d070508000103040c5103592400701600034a110034450908040320140006440292800d030155656240d000d180c100c0c10001a902c0e120040c502c03d00c902c1d00921619052039940b241180c141240094000c441e40b07840c1e1039041c691644614045a4a6005016002c0000c1186018009440d90300505500825581c04030700001c0703100090f49145460000100ea0701e1044080c41c41c000d460f48a8441c01c88152504e00840300640c01d1030000d082180710364105281030041c00c06050041310004038030f00d40411551a5041c060303403a1480291050615400c0840c0824044c1c00c10003200c2540c0791052043c000c460921841071600305c03540c0545102240108000030224038510060901907001e800010a041d44a80e181140071020980c1259038100c045540d00400c0411b021040c40545040c40c074544150b5a980020900d0307422030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 533774343 1250 533773093 533773103
    0x150601090519050603041a0f0c0a03091401050a0219020304060f030218030a031e110a0f0213050f010f0803070507090f020c010e010b09060a271103040c0501031a010c 73
    0xb00a2001030b140941c0c0c11801044081c0031075980e810701d420581400400f2807a0480045414004900c44152410070240b00d4400c410719917080600c1c0d40d104402621140700190b8203a000c204100e14402307000c0c42281c1c00346a201d080180d0302e1004600341c0503010b8000d4100c4095410a100420a9542004080c41840e400349001680c4143c083c2080d821002541d14154152040407107050400d50000c414465200d400b80c3d4494500f4141d540446052240400010301034200710380301c00018400c08003d1502910003402640200d00f081007403001c4039012103091000a03050030040060108888000e80501011409149089545d85400b50307a4000703881021032443e0740e0268040103142c6a81611400c3c210f5100038000c1100f0300c144e6501030000c80d00a581b14442c0000460135900d002c90803130080b1103000e00c444c00c00e1038010016050302c900c15100395801580322034030300c2d204447c044000c0d841540f20305d241a01c0719040000040c11100c408802800740d40c6030103415501c42e0f801103900101c0903808 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 533775593 1250 533774343 533774359
    0x9080a03081306020c01060501080c0405150a03110703021b0103060b1603030b030d0818071d040c150203030a1d0c062104080301090c02011a040b010e0a0807081506010905 75
    0x1c02e40600d40c1c0c441244010b0321661021540071024241074004c1800c031102681d07000380e107031502d0b440c00a19205601c51540d01010751604030350071103140c4002e480c0c800001c0c100081da92500504045c143da014000403001030300202c0d0706c4400e5021171494201000001c0c47d0405c0107500703000790350390944511480000d00d1034a2030b542034209442500448010240a004d6555003013201d28003400401e0281d40c081c0c40c544d141100140d41c000001051011940c40b02d07495201c000314040c002040c6100500290340c124080103020030b010b1404164409102800e0b8002c569900d080d071065403c4500d41d04950040d06809001080e4444000a00032041d01040307079000e6031483e1045030341d01001c051040b46000d004101c0204828403002e50042c60490350b80d0b2038103016814080004038201c1c1c03a4112030108640e00c1168010860506910880b50a8410b04048000012190024110642607030048442c1d5000006c00e00407140280401d05440d458080d035014142407070701c00a05801c00c5409075034020501e17 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 533776843 1250 533775593 533775601
    0x9030a08280f020406030b0316060c080d09030804050607020d090b090102150a020903160303020d140706090506060a1d07080c0409021303031e080a050a0204210203070609080a0308 79
    0x503140850110301c145640030000000c0242001001e500300d8414500424600007448045040106440c0240c080d014414460181442010340381a04131400564000000303100c0e22089804900c9402000380c000c0c2c455903181d280501d0904d160040062500d021900860b80c80d20b80c250304000200d080c0d550064400d038032982d003000107c0c6001d030302031b100310f0180f4107010a1000980075980106541c00051b42911100c1e040c80321000940206e501c03006005030b00490300d81e03418520900504088464199056181c07400ca40c9543c0d0644400510a49281d04403a00340088d502d00149408000c140703410941a07071000314130b43c1890b0107500401d10800e1200d890f000901700080c1c1022a000760002c00011510340407203080d403401c0880d1500007240440c0d14506003138024000d82c02c0007580c1580070b50724882c0320f94801d0721040c050036001c0c00e910701d070300e80034400800d2071780000381e155507942102051140081010700400d898206142e10010078401010703424080c115020a5050500341c06040484064031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 533778093 1250 533776843 533776891
    0x81b0d0c0311030a0b0a06031103070f09230406060603060f0305030f070c1a091509061b010e2e0506010c0809030c06031303030c020c010c140c1206040b09030a08 71
    0x120a500040c66511740408104980329190310200940c0d010301020700604070040b040c90f03900c400f9401003100c040c510140400413004075400880b5404210008900501c42c454040134900c502501e04441c10354803408180402585072090100606000300350072001459a1101620b81c0300d041c8009640420020380e900c28040d4030100030300240f03060035108101910003c2c1c0310105410111b005031003074000107a2007600340100d905031030074510002c080b540b6000036405600c04049641d02045030a540710380e20020000018042d9004000c1c2e0b506d1200d401440420240c039641c9038104022400038902414081640d90003444000040c0d4800d280f141e540b42d406c80024600310070f141c4015072003c000010030446200d43d141480d1107521a841c140700c80e41081400341e840f94480d4032000d0000302060041408205d00060400200c450b8031700b41c03070100050b43c0205248034240d050b81040e80d4001c4003807008015140442d9030f032204600c00903500304115500010001031011341240740c28003070b00a40103a162 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 533779343 1250 533778093 533778103
    0x5240a0506070308180304082404110603040203160b04090e0105090309061c06090f0b01080c091e030601030f1a100905070302211803072307080106081b0d0c031103 72
    0x81600d0106c1c1c0d210b9650325296943e070054208200703803e9400250b09034000a0920b40680605c0d4000c042d1a103400400041c07022079000100240d03410710410310b54004001d010150300014081c582c1141e95228146015102596910041003445a241c1005c0000d010404001e40341515000c5480a6440903803c0120941807242e10242c04440e1400400049a0391720340d0066a58010200c000c2c003600b81c05030300540b10181c04889910b0402001c114001c0c891800b0410508039402c044080c02c1c0a45500000c01c2c45e00360260800c56030100f401030311405012001c074507aa500d03200c11042c0b80491034440850024140705104442c4402e4980e0081a01e440c043c3d015203c0b40084401c10300103091010303260b406400360560301070300c03024503640c0c0f03015446101000b00d514041d000380d1100e4400000c801c0c4072103040c90b1940030090700c1c000d00c0c0000c41c0c500400e02170b0800504c1d0503401018501c1c21a0100810081c00c8000d50744508851503120000a0094410030103c036003142c80c092081803500080b034140 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 533780593 1250 533779343 533779381
    0x7080906130f3002010801060e011101060b12011509060f110d080412090308071211070906030b180c010e060d09081b0a020108040b06060d05240a0506070308 69
    0xd0100400c041a00344481e480400c1030580c541e40e40c1d5001402d0f140c034141440748158041d0000d203010340103100c441d0060130b080f08802e40600d8280540c1c07408811243c00c49515401c01255008000340c1250345982440c24180035005940e050051a03403010b001410042041c441c610500540040381c40d07040e0700945001c404c10700b0010680384001c0350104c00400c96001101c1c2114803502e19200380c032115106010502c00d40b0fa000100d940780011503120709120782010700800040225408a124207006c2c180903000080001c10703400300f4042d095140a0040c4200145040c00702518003e44160300100002e401040100a080c0221f4040151010503030500c21001001c15450800c2445020018000010401241d06080c2242005410b850494480e015404040e00242c03c1c280414082013070345402a42020303000300700601e002c082d4540c00d000e0364000c0b94450040e501503414a010000ba0428880300038801725200c6101c2030800b00060480d0003001c40c054108011240055550a0403802c82c1c010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 533781843 1250 533780593 533780609
    0x60c0203040e132f130209030a060f0e0708060f06030a0f140106050613051c0b06120109020306070f18050a06030216050703050f10090b240d03030506010f02030708090613 75
    0x18015101050251348024003403103030240514140c000d00c01ea40030300c01da800d5800c000b005040c4004042e01c40e00080e1440c50100c2c4186665600f0000c000501000000c005000d8080075100c2498401c0b40200c000301c0c0203056130700a4103e60103850014200041c51586690b00c0b0311110075032000840168018221900320f0b541024000904983d0907180341c800104543c000c45500300404074800100c101c049034140014040f4400310046075180c6401c02009d86c56004000c00007a040d80b031500040d01c3c0190540e1450082902c842c0c0d800350640c1e101030a090800b20004c40700c68910316010108404119501c9503000f0568045890005003070391100304403015030003100f16000240c80381440c5445d099410340d100350318840c1000d5042c03400581c2c082c42c20a04d400c9480d24105680350704d40da6020f62003000c43d240c01251080c00c040c1c00b680c3c0d641c2e1240c1c03045002e940c0000d00c0b4a009400940364201c01c40c58502550320522401f400211000210f5080c050143c0e5811786504131050300b10b115002c0c6800c40c40c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 533783093 1250 533781843 533781893
    0x1815080717090715110309060906070b0c0301050406050108040f1b0f17010e07060905060313020405090c040b030c030a020f0105090d031e0e1f09050319060c0203040e13 74
    0x41d00c0c0c40001c4141c1902e240c25008940520941410b481c1940c2c01503203170b0714541080c8203640a07450f000e0054268484013074107403454040c0d556100040328000701c4420002410100060006091621330040a403100b0300700034000e42001e0320340071103003044202d0051501290300d110358850060071032100010410101140107071a00e40d803030751480c440d07025090540c5600e031409507205030070001032100071110241c075800d010b1810141400160b9100820500702002a610280c0c0140ca452040d18451004100070709101c40450040000380d50048519611a0b032001e00d800995560208204440795030403283c586e8000d903501d005964078041d02810326030158130300c400309041c150821012010090b06541d140b1020002c48020343c5c046040c0e103c119041060990741030112564200b1032541c2003160300b0b05d191166a1000041c0c50b000e8a01810f0504144160700c000030080580141b0818288038000755003480e0030080c40040d04c2800501140c004001c3c0d1000c1018070031003404102000240025050b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 533784343 1250 533783093 533783101
    0x40605061209060a11040e070201020910030c0e0a050f1e10091a07030c031b05010e01140a230705070b15010806010305071b0501140a0c1815080717 65
    0x1121081c1c00302c851480c9401814001415448144200c03540f01904015503410241480010b410401000300070070709540d4200301d80015907503880ba2090b00121140c0e030100c1c0c803902d0510010700b950000c001c040e0188400840030300c9181e459040c410006502600e00724072904400003144050300e98200c8030350304210b40704042c0741c00692142c80342d003d45900340f500340040c0081d0012101c20380b2450304045d0001ea00c0b20304002c00244030b1004401840040004080390300e1164840d5400c48e000c2c01b00c4011160b560305a074502102200d46620742c4482040310400040c1203010005100c43e504044041800130740d0b000040c59140a882a5025160428003c07036091034110b0800203029034004190b0f0129081d000003960a601c03a0041d1446903040382e07902d915080041d811186004170842d0121055501c554811440d00d06217540c90340308080701c0001003802d002c0c190010340f103a400d400e003c21807070800b80410300c115144441682031081c05482c200e000d45c2d545110848503441241d5548050b0740501c001d00c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 533785593 1250 533784343 533784367
    0x2100c090f031110050a0c110d050f1e0303100317250c05030a151508100501061b2411070c09051e010315060803040602010e1203040302150604060506 66
    0xf01e0003000e41d000300310840d40d82c03070941e45405030511034400030304220007180010703150341070794409451301070800b8901146903a5064100701c0d00324815442a4054241e03110804807084042012400c1100a10718508100141400d448107900001e00065070320700c80b00001c943e0910460304884407111024207607c550200103a980380c1d414000f0707180c0340310f02c1c2400f00d01468040350f4201303825481400740000942089040b0003a021800805444800c41c2c0000510844c081c444010f4601041500041c15810444090202d0004050440081e5030210860300028101090b0f1708418080c80585120a900c2c2c0640201411481c6021064500c1c04541e02c6d00f040b00f650059001c0c3d64070074509102c05d40e00d0b003111102c0813081c0c64010314101c0ea03600c0104041030394030300d020890113284c010100d01c0b640c0712480540b0710b86c0941e020070011f0f9501d0b4401d03201024244100710802c82e06000325440c1d803c15403002035031800e590510505003440c0002103609a41c5a50003070009141c06011503446200314025 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 533786843 1250 533785593 533785613
    0x5060a050a020d0f05180301020f1b060708010320060d0608060402090a020c030702060f0c070303020f250e0a0b090a0c0e15070b04030e04090b0412080702100c090f03 73
    0x1520458250b100c0c41030164080440d041c2c0e01e5980e031410301c02510307140c1c40003140040840c7e4040d582005409040c044040041c40501e041034441c0406601388810303d403408900904440420041c000140005400e81c040c07185189443c40c1c18210f101003030800250302c0d21492540c1c0a44170b16105000800140100d0414402d0f030007100c0c000b54035514030b8095001c2e031060341a401c48542041081800515040010f80070040c0a10350b12820000c00e141e0711071810500e50000c1d40035038010700e518803181104001308a5801e20080310702900c400c0c80600e16040c180a4081e804240f0081d43c005102c0706940d030720215031000700510451480c180406000001c000782e00443d00001c08045107101207040100b0101c1443c007501c02c1d440d24000f60780c3c0740c04040e020041d204504001c40b00707e0f0b00c50301d60790702d02486040b24001da42140460406151a0242c02d107180c04201c01d10400c0c104000d1215004100d650b140780b030112020642c2011490100ca2050070344c0c1003803444042c0c92070080b00740085214 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 533788093 1250 533786843 533786857
    0xc0c1f090b0f04030917030d09111f05070f050c0a03030e1009031a060d05101a04051b0309070b04120c050d0c140d050f1005060a05090a021305060a05 66
    0x24074200586a0581c806021001100c014000c208540b03801c00c50060204030301100e00069070103407400d1186104000d021780700c8542050b85d5407810021031007040c1c5040460803c4411803548031240030b8020400161440c002e41d079028003ca0302070a0240203000c4148013008213094028642201e4648034a005080c0c02400001d460203180b00e200c01100d1140600f89100949411003125045c0c81d6a000c19044214001420030740c01020214500002480030041c040d181303491994081140c075603030030149082c0c4a505000314812800c8c801030168008048100c0c2d010b4070040c501160343c07655041c42030703071501c0100d500010f91140001400180231103d540d420518501c5281800c0040340da92041086219041d0406002c0303062a10007040304050701780c030705045400080d2508100c10350b540c8560b400c0c075125013401c401ea9002280d190075201404d200d051386c44207044942c0030b80242070101050002400400c403200b61540005d0040152284400703100007070000800703490752190360540042c220782000c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 533789343 1250 533788093 533788103
    0x60c0a0501060812040521121206090601030b090411010e1917060405100c020c040212070e03010e070603050a0906110c10060510030f09060f020705061e0c0c1f09 71
    0x204406004d590a44100c0742111801009941c48903000c1c1c200c008003204020154105110300c0991110768903649014012a0345119601e0500786810020301c075040318004e00700d034109490300c004103c1c69a1b490030801d821a400c464004140c00c0c5102c01621901031901c4426440701690030005840b020501d091000d683c06e030714406200011148540d61354607c1528002c0094001e4075584041e0300d800e6004249001d02072040741e002c01c4046010504a034801d0200c0040c0c950210704004007290011070850701590305078000c21014803400011901d4400900500c820540c880d00440d400324601d0300704014086c0c00c80c5041155040c1d50586102503400b984c0005414025100114030600b110701c81c20003201c401401c0407101054025003100140340803a9950010fa0380ca01420000c030f4400d01c603482d24520818401a41c0300301a090080c540540140201e142d452941b1203d1a000c842c540e032107422010b13154456450701e858011150400554000c0441c85000b0900034805480e00e50b0450a055402030f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 533790593 1250 533789343 533789353
    0x50c0414120a0b0907050901141009051318080d02071e1703090a0611090f09060a06030b1c0b061f2f0f0f060105090106120b060c0a05010608 62
    0x2040512038400442036031600c96400c4440b0703000110301e2080000307a208600c0380075038140d283c85a0001d04210002e8106412044121540c281c150401000c0140b9069403814172060b51494040003880703503201c84034441e41e25521259908103030100300d0000e401c069804000340340c6549443ca6500000d4100d86001d65551180300254002d20400c09207450305540c008061701c0c400b450801c0080940c3e40003130901d003541c0c840c201e20f040104d0075520810042d424146400c0d80d0341c40c0c4c014204070002c101480590f10030500302c0148400303076607542c440100311115403c002c115169042c000811069490b02c00010300380410310444100540007100920980302162008101610840d030414801400c00801e80404e820241445142c1c1d0310080410300808d5002d0248504c4000c0d20005080c150f101070f81c1425644404240140c01e8014068240940b000355070071005980b42802c01441c0c0c164001d110300001d550b84410005c3e94454008403241080e070042183c02540c19843d10a0003030500740300c0e041080c060 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 533791843 1250 533790593 533790629
    0x60306060b0910050c06072f0d1101020a09090e0c03070e06090f06030d080a0e0703050f011a030a03050702010c02060f090901050907050d02161407030b0c03041a07090306050c04 78
    0x450683d03071703e042050000c01d0166110700e01555240c02040115001c0b1020403540d1802c690350f091981a040071210103881009083e03407001d1301c00c030b14020900b005a4014001010b00c0daa000c2c4100c400c0300c1b0703e228046100c004602c0702c0c60a00349419035840d014046c140010658000b030307060282c0501c0082e14110142d6442c811f01007c500381c280c42103075140d0410383c0c500e0700301445400e8103504161042c400241005113545540d00e0150705174000c90340703a00000c450341c1451a081c82900b003628100210900f9800041e80021384a100c40600101440404908002035900c20a0074940340c90740540301c160341d401071a403041c0c0c00b1342083e502d90303100f42c04010011800741001c0190074082d800b07a403612424403501c6100000070f508403514003850f91154803401d5000c2460700d50039140503607190025080342c90450030403120043c001491401c4040c000c00a1000040e50500d03082a41c44008094031640d440b85882166081071944c400f030700705400d01c81031051610074400100f0880350220541c0b108105 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 533793093 1250 533791843 533791847
    0x120206090703150b150a0e0301110a090b0a0302041a030412030c0813060b040612030f0305060607020d051e010c0f090f05150c151b12160201060306060b0910 69
    0x2074000184500c2d00c800504103060300c51340049201100060030442110240c003203283e80c580000658500050140c2850b074003d0400b031081c0781445036488801481c2080c03c0300090492095071140d544c804400240325049d45100340e050b240508140c4124003d07542104655110075001680c0a41c0d8031402c051108190074000c2c803400d1010f0006071252421540c42c03142030030700c0014041003a14200e84450035005640c1d50351203040050001100030b90301d2007215050003000108642c4d03111003814500400d00c803950359a4000e40b81559411140881d4088443c03502a092200c0c03001d08400d10354401811b8014180190400b180c6a141603450301c20a800e400c070110340510301762040341c04079021078030305000a040a4110907420399070122954030f407602d4240594a0700c5542d004e0450301210440030302c61013071350340801c45150503107402c445030030082c00792124091080064001b0407001d00c01ea8882c0807550003034100c0320045030000700400c659a0789414401965100b0304c04580b01d960140340d440f91041c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 533794343 1250 533793093 533793103
    0x1030b0703090c050f01050705010603081e0c071a04030f1202010c050f0306040e070e0f061804030f0804020a080d05041809170a0905060414010305010602011b0c020a050303040312020609 82
    0x181d00503c084100321314080c1440500c074a00705032541000410840c80c00810b00034051517005600c01d0b4038503552a06540540c0440c0c070710149070b1b0010b01c81c040216000d00c8000090700c0c01566241265520459406910105248180d5100400c10035803601d0718402d0009000c00c40d4810301490b0004d2081504078982200c49204a00607250700c0b0a007400850700b607082541c0f116201c1c9140d4421902c0d201e40380d042105040108489203800112140100038070f40c24003608041c403c900701a039000090400e86d41c003400c0c0404e400d40c44000c00515200040556a8040c01030000341a09010303181c2840081d42c00070f026920601407420340c0030036107030004124400391259140060b00400d00d1002c503103a001c0441c21341d500c80742c291001c10461440c00314003507444400074002004055070606a0801640014054802c140d01030019a403421000c00510740d5260400b030402c140c145070240b60000544001a417420864004507003520000c07901000f0803100c03030494400c48129800312500303035a03825216a070320 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 533795593 1250 533794343 533794361
    0xa06050d11030a1e14150f0a0902090115080609040c030305130513020c060f1b0706140703050f0c0406021b030c0d061a04020403080f03190204080601030b0703 70
    0x11800c0c206001141518000240405008080c1c40301400140c45100b80d0450048802140302c1040c195002009030031400102d00224030000307409007544038052190254001030501c40c00001700c8000820106059200c010402d6005040c480c0b9561217407058418000c0d550b00c45e4001c01c01500124086103020148180b0466211840c41c0a01e8156078040f507161704021a8002618500c1c1800f251130b81c0c9821a000c030f100014800161990201c400071440c042c00a015402642650024040112081c1d140c131000f11008040c1c46030384914601d0510700034400074042002c01038580040c40500340d0705403c01d5001d01d0030b41c65056410303280d607010546944103d1140c000940d001c1400260b05490040c000000d9040090540b0b440d80030030004900d10030440602164425030b01d20301e912045079560b92108082d881500d08509080c219900d000013031041b05807a410b00d11021001581c40b0340168003450200d06090010342d00c0300d617203e06441c0c0e40c0b4001e0208075001d070802c0e8001480d07644203104100c44 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 533796843 1250 533795593 533795599
    0x605031e0c0904060b040e04020d2612011d040204020a050705150a0606111504030c021f0206070c11040504111c060609051303030b01140c0303011a040b1c020d0f140a0605 75
    0x1039100c60b0308212100404034ac040b90b00d542c3c203014418142c0b6141500c10f07001d480f8101e255545940000c03089407140c40c142c00038542450b44100d030f10044001d4403100d5501c40d5058400595a0f01d0b01e5109841600a001004000784211410070280b00441203a06008817102e15043c4902ca4a40c8025104007042654120940e80881c20000d03260b41c0000e901ca03005070003405c3c0356812002e15000304610800303410f01241c8010030f10f01111095941081401e50000c05442d0281c0414103560318140103400a40c40355100ea40c4400114040c00307002c0300900307103d20008019454950340e40719811006030302a5402d0300c0103841c0680010342c103100c6000c1d07544038800c2c0c07001c04415110140c0d802d40c0241591441d4504104883c00580382408500000b4015441203400450f100d40c545140034444000c4101c1801600609000c1081a06445015501c18660f014801000d022005c3d0141000b8003071113a00141c03081c20800d01e4030080f07440c0d9120343c0f03142c00701012000c9203688010908080d1001c1e4482c0c260 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 533798093 1250 533796843 533796869
    0x1021b0106170d140f1303050c030706020106080d110f06070f0e0a060c140a0b0c0c0105090c061c0e0a0803070e0415060c0f080d060f1703040605031e0c0904060b04 72
    0x581d045004c0014165a85a982e00e20300344404040009148070301d58204941551006441c0c424034a01040303210000d0a1610081c080d0504100d03c0e81d0310743d1014200d4206011041000c2e00c03800d48103114480321840d50b1022a1540e1510000041811080348068000704048056807609030614000140681d407a94903646840c41060b50f861080142c0c508a0751403c1c0141c640040019182d034039500d000d00c0c4400181c44c1c40303c4200c031320711303086400240030300c0a03640c8030140c8070303070b070b54440c43c054550100310740d54005007041c0822141c101038100400c40342070360b0040044100410403010041c6010b100b10365500c54640b950b07201400221852049001980da503400e01c10087e06100b071100101075841203002140c0e059590b41e0318000d50300310195003080c5d252038400c00c0c003070324800e882200000d02d5140c0807004071000001074a80c50381b045010313103420000000300040f60b090b04080c1c00c82c1c00c800150346800007850b0401c0f020500360031140600f0f00c900d04000000415410101c299000da805140c9405 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 533799343 1250 533798093 533798117
    0x3032a09080c0603012102030a1b09090209150a080d090e0a0c020a080a05070b04061b020303040308040b0c19270305030d050a06050d03020607020c011b1401021b0106170d 75
    0x890040f1802c60b1506c090302014003031005131404d001480300706224403083e024100082004c1800b52000380c00520803585401c0b12407000d66520340c25241c010500d120540000c403d050045500300c20283c20003602c81c810014038038102940006d83c2012183c4003000100301e0380300c1740c060109881c0d202e100304005a0001d400d0a010542d194010421040725003030a524001c0726503281d560100c02120203481581d030718000320002d4442031181428841151010f58603500d010b50300a040c10101400190015201d5400104640302070341c01c40b03100044060141d8940c48012800030140441500c4d011444c0664400f90032810440d030201c8815070360310801a50402064640c1d501c02800000c06e02b4607041e84640d40040c2030341328541e801c582140654040c1005250040004c3d1900c841c50f005a070410800c883e02d04514090a2848130042d54419400d10703881c10b070000e000740640107605601c000c05055482215000c04154800707001c641a0402d41014040328248140e00e54180300007103004100d24040344 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 533800593 1250 533799343 533799359
    0x120109090503031b0d09140114070527060d020d0c140d15030c230a0b0f0a11030301060e010806030a11010c06090803010b09040b090c090d03032a09080c060301 70
    0x1141421016130f050705008a00c50f00c40150f4946001c01d64200c40c002510581080c006e001c2c80c48850341f084c109005030709055000038003030700c100c032002d403c054116940480c60b952440c2440c0c001c820300509886c0c0b1000700010481c000e601818a00c64541e1a12002c103800e140107401c48100555117040c81810308102c1d07400d0f04082c103002018844032500b888400320016410b0f180c100040c02101d2240040d80c1c180d010f9852000c03202c20384080c0b08036843d0034100641c00c5004216402c010490310100d481700c50103d400d0303940c0300b01e1f44051700b0140004400864120b038040040381e1028070907078448030b59460f200141138588004450103000564060541100d6501078040030305018444d410010320381410381c4030b04130b81d904203802c00321202d0740010720381800d0b180a00517448401c00840d03000203141041c0c1d080109500c40d09086500580b0b8046610342854001e80c0310304401c807400030411102403441d01c200315245420380c1210340881c1c07000c1000f1070340000c0014000e1a0a0300a081c07140b8503400c040c2a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 533801843 1250 533800593 533800621
    0xa09050a0303030e1c350406060609090908040504020702042009012003030417071202010b01030b18040312060e04060606020d11210403050d08010f150503010512070e0c12010909050303 81
    0x8004d8010381407003642d00a400606d01c000d03100b0303401600e001034103d00b8004000c1900e03c640d0b205a154a0404400301301180341030040718101c89044070010b0b0b880100d40b002c80c0203440308240a10741c04002514080300d28401200030300401609981e484624880b800d000c505028111400511961051000400040324441e6481941468000c864140680c60f0b5503403490f4a0100400c0d070060351156407400130380d41c05010307040c440e420417140c03050103511012035a14603403001880a0104820f000c188170b0540051ba0106000c2e292246c14100186010300f001c0c40604058402c10340140329205d21003506034402c5410000f1041c0d83c001806050301d1203800910000d0440e4070381410150b0400c000000140d0030004180c101d099610754014641c94498a0b281052141c2c0c015802d03003071484000f80345254070808503410354100701c680301060902406528645913154200700d03909880241813211508910001d029607a0b84440380308903d030b032682c14007009c0d9a0541c0004100c3e600030f001090781303111104c2e0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 533803093 1250 533801843 533801897
    0x60506060f07141203070903030e010804051515041a0f09010b0301140f100201090b0106140a05030c0f0403050703300e03100c050c150c0f0a09050a0303030e1c 70
    0x1c1158205130103c0d0328095641d10545001010441c0b02c8010010581c103e2403582c403500302401c00e6003092500d0340b500354a481102220700c1b400d090a400207079428054401c15108104007800c00c01c6110010101d0000380588544664400c1034035808500c114130f00780301c1c030764182c1b01070100a81c203691a00381c195040341080c1c404940e1206000088214a4540d0309411883c0c03850b0b40d0001c54441c1c03482c2841c0503000010382114080008100c080038401c00181d040340d0011805107040e50ba030307a0301c0050001250096280e280d808400018001051000009181c01a40e000304005030848203030307440320343c110f103102941803035007002c04148030885502600451404600140584443d00d1905100d101250b6460107043c020401c0442d03996500001081825818009891180c941c0d003080801030344540030b500142c103000480000e0104400b841900120002c00d00680001c24507030b12894040c0240085e86030008170743c420410880908118112440b0302c0410030b80359400310702858178500c2100d400f0b0381 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 533804343 1250 533803093 533803133
    0x2120307092102040c03091e0206070203070b09150a08070c03110609031908012907050601090b10020a020f01030f150b0703090e09030f0d0e0f0109060506060f07 71
    0x79500061004204032901160070715000c00b04541c407100d104020407a07070726003265410185403031684e10000c4e0403441c0c0000c0b101c1d072007040c1e0b03681a8600c3c800224a0b01c20303581c1c001e400d8081c001c0c00283c003c0c0c0e06005400342c42002c40b8441c803142d141145404c0c2c180904044980001c2c105c0012070901409000914150341c003e02d000a000350940d05018030705001036440d400b2540c00010010342240c018403000e51107031940d2810000552400529817503070381095042c480c0501604211003e40c0461104030f0309031980c4038050316600e41c0d440e03020308020400703c4c00d118001e096030411600014400301d60f0491060380209000e40003038000c00110010f00d02160201c4240d60340c2c030a03100000886023688001800c221f09031030364904107407400824040c0c1e29800360419a800034144403043c0404800e807850303810440200c80d201d40a000742d55004e0555002421601e0181d40e610404041040d0005130791280a40410f1103030f070711a841442650300c1543d1310082100c605010350300c0000c400b0007210000060701 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 533805593 1250 533804343 533804357
    0xf0203071b080d02070515160803090c0a08060106090509160305071218020f0913080a0203040509010311031213060c0c0e0f0a110a0c020103050703060f0b2802120307 73
    0x4003400d614200d00003450f0005a03009400401244c50401110300e4010345a60034682041e00c2d407c030910390000c0b01000104410004000250707145401c1000810105008021802c0d0b10b603540b085076220030080c0100b800160010f1408503c0d03080a0b07000c203014085000b8401316516502600310300500c0094030340010805001c00b49400342c5400d000d0500040000e04030000c0d4141d26204101120b40a001254013610108041202019040d0010960681c1214410f582c603410f43c01d040741107101e150030003503100580303c00110034031110140d1500d116030309408580e03811000b28800b80150241c28103030a4040000c40080c04150310490242581501c604507141c2c01d1511600980c50b042001c444081d14081110f0802422200a0051554002443c80c02c01d1070a04003800050820400c00310280c1495143d201003440c403403290b40540000c0000b21030880110b0f03104c40c0194907640c043c000c12039000071800204000300003594001320548010703030014170009480c910300084940000703041c41c02780105 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 533806843 1250 533805593 533805599
    0x415050411040e15180304060c060f020a0809060f04020a1a251203020720030a0f1514090304030b09120a09050112050601120e010f02180109060f0203071b 68
    0x110f020701d07411000c40c500902035071190704c004a0320720803004240300d003c689642000c1c00707445030100465094031104c0c5822100c450f042d08041000c4d140b142c1001c00030300d10005803112500d038804061402550b84100351001c2ea210380815864414054a000c1c0d4801282a0100940b0b40c0043c041c0e85442034061070b80342068074091021420482040d681103518080c54125020883d02d840e03519441e2915040444c02c08580b502c84503501a8001580324280700141c0d104600c90760308000300114a0341c400045441da801d03d01d011250f2014142c0903411590601c98100c500841d80340380544114070724170045040074555141c01d403030304602a0801120b400344120740041704400301c009110000d2680c840c050108d140a000420b10b250141519080d1444e100612840e83e92203100380c1040500d100740441d036041002155801000000321009105100050300314000c0840460729070a140262101651241d43d0030090b1a0525005895001604200150800200c41030b44600410850715054440b0304d0f1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 533808093 1250 533806843 533806849
    0x9070521010801050603190b010b0904140403032405180c09030f070618080309011d040911040f02040501480c0503070f0b0706090b1f0501080415050411 67
    0x281c01c10585651220f040019a041c07c00400e0b0a1540d2607031240d0600700191250346800364103001c2c110500b080080d00e189503560756048490f41c641c29030070210749801c2619003d40204200728101c0d03082c1d8605c0e2101d0030340c50045480071003210350141404540c41501002d45c00860401055a54521028040001c5548003000101c030550200c00080c03003000e0920030090300c110140080b00e100c4e849031070818400b60300c0c04025514688c00038200400303c00c408000c54074116800d115a00d800610f4800c0b541d00380200e060506c00d400a058404001184208500c00700f43c0c0310b14010580411944000b200c0000c15004441c504400502c2a00389000111040282c486141100588510001900e65003c0c4028811106c0040604400404181340b8141003040120114490078184030300108051040c00700c1504800c1103181d0102055041c3d2078600028092900d01c010a0092000b40c41d10200e0154010802076001300d0b00507401185c0442502412300292400030310850718030b0b00d414640e00c0780d91 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 533809343 1250 533808093 533808157
    0x321130308042c151210020f070201030e160b2b0f180308061203040f1205060c2115030a140111041802090307030c0f0f14090705 57
    0x1480d648490f1188212641c40c0303115440000c2c00d110501060010300c162180a0603420040c250269003011125183c034a00f00e0410a410b030040c0d0100303000007100200d100e0104003c0c05d00328802d0b2002c11100c04421071541d60b5000062106001000b04a130a00220700c074000a02284034002e00c061124805c00d2005031540b007080303040c81e440345464074180807450b90030b4003601c00b4040d0305d0020054060410707100104560405040300303000b0100600005080c410500c00c8801401d40315054040b441d94401003098401075038074040d5402c2c0200c4010505446140d81120320140f885d2444081c045140f000c1180e0700d07180035014841e0180d1030000410551424880364401d0740c01402c01c00060342000c60018251410b048001114442c2000107204124a159440359091074100c1d00507128180389020920344011600060310311035007400009071201840386c404040d01c520110880c803c65481d81c40b00320210b44010740c1a07001341200001000144150090304200c001280440d81c2036003070302e000c400c0d00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 533810593 1250 533809343 533809349
    0x9020708040e091221010506030417030c0730050c06041b0e07030e0105090307080d09020102071e060e011409010c060b040e150c0306010203040608100e0708070806032113030804 78
    0x1702d0821402090090000003681d004000c20355060b459440c0655503400459100c0e4840a120070020000c80c0440d08000191641c469220790303104d290407282041d544a89140030104454191203c1100c48145d00c0703541556103001c207031001850b094407640d8a400c0400c0602102c90a540c241d86000580c407866594403a00a50050300e0008131480001c01c0e183c25194002e040d910355a104210072000a030030f90003100c501403110a0001861181440100e003030070304550004980c003207041c560900b41084611000200d44c5a40c454070b0a0f892000c005545140041c01d80428800e401e104071030a81d4041d2004803074080c840c580000b01081c0703850005040740c0559181c105154410f4141c04a030024a026040d0007007204100b00b401d41ca4602c000075540e03c650b008000c1000103010100d02c0c10514445140f000c0c20001c00032642074070340030300002c00d803820494421002591110116525041c0403400440e40004580d6900b1403001c0c1e41c2512113680e01205008000c4948904000080399141c1d0140000e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 533811843 1250 533810593 533810617
    0x81612030b0f1005040302040b030f0d052d0904051b030106171f05060a030e060c0307031802060301060f1404060e1e090609070c060c0e010909020708040e0912 70
    0x318400301c505001c240821a20700c60b000b0010f4103502c1e04407075048415101101e60460340450207401c100c012a042001d04c0100040c180f0502106100c103941110282c04082d42c00e00300a84085440da440d80b10307259641142550010081254000324182a04040d50013400c2c055000c0c02c50070782000901c46039209074000000108440814003e80b5154490b560308005600c0e100f40e408003a040c4055225605841554820300c0c0001b409081300b0b029030015030b00c0f012000c007038682c2460003000701c814030380c02160030300300007458040060440c4ca403065505803800d4004d041141543e01f010401d1300d1400400d01c009003030100543c040d000140d0068024006040303e0f0b40c4052240010006200301030000b6032540d01f910004038003030103040d01ca2150700341e48008210b6440365192620b50741518140f81900d406032032141801c1d400149107800c181e103107503a45020390b224550280e54003c414124003a080f0002c003585c0e0200070801a8003041c0314601d400041c8182541c1c030344c0181714a440c0f080e5110043d6248 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 533812949 1106 533811843 533811851
    0xb03060a090c1202030c0711032a030705030601030c08070510020a0b130819021b0a03060c0908030c0d08070504060512190c02030306090702010903090308161203 71
    0x1003054880102156031b410507440c440442d41c442e05e4151441c1d6110f040448440c00d0010384180542d21000402942c8404000c0368004401d04078000e6038544580e41000ca80d681c4c0c2446807070300035845280c41200701b500e4061b01d6400c01d0403c0d4002440740302148800200681c011800320380040e4004080d41e4560345910110f02801040b80340913000e40ca010584020586404104040500b036030380849010291465280455801c01d440140e000141580100b001403034517005800718507260b05107a1034094898040510f0b40e040a0b44032403213030340048842903183d81c00100198020006103040e9292900b03005000d0a244504904124541d02000000300d20198480d00c1d041d01200140e404d101018130031078006c0d601e030001d4942034416200a004184418014468140d166a26071038164483d0329580b54402d00350042e14001c034040d007035021300e1000130b101100c541850f900703243c400003 = true := by decide +kernel

theorem cover : BRFrame.Cov 533633093 533812949 := by
  have h0 := BRFrame.cov_init 533633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 533633093 ≤ n) (h2 : n < 533812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
