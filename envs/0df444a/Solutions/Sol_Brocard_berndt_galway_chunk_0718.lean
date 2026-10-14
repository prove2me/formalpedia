-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0718
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:19:32.037028+00:00
-- url     : https://prove2.me/submissions/747240a6-0d72-4031-9ca2-d1dfe3f97450

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 128956834 ≤ n < 129136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 128958084 1250 128956834 128956853
    0x1103060f100f03030c060e010b10030204080d030203041a04021f0503060405090a05120a030b0402071101090b03090304060c141b0a0501141806070206030a050121050d0807020f0a 78
    0x81a01228100580214030342e000790704150300301c9405549100007a829a200d85c0003d05501c0c04201a41d0350b0b40c1541d03c503a817207a12034803e00b0803e6840050300c542c5000c0109050042d224260130801d0710402c20000010f04104103150302c0600788416060035541c0b44003045c003920301100c0c2000e89041d010003a039440380d0300c40003e5110742030503074082c811612110030095440c14000c00040071508481c03440d460b29403568001e452403441c4d0780b8000c00d5800b102c4020a0403603205880c2600d00044481c218809035800544820041c59408040740c55403a103d0000c6440780110b015203800c01c00350307480420601c8001100c03810100707021003d41d10310340c1450b40881c2c205505c4a0550380501f8000c0c00004e0343d90f01031004030011a0300042500c0c60706680c1c22200c10300c880512092540604103010800140e15504091881501b240781e00080d9541080d41d0b40700c2046200c81e240b10345001410403180000c2c400b00b08981410130b40e040c02c070302c20385400c0c030140c1c108588170700010940e11903011007100388454080d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 128959334 1250 128958084 128958091
    0x1206020721020606010e0a0f08030301030b010e06010c030c0501020405060c030c0d0f050405010c021915080a06140f011e02010b010e030106030215030a0603051f0b03010605100c1103060f 82
    0x1194030080740e0312400300308031461540c40001d60420400651654007860850b08141c600800d5405066110002c80303240d505640c200c3c00c0d45038000b02c018010040420b002038090043d190f5501410b2402400003024242d039a2401020400940070b070000b0400d094041d034011b403000820094540d611003510b10782daa0015006205140320302030864410f036006041640950410340d03200d600e041d081000640745284288030480e000103038115803600a0103664002c202828550303080f03020f8503401c400d0003880f50174050000c5080500d403110800212000c40000c1c1850002a01c031107291041010041e50840410f1581c82040b00c4940180b0f06142d506600a1041c0c032003d03240c2881c0c4280b9002130500301d03851307400000d400800c131b0050706e00e42c101040e001d50390050120402240c8161280d5826040440d154070a101800e055220403040a00f14000c841031030100b50001c202c59403070f240020315000682c984110500890380001c1041c06040c0f4500c4415000103811201c0c40d08005645003100030003103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 128960584 1250 128959334 128959343
    0xf0c0129040c03060f14030c0402070303090201140903070614070f12140702060301051c0507030302070e0603060405150711070f091404030f08060609120a0c08010b0603011e12060207 80
    0x82c20050300c0e01911030b50080e00d1200040103140c07400d240700140100d0181c1c90090b4588103203030040d01c1c02c0c0d6480c001800164441d580125840070148000362803036109800038901c00d1400e200e1551291400151601100d181d4905168905414551504144070301c4c803015209064581c88402804809030018003c08066541c040c3c6040940884807010301030024001c0d40000c080004003c00d01c7d09201d0003480418884801420b4090b5079a0645861441d038070072809a048441d08100070380361071502c10380c008415405000285403a65600c0c2d103441c0c690001c5c1b014950480040345040d44501d555822064071b407800c980c10f882d1241c0d500c959441d0240701d0082d0282c1050701122800382c446400c41d00803a41901c4807004654804000d5401c1c0c2c40041c10903401102c01d100c2c039400c9942e5419102100540f80001e000f20100b1030400290b80b03045600034445582c1007004112440e11050308a0341142d51f250102c084c1209680704003648480c0c5648500150f5912a40d0101409283e90041818078880d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 128961834 1250 128960584 128960591
    0x60304050f0d02071a070201030b0603090106060905040903050304171c0501090501050402040303081504021611040f0203010f0b09150c070602010c020606010923060408010c11060c0f0c012904 84
    0xe00001c82c0e407115640034030314240055503441900c3e17522600184c1001481414042144c00e0f0002c00b0890542044a00400e030b80e455080400c951900008080040c0c46d0942e4180044a4140c0b0050315501c400303040100054000790000342d03c65142000e56003180c2140b51800028218a40c1d0840980000e0081201091a14000150a24082c403c0741c0480c0c1d85516505100e603501c0b120460b031424440d80c800d400c00e8017041541c034400b0340c0560707016a8a106207a04a000716000d001d000c00c030741600c0c0006203c01d10400040c000804070350000d5080350303034070b840d402e68071070f03a050100f240e0f10300c00d0407046040700c40030075031489000303001c03400d801034071000d50080141402c0b02004a1762158192400c0c1d011664103a0f0500c0195010700d101c0d241f00d0440a0038901186000c000704e101d9502640c0300840d00e955403078981146c59880b803090600e4450310300041850303040448000ca0140b291144841e00d44c8000a03006103401380a4101107100b4143e00c0048080c90031844009000c44006000b00380308614 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 128963084 1250 128961834 128961853
    0x702010201060b0c2104030f0605150a0308030a020906070605040605091c090b0304141c11060103050c0909071a19030203090a020411070209010f091107151505060304050f 75
    0x20084103440704041c041d00107201c01050300100c2101c10214802580051740100000300100b00d03400c004044941c45580c0c00907031072402c1035003203500162540c2907501c12240108100f000c101034a040e00c0d040f8144031001a6604405000220640305a8100826640c208003c101c144444d540c031252156228000751018000403184e14140042c00a25103c00300303669050030b000014242c005103500c244a01e402c480c0000b490b41205252249003400f01014102d504150101241c3c070084180c10081c410380207180950540ea80c06845545508019024906050015118910803c003040007000043c60b50141c180010480c60130720790050040820280402c4031300100a807103071003100c6c0b050900002804080700d1035400c02c0050440a052203440410902c220f80141c1e03280700340280203201001200d200c451a000c20030065800e10014243c01000603c20b4102013040641c16228030350300b5400001d8040218003004c0d103621050b42199804c890040100000c03c1070000e020006503042d10202e07241d024 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 128964334 1250 128963084 128963099
    0x18050106050a05150d05100915050a140a030602070201050f07080405030d09061704020415060c0203070b07030912080f0c011406120a0201361809020901030209040c0317070201020106 80
    0x2011504040c9120f00030007003048030540c9940500d8000c44418281c25140c0c0d60390030250242c809c14201141c105450340001c00007440c1c0b174075809004082051141d80510788880000700300c44940c0c40040d02e01500011100c045a10900c200e55003082c4192000e9104d43e02810801071070381250007081c0c080d104100c058401e45004065888c100c0706981d13503107402c640281c20403054514014104982140e1641852246103c00c041c1500241c050303a9a103203100740c002c2c0101440c14900358800c10303003414200901c202180d840b0325610155000c1d83c0e5100f00c6140580b82c0280c0c50b1042849184a00700042004080904190454000500010b044000e181c403640104000b4115002103201186d20000903400154094206003400c070300d49200c1d01400110400a0103601d0454100030b4130751102410045c849201204078403203003070b01114070820014011781c1c0400c0c00900c0600000c0d103d0404000001d0811441000c5500a554001e01070f200500a0500c102169041440c040f405542420380114245 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 128965584 1250 128964334 128964349
    0xf0d0201140c0307050a031b020a020906041109011805030601030602070209060f060904150503010e060106021b060a030f0207020d230609030a2303010b04301101020118050106050a05 80
    0x10506800003501c1c40c3c031036500c10b17100c81e800000810249501d030f5289030a500241d000c001c11140050300504004100c920401250b000c0080c070f030741d100b10314200300f0031103001c41a0151400c006085c01c02480f19503540344000e01c1e0b052168842c40e41407003100004802c101440e0050a151403007039908a1031522076808006c042015909001e03085982844491003a103415044444a1840c2007000000180c0b01d00120342502c1c200c0001082030b81c00b03076004110403941042400318030f0950b010810f82c006040d41c002071961046107c003200305525a0700e2415100420b6044403a0f55030300034041504c18a40d481d007420048622801c82e286d0044c010032108000e0300225070103201e00741c0e1101039454190041800d85000191004075034425207406070020a00100f41d00950203080500c417495140c52500000140194100040d4107250301142445648024054a60f10700c041c2e002c450283d032002500d004034010054000c03c01c401c40c100c5441c2d030050040643c0410180c41041d181d07010560f45410511545 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 128966834 1250 128965584 128965591
    0x30b030a020906150714010903080c040311090c041e230612090a050a030302070507050f01020c12010e010908120109061215110c0c0a0512030d0218030f0d020114 71
    0x80200740780010110301d400d149051030220164690b81c10004692902903c07401d01d485000d606e40e40d115012818140c001c0c418607804084c02d0b006500e42420340ea030b0002881c4a1b0300321103005048540214001d2400c82080e940600020840303c680710044049c2c1c2a50084a442191142020411507200044000c161511341c04070242039149440c10b148801c0016000082282640d401542d80d040b0020f0000e1052000c454020b96001da121031681c10a10304194103170b400680303d00c616039038040883c0d80109250807400000c445400e0108502e086a601601100754050680d510b800c60500400403841d01921104844c06090001603807101c0c14241114014010403090a042c02038040c0003580c040004880201400c0b80030407008000d654880311034015800045d0590069800020f00741841b400302e40041030100c50008242c45001349668692003107070f110308000da40020300340c0ea46100030600008500405012904100d0004a00d1512140142c0b9200015401c203022a1001250100424007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 128968084 1250 128966834 128966839
    0x405012a0e0a0f14030708150703060b0a0801090f0902040606050d0f060501050f180907050405030c0d031b05011e05100905060609060a2003030610110a1101200d030b030a02 76
    0x5089050a2400840400c0d45013110307818440c05401041d906020300188500b0300d1054100c2c00c3c43d04100f540601030f40c0c816048154103100c1405080009940088280d04640a0400018038400140680e0000e4200311101a4001341004400200140d100008001850390414104140c2028095540503280705105941c0060400d100109104240c4001442c685020203029080f1000c06030100b0070030101110302501241000c64104a6070074280110044c1010854800550760016034004c1d11640b2005520420103100c141c050007080030175070005800e68828004d00c100c60f0200c0031b541002e0700085031081014103001100140c001a580251801003074000d0900d814080200c0900507103400100d0200200000d194005000c1060660420440110b20014583d240344c10000c1c0030211803003040504c20429441070f00075a445000c82c1c42159039034042e088640c1004100e004070b680c00402802c0041002c5a495a080c240034002200068018245c40900400e60703060205030300c480c11030b003000c0d4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 128969334 1250 128968084 128968109
    0xa030c032a1812020f0607030906080c04050306040b06030d0c1a04030905060309011a01020a020114070311060a0507020c0108063a03030e0105010b040f0b030405012a0e0a 75
    0x50403498150501c007803960503180c110000c0da0a01e91075803640d842d940c801000a0302070b04080d401d50800403000c0c0c0540b182642c6451801e0480d90300200f1400252040d90200f04140b000301c1e000c03c0340b43c0121001010018200c074400e0525040280400005481c100e0ac2032065446450300140900c440ac40d006800241031007995548040407014800010310440c200b21030791341701045981c0c918010b54000c44a03000001110088007408604414584d05072134195446a54400010f03a1320405a408503201c0c01c8003076840364070b40e06e42505c0c01d1910030401203040c00340303000300a0040344541c00107103c2d50b095421108a000c991006440004041d109d0035003040c0c2c444400e0100c0004c241840d040d8412010711090410700300309488480c10303001c600480000b92142503061000809000301c9001d4000c2c01344051506147c0400c000c0340085a11030b4500981000c4000f80500800394001016007004050010001c0014030341c070389004c0070034403004000ca005403500b0222801c1580503902960860400031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 128970584 1250 128969334 128969381
    0xe0a0804060e01020703020d030c0308070201150b070c0b03130c2102040b0d0c06030204180c17041a010e0402040c0309050309010e130608030c1c050f090103180302030a030c03 77
    0x403560302400105076815489800e100000507228648c0152425000b940d9218021100e4500140010000341c4207404584c10001c800400c203507404180003c880c00668440d0b590032003440c10b0700c0e1503501940a10744100d800701c1004009a00100c41c0c040451003412807054aa4481d000565002c4088601c0501e411120f040e0500600303140e8042940300c4002400c0424440c42a07984000004c0690850f80c0042c0c0c01040c208440f038a0b10301040b0014200035801c2c0005030099500618104004110707400391840303c3c011038240180c902a9080c44607415101000c0e640e1545440c000c0100c054500302d00842c0fa0800e01c0040d11722034801c2b01201c81d0f21001442c82e15001c0e10046416802034090150300ca40050340038084c81c23a0500c1058018002d0703201075504c48880024150810490321400031806044610f181441c0e540001200d100d00e08084560341c8522004004900410850003008844004452100309254001004d007116081640d8140500202e03028110305441c20b00081001e800105203a1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 128971834 1250 128970584 128970587
    0xc03030804020d02090c0d06060806100f0512011202010905090f150a120b06040506060f0d15081b03160315020d0b090f07091a030f06031905060a0e0a080406 69
    0x3580d00309000600414004200d9000116001e005407440c601c40c250000c0c19854207130050141100420442c10b09549601d010400301d83d82007078074104001004221320b41400d2050140054446100304094248050740e16948141c1e45004609000c0c0d0103e200341d440020586860381455100c2c0e15400064885500c4010340c1d900d45051100605521081030400411200f241c040c2045589008418031005414503600740070803504c020b003449020b000e08200d20b881c43e40c4608202c0d50000d002c0800014640d00303e020600070700e000f640164406014030149140e00080300380c03511071050400c906891058110000d10300b0003417800d2000504030035a10780000200c00309640078019040318001c003c0341881c4100000f4180030707411a444d4000042401c240069198040f5900c0b001c0c0c1480714800700501c039001d0070304000c2e0000401000780303072a0000001d8800d40342804030042403849251078020255880c9401031b10f601c022558118074515191801d15035143c00924925002d030015542d91415052060 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 128973084 1250 128971834 128971847
    0x12090718110a0e0f04090312230c0304020d08030103030c1103030a0e090a0209090f01061103270f1e010e040b1f050708040f030302060a2a02010e0d080603190c0303 72
    0x100154886a10f01000313110703848602940e050709121342d81c1e01c41c10141c581160b800f01c036840100c0010032103040d450781001e450749a001941220004070300710385035520f038800909503c084681c003d0007240080300000405810490104040d44609401070b440040d8006244d41c901402000c0c1c00003a0803904040254100301c400b454104c010242c0251030401002c001c507801c100e06860004c040070680700104400c07030340b0000035070816400394043d42c6809900c140f001e5240c40c0054200301c1440d000c05102c00d99a072011038208a103100a8004030001100508003810b015955a4041c042900d00e071010402e4600382c410301c0c800c4007000300400f001d15032200c20780806c40c501040c2201400000c018a002040d188800341c002440c07600c815985180c11071800a0528002500018845042000c1e0500c0207030303651603000041d1580040e15107000402c045c12405010b81041c0d103203040c06180420700b00d00b0b81c0440100e04ca0b290590858070440c030340070b07100103a03040c581d10042c00e209103100050002078030442 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 128974334 1250 128973084 128973107
    0xb09010b07080906040f15080f0105210a0303050610020708030f03130f0501020405010e011d0103181a041e030e04020717130e010b0a021b03010212090718110a 70
    0x3030ba40c103210340b06010500d0740d445500405100035200c102000310368403209001044610034503124504d801d01c90500c2400702418060148902010381001d910801c510340306201015000044a18040b55418094024403055521902070400c23402c544841900000f00c890031640c50720000c52402c0702020b0850543d0304094008854055035190707100104004c0c0c0514103846010343c000594551400b4005401101d5441c1d45c14140507031014207030b001082d19404114000c13002e0801246071051018400090b160a100003407070304079070001761502804403640d01071007140b20f08500600c41208980c000208000000d0090000b0380c034803003d0a90b41415000780000074850ba0319801801d080e07460408041d00500756201d03000d500c40b401004490003202c01507004100d020366281c50700c0c1c0104402034685801420114003041d003179440040a0310300b581160600810342c611400c3c02d04108103804d490354454840c41c5240000c0c04000d18480da03280c480c0c070311107408040240c1d103040c080c0340082d134514a400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 128975584 1250 128974334 128974343
    0x30a05100302150c060a11071b050d1406010e10030323070b06010f030218150f191206051c0c0f080d110601060905060c0102250311010b09010b07 64
    0x404000016183d07082c001c00d0982c11529070342c1d1501c141100451400800034485880281480d801f02103811404080321016030b040118010130744540c0c1c4501c5a944055404250022105105803091042041c40c110800d03054909869031644d80e540040c5282c0340030b0f21181e4035024080c1c41000001c4c01a083c0813427009100b01d00101006102065900581001ca41600d03045203036030401c4030030740c0e01c800494100b002074101141803500440d0640390120042c00c6050040600c1c0e0081500820000180c4403860803010409640700b213088280d0013050201d01090300441c000380d410107043c0c8014000c400a6540c0944141441000c01e4501c410301e0041000965200311201008039201c40120084405894000c00070940340406807801803400f00c507007a603082d00b50020001031100a82c04417941c0c1c121402150703425219502c0c0d4140c50b00a204440070100d4005411000741c112440780071141000d00d02a46804d160289588015400e0b00d20f00900e0310307403101c2c504e03005112520200000d05103c9009 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 128976834 1250 128975584 128975611
    0x100b0f1e060304030503091504030807050c01060b0a030209010215150621040b07230909090f0d02150610020616020102043503120402010f03020d0527070308030a05 72
    0x300c0d022034003651003520140c00048000040051030740040040107001d20051107117041b5807800e071b100100000000f62005003002800a04680701020940140026283e100c0c0e01540d24040040094000d44c0102e0a00c0e015000c0c190301a2103030b03071081d12520322030641010070916402070303602000a15400549188041092400c031404800781010b10b841c8100e224044480e80e9040880b03020300380c080b51292040c2862841d4400c500718506410941d01050016074007403015440d83c0d81c80d0b81c01c0c084080b13580100340c801c20000d01d11660380002c500d00c0315079280f801900a9215101880300000221070941c0c00360780142c000c9810405c0440040c00c00700414400103040a0301e0303c0131014013040b00d41d41e0f0440c040f880241c9404140e188101c501c0c00380c070010300070361400c55003d20861526600030720107030510018441c200200c1b406501155071501620404000c00c0c9816400c0c8c140c100c690007268400325002e261382c20360320f90b800964030041d00d8112648a00b541d9030012020040c020081510454002 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 128978084 1250 128976834 128976889
    0x110703030c1e050a0611090607140703020d0c0f050619080c0409060801020c060609010503060c03060303040306060602010915020c0307021338010804121206170708100b0f 75
    0x10090030008082d4440d0010342503d0f011810304000b5907002d07100e610082e50301004045030725600c080498111175480180e0036118200724514504004545d4401b94000d00760303a04a00420100400000c103a074010000c07410030139150002d0200e1402114480c80103004c8200c00c02c2100c0340621003041d0300c012034045051400303803100d40e4007060340c1c1198003c0260743e401280d4070040c04010300c01a070b0303c0441540d20318625072600300042c0e1303619405000f19148010001c00301e002520107008640c0a5508500c051207025030f02c1c4402802071204241c152910030880f1502041c50b046402110000c160600081d0700300902c5400b000038030f070217601d007061106944031060700ca41804091550900d00e01503a05c0386520145080c00c0700343ca2448002e49040001e080200f200003005004e54042d41c00c2103103042c10000021350350800003085a5040352112907401c460700b850840000031024180c43d2000151601c581d41c2a210b80309407000c551816a2010760016112004d0030700b42488030a0403c0100031454180 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 128979334 1250 128978084 128978123
    0x6030209040b03010f09050c0913030f031b080103021002070305060a0b0d0b01090b01080901150b03040206070b01080d11031207030c05040e010915050603060f010509150d0219110703030c 82
    0x82a6030309035170905403214910000d024080c486800c840d07105071031600203450042e04180f41e051800e82d00030188a000341140844a01c81c0e8030180030a0020f50354004d00000c01440a407045d50248030881c881c0d01d070107240c405100c0c40810104104c0307520000078241c41e11081403031030241c0202e03000d003508603035400d1500001c940e403e500b0384c0c000e14000800140c0c01c0c94460005000e40030040100810360705186054011140545100c0d084503200560661241ca89100081c00383c800d142c00a8460365005002180c400360100d50107001c0203c0b070f05c0e40c00d03000034441c0819480303000b600142420400c220000130482e074025084084007400614140741b40680b84c40103540404800e800808c8600d5542d60001b00203250604131001401e011140300b0b0a500e82040000d25000640e09850304220010500c01035503180e4408413601d80104031001c41c0c690781a6404c62000350400b503c80303540c820040014281c806d01a42c0f2107a039001f5810080e01580e41552025600d00761001e02c100c9075500304581710540c65 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 128980584 1250 128979334 128979341
    0x2030d020f040801060f0b0405040513060203150108130302070509090a05060f0601090b09030619020d02070302010f0b040c020d2105160306060509010518030304090203040b010618050a06030209040b0301 89
    0x8624141041d511107040400450844405800640e0740d10710f0300c503042c429004a1380581d4100c80c400c03580480c966480074490b0040102041004018600101c14025180c901e01281c2c1d0814030282d0b504c1d0070a07610205d6502c0052141c2d8809030150b04024401d110500f0f1029140e40d0010306101101e03a824001d40e605454503030b0456140340c1a0301200148901984d1200384100140302860116041811700350000748c5540e0b000d4428100100740403998040311340150103455000c2e492820840d01c80c040c608000c0d01070081221600501464441001c2040c41c1078401c2401030805540101100c55692000352500a080d0118046440c0c003101e150107040c2c054003c083c410302c41c00500040da4146654080d003075422540001061000c18014601c542e640a0f081c0ca5070341000e00540041c1d0304c42d45003c6411882150021100070780004204001e00840d88880340c120b0b0f06554400141c001750784010404003042d405041c0d4014644401000101d10a030003400c0c01000003000010801220000030703084 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 128981834 1250 128980584 128980597
    0x303090807050d120e0103091b0302010e04060e0601050d06030c030305070312060b0f1b060a0b10051602040b041e0f0c0306050d0303110d1404110d02010903110102030d02 75
    0x10620681489021030501840000380002d9501a000b03d03a10703501c26843d010303880f00302410400d2a0480a000760b02c650000b01003a9003058106540703859034140c0344505000d500060340401c0c0321074441c507624100761194a04803001c00b00c0d988501e480c2c00c0300444041d8091000d1203d0591141400b0000c074400040b00f00c001c6110342c449540c1c400b11803402070318040900b603100078443d240c643d080007040e070900104d4111400020806940c0c0b070107808401203c084121040f195072240c90f040100002d003650000740c602e0400c0303c8502e1041c2403850308860900c40c1d804500c5201c5800c00306600181003079007000108000081c00400c0b141c1075503400b48941840c508c4404050b5445680c0c07013103450b401f40f103400c214030550310b41070020794203103000f003901d94158410007400c0540d1403c014100010b044281d8003808020785042c003401400003200c4072030f242c0c1500d09943e0f5050f1011014184d00e061034104080e25410b03100c4c0c0c2c05403441d50700d43c0d00c1e0356410486403a0643c0420000c2000354a800c0c4020510b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 128983084 1250 128981834 128981837
    0x60608060604050a0b0906060d11030a0903140a02030405010e060d091a090111090607140d050909010b120f040602190903050c01080405071503111903050a0510030609060b0303040303 80
    0xa45203069020082034840140410310310910702491895280c17150343c2c0d200d07440b41c030580e40507030307284034015002000345104101d114ac010004400c0c08000d00d00703500106a014082c4d900c4501079520403030032010314841d901541015900800080095500600116082c00002043c4a007002c00400041042e100d4000c0c04a0b40103542c5a2001c04240c0030203020ad421540c0c0300300030001300f108004080e25907c1041c2d44140320341d4021034030300108110b85211021604440040d10308040c04d8082c0035280b03810502140344260224400410b01700d5445060f51800c944c03e02c00851071352a40010f2034000040a40191203281e001c0012400d8014802e00300c0b484401103540780000c02d4550b080840c00c0000314040c031410403044130184008034000003804e001340c3c1c0c2c503441058400f140040c0c066001300710340c2440d01c0000f2004181e4141001d000d07515410008040d0301e003448540d0b03c020840c4122082212180340e6038050100a0011400710760084000070b01c201d80009814078071138002807070350b0000e074011030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 128984334 1250 128983084 128983093
    0xb07050604021305060a030209041e03020a351608041d010e06010c02060313050607030c0e040605031b0f0409050d09090902010e04091a070f09061713020d060608 71
    0x800c41c106207440180c1c0f8143c1060030003180c108400090000c00c9a0f1002a100740000f030b000c1002e000000c1c6843c01d020801d2200810703002d09500d0041e4640321044001c3e01d0010450016002110485e88150510130303031000c41854007a11038010348407903001090021b40c405040701c026030008503000b0003000a82711a040a200700340b4581c1551000140580007141180000340a111050f42c00c8407004500950488025031a50798074501d00070092150310001d8424810242403007003064260b40100400025641c9510b1150901d200380001d440d1288211074055103e1243e05006440c2040c1c80010407000070046d4034040d10703da00040070340b81c00b10f0043c1da880d041581032a003402e400003244802001c40507001d1240c03042580020f0100000b080c100ba001c1ea4444250074100230b43c548890000801480b0090b0f01c500380800300808441080403140c02143e403c0e030b00410b91a0040702c1c0c500400c0d101841c41a0295220100e820b6003400308441280c01261960986c1c0c00a21036000e080040d02c14400100b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 128985584 1250 128984334 128984341
    0x50c01110309010f060810051e010303030f050601080907060809030c060a02040518040f170702130906110418020c070305070b0a180b09041109060412020f180a0b0a0b070506 76
    0x1207086130301ca0544c54840518122041044aa0128801c00c91800c1d402c00010180c0e144000352000c2c901805c01200c940513200001b2041580542c000c1c01c090b0301c420400c0200f962040f0054840e18410f450303070842984600f0301000340303501c1080e1195111200d50103407800d00301c51200703491070800d0540300119110740101d028025130030100c608580940349489203888a05007512034072400c0720f101d14044c0c000701941d03c011940440c04011144e001e5405010303c0c20f580000d90034500209040103044461509046441141d02940030070340741071320060502003503180501e0490740c00962180c002501d1a004148001000c6001413107081e008000c0740c07044035a0340289000040c0050f1030010300c0514041d41d540d041c0074032045c2005450781e6030000c3e14005104007034250910018002c400f98150700ca040014007048081031116200441882518009511003103e000c000c00e04042e84c40c1d44048000382400607070040e5aa82110f42c0074030f005861015119200c40704c20300e40354008803042c0c680c0d61011060 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 128986834 1250 128985584 128985601
    0x703050a0212030a050f0a0207120b0402040c021b06131a03010305070b07030c0318050402030a0b090c0910140906040303030c0e040b0319031701090903021509060610050c011103 78
    0x852030903841842c051072904107a440040c216008985071000045000304650b64614020400000504103d448485a0704c1951a008500001c08c440803801113051100300c02d121030002900c41d500d0304440c50860500700004050200c0f5030480c080d1007480f41d82525000038440b0414290b400050040c009060380d030340c1035042c450703c1c0400c558030140300c09000300104000721760702c00e0f070b11404550b0622f081d00d88060800702031006400039405c0950302130320000c1400b041001d5a44007082599096a040b0410f0742c5442d0035031058014400301c1a0080c142104c10035185118013143e049020805981d141403070783d81342c041001c43d000317500704030046585e0b106846000c40e04050300524000c411542445441071001c00b10381c8030401015040e1150760507404020030140038400c42c4091500c4805200020b6a55102000241001410079005800b846012904115800f406107100f060b5150007020a83c07100b005000e501c41710f07516550100034092114026421080c0151a000603c56404030340700d042c00c649 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 128988084 1250 128986834 128986849
    0x231002040605071e02130c1107080c01110a0b010306050403120c050405090c03190c2d080f0c0f0a030f0912080603010c0215040305090306040501051b0a0e0907050405030703050a02 79
    0x10796050710009040d4030fa006a90b01c40003000e0700c13400c000380420b841000301000c2d108c264400988116600400074003040341000054101c4d4814801d1f6200c3c01000740c980c807200c1c0c032400c0c5c02c1400742c4146010001440400c0d190707008503400c14401d1074403094403a800c118041c21200c403491081c0004000003802c11161404023410754204c030352410501c1c614100030b0411202c1f05003540c11401c607d40c50300c0200d0640d501584000820030700b03480d50965031a0160401040543c5014580740100f04d5120209074104580700c42d03244650a0004c40e80d26011b07101c041c000041e007290304500b040544407441991202e805004244c00c032442149817074865401c010000e45925001410f10380641c0c9480c050f903610540c00102d0314441000060b000080344c880741030813100e6128811a0940500c0f4000500080003c158045845041051080c024005417100c00070074038803401003003000003000b11001c00c0f95031034804244c68100c07519091030f9140c10740d6000030a017000d14950040d2201d41200d280380782076051050 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 128989334 1250 128988084 128988113
    0x3010e040b0c0a0e09090c1519080910020904020d060e0906070206070e09180102040f0e1605030c03060a0906120302010b120a0b071101050f06030c0d23100204060507 73
    0x40902c0e0600340c288038010a034540c0380b02600d2141404001003140b034001840b007520303140703400b40c0744402034143c0400b051504d134050711420f40c508910030250307081180704412040c0500144005818911001c0c0c0c1700c0d8004c0c0d00044241544142c3c01c204410303041815200d41c40c000e024201c2a103901e0b2502c4440541818001008003003135400c20401c010407035900441d24011a88111110740058a6501d00c0c1c400c3c1c05074a48100903950300c0040d02152904482200c0c200300c1e0803000208170940e5450b43c9011400089a1280c0c1c00316000780013107400021410041c41d07000030040d141041103a0796080311419a00e450b40203c400184050034001810703428056030f8005002a220b201901001002140e40c0b00729100f8058010b08034000407a81c6030b072107418007540341e0420310001c2c001030528030800102500d09460180c0701e441004443d54007410a04c074001e0741e00340c11007200d00300008148115004031104809404c49130007842d60490320000b9a01c00307400078243d603544098461405241040308a400b62 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 128990584 1250 128989334 128989351
    0x1e060e1903050d020a0c020d030504030b130b040303020c0c1504060e060301050307031e080c1606080405070501030e03090310050604150b0703030216050d0c0204061d1503030f03010e040b 82
    0x4803030460209811400f141e443c110346010041e0741d9000c600c021120482a010000d502004514a041c14107a01034081c3c810b1768000c0641a580b500e402c0c604640da03d804260080c41e42410000090101b80a036014203030094030202992000c000340c0000a542504009000c0c410000c080780074000c41e6840600211992401e6512628550410002035603802c024440100b0340d00d400400740c880d40504103180680039a107c0310064030707003d035040c2803a00c90b40000c40458900c441d14800103915885000003034080c60301b25025250045c2001c0c0110b01030400d450002c1824401040f2070205600c00f00242821303082034840c000f03082e040c038104000546a8413110510009079080b01802880303146c034100d64225600d406c0050f520150950180e039880d401c0b403c090b105002e0f451a811100e03400c031001022940c0300b21001c0004544525022001243c0c052640c540b00c404c8600161340319440d018507041c88038004085a041c45828045180f055000b604504202c101900c148400c01030400d06d06074005218 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 128991834 1250 128990584 128990623
    0xf0e030106060221120c030105031b061921050114030a17071104020417010c030509070308070c03050303010b1c02090609060d090203030d020903060610020303010b03041e060e 77
    0x10040000c0d510058240c2c0d0440c410060801c034940c214240b412140c203129810707450300c8585400c01081c0ca99420274810203009016001032040c4081c1c03c1201d081503060001d040c01d080001c000785850019465104840600645140c0800510074001003900c626600000c01f0a00d0340c1010742120368030582d02c1016000c0d0b40158440f100140241041071604090200c000c0d0300c0d01e1090800d0b502e100c103854080740c0c004c1d03c0002c011510b40400740121000d0721030000240b00d014203811003202241c104851440305500700002c14000169540300408416004403e1015129200c3d00d60754110f91007a40301219201001552090514501c02078038014001d6407411802d08124002207142803155030101407150b0400100308001c081c031607000030700c815000341c2240d40ba020400b000c0030003076000042d0719103c1e2150800299075854900c0ba0b40384000e203940d000e181942d01e08041c00700990400350046a82d84141c200b0740b4001800100401d0b0b020b03001c1c1d20b020a0301d612511583d400d0114090314100742045 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 128993084 1250 128991834 128991839
    0x9010e01151a030a1116060b0d02061921050f010e1504020c030d091209050a0f090504020d06050c07020a1e14010210090f050d05030708040b180d0f0e030106 69
    0x202003000707050001c15210050740c96466400901c01450340034905117502502060885401c00c003000960841449030318100f140f124007508000031200c4100f00254070810420a80340d6021743c00e001103044004604018840d1084001c00031464240e010313081c50866030380d104214400f4607506485005103980250000079045c40400c0b81c2c3d07800007499580d030049400245a0500580400440d0040c42c01036100308048121468400e4407003141c0150480043c141050207e0a883c0c034012100850f0009000095028604003420000d41801082aa44000780d0f00d1100e0200d0703814040c0610800c2440d40440d42c82080f48100601e40e2000e8001071480a00014640010342d29090713060162482a100301900b010000c0040b46001038112407615554104031441041210102010541c40e02c40c800361080807040000849003030008603243c100003440340001c1000305d2000c81d00c1d29000701c604180c8030b0700e01c0e0302c0600082c40c021040005100040e100003144203881c1c1c0c4400d2400800300118000d0015a1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 128994334 1250 128993084 128993099
    0x90115050d0504080403050d021b0105120f040602090603101e030201020606090a060f0f0302040c0302090a06050d110423030c0607031d09090706080606030f04140c0909010e0115 78
    0x107848140500386a8440215007031260000566000310761000449200c3d5484101c000d4542ca130342c46c0b0f2651080c90403e500a8158004c80507540c1255010400e4401c9a980d4580003d0610010f0b00540e8555820800800140c98401c0194451f888060340e00000c0340c40c100c80704029901540e01500301d400d902d102480140ea0100d4078a410000c12980041c10340ca03a201c101000b000c0070742c4a001c2000103150001840420120071a04a81c0200e03400c1001100c138407001c2d0142c1c4241da500a0344002c01b002c040c4140c03406a00030f8401d07003200a07400144441880c014441035486600030495410000e1840100d1013020215405845428ac0103408144104401f090b054014420000c00740701c3d0080c2030742000080055120a03001c4001e02c06c2026003000c802c115101d070054003503900010540d400241c07113070a140c41124002e0800398000700c21995580ca411582e030000c0641c142642c043c11000c00c8044d03980e0204103005042c244000183d50110204907421604045604402a4000e100400818 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 128995584 1250 128994334 128994337
    0x604090b040b091c09050108160806010c050102120a0915090804060302090103020c060f06100f02060105040903050706090b060310060503030f0304050a0b09150f0402150c0111041409011505 83
    0x1561020560031151a10000e00703041c00b118510064021411341070040350706034410741d000201c40b4280c90b00c0459071070380390100140350140354040d00410310b500085501303940302da6010441e1a00a00005007409124504070b140403805565040000c0d40318000901130140000840d6454141c20340100090070752652440014040c0c2e11404c420b00d503000c205040d4503400b03034040362446200c0d401642c3c1d003841c1c02c85c200e20101d0401d03074215014010848503030f16158001e0b0f41d03042607941c1d507800602490b032130710040002801c03004a04400f001824821076000400741c1c094000211300c1a00c1c00c100c903207861307018140f820b414080003546160600900300030580b000320885120080350064a80d0741c5d40c0307504200340351011101c40181541c80704410030410010105442441c0d042c2e640c80d600c11510748545a038160901550047e51151964042444403120000148600307a1403000200c1c103040201e5143c5035a4020342e000002c0740c100107045d000945000c100d11030141c89400d00d14064821040300080070b0303 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 128996834 1250 128995584 128995591
    0x18011b02090a020d060503010e010204031202030a020a15140a050a0c1b020405060a230102061602030a031d12040807060504030c030b060f04020c0c030f1c0e06040911040303080604090b 81
    0x20990f0008404034182181e4014501078280a002880400280d80c42d19000f94031034030083d40d0b0050003585408180b440442200d8a04c0300710350041806a03025101c4480100411f0500300c00d00740c0e078250321980414000e4500d442880e801900280703515103541404c05031003554110760100b0006031440800310800840f0380d010795805680000e0680e840703d003c119034401c03d401612101000b0440d0100d400400c0031400481c020aa00307581c401d03258a20080741100740302044001580040c407c054200d0300c00e41c40310005103607148809331700941c400e003114201590700045483d28440040c050044600030403923440144118603001d841e141c0f454131030840364045800005c0100303810001141c5166203445850380c480000800440d9540d100360300080e0360b49041c41c450b9006c0d00840002602464001c00d404280c4848042a94031050851b007048543c0314400c00301e2588808244000f040d0640b01c1d218840c50410402041503855003503090140c4030002c000c00030b03845581040d02e0f01d4006900420030580 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 128998084 1250 128996834 128996851
    0x11060c04081e0a061103100803040609050607030c0b07050403020316080309060d0b190815251b0803040b160f0c08091201050114030a02032e0218011b0209 68
    0x5000c1c148002c41801c2c990708981c00b9003c3c608064041c48544820030085005e08070b11101e4059041d500c4550641f2800b13a48100c5000c900003450400c06070425070001c0c10000c0c424542002040309503501c4d118010010384200001a002040c10310031030500b04a4286a010450200ea01140c5006400c994a01c90400f01a00501c03004c191a8002c10306904040000c01004002036000240b401a0980d4000c1d00e1042c110340d80b040501018940400104071401112031001129075080409503c203406801c18081c40100480e0910f0b4901c2c800d60701d40403000d000e11454409a80f4101410907100d1914090101c031170742400c00b1445905141c00c101d10801290031410038036070703444450401d200d441c001e603004240c12220005d0b08810000c0194480e5050350000c22401100081c07600c10700d661500c031804003d4241d480400d0300d1701221020840000c5c4098401091340d0303602141c452043c140e8012003000c4d2200440e004001401d0b68100850004041001d150580701150790740001d860010050700450 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 128999334 1250 128998084 128998123
    0x40611011401061808010c02030d1d0d03021b100e1e150406020409050a060305070807050603010b2b0b0a12021e0103020c03210105041e02090301150611060c0408 71
    0x44000810400c000c0c844400200066030687d90042d480364400c0000190440c6003107551503e0b07404400000744014080001004c03001020102035009510844804d0f41c040408110919481010052804201d00c0382001140c404208010645003d111008a080626a035041091408800103c00c600208001007a00603a11035050890091160380c0000d0820b5003440100324100b400d54100c041140d1044048071802913640120300e4a035081800f8060380510101b004100c9005688094401004001551081c00020024238200c0141c0c0c450300e6100d1549440a11400e480d041980100a000c00c000060891499500082c800d1801b141c501e014107403c46401c0049034441d03030540e01101c4961b0304880ea5151710320310100d180100c480d481075126414034000300300740c2444d004401008120400384460407004681c000069000408a290190350300c0c2c00d1350380b0140810700340000408042c0c1b103620300441d545151a0501e0802084210340600400c020082e0401c0002c82d01d8000d5419403a21 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 129000584 1250 128999334 128999357
    0x50f22020d05090a0203160f091a04020a120c09050907080a09141b060a02120705010216080307020c04090201020706031a091f0f0303090e0612060702010204061101140106 75
    0x2100900568a91541d01440c05007048504500000c90030313000c1c1d0080741210800c400e61449001551800e00402c0039991490343d08002c040c0c0e00e500402c00a45400c220140e1a40009012508907007140c0c0749803001901021110f41807811a11401e2071503956407174404441810078000c65200f10f070282124080180400c0000e0a00e2034690000040302e500c891503a1303112144400713469441c1f1440186030848448850499014035180c0200c0300580d45640142c0903c814842c040b50b0380741c000c0642903a441d5020800710019614103100506183c0c0318160315601c038141450028a003004099504e4003c0d45403001c83c20150781c0018500f002c4900030f24002ca0901e8401c80c1001c82d5490741001107401203003501c1400380541032124040400b403001424070b0341d969a030310082260708401d0b100c082c011070700c4203078144094454408001c0d40aa0040d19102445224403c0680b0b442400ca40c0300c2d0040c1d40c041001d001d200c0d4404e58980c400640c030380090107407480385a41003010300c6040c0304400500c2000f0764139 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 129001834 1250 129000584 129000649
    0x190302071a090a0c08010506040606110601050d03090b040b1209060708060910050607060603120206040c1a0906120f01060c02060909130510090b0c0f090f0a050424050f 74
    0x42540c0e0f0303940b001c0c0c0c103c070f519600d942103400f800c4103661070f0340b046040980101d011440751410310382c0c01500c400100315591070241400101d81c070944054003007184281002c030740004131000500080000f03000e0150382d10400398426013109805011002590440c4c4188041164031111031600668125485210303078607000601d60810700356a01c81a00139070003040510902c445940010102e9002c1c5a11201c0d080c1140700884e19414204c4004042e0303500800c0c184640d4100051800d030020144411030b103486107000010301c1301e80080c502d0440a03070341c0e4400c011004a1807584070b0b004000c94200a500e840c0c05a0006840d4000c00000324000d1046000090440001c00750354213055030401d0503151a00d0800e6016405492030b03c1042d55106000c10114441c2c0f1700000071103242e09029041c05050120303010410400d200138000c441e901c4160320320b001c2504c0c0d86910541040100d014105c450841c1041030b108502c4c2010f81c4100d06c590f4400300c0803400d5444503400b079026140c50483d0022102d0b1170751032 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 129003084 1250 129001834 129001843
    0x306050c0c0d1220030109230f1b040e0702010609020a0e0103020708160f0302010506011701060e03150108030903071505030601180e010b040602060f160e0402190203190302071a09 79
    0x1303489405180501040d80f00c401d00401035044c0e035030b0400c0900607400100c51900c48210072800a1104280d100001510701d80300c0c02c1e0700e9400030a8003261001d201c125074160305254015411895408880b40c0a100c04160244506401010f0016041d802d004440782301502e40e001134a44107043c0740d00001c0e8a42000041800c803500306d4100070000d1522031a9041041c1030b0080004120055031034080840c00b40c0d03005103101a0520a040b401544a03824050200c5450083c4002c06030035102d0f800300b5125001120780014080d1180200950321540b9200400d0b16011380d6911988603400d8607650365804039400b0041305d600500a0030025961240e01364001907680055000d0900030031b50100110320000704400900032111503600701c40040d101c94039040f0110f281940c0c00700200051318004407082c0e00a50750350300106401080103041012030200c00c094290965402c02c0144c00004484840d00c0c2061418560040c951604504248281c0e58800341d9003108811010361070003100000355503000802 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 129004334 1250 129003084 129003101
    0x1110a1d150c0601090908030103140a0605071d0603010305030304060e1015060801090b09040b0714070f0201170c0d02090d020402070609030e0409080414190f0306050c0c0d12 77
    0x105070391a0362455000424580e04811542500e6003d40000010860043d004400c00560041e550918607441c55030359a1a03d800829005203078010f0b020304001003025440341600c00c492030b8039580700a800e1204031110506818501c00d104d03c0050005001261000094070751040d0300041c0003030302c00c41450f0441d25050132490007e401d039040c0849100b00c2c180c02e910742d408860b080e491307965103a40c813925600180c4d02000840c0d50021010800140402c0001c044141c0020f59818003966441151a00e0364180e444083d090f1401241c00c00240b04559000d8a030768001410441064034030704028250020511840702142020350300032444071550380d030f0711b003401c4d5580b076000344219580c61041c40c0c00030180c032141809170041079502c01c001c0305030308043c01006041648800080e1030181000c040d030ba06070400000e6590002d04019504e0303146005051450003500d14404580d051030b02e103140490a5410040c403d050005048c0668007801ea400991103c4c88946424410301c8000e91400c000000c4c0040d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 129005584 1250 129004334 129004339
    0x1503010603050f070e0a0e0a0209060f300303100e041e050c030d050405060f031b0307082223120a0f0207080a0503120408040504050a05071101110a1d 66
    0x200aa0500c1c03c400044040480d00d04141e9104c041d42d51b00c10344401c80d4100c074881982c1e600407001c00c07401072a0404660b98085c000a00859a100090000c9070080002503420302e41500101f00347d01c00945101070b84520440414001c51035031620824000c19080c4601c59000002e404101190801c9882543c9910128207200907001e018201d04003660795a5920351100d001e070107406c0d64401715030320950464041d560003900e9245088880203640360f040c1d1000303081c3c5a11a1910b1440c007052140c85000b58080e00c80c07655440407504200050440c00e00c0d10103002007a2610755018100001c01d003001d000c07885000c0b0303216148921103600d0b455007059046000020341213400210b0b90406504000004882c0c1115821941140d0b01c41c2d20f665554400440d0191960784141710b44100344c3c1130042c0c060340c4a4400c1504a09040d6540082002e461007610070b054800c1c1c880041100705503014515800301c0c0d103041c00912450581543e41665031183d00c04190411004190304c1c3c2200300307200071101082101 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 129006834 1250 129005584 129005593
    0x50f0705010b03030715150609060f1e020309090a061d070c05010f0614030a051005040f05070306090b090a0209040624030f031103041523071b0807030803150301060305 74
    0x10340346c482c2d41240a0151380014900c0c01c14142c081c090700e94032060580e042d80c2c4819400c10704250090f10000b44005041c0104140307041001c008231312030401c041594120747c00950301c0e900c0304810440005402440c44107628982401041106424a010300411640d001a2221915091021100404000c00180c880d40c2488800a00f4555503800502110501c03038042403c1400c0c002015120042514042c103a40e0001d0711340f8006022990000b900584183e100d82c0d1400c3e03281d40c03030302d05040443d402616000d0384d81d0a500d040c0000c1c100044da0285981014020f11300c5240d001654035000640042d1185d50754000030364170965021070b0702d145000803500d0300111a07580e00c0c10300b50500b810001140013655042c804c500960000060710b098810502c10304101c0e00122100303c84a002003a4030520008000000c104005049002401c0441c0030f6980c02d03000389180e91050f92070994a91081c4544da0042a040011410407815290815050f0f9182070001e401072000034098036040d04050900d025 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 129008084 1250 129006834 129006847
    0xa0306030609050604020109351606030501090b04060303120b0f04021201140d0209010b0901170c0c0f030c100b04020c0f10050f0402060a030207061b0f0801080102030601050f0705010b0303 83
    0x1d142c138405e9100740c1c1d03803454040d102d001c4001350320883da08081000d500c0100e007800701070400e140341050606840468034100100d100c1c00380a5a101e80c008004280e0700c000600815a04c2c2c0500d0a2404007a181400400d00d59030700201038100490005003001d40d10403001c48142d6908503000c9042e000100b003951100456420290100000c0c0306100718841c4445603013940d8140308514a00c100c0d0000e000454030780c40e010809c401980828100d504102e030304c248840e409400b24000e20b0080d8804030b905900c6082441034145044681040d64038294814070014004040005500c012410f6038440800d640788002c0103d0040c3c000e007a1403c2c607c0c0a5460081c4031000000b0390342d1981c940c1c071001444152105001d20101100548000c0c0d048001001b81c0055980207400a0040f01d04c1540c0c000b44000c7e0000750311220612540a210019503172000d4a040c5035403141002d0301400d0144001c43c950308240002034164400d500120800200115422040c40421750100c0403841c00542580d60b21030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 129009334 1250 129008084 129008093
    0x91503020d1b1805090f04030c06020d150e0708040507050f0301020705010f230c03070507050f010e1c0509030c0f0a090207030e0a0e07080705250f062703050a0306030609 75
    0x4a02c0c0c52000f0301401c01080004551070036000c03440c040c40b0104400320b01038440d0303101101e42c0b00007040c1c2a21965000c00c40134501075007601c00d090b803d01200c00c40040c4a0b00b0316110b10b401e014094004e1041044810030301010510200e151002c48a04542503000500610086806030060b5403000d00a540390070301ea02c801c0011031b0401c440e0a490400306691441010312a403610700000d1b902d0300400c13003081c000114103038040d0340100000c40c01482107843d4083c80740c2d061401d40d00303d240e821249800050a440e1a10f2040802450b107c1c840d003030280c240300e0304402080c1d9032240e0000a81c8104060300c0042c4032611520014005000c40c07420a55507000c0c2d50401801500903100140d001d440141d50018211101d0400035005900d981c3d5581496100c040086400d07402186141070b150000c1c14200090b45000d11000304800c3c490403880c8400001402c003d403c07602c0340300c24058481510707045240101c80c419610420715a0505089032104100c0c6411002071015410080169140188010501 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 129010584 1250 129009334 129009347
    0xe090d031a0f01112103061207030f0204050c040806090c090c041a16050607050711060f070b04051002070b100608010608040f1a01060203070b0705090609040209130c08040c06091503020d1b 83
    0x1f080246d40241c0d801041e910840e030754004510020b051b41c0b5140c0d090600500d059080103800c5400700c84450300780350b04d90320f4075410f04009881c4420264445d00e405040342c01c290803100c1c1d004602c03003031107400c01e4a003803a1400c000c8950310303c0e01010140021035600030120350015030700f03242e000001c0755010301d40450086c1281e4004002510000940e0101800b94642402102e0700c610006a070305e0b080000c0c558825000b00070103002207841d4052804080c0304145c892002d044085e00800600c0004e0420150082d00f026154000c3c07002c110141c0018013540f90054059030300149e210b003080c0c50581c0c46041a940f400b1814100d031400640c0000000345040d03001010344806402050142d46036103400780c059880f03215004900390880d8051013016514030b01503018086904028022048d00d41a014a040c1103408460104001c504020140f1041c40203940c80c490149c10303203050502085042501580d81d5041c240b031030301d08164000443d00c10040d1682c00401a030101d088540300300342107468014249 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 129011834 1250 129010584 129010591
    0x90501230906070f050a020a061b0305010b030103170a1211030403030e06060f011d060a0903120302030f0f0403031509061706060a06030908040e090d031a0f01112103 73
    0x28551031101040c41c80030080341540c01640745403211a20324842c0c51060700e003608407600c51000c0d0300810249501240090003118900201c140000c204640c0184001e01245c606801c0483c0e00b4005000510000d103140b1980ea5031044400595502c0302e40c0c0d80750450b0400d188500c03031404e003814958256246d10240c000b450146100303460901840841240c810368074842100e03a242e200e071000118000b29401558111204901801480b014110740d01c08110349900c411000ccc80000c95101c0100305001c903d50400700c0380c1107180340075851130030040601a0078605c0600850f03007001d2040301090416000b035210400400200348445900c603619600e480c000c0040d031203017884066142c0c1c0b051242440c00b01d5903601c19071004005110300ca08060080f402441ca0320000c8070400c4042001141c600000300700180324420f01c00003002c0d002c81070f200040c15200c680007040300b01800704c2c075181e2460703854002c20354001d1000c0c40c1c1103548030107030f90445180004100385002c0c41f101c0508101072160000e001180f1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 129013084 1250 129011834 129011891
    0xa0b0a0806100e0d2a0f05030f06040807170c0a0609060605010c0302060a0207060b090a060f09060b03060f01140f070501050c030903030a050c04030c06180f1a0d090501 74
    0x442903410580d040c60503e810254405440316a0f5400200c510320000f90340c3c40400002c0301006001074540001c010a034008542c00444460104498a400c00913107203204040005003085084c030b6901c1c1c0e1a180240a0010803610038190701c1e80c1c02002074425580380341c045800321608001c41d41031000c0103124010040d14150b041c41000300b00340d4040c11074840e5980c0c4c95401480141c2da2031880d03034000d4000003411621243c032031080c0ba1540d40c400a115014080703558002410f14684040643d040d0025171007030b0007442c109042049900e583e1400d4075401801134500c07407081d00801c0300407a4040c1c00c2da0040103140d003010406541c89907070034019060302c500c1500200855292425030004900046a03682d10650007000061040c11803030300556001803041180904290b01da582d800c40100722a08020000b0b058420001901556010904010000c1e102c000004a0411b1900d02d800e2800440e500c5a507180080d4052038800717140d024030500350304039008000c0112242c500c10746d020211081c164 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 129014334 1250 129013084 129013099
    0x9190b07080a020c0a0303180b100f061b02010f1206090204170303040f140118080a2c061c020d0501030224190203090a0b030702010c2c0a0b0a0806 65
    0x44a220451013180c04101d144c2009010703015040d94210060f0100c181481c040103074110340400020300322454203000c2e44950070081055403e0040004010606510010411401e44046280c01e0201240c0c0003d154080c60302101142002400381c0b450076402c0b03143e00420780341900004031600035502400a031110040d4502a00344180c1d60b083c2e0324003040d00c020b4410900b82d0b184600240c4a0707180703001c0d0035483c00c00101c0c60b482100d141403d280c0400f08241c030307900c4000030344141b21a0301c10500d55008440820100080c105089440c03002070b8001d884130302a8000240c05c951074004500b0b0841900341d9402e0955507403807251041070140400388001c9004071380100714201210a0315120314800100e04104c0c0d800c0c491503500713482c406001c144040e0709501040000d4402a01d078945c2d004050a003505e50700d940d90410800081c21290300c20450403c100e0208034001144a851200c001c403a402401d170130404103410b000044902c0b00960000c0b000110004074040f040360840d041130300c14613003143c162 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 129015584 1250 129014334 129014341
    0x914190608060310061d130b040506071101050f04021e222d020f040302180f16050319020408030c01060e010605040305061b0903011a03070b0a050a0809190b0708 71
    0x9419940140910f0300c1141003070000f880c4078840380d46c80c50743c4191805c10082045841e5201d06003944002d85007950b807504a00100240e4907001005400e00100c2c5100070000c0f4038102d8072280504030040c200231301c140d0b40300c40c50803d61841103104a9607000c001302490300044881c49244903074800800307058000b9040c0102120036a50a51482400b203020007002c9082554180906000307601906100000b041d00744008400740e03d485902c000b140c2c1104e4400035443c18008400c40324000003e2004402d200d6102d000d00030140d100c01500d070000c160f035500c00d8034843c0301c40041002c0e00072500014414440031980c000e16140542001e8203c1c1c1e41e01c0304400d0b081c1d0300d0f42c1c800c581e81e100710701010f0a03541c458000b150112488026408440c0c49002241c0c2c01c0c02c074288000307401d54644030072a00d020142c8259003103161400340000304c020703c540d101c00e034a0807541c418040c006000b14404041031022600016054000c1031244d0000c0e611030311845000352101e403604174218917041d44c80900007080380002 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 129016834 1250 129015584 129015613
    0x7031505010e0112020301020d09030c06062304050618040302062a0901050a020c091504110304020306011205030724150f12150903050c100c09141906080603 69
    0xd090680700076468218982e0b0a0900652000710b02070804c0382c042d035007004081c3c50315290384604107000d0f100e40d403104006120b608121041ea00140c20500646400c520302e64074040754407280002c901010364021829a4030680040d03242c240300805003500344484400c000400d940855840c1c41004030040900c4124002c1030313012035182c04024982da680f82c04105480f00d039030080000e00005100c0e4411120425a0700d0003041c81244141d44c032503103142e1032010924181c5081d000316201032b08020311450462525400090755214184198540540c4e030074076550078018240112105e50360810540c400c0d084100100640701ca85a04400503901c0c545195002c0c680340c4119410304807003803180140d0b505810411450003d21030044101e421407801e842d140441705450103007006050094546684540c4640c042500703007400d1205403041c0c240741284c401c41c540d400030481010b652a41030540020101180861404c0840209464111041c0500080e000d50b10040e107910602080e010356031000c110151 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 129018084 1250 129016834 129016841
    0x70f02060115170c161112060f04080a05070b070503010608010b130303030b03010f0e010203010302030705010c170702010c0204020705010507091a160303020f070602040302151606110903010608070315 88
    0x481800140c1455043c06805400e041002e812441100d805840c200c01107010f510a401c29030000c460215440b030300d81744640380a0810701b100840010180c00d540c0360291801d2204900100000c225208c00300b03101018a110303000362910168040c15800090a00d101c000d04070346c00901c14400059014400401c281d4000001c0e20150350a40c00b02c90a07450849e034003500540318890401c1d400d90742c0e5015601c110202d82c001c00c00480c1c0840c000680c1d07941503005250400140360012810701108000702e800050103005c2c91441d500c0380303800da03c0d112030680c80101c0d03a0004481001e980300d8008100b40c4144141035015501565043d180c0e80c0c542c1c1e51f500c4824903990003504044005100034808846010a0b019944610300e00c2450300616000c904080c02c61150002304050303503107980c0800c007442141030800d541c0040c4900c07611524240f034a030100c0c02c0130320b50b0354110040c022074441034100600070b9104180d8106190040081c0003040e141d012103075803030465210913070707214540d20002030000c0707014807 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 129019334 1250 129018084 129018119
    0x70b180405010918230304090207060b060703020d030903030b120c010206071b060506030307050111130501031e150306110d18020901050d050a0516080d08010b0919030b070f020601 79
    0x918a480b5440584030070100007003c05d241d6182a50360711803020854810300007800500b01e484001601c4404c541401811100b008c0840c0e0300486d020004e1002180e00060f581d00951407916010540d4940c92034210080c0c040748a1050b00007075210103100e0564400300b2081031802081c0d08890440d5a00c0008a03203c80b180c8204880c50303004e454a913801b25240d07810581e407200002d012607140c401d40d6a20142100c01d040131050091340040349069071680b1108205004040174a424017280204116a01e00b0b80030410205100690710f805910204d01e2001d0050300031500402d042180b440f810102d85801e40c08200346c3c1201500e045135a545074a4800c00c01e00d2415000f0b0a059aa41c1c00c00d006c2c40030500340c41105503010b00c1116071140009a04100164000100c1d0410a440c14030f080110b0b40b4252000c1182d2051040500042c0f0460501905a41c800a405c4413002d03030b00608025200300507840c0c0e1f040076040c40511410001d900760000881c7c854041150300300c82860781e8a42640d1960407198 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 129020584 1250 129019334 129019361
    0x5060f010b040b09010207080604030309030f0f02031c0f0c031b0c110402030c0705030406090e01122a030501020708120f010e010b180d0b0109060801140c0705070b1804050109 77
    0x9110a000e98820311004d021092130600490f5407454450906034506681180d0440000b91075846003005c040d84540f401c0c01d0500c5c40d0030540d8502c43c0c90f19002c0c2d103034050040c0380850306050355130b944192010f98001d80c03040540c2c0755003080031884400006010345201070844940c0a010040e051200303100300c00c504445a0442b80c2061000f8104007000301a5002600601c085502442185e020a40c00d100400007080c0c103803100d003500340c500304000c0c540e10016800700d110090211040c03c040344180401130040c1a0140032440345074003203000324070030700031503040607006601c0480e144040080b0100105061030380740c404503a865441032841145481c00340585c9440304c00c00f400401164200e10050000d088401e040c6c42134008503800402c407202080e0206582d00c0024500420000031144501006804607000034048602000642191581c000c0c20919104400003070840c1481000c0c48050f0181500803680d60361040d103907154800740b12001c010301c0d00c42c601d8640002008076075407043c4080000f0b031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 129021834 1250 129020584 129020587
    0x305100302060d0c03150b0405012a0b0916080606040509240c07060c0c02150a0215040213020a08040606060e010e040b030a0b1806090d1e050c120705060f010b 70
    0x2181c030f0007400341c80d03010036000500d51103091082c2600745542c403440103409483e544c10b40710340c50480010629801c0c41142c900c20401c1052580038403120380e0038040340c0e50300324035203031200c6c0c5520318441d14110000254481e82ca110450225240340c02003070b501e0107010308540511498a40c400c1654480030110f851031803501040d1260840350305101642603102095116140c14503000b900c1e40300644034100c200000080c1d034805440708516112036003085041503079000740c0c10001c2191000e507440706000c00392094121403100160441d65445524406c04004681c1503441b60212000a042d00c401a03600300c1d13800b400c042e80800c1c8540708550444d03101d86d059444130411411002070100510054030307819014007450030044007054410800314000c04001508800b554036000c6c1560501c03801510b550110b8220707080c488401e07640541d400d0302d40026245420030759841140c041c2c59910400d62810224060069030681040414000d00209400f840036550f580da603082160f0900d000074040d00c81c0d00c000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 129023084 1250 129021834 129021847
    0x50a08031303030f140f1c050603030412060902120a020a0b1201060c060e0d0f030b06030f06060903070909080304020111010203090618070b130f151d0f090405010c030510030206 78
    0x1c115040c0c1c42005250400d000305140340d1185030411b600220700f050301030f8400244c0c3c0d082c507400c42e0286110090044820401070800b080020344074400c621651203034090210707011062182c00c1c0d114194546c0c0c0140342d07501048800c0380580d140c0c0750840043c0c1c0300701000710001509503201c9013210407035006260101460b0782030030000c0e030b40f0b10343c001d40c00d682264ad03465214849070002c1000f15943d000c1620b54107815020395a000302551400c00c4d04c44c1c02410306000344500d51545800c42030f00000101c0c1ea250700d640002d0046454410180d00c9800550300b840440341c2403040400c0298047d60003aa62802d01c0703802c40c41030f10709030300c4261a0400203034030450002d1801d00702d9407138150450900001f0f0750030541c3c0c3c4502080e02c6c1e401c0301110b0b80902d0310303450f001c0091200f1000b030300e4014a50900d003c41a0500b05002400342c03820260f00000242185040041d5a07442c8e80e001c072504403008109501d10b04082c1010b900030000717041c4003408245400080340091048044800c00c036a40208201d00c2c004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 129024334 1250 129023084 129023087
    0x31305040507110d030b0f060c071a1207080114040b09040f020303040915081905100509010f1a030c12031e04080307260a050702220507020106050a0803130303 70
    0x41c002c040500700002d5070015018560140f01038107940202d582e003c10020131850400800d944080700e014441c010401024204120119048040b104c2c80c180380c00400801740c882500c61301c0341d10020309054040c0c0d0200221141c116600a05841014800d282c2958500303007800219058007100a03801102800024000341e43c1e42c081e034940ca84090f0079203040c035644498941c195102d410035a030705420812030078808160100007a1903801188641200a00d0460320b90030740ba91002003400001c5034648000500000c02500064544040c010003040f42032101003e259500b04080440e912a004000302884903241c5002800412201000550b00e40f03085019001c207421a902145910800140130015000c88144060401130380603006810360b11520b00c420000b03a2100070f10341440342c94140144040a5800b5040d0358030340d681034405500700204079100020f00e03500440301075032440c01d00b407c0002c0c6550640000c42114410350b5140d19280d103130031802e074603170040070b19408400c01e1a11042020a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 129025584 1250 129024334 129024341
    0x19150e090402040506120d020c010e0a2601060302130204052416021801030308091e0718020702101d27041407090213050d020a090e010f0203090d020f03130504 70
    0x5d4130003041c4004200048868500388441e21170000c0151700420004c940650f000103011340303191422a5200034282c18445881c11240141411010140010103c001c4603c800d500002c007079500105008a082d6282c44074001a5000d0302642d801940b043c07209019884c0501480d5040d6000d07801d0382e9080408001c101d510070112804184e234059803c40107115403524082e0818042c60003646c4040003450b1040c405490610742c000440e8140c07014103400310344940040342101c00e40381d003c01c540000c4884001c3d41e902038007891002a510032264034601c4002500200c2c10156010701024250700940720404108803a40301d401e500e1408501c00b040e40348440d015200c0142d2141c0f0442c01c14000000c0c42c0c03402c618084070b6801018480e94005a03d041032072100d1800070040100301c0e103070500f50406502103180f41c580d42c801d100100c1d807107070b04840540381c00790001d052000c11600110744925148400d907540f41d94465240e00507000d0390f5820b98601c1004021105212650080ca4259034541024823008 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 129026834 1250 129025584 129025591
    0x100b09030703060c1b08040504050711070e0703090b09010903020705040b0109140411040801230108101d0307031e020303011d0a09021206040b010807270b19150e0904020405 76
    0x4024115101016400c1866580c5c115130780255241a00c0d182000144000c448010b00800d0600002240c2004428000104c03d400c0c1d5460700d45440168503511030a8025001030540108030502400801056680551082c1d401030301036800c0380d001d65600d60520048800c0100315a0000b035441d80144055142804c1500203c1000f03400040c1003801028035440d1340d000740c2c0006009944030180c2c520081607030300140001b26103003c100506949442801541c4602d00282241407607201d50812143c44000e13080c103003e60101c401134a42c0c442d0185030041200c5d040207807059101c50500c000704070541c400026a03059694800000c0d040070f0318a80394a071901c0d0001e0410700c401d81c44000460040e1603030044910305d002d826000f000da0341401e140c4a080038805800c9a451680a22800c024003051a2000200088032401d00c1e082892000027000150003c007440c1034001070001070b45081c0c1a15002c0c09800c40b020001041101c4070001811100509032401265000c0c01200c04107000d0328007940700681 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 129028084 1250 129026834 129026837
    0x18062105060d060c0c030e040203100905060a090c02031b1b0d0f120509120c10030b0316060203040f0807030503090f03030d050a0204081b0a0303031d03030405010203100b09030703060c 81
    0x10b0310365a660502500c80b00000c82d00094000780005003019084111040704100c12502036082d441c1c00008000058828070503500841c0d2920702040064445d21807080c050310044200303100c0b58110800184d941d5001c0001d1010701c01c00040010340101020403010340c444e00d20048000c181c0d4800d010861503100c81d0384250345109221440000003440407000112008580e114261910225030030420016400403090456821a011501030350360f4684032003409200d94140000c4002620001c00d203810110981402c2c0c034965000040703001500040a481201c0d0450480d1400e1034454075801d40b2800c0c984402009907100348049030725803421000c1c10f03c0c01c403c054202c9007400c0c0c015a000c8140d0f80c0c00d40320b4801c1300b54006401c0c0080c5c4000d000310b121802c69590b030107040042d103002040326680b107488060101a51040c074040f0b000810746e803c4100850303280c226501c0c0d0034181400c6000394010b81e018400710f03ca4520005007034403048140c4042e0000200504005407a42c1c4031503014266001d6080e0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 129029334 1250 129028084 129028099
    0x160e03070906080604060b0916110102040518060f0d05030706020315102d1211161401050708060907140c0a06060302041a0307030807021c031806210506 67
    0x41c40019611030500101034280043c5980d0410b424140c00300e0380105940c81c0201000d50070010701220303200801c02040c03002c3c6400041031881e01082da00a000300d400540d440903e1841420b8852440308081e4043c1800700c400c0d101c8003080e801000455106214010103e0304140403402c00702c0d502d0741c0515401540c0215600039807800500244003505148a480c01040c9102c0411101c0c501000025042894140080b0314088a408000d84140601495100440d855480840801c2c40b440d050398411010406154403400c01c0d840e00346031409015088101c15840c000c0001d029520801c5042c1c050300001d0511542600e58440031190302c1c0d941074144480072070030411500034120810402200034000c26001444900310302c1008140c80d1f9500004400e841011181c03403050360f01013204000c0b00e0780071207142c0d6580c0c032038404101c24854841450150b002c007041d07010305041c0c002804840c0d602280c0610000140c403a002503404080c40da910340980c10003071003035030b140e5401903000c1900120020540f4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 129030584 1250 129029334 129029339
    0xc020a0b010b0705010507031a040207080c0115080d0201050105011b0c030c090207060f060303170703090b01091b02121603090b0703050405011107030b0402040506010309140601050f09160e0307 85
    0x51003080c02e07800010201030020341c0009114080c401c00350040080d140034001d107000c038020b0b00100c80c10440341500c2541d00150110800214178101e0780240d5008000303200450100010074a54800d52180050324003441140600382c62044c030070141070380c1050710742c148250079074075440000d41a2008120b8224003140c102001040014150800034100d000300565150441d01d8070505907070415440050450030040d00703200181d007010842c1042d40d0600380c598039681c0e500704210040c000d244005001000c2c004004540c03030400360492103401c40c1d01034854a400c20060b804036940c903501e944002c3c55100901c014919406c0d500542d0301a03038040d140c5200709039140c0e10710b901340b544132000490111320005410012940c11080343c04d007c521500c01340601310300e1900c03900350190004100a2045644500007201603000760b05c6103580300d40214130802000d940130078065866600b800303076a03c0b9210544103c0400e19003841c0651040d83c1e011602e00d404500314800361009460405020307498020000e01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 129031834 1250 129030584 129030593
    0x260d0f02090406080c01020f06010e01050108070203221a070f08030705091c0314071515150c03020c06070f060216021c021507051b0a08010f02090a0f030210030c020a 73
    0x407a07018041ea00c0151061703c0c9640000391820310400480303481e44c0c0003080100b002d2982003002a044880c2800c00c16015a150071040f801c0d4403030092101c82c0a00d896005100d04444509018140c07403460702880c160400d010424403460240303010080402000119200000300c1100185d40c0001c018113102d400c01c40c003500004c0c48490004404900c0d444094100e00074540c3c0000c510f400783c544840c1c0307a840c20040d9242c020303110070400c1e099864940c8814ac45104410070602c3c1400600c1c4101c82c81000600350440207040f00700d61401600188503c0d660304926180c942d0807180310550000c00303d0801016a5240d4000c2e4016180800d0220100121080580c0320080b8016a100366142c0303c0380c6540c030900c10056250844039100c00032800512005001500010720505030312501c0c0000309038080c1d4000014040c11080d0445842942002040c42098075260040c0554980803203a03000600d45420202144054070f100195020007100784110400703000358420b04940340c01d4415112240015142d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 129033084 1250 129031834 129031841
    0x329060f03102406030c120c020a24141003020108150607080301090501060c080405091503010f0e01060518040b0a0b0d0308091b030c0f01050c0601060c260d0f020904 73
    0x7182e8108402c0d80c3c016150703c0a440b5000d10140545080400c100c00406400400f00c003000440c540364150f40e1550005202d0081103064031041d80b1a0550380d65001c000e43c948600168070140b000c50502701002c0302c02c10708240003080d10400c407106420f06051310b10b07001181c00c1c180c082e0005800c130801044815554880b45e00500965004500440c0d4035403404000304200c2d44168411010413004180c400009401642210110350003200c26a03041d0f151103402c0c698512803a00910342c15841c06006c2c0c0f914008a8005601740030b034010007040141d60703420502030400b00702c4900c2c0700d01032541030000b8006460003981c0b075089038400d440040c81608580c00f2038041507400b9015001710b5000c5d4200f141030304c0b080014850140b0313044104500a102400403c0d5a200b07026040c41c410712140e28100803d0b441441a610000c8002d402c5a105595400c0d000d014001180000d030b0302c28000104041e002c0000810400707102c84a40685490304078100e00081c02000c0d42070525542503020001741c49140e84900 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 129034334 1250 129033084 129033101
    0xc170a170c041706010b040e19050702071a04030c0e09190302030d0501061803031d032b0206010f090f06050301021201050a0f2402070f0f0329060f0310 67
    0x11072a40d49600b0100700400c0f500308401000d1940e4400c00041c000d074010340d01075600301d46c0e20440480040d121a05035050b0048441080c0071940d1070b24081000c0558000380300d03000c85006081243c03681c41c81020302745140c400d900014010040604040041c000f20440305030b0f121f862001599007400034910012001242c04406a005038008034850300d94855500c10300b0300405c41810b04c080300c1044d121140c04202000e1101a041c07110b00c1c4c003004080000103044510a000c02001d442484403400484614000b0a80d0050703200707040d0300d00e6a0560740c000a15541698000c441c03c1c210180340c001d569000e800640660341c642500c5038030005140d1400d0000c1c11500045040e43d2a25606200078014481450760040c060b00c40c40c41d03010040484510071503101300021010121140c1010301c01607141600070f900c00c5115005880b00002c440704210036090550b482508440344029030b4801820750941400c402254082d510740120304a880c000b1010040729801600b6620081c04800400c000c981162 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 129035584 1250 129034334 129034351
    0x15270f030e090708091005060d170d02120405071e03062d0c030b040b0f0906060405030304030f0302010c0906080606090d0b0109020403170c030a08130c03030507060c0c170a17 77
    0xc0c0000d021043c040513406c9491a141001130345402000645900c003480c802916889001c20609030741c200031012503400313000307501c41995501340d0040e43c440303040d4044400359030500804802080000c02450120035000600301440316090650316100010800d0030f061001418035518600e481c0c2030201501490b0071880c000005450350700c1c082c064291385400303030054440c510f80310000905950300f20321078011442c1030b249a00382e90380f90390110b0854419600280e925200105000042014520345c40c078240d0f100354003d0003103000d000826203000b0081d0140c0c0010420703210000c1d400d4104040503220f0088000c16a04259040303440304c45070301d171003030300070400d01900020248117001c1140404100c24900c464220310b040109030700340e902c80c041c3c03003c10010000d21320701240f040107001710105551900b09013034a100325900d20f4080c1c00d91380642d0b0121080b50904144501d400e0203500602c5510341c00c80c02030031100051030445405640404a0300d024000f00401015441003146e142d64429001d8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 129036834 1250 129035584 129035597
    0x40e180d0e03061612020d0e010e0d1b02090a0209030307020a0602011b080f07031503050d020703150b150d06120c0501090b0301062c060715270f030e0907 68
    0x400e09140c2410300007440364400c80c001c00d5561350000c3c0d0101840c200c15941030401078030390810124040180510020081e903540c2080d0102c194060041141c0c2366240c0c41c0d45400050360745c031001c02c8018030806807001c0d41c89025080011001002500203040104d4001e040d82d250240c4c990018041404640000e001030f03540f6441d0140041010384030004905190030080c585103002c1d0f940b0516150010000010143c458801100e281d15843c4004061684501550314402a801c1c000f5650b4448ac40705543c100d04503140f600c280f140d10301c0b07440345140b4090f00c50040c105101c82400010382c0718915005800380da410000131652100d2200e840d44a2098501c001e4032450100010b14002158105443c0c207441000100070994200b00b13402c280070b1408001d0310440119940b03c00e0000381d20505603400041c001003074410806800e0304c1652106001a00b0807080700c50007204140d54500b0608030b07907000c51901040d0040355410030200d050302c1c428980b000b4458030080100e100c407081507444c2d00100d0311 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 129038084 1250 129036834 129036857
    0x21f0206010504140402040c1815081503100c051c0203150906030d0e0d1203020310151409030c040c0f0905030d0504030807060f060f050f0402030c040e180d 69
    0x141401554014201203c00340700d48400c1e41900000300401610003481580d07101030039818203000301358801840d122102c01c586001e80d258460460a04061a910300140381c180004002c9550300d9424480440003500130071265007101607500007401c0762207920f0144a0b0a002e800612141201429032a444000700981c9030700740180d01104120107001d910b07100340ba100c1c0801109490016102c05180c4c0c0520f401e03d00502c90b40f0209020405004000d442a02004091254550150000c2d03000d43d40001282840c135030b89188440c0300382094001400012015640541c584440d040035001550004061702c001620500000b0201c80103096244003043e111200e0101c03c42d000f0980c203004200c103601a0446042c60a0010064881e5000007070040001241d00c00c280001035118541980300380a04201d591b40b0741e145058840f0b00c40c828144565404042c00d00d441c1807034020b4030702400b580305071582001d04144800d084070000a2000018102c0c0060a451994080004c00010380180c1c4603482c2004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 129039334 1250 129038084 129038087
    0x602070503060f0402030307030c141b032a041a030f0706200c0603040f23250504020c10180605010503030a08040b180a0507080c010c0c05011803021f 66
    0x70044800072448030b04000258801000f190440d07980f4aca850a80e4401030700d46aa150401003907000c0c06481440118015180c082c4500498041c0c02c4007210803201c81b610800c0c2c0000030318003103095248078450310301ca80ea00300b541140e8100d80244507c2039a90401c64040b91403d1a00e09125199610208080000640140c083c24203412413015001c072806881c0c441c0b556904862107128040c620000018040c480c958041d4084254041e07951010140400e041c80107441c88050b00c103400340036000703403079000c4101e20070702094510a441043c0d171101d10b00800c205c000d400078a0711000f18000c4c8500480032140034031500c02910105a40200380800504090040f039038160012400b80d0700c1003003068a800c0d04003000e00c1d0312590100348289180d841c2117100656160040c0800c541d8071854a110040042c0480e030003040d5a04002281e54101d44e40c0700443c1d9501000b030b00640801e000701400d010320751040c00c885075090701c1600c00301e01c00d517130b0303940821500003001c140c185403864003407030300e02e20217 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 129040584 1250 129039334 129039343
    0x30f07030b01020a08092101090b04030f0f1407030c0b160e0d0807110307090e060a0f14010e070e06071b060e0f040518061602010b03060106080f090708070602070503 73
    0x30784003840140104006a40c03404003070300c101080c2c0c900c1041d2168882215101c0302c5481e030512680b0070020f000e4000070349001405101c055808502090600078561180342c410b103248030880150765903400c00f440443c2e10705d2210b680100000d80c03c1104840006020951084010b405184112040018400c1d0090000c000303401e08904140300d107030b1180403000821100010b40760403503041880b081c2148047d030000782c50007440354848000316080031200d060b603200126030700d40f01d548242e105212031207a90003072030b04480e040c00c06028030001c05e00040c05041c4c0c0150720740f80d0240007400c14422125a0000280d4640c000803401c440300b403203000c005d902c0341301d0302c0726404014400c2e420b000003c072002a002800b40c1c03501e450000d00035a0790340005150703841461448090400c481003541c00504005c02107510401c5245820b101543c24001a0303800e03030800051743c50480701c903a0345080040d01c40428008081d0346c040c0a4540902c0b80040c0400e000381e0a2012030300824468000b001c1071440d180038107050 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 129041834 1250 129040584 129040601
    0x11070201140d15061704080406030222060e04050105190303080c040f0b0720030303070507060902060a030603050616020604030c06091a090d020f07270e060a050c0a02071e05030102030f0703 83
    0x1450950070906c40001c607640140e40035900c003070a0168072118803480361880a940409407022421a600c40060280d4120440c452404021341d8184260383c0c03a9014095444418140201c440d00461401c1010a00c929070403034000c080c517840286096602d100680c10201c1680100ea10000002401820088543d2504007492900000c1c03188a404500002c0d844e400000e0030b410500000182240410280b81d20964000343c1c0240200e80390301080c403005005105030701045504d0f22803030001c201c40c1640c5004510400f111075006012070342d0f555504a5440c05a0310003261940d84030440d140c001003205440e1201d4003043d641203006442c0ca282c80b05c0c40c040000c0046010744d0002d41a810b031369540402c0d401d06580c03414820300700c00c0d500c40c001d004035400c070b00030f814029a141c524000300105010904c0e5000d8240c448050010351900c611041d82d030311407200098096840181c04101c0c061007000c6050081b00000c541c101e602e0b81d280302013400c0e0b0f4011140d000d15000e120013080032294051080381e54 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 129043084 1250 129041834 129041867
    0xb090109080d031b170f060103060803030f0108010c1b06090f0203100b09060409111002190503130f061e110307140f0604020618030703020d050114060411070201140d1506 75
    0x303480400d41c4080d017107080003030111820840e2600000c2c480f40d0203034000130000e08529040320768030b10704011050b102e514203000304c1c203d55007410915018184500f601d00e11402101c45444141001540d40e24018015008211130074540040580056503050266001125100c0e0020480c42c0c040d0b81000491440108424481d500e41005400415100d0b84134054402050342c126014940c4103a050b07140c070001441c10300c090384110b410b80040000c08009480c400041d045014111622044043c0d103002c0305001c0c03040025180540000030595681e4112455071280c280011100d807410052411603004c0c5c00700f55803403a048241c1c510078460400415005000b00c0001d0419030609900003560351040f440500c01300b804c00e11203445169400d002c41c1000350350003019000e00d0040d84c51702c0c5019042c00320003440d060030440e0004220b41481e0045562030400150000e1130038105500641d14034001c10b03404015030f8020b00001e08078250a10600b09e08281460041080300d1501e4001408031000701d40948 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 129044334 1250 129043084 129043097
    0x140f030f03040504150305010903020a0c090c08070c0317011e0b0301030209040206030a0608100c080601030c020d0c06061a1b03070206042c04060b031908040b090109080d031b 77
    0x1940d0004400e480c1501e0341104c011440400e408414030784132030300b9000a4110b510741604101010b80014002000c24400d144c03000b2403d030b84418003400c80b000b500820000c5002031000420032413180c0c8145625034880d081c071400c201800482109004001d800507070390f030200c0709000b0f1403411010500c500105130700c1e1040b524640c115804218030030009800240034050100101d421003417250045d07000381c0582c1c02140d4401c0080f03040b00000d08001c0c11204040340c6158041842d80d4401d00075034115100780d40003401c0506040038211074510b4001400e4079403030b65492010402441a100348040c0803200d030400b6459080c14082d440d0341c42d80030f0b241c160302540b08100f0400140c039014280d80441e11482c0302d038440c540d0b00c2880d4810410160300d41840c0001c5008c02c1008200841c2c1c85800c20100a0307080b1782503035200540003c408002c085002c0c0c000074042c0810000140100010301c032080c0e0600d81106520f5984e562a450100003a45800110b500d40b42c0f15140220080900300c0e5240080c0f1744803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 129045584 1250 129044334 129044353
    0x706091e050108040515090a031709060403180b1b0c012c0d06020c0a051903120b360606040e070e150403060509060c030103051906060b0301140f03 65
    0x918090030348645810b0110f6140003030140b20003441444144811480108200c0ca48101c54589510703c01c40114041601703248101328500031018218891815900140000e844a40b0b050b20141141a00040e800107031050108020340f0207400703810904090341c14601a0000c94140f2802c0c0700d603200c80c0c241008051080710410003a214802d1012543c3c6146100307000d07602102140080d02a40d4001e1702407800002e20380c0c651040042d070407c100c1d0080007a1045010703034403811100342e1910030703019001a9100a014006a105900540003200004c000c00c000380400e503502d64200c0880248140319102c0c1e41d0a00000f4800a01c80c1544820229074040c9001e0a28500d008003c8000d001355080041e45402d00c40d0f25141c03280c00c041803080d2122119115540c925107100900011101e0603403500a600120311a24401d1003070781e050b82e03031020140c0f0301c982a1280c00c00071051036800540c2c0c41e5443e040c0006801e0b0710b5000a40c06041611005c1241104003424019011801c058050107135000b14540e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 129046834 1250 129045584 129045629
    0x809120f030d02070816080d0f0c140310080a0b04062706050405120409020a11060601050a0c1704031505090c01022d1605090a050106090303050c030c0708070609 71
    0x1c0303a0b0807240000006031240b1281c108000b00380031b12203140c0b03403901c2074456010a000a0001512980d4003640041c810720030007038124800d0760400307500398010544040da4080803002c0035010f0356201903606040341130241c2e6091020710302165641c01743d03040d80c41c0d4400c0c00140a0a405006540a20f1040c001c8801610100d89008075022500181c083c80d030707035008a02000001e2102558109040f850561166240c0d0441802980800094030101e8624507030030f070070072102040840c4201d00585540d41450100e900903100071863761000c89460031100d00e000f80300c9044c940588003035030182d4049101d035010750304c0b8101100d0000e0036016456201c0c0340f8826240c0c0e400141d4403201d00d0032a04040c41e00d840352482070400852107540e10090f0040e0041c010111809001200840e1002c680d064641e44800c0f5040c804c645007030003480c001860030082030003c00d0148000f41132499426088030b1620300c004000e80e0600301260459a007a400c000f0003086030b10b6000c0c0c60074007c3c02b13030360201c03070318100100c0f07403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 129048084 1250 129046834 129046837
    0x1200604030f1b0503130807050d06050601140a1206140a06140706110703020601050105040305100c05070605040506010f1d0615040806190f111e160809120f03 70
    0x80c10405266690715480c0d124000400e6000d1500c2060443c20307810340740450322600300c010a10172103611070304005080c2c000003c0010441c0c0340580101c0d401e030140c0c2c480801400008181d0750500407a010440900d0840400500500100d80d23907040120074502c0e040019038427540d000e00404580748280a44a68071b580c80401280c041e070920941781c070720078901c1960a004082c2d015213402d16140c00300b40c0310040540103056540c425401e541d0640c1e281c0005541c1e50140d07010141044e804140040391740600340c0d020805020f503500b005400c1841680c8c8050903280100d4040700d041d00050300401648891f00c0d5040040c180f940c1c140c4585000541240010b0000104803500c02c8019288054610b0a410704a4004c0d00ca5070081c1c0b02c45140064200851f14006100101514680014130103e60714034880c2c40e804801c068901880e100c00a502c0f8001e1000c03030501ca2858040030030080d42d00002200300d00c50341504c0703a18001d44840702ea9081044825001c1038490207500f0080308600702110220 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 129049334 1250 129048084 129048091
    0x9012301030b0103060b0d0203150d1a090a02120f06090d050702011b0b010305070e06030102120403030f0e010e0f0f06041e03050d110405190b03070c0512030c09012006 74
    0x10740050250300b40340040b405420994403400728184001000959040a5001141316900602d5804402c0c44070006019000c0c00d94400940034804811042448080000095401c410f000c1d0850b5502c203c00d40006409407081c41c0c82e0841c035800600c80c0c4640f00001e110007035102442902428100070721840207001ca101e046030003030401444041c4004066003501401031041d41001d814a415071710dd150442da501064000c408927865003800140c4940b405008031242c3d00038460040740b03079071a691303030a8001d094800c0c03a25401c40d4640c0b080103d0740c082480340c040d280c50881c00404401484007016810801489003040140d0813140400000c1203100441e0226601100109040c500490400702c034580107820b20820840e0601907003003006d282040140040c1e8800b00e5503101c40041c2d42005014440381d6201c2c01a00705801e1001641141c061034501c48194010025607031042d445140c0e200306544111007a04d1111001b00b020350309075921191a11410003c50900c0750902c00b0846800c0e500d20005 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 129050584 1250 129049334 129049337
    0x61b030504080604030c0209010f0f060e04020d240906051c02190f03020913150506060d060e041a04050c130209030d110d021902130b030303010f0509012301 69
    0x1544044109031052040380c004142001c156480b80c00c1c2480e00820015001106a10451502002040d5103205124800844085084a95070580b9000d810743e500030b50081c40c41d5104c0d07030074015032061903014000d140318400410450031000803d06040c0360741c8803081d00052101c41c50b044080c001612001801c030050884103008500b411070307c2c400a07003511720f003c3c0a40d5643c1070010340002d500d0100d90b0300c81c0a42c0e10841e22403000b55903400061035080034065010f0301101c02100c081c0d881040d180c9c00940c010760b018002d83e1404030401003401c1564040d902c0101780d44071503c100402d103c42c040e04000402405940640300741040e0f11603c0d40c6032105100284a5071940001e0300e82d246c01507044030310a41026098407094002d5200c06000340c001c054040c4514010011aa001c0f1840400c220311001680d804038102c4840503024051148074050031800c04030b03034452121742182c0c0c08002840c003d1040072102a102410103091100118040c1d01c0341d20599411190f100c3d18009010035171400400a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 129051834 1250 129050584 129050627
    0xc0309060906091305061c03020d0c02010e03070b03060405010902090303030411010c02130903110106061b1406090601060f2c04090602031f12050705130f06120b09010606 75
    0x40001655500c00d425101d0350200b041010351301d0300a001d4021600c9071504480b0a0040113101e02c01e4004c01c0803082001300103030000c08010028500a01210405a0040c900015100201000309142045c1500304a0202402008000f00b5140500906024001d40c42043d400d0600b018003082e5a4080608002d0000307400c80d00c1110315903c24100c112900350020422250011001a00e00040800c28070640010740048203000c001d0f00140500d034219003440e620015003050512140c4000300500c078007142c0300349502d51560080042044498041c0c00d011020b40388551405001500e44106107a08000b801000303804214011040c800705c40120f00d8180c042541110100300160062010b0341006040034808010300c4100249455203503010200c07600b400301142e49a404404084282201c0200f055102000510090a00540100d00028050004034800745001421401e44115810803500303030700c0b8504034a050004480d14039802c0122180200401418400010242e03100f005076030060200 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 129053084 1250 129051834 129051847
    0x70512030702011803050c011404020f060f070501062d06090504110712030c03140903030705160611072307061803081216110d03230f0406050109020c030906 69
    0x13034200b940002a49961202c3d0142645800b0300305410a5a41d940707951b02e088141c2e440d00e49034210290083c0d07001000401b00d42c82e00010003000e0761103106405c0302d11030180070600001c0c2d402d02070701000c0c00c4d003110584001d02040e030303034840d81da034060000200c100701c0b80c07104010094000e042c4609a60f4107880104400080d00340c545002d11031b012005240741001c03042e042c015649940708035004002d0380d5052020700c83c800000c031502101030340d4601d0640c20400100b5000c0b40103400400c902c58201550480740c14550311001d0482d20540c026092203003002540a04008801c213207c0c0c1c1c5841c40140e0841d404205510743c66481801c1d00604090012000c0d1061054505504032802103521541440d0b807241405440500814103170749501c0419820010fa0013024015400010642403483c0144007000240904074054102c64401d4001d0b0316071440200c1084032821170803031180a2011403010b0130b0400341b42036406c03194164045e410481c41440740c10800040801210940b40d03046071519210704 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 129054334 1250 129053084 129053087
    0x90f010303200d03060807050402070201020c04151203090602010c030e0c010c08190e040e010506060f0313080a0807083106020405090115020606030111070f15110705120705120307 79
    0x405410a10710503c541c094200c003060707060308028299000d007804d4a05003582c64052000b60b001c1e000000303025801c0101c00c0174882c18143d002c0e00c68904031140c0c1900480d514413068811982c19842540002c40300b020038018660240580e003c00a210310b420480c061140c95101c2c0c980b40380310401410810841110b106220080080c0c0d05010b201e44117003040840c02003805066101420000742c012400c0032980151400184502e92040d00042d145515000c0b5503003c4042c0c0382c2c0024042c030458000f0103003c401180c80400600400e1f80507850744902414106805450560020310400c44510010b0b5195441707058602043c1d55101190f02902c0d40034003620300350010f03000703a40009070080311100c000101c5460f0394400c50504030840d0282c07041d0f0345a00050509031015002e125203500320412041001421030800562580c0c010b00c0391480b04e00006800c50182c07100105002c2828001065043c1409018011030303c04040340c0e40e445150000780d40d2003c0d2200c191114902da0b0300c00100004040d107 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 129055584 1250 129054334 129054377
    0xf0a030305070510060603060f05090403080f090f0d20010504110d061407050703080901020901051c0b030703080d060617060613030c080a030e0d02032e0e0109020f090f010303 77
    0x12561007601740001502e03000e00a0040c0024881da8070402c4a6420008150400850980c02140c05568900701c1c0c0e51001404500840041d02420340c074465019a10848001401006409070307183d550700e8840107a140b03048500c04a41c900c9480b050345880305000002c0e82c0b07520001082e21041c3d03803100c403a14907070500c28010f060f0070b00784101822203101000340090b440303002801d841d0b00c29140c0b919242c0390010b0980c200d00420503500e000c20010800f101d1002401504c0b0303085d016154901160440344603000c01d00781907450b84100d031200c03c00708013450600080d00030040941101e290145440e8003018850303140050241034503000c0d540001d0500c00700c1114400940c040d6401245a401244d60b61100550f1140d15030300640004903c0c0e00c021815282c42c030300c0f81c12415001002415500c1e1201c0410f92031184180003804544101020035031140914001c880c01c1c10841000050076034650300501100c0d91460214502c034444000402c025a00f0f070389410b6055941500d024203550306e0410b86042031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 129056834 1250 129055584 129055603
    0x201120e0303010e06090705031303050f0d0e07030c12031d06041d100905011203030c1b050309031203010303140705070909140c0f0102030d020c0106031202030c06060f0a0303050705 80
    0x10301000001003207002001139141c0c0144010781e441d06040d6141d8038200e40d1404142e82400000201e0301e01c480c0424454405041c808000521035880d10b6807900b004811a064640b119031550401401007040c481c1111040340184600c42602d00c2c078440940d402841009840086240304004030b45c48100c40e166801554003900381e4036040f0031203000907111815405002c403083c52001c8161100491403074040d01909040712244a44101e00c181c80e9601031f800751126203070203000c101c9940380c0c40d20342042051030310b440180100e0241d9551321400d01414284188003000d450450010401080080d9120341c1103841c02e2507600030b8680f6070780e0038609a03003056030550104081c1414000c021050022800e001592a10210300f140c09040150003030040014107941100d0141e00144061400380c100345c2c004003c001c06c090000a1460f0b1265103102c0c4460328000800d0050303102103459100d0402c00c00c002c80d00140201ca07184e41d908a01400110342d03840c5404010204500450f81104122040000025 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 129058084 1250 129056834 129056861
    0xc160503281a0c0d060b07020a03020d02033309030c061303090302030307031d01020a020906040b03071a0a02150105130c020a02120f0705041103040201080601120207060518010b01020703020112 85
    0x9041c00d010543e0185074000500004240b45402400076002d000030b03007122406540586050800c5155800300b01854040b940c090341c050007007402046540041c0c2050811441e013103100c111503407000b0304858801c0403004080f00c20a6000f040070007074100e000241300741d1040f000d400ba22140725051a04a856a401c4d51000703401d40f0010840d02c08040c0c001e00400da64045040e65004d118061400490b80d03801d81d010701941003078650700403c0c0c8905041d00840302850015041b1501555500e55440480c58180012900e90401213910020254140320300e4040100c1104400340c15410040040c41012000e006040100c0d501c00d26020010300a1004958007a0020881c007002c0402840407604c551401100010a004441c000b05161416103e801020002d145d8107600755a6942d005446240000d003501c0e051058120140b0120b070080e000a220fa944a41c201140c58140700e00800f068140c505070b0030341140d050902c0c0c2c13071107a40c2c00039504080380e4092900c41360003071188803460020f0044505244 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 129059334 1250 129058084 129058133
    0xa0f0e0411031b01030e01060f12120c0305030a021c091101030507020106030b04023313050a060827010e011e110a1d060c16050328 58
    0x2109844244000d00c00c0d4040c1c0380c05401c81074200d040548070f81c0c403e100041e01d00d00d10841103010f948698014001e80442c0310001400e242c075990140110712039a030018402c1d01d0a070b9084002c0021881d0745204c81c01490a001c03041240b0b0742d07401303040d5003c010418001d0350b60106400054103c8e0b1602002604424401001500e10505114001d2984104050b000c80e00f80004038880c40d05c140310f800c04984e0801041007464032107500300602c207411060219900042c1c43c0c0243d940d000c140d00749a40c0c40440801c1113035120030f03243c114550b504403035015a100b080001c100b0403800f0f40040700b0507030005044030b007075900009c1b040b00d0859814646542000c0340d0f2030a0001c4145010560102c41c180c50001e90b6122004030fa03a2514007075801c0f02d101c0c150341100a006603c40745016090031541c802d2800d21604540c010040441d110780c02814524007203074441648642e40502c10380c1c0070409410f00364054010805001d01e07206002c126800c800e6210104600d401d4148510b000c0e01880500384180c41c1d5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 129060584 1250 129059334 129059339
    0x70203030705090f1804140c060703030917040605030a0b030c0108040209040f211403070f080c0706150e0708071e0c12020601180614270406020c010c02010603020a140a0f 75
    0x2c0c0c0317100846d8100e0341c800e500c00c0d921040440005044c10301120040c1034900c0c01400799802c90240841c1d020880d0040d0b8008804085903818801500240074240d8a1540340e2138429072083c06c0e079142c0200e0b80d01a4112201d01082030b41d03c036010650183c0c041e40c0000aa4845242108080442210145c90542c10340361842e0042004020862168821b070394881c00c1c0c40c020b940c04203040c48140c4244020607222120346403964000d0701a01e40c048440140e442c1449401d89940081d44e51400019074184d415203400c1c4202640c60b00b1041c0c001d142403401110a15281d00c02422900380212880400c000c81409061424450b461a5900d00c2d0701c459603054210742c47c00081e6a6210070700a0f001588001d140c060900201482010102c503e2408070440c0f1010a10602c070b00481c21030b448a01c22004500c00d80075564042e041e041c02036118640041e81d07090500d011034212110b85030000116411315408002598030346012605503030301402c112104403890400260290910f9012030303212491400c00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 129061834 1250 129060584 129060619
    0x30e100510050120010c020c010908060910090c21140303040c03060b06040914010801050f040b1f09021303110105130e0702010209120109020a050a1508101e090b030303070203030705090f 82
    0x1048d50701d1030f0030f8a492002907200d0388203540b2071000302c0e200441d6a10107040a08602980c5c0c00441c0020b002e201002031306915001c43d45036402403500c20010740030590140c6000c01c0301400b000005401d455000c4c41c1582019134807c07442c0140d03448007802098545401d80656a13510b41103400512040c3d104026502e115800b10700161003d10641c40e0719440d0000290340005810700340d078481c03030348440d03d050f0554511b6442605001c04800d005400740c44494003062003072891004010600046030820b03011495842d0038501c45500701d1400b03041003428005010761240c0351207450182d60000d455a1400d03a50b01070300300e00a0140d1180d081d4810540c4180100c0640194400310500d802641c1808645443c1c0d004e000c1c1e024214414001d80e082c200b880d0803c00d034410301c8142d4120680350100e441c260303500d000e051210404010342d0105543c604a00300100c840c54440c115070060264065419480c0a0201035140d02004080d5414003e0014900d40a40c2d0341444081c00003400510403124042c04994 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 129063084 1250 129061834 129061843
    0xc0a20030d090c0801050601020102120c16150509061617041106031008100b060a0804020f1e120c0105040b0313050a0807031b1e060f020406030e100510050120010c02 73
    0x70700c0a44d54681000704010303502c18021558079803141e01e6905c901e0b4072408143c103103660010ba11001000c5000d05614000b079800520500a48440e9a0106260900e20b40342e43c182070002c1d01001c94091326194a024481d040f8140300144d00d006680d900c0f031581e4504141140341803061900c0c0e80840e00104020701c200d10148500c041e580300b0f00494a04c1c01940c030402d01100c030710499855100d030007800010b0007a80304111059000d4405800aa0a0310111020500c0000c0d6610050a869091000d07101c003410458210102c6807484c00052090326003540000e000391149009503080410000000317074186c0080c0c1013080c0034035408030440d000401c040c14086c0203034100003000c40c00a480c41e0408804079541a507000000c81c1c208110700042105481d0402104105c40022642c0316154038840041c204035101034402002a03407408201d2042c0607a01c3e60416007520529490303540390070180082d0702c1415254005880c420f0038a010075804521210758200d02d205030304980c941c200380c54500001d50100c0d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 129064334 1250 129063084 129063089
    0x61b09081e01060b0a030905070608060901050603180d050406030c18090b06041508010504060618050402030601020a050106030c06080f04030e061305030318010e03010e0a06050717010e010e0c0a20030d090c 90
    0x41c0e55270952214011218810141c41d0980c0c84a00100180708600c0c00600654115a0114054000c5000401804d0820390684148000f0a0f4040b804211141d05070286554030582071400d40b1005075000752549107440e65010380a0300070365560616005456883c1183c0c090700c50044e03004200d0700c560100400600c0c1c2401a20300071820040c002410a004a101c01c0300c9105200000c1c00e11420b00302031000940000b04564110701c5160030703640100700284210784c080d43c041c09030f0700b00f07840c20001e0190075040060a03010500c2c4101c0d0800001c01d0340031861817088001115480d60714a5041031041510700349030001c1e6414000000c0d45c0c090140410840c14180e042a200d0b2040c0300c411804241c03c03201c0a031030464a941110004400080c0d099102d0769001e030030360411042c109020300490301588400d070801c480e4006400c0050122140c9866069440030203c440c1c039160100c44400101000c1e042d610742c55040a19408c01d0210740814400e44209600c40f8400300325812240c02c2ca00010341907407 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 129065584 1250 129064334 129064343
    0xa0e0d1b06050304080a121104080319020a030c031d1f08010b040609210605010f081005041a060411180112021204020108040503040302030a061b09081e01060b0a0309 73
    0x580c00600c0a000354240c034421a0032071611410018002810f0b180380706c9a503028000103590380301c281b056480d4100036102801200000355120400c07030524480c0e5801006120007550702c0541c1c42000a5409116250100e0f858a4003203040b0300e03810790901c0001002c40800703601c040d8116000703040f0004840b41c50080300860b614411141d07680c66426001d03109901407840080d0000d04244510000005520750285100641e001c1c0100c042d10f0350800c4640a810140500400700410400e0030010401d618000404120401003402d0036560001210540303500f403100c551918000514541c2d0729032140c0002000d82d0812903485010340c0c00c02c800401d41c17205160108490001c3c80140880034800d803100c1e840100980c24207501c2c0d0360015209141c00520868080c8800c00012005072404e0245500704c42c1710f1040442d8070303221080030024052080807030700b0800030908800c10400e48001811000c1c0200404050050005050524054540c6400249a400c0c000420b082d1aa90690213404500e014 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 129066834 1250 129065584 129065633
    0xa020304061a150f090d0c0519081c051201031b060c2d050f070f14010e06030c071407051002030f04150c020d060f0608010b0d06020a0e0d 61
    0x2000040016000b0b00c4100e160003014501912400c10300c144028210300f03050710100342c00c01d1440c000150300010909811281f0031000c500030415400c0c24040d01590250090085d01c0d401e0904000c00c2e5941ca10041444c010700c00e01302804500b41c01081155a0701d00c4102c4400202d6849091650608100c0f120300318180030414030004807944a5148004801d9012000c0140030418800403000900481785d5812140a4007a144002480811542c1200140107000d042e00ca0b1511001500002c05039120741c0e02901c00041010343d9030f900c000d041070040f000b20fa05a44035190007022141c10f01075800010680281200051000b070720000743c84040341c1003110740c0389200760280d40481c0caa0041406aa405400901080c010b661900d4040505041d492030035100c900d1982d000907040d00d600030000d070f48407a5110301c104a00c062a00585019003880c1c0c0091009490000201d1500c02c106840034011540c0403810ba482d0303078800c00d008420030038010000c0c02c2d00d0004d42007030b0131000036440484220000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 129068084 1250 129066834 129066851
    0xd120f030c02030d050403090b040608010602061806130c080a0c0503060c2106040f050a0902040c05030106020a060209030f010c1706090c0306040c02010f0606090603060e1308160b0a02030406 84
    0x120780951841507030254091070419030a100d150b0041c1c00060021010f1004e50000800c1e0581c6410240c0001d010341e40d03506007154503010003c0e040201c00350a8052801140351401c0d03840c1000142590403e000194128050142d82000306407101c29801103c840d0061240c4074043c07200589410b1305480040b01900d0307983c0c403001c50243c0395104035230901c41486501400c00307a240c1114015a507000314080d0010540c801144540d804440c0200c03448484a60b0329003c100c1541454425610b8004060815238519410800d029581e88820f98000f4840b50300044c4030100c1c0c0c3c0301445001d2100c00b5080013401051081000580814482c00e240d203901d61140d4009034151405441e100d00580b00350803000d165444040601000d4031040c101c41d001e541d00c40c0c0e01c10350001214460350b0010a5281d4400d59041c2c00c00303000034261750309035100d44034105c0da50302441501909854880c03005944070504a035144040000131079044454007001d055860301a040043c03075001c2e5001184904e209007003c20181c00b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 129069334 1250 129068084 129068087
    0x903081c050604090209060607060f022a010e1f06030203070b07020909010c0507020907051b0606130e0325060203100f0501020a12081e04050307051501080a020d02040b0d120f 77
    0x800c0d4113000b81d404000362002c1072950410000800d41035029203c04980c80b81c50303038200d030241c0c2e12006089400f800c3c0320340300b0b000740b51840b1001c0c07200d00c601c1e0009001d0360010281c0b007591040c14061501030b090504000c1c1d00004101d40c001e000135940034040e10301c01c3d661400b00f010725811a1200342e0240683d0800140c40400600c510400c81e4120384403142040f445030240011510018034000034000d0410440d19540d41c005c0380e4222519050004140c18030302041030001c021540c0c80d20700001c81c10200440c00d0108003100f03590113200f01200d11b0501114040140b1801b03111817401030174040c4000280081800306030494000d5485d14504105041e603500012039494005000141c081c000c402003900c0054400c0380481d420241c03045c1c130000c10200c5401d0b01c211940701514201e0b05c030341c400182003080007014464810400d182d80136100da07540c5440100b036103604154038002d10414408141c5011035840744e000e030403000800303092042c0034010340ca4031400100304800140003003600c4440030b000c103e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 129070584 1250 129069334 129069341
    0x30605070206071e050307090503151501090f0513060f06031a0a29130b0705240106030f021b0a0c0927050708030f0d0507020601030209010b0a0903081c050604 70
    0x1480b010356241c254072400101260785d5040588032504200040780002030310381c1d0030028690808410a0850b52501301b05660b16580000000c0f002e040c480b0703443c02040001c250705c0740700d001c45009039620b40c040341104601d000148031a802041d0304030820704000c10056856402031020305a201e0806038101c0f9100100101c5030b07200d205210405050140040103d5203072031807070912030002c0304074038180744140316a801e08240503000750040c03000229010080c0141003100c042c0488065101c8a07100c13005c000640d182550500444040c1a1200c0c2d811218842e40d50407240b0703040342000641402040e5041803a21404d80140076981e00340c2c0072201007503041d8248034101941c00070404021100e00ea100d41160403842c00d010a42d101d0240302030008542c0400c0c80241417600c0d160b225281d84400c0010701d007040b65409001d02086511210047c001602c2d61032140f41903d22484400d0380b01c900100702190b425426410051404c180401c401200702440c03c000018061400014021951001c2c02d0200b01c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 129071834 1250 129070584 129070607
    0x30212030408030610020a02062709090a030c050f06040b07021c1209020105091e030709050105030a0201030902190b0a020706020307020a0504020304020d0b0127020310140d020a03060507020607 85
    0x100c440800200700c4c1481c00c0b9183e40c0c00d80d0703c1401510314080407500084d204e0307000702071200e0349504c452a2924071082c42043c0c0a0445500712440032040c105681e80680d039243c090001001d0091000c11501400f10401071200d80c04142000c4a48038503007450304240d6103801b80c80b103501500c40da01e000d115040408084940c8088907956081000d0303140700710180503110b005000d80c140034003080b8800041e2180b41503800782c407840300000502c01e0a00c4080c1031030b14002d980020a15840e1000500041d0307070124650b00f600fa02440d000c10840094000504e80e1760480c0303484400240103100025800e0084c2000d41503c010603026540c000399250026071b243d106071036000303602a2401500340a1450702e41d002c8c6402c0390000d0000382208080340c0c0c1c1d00304104001e030406001e030810034980480c100c07044110340040c1c013240e500950560401d00c8203000c0c00b100034040d00e80c022000010035002034550a81c041821900103091440c440e0780c0f4200b01004040c00c2d52084018082e40d07000904103030040c90304800 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 129073084 1250 129071834 129071843
    0x6150112050c0d11070308150d0507140a0b030108030f0306040f021902010e0708060a021b030a120501060504180504030e0310090204060b03090706110106031202060f0105010305060a120f06090b040302120304 91
    0x160745862011004034011811541d01c140310000409c04203904201d0100a00782800862a821020310100310704c2035401d41c4510030a5204000510030b20401100703076540341d09802ca400c2c3c1c80c0d498200004003c2d008607402151070510115801115018800c482810921660000c00120030002030050300c8510501414040d0307440400800d4041c503069000f002445000040312680048812450b81194080407449001929001a0040040c1984591801004541806171400e0b26180300c0e4500402c00901e11015a50384400040a00d4007446c078841c0005001010b54003904100c8201c0760040010250613401140341c9003002c11400c5642c1d080701e0143c08080b000f0011076207406000c803082031440308419415500c41600000045403c050a11140c0c402c0d00544030525080c110b041a0800590000c0e0400d8280b505005298079010414001d030b880d1428041c40301810b6013080060034061080090945142032144818010440040c1d03029502c40d1f826949030451584116640f0301064801a0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 129074334 1250 129073084 129073097
    0x16090b0310120221070f1e0b0c070305010f0f110c03090d0f02060403030f080723250f0b070201051509130c080303090705010c0506150112050c0d110703 67
    0x1207510318900395250142c2c802804503220b402c03c02e081000800c100d50113820203502204040c064641e09854040192001440301e061001c22401e070804c42c07004a00c11603000c044001074003e03050707030140040805903400000078002c1c2c8081c4602c003801000e4004c1c01c107251038070f0003081c90020001d0000321070304c1071400c170700850800310a503040220500d072100040341c0110710782c0d1507000161211809400214001e8845510b05145410040c110010081c81d101c200078400e840c161001c00c80c100c1007400d220b500c0d1103003510b500485c0c2d001c0f103640e8810880040c00b60140e03210300042148900066807064401c2c01d81c520326407100c04051303090300e50580e00340012410b10f80d550141802c02d004203940c00b9403000c1950b80711000a840d2042071084541004015810003c1000b0b42d40c03034104201700040200703292104140001d42c842070b0319580050f1100b1000310080c0da00c601240c2c82010b1000b4000c5415004018074101050034075120340c000382d01c285001c1e00b09902140d1304410310060743c0c80650140c4030171 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 129075584 1250 129074334 129074339
    0x5040203060403140705010c05031504140a050c0d0e07090b03061014010311030f0105010908030a05030f07030b06040e06010f05090f01030903120f09141f020a051216090b0310 77
    0x35100b65210981080a0040c05d0105c880800c100f4020149104910780b2000d5481c109543e500b00414007000f41140034078284043c08060301604022203920400003840001c82e600d0300d002c2251584210070240d44401d0500820b40d130789900110b280401c5840201b0708112000146d000e06031034200440b43c0102801c07140d1410440100420380303203030694105140001c0c002885c082030391442d80080c0c40c40050510101d00621003540c210304e0320030146c51480c1c02581002c5c0e40c000014002d01c401007800b4000701d1074401260015000350058810004000d002640356030f16221f8030051a201107a605000995105000b14940e000c0c1d0100d0f1012000506580c8140d25100300640c05410820801ca08209801144040140707242c85030700c0c00b1000a0300c001c2544421070410700e003c1602e0f142c0810440d0065840d200b141c000d95882c440001382003401c01358035242c0c10b24083e20f050003112159040340c48510100b013035805c040c4842044094281d00c9140b075494680e1314190b86400200c69021800d228484103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 129076834 1250 129075584 129075587
    0x90703030f03020d06091b0206011a1312030f0806190902130b03090705040605030309030727050c0405031603032a0f11011e081801020c010e030c010f05040203060403 73
    0x35a080d500301e801c026150404030b0140c43c1c102c0f43d1aa1004515980d1021780d00c031180e0403568105c08640992000f00000d50400d40201302c00b04059060641003480050502c800580c50b124000042411000600d607103034090501801e8015000030441c00522640d002840d1032030842d242c7c8945504104200710010b0410000c04002e500c5110041201d03615500002144160f80000f10711900c1488042c0070b04030b1804050009548281c0c001511981061001ca000307a203000588100b15000300310942d150501c80182d03003072907100351560550b00c2400d0408000c0e42c1c51703a860042003118000c5c0c0458aa0304c9100c411401c55034101c0c0070050002c0c0c08802d03941036100807820001010404d004800c194100d0a60b01d1000072000e4210407512a61030420340b409540c0c100314202440760886d134014500800c001d000400c0070400600c6031406001d00c52111010080075410b2750000b6155500070443c8140114000390741c0d070088241815258209000e004400801c2d000d42030003a076000e0010085030703c4e9690f0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 129078084 1250 129076834 129076847
    0x6090f01081908130306020a02010f0612231b010906021f02180d140105060a12081c0509010911010f0e060a1803030819090f020d060609090803091509070303 69
    0x2000e80300f0503024400e2a001c84041c40050f8015407089000694403200144040d0079980282c00002607545044804c00003092062400482c20b40d20150500313020a1110303500120355000380c6810103611681c414541101001034410000d80d03000d0300c542c0e48a40d41c60408036518445001e40c4d07220710004143c0a2506c0c0340e00d40140030782d00b59501d81401c44004400c080740181100140c1550031030f650021100c1c0c1c8080a00c1050340002c8242d071403851160405e01511003041d10040300030403590000400340c80581c1e55a10f40c0c0b0002d8000142070210742400c0c202c031070107003400c040140d50009044088e810300e036001d190800c050075000d8461500c0c0ca590741c01044007e03080303010213905004030006e5407804401200d0200c409140300751108101e6007414815040d002d070204000d0301485107002510000300740820084500b2946c102d4081c600b0007607620348000900402d90085c480c0e141002140420403034540041d51060902c842142c0e030b68240000600340c031b80e609460300f500e55001903a041c00400c3c403502 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 129079334 1250 129078084 129078133
    0x90c0703030b031f060905060907020717010f050405030a02010f020c07050f0f090907170d050f03100b030a0608010b040c08010b07050f0d05090118150507050c130506090f0108 77
    0x10181d9908030703106040b400070301403201d1112a004d903507000140030301d042502c140d43e00504151030240340b9251024011750b517a8158018034001e042c9941340905881801d401c8003200181c010020300c404c0c1043c0c0b0748107550f1b412401003180954244800d2a0302104107100b525331003400f081c0105800342c42c0000380141d1714400030480b50040004456040c00d511500521030148901000810290b8509442c000060240c41040b0055401c03140d13136122095170290965a0300030300c20045981d682c4444003890854500c039440058441000702c01c100c0e6030601d562140c01112101c900030b02c01229080200012180c0150f420b00c0071a441d100140030b120384040240042600c59001c46510000c00c50300240713015252a03800340004c2d40020161990350384009034440c584440e0000c1070107142030180e090010b00450030508100040411880148003080088203890403002d031812228001c400040c00240c90103c50842c02680c000c408205503c125500c10342c12224038030040c1400d0646513941c00207030310400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 129080584 1250 129079334 129079339
    0xd030309020402031807060504050306010603020d0b030a030f030c080c070b090a1a1b070c050907090b0f03010f0f0b090409080c0f0609010501092705010905061311090c0703030b 78
    0x440c524001a110b600c02980503800801054054500109041e032920030541c2015081010511040100380c07000142c81d4151001d504000d61118207620292000b445110001a03152258806d401c090540241c9040c400412954050101e841c1a440958070780100303417421001183c1c100840c0000c00d030040020b581010381e030310684401c1a11034441c3c500c500e85441c2003951403020101401101104030410304c0c00c01c200c110700b4904140c21502c5500c00c0700341c0e92161a0299031100d0009100c5489080303058080d002c2484096103500221943d0f4070190400d009a10207507201100122300d614416100d00e08880c0c01d01c00c41864645c00000b8040607000d500000c40720401c2c1400341016904052118405481e1600010940c91400c0b4410609455040c0d10402c2c04500d005c100c520005440d8280030b88401174407040e0080000b07d440c0c064010030584001400c140a1102800904148400700200b16030041d0f81d01c203c0451008200a00402c00b030700d88030b0403000100003100001c1d000360032028004400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 129081834 1250 129080584 129080591
    0x1e0c08010b0d020f0102031c141303020c09070e1002031309060b070303020a0309020406080a050c120c010e0a090e0d020c09010b1b01060e0c0d0e0106060c02011101060906062610050d0303 82
    0x1c010412185070003030004002401e454050945161860307542c03043d4041d001046204a42b0101c1d10080d44400380c02003010301411400300080d00c96030166100c180b210001a010303031f408a520386002911303500800a04440e00328120f00c00540300c521401924240c468960403107140901742d54041d802517200d0240030040c50388901040015079594895080208a5100544140100da103003681c204000400c071140300d240c4010552945200c0043c0d1840660400c0c204009a118168001003110320b007644280c0c0d12505060400500c01008a5010200c0c086a0212403d10700680b0400590381d00034040c2780110030062140b88000403030420140400340202c800000d40648482d00600464012100078041c03090020311401100094481c0710f07007800300d20008001090074403500070441c16502c0006030401c600c0c940c6060400c107003940704030002c18100c4030400c4000c0d81c0c1c244c0900072070707811000d485e2a10b14480401c5503000300c038010700d442581e00c1154030809034200002c000b042d4084c0b95041c0c003003540c1c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 129083084 1250 129081834 129081847
    0x60f010521010e0a060b010f4116050f01020c10050703020d05040b0709080705090604091a1611160315090206040e090706110606090a091e0c08010b0d020f010203 71
    0x3092110b80d540e13078040d440118884013294009009a020721700740408001c542e59030808210242d50181000035243c60f400c1d50640101c1e08040d02e8460100580010300c80d00140402251010342125171803940b08a044e210081c0074117440d01d00300d003d483c840d0180354100c0549401070200607031017603600c1801c1c0d040044c2403a0303441050000312282106c0440e2000e141d0402d01414a80082c0c86c4e0000f022041d0081c407070503042078081140c6540c0508424042c3d40c0b01c0c0034040820070a0024080711424100c055101c5142840748080d4200c05010301d0740228584510410144001107030107030704140c800040e03a03207003840c590b02d100111054910081d503240d590300301500142c0e01e0400410081900c1d00800c8107608099000c1414652594000000c4c0401c1060342903885c8004100d89612a0b81104c5090940d078030440e850028104245004000b801c10002c03114228640c1a0200c0449005030340c600c00300b985801d035031400c9580062503158070451682902006141103a000d103608401813040d0f07402e100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 129084334 1250 129083084 129083111
    0xc0d030c111006050307050301150b0306180708010e06010302070b040f0302030c010c180801140c0c1204030302030307031d10091704060c0302010e0606091f0302090705070302060f01052101 83
    0x1d034018402c400c01611000c04000350319042119002500d0200c00800500400c455000340c103241c10310800f11800310200014499545411410404c05030403d11242c09260201c1c0c01003041c04240a11b8400741c003000003090b00c1c4d500c24820303105803551048141741c2a84542c0c64001b00c540c40b80900b181184800c0291400c2d0300340c28042c580340154152280d001000c240001003254074242c1d00541c140d80e14280b0204d86440e08100407940101c40319010581e50080901d4140c2007680003442d080c0083c01c001000010160700100071441036003250380070489200c00c4003005c4207468509401480d030303900c21118040184941d5000701016840303000c1d0034004801003110741d500c54000d07030700c180c0c04030300a5200c3d40c06054080c00350300c00e02c01d03590000d0951842c00380b00140b0084000762420601c0300701c8801106c000034484401030050740e002443da00c0e840c902114010280d9002403401c80c01401044045098128400c0c180d0307040c0e48004000d5042490f90040c2070040e81d60340b50a07001c0c9503403610720954051 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 129085584 1250 129084334 129084343
    0x1b0206031513060305251203120606050d0e0c03100c1209050a0201121104120816060b030f01060b0a080717070305222a0506030c0703030c02030c0d030c11 68
    0xb8445000304110b491411300302d041145406d442101c101c420305151030340c00e005046580a4840c9040d034141c1d201010b0074119038001c18034580401d940d1130320a0109036550003001409220003504014841c1400c80c400342c0380c880c040c1d181c080c0d40541c0319551003140418507810a070707002c80240c41c5c140101d03079500003108151844807500f13903859041a001c59080d56840301b0301d6410f03080456828040e00801c664044824401c0f40302c1c91103850383c080d007154100300b105401c5803c0e43c1c00585481030340200c80d04100d80200b8041d0078951283c8107030114920484010f0045e4011a812240040c0c18496031280590318030310024006000c01c01e9000e8040e90b5484038441c010b02070503240e0340c0001c040c5041c1c04840106998001500125440114802c0001c0c001c0310841029000590030f518135200044c10040b074582080e00001d901440100c00c0282590429021f09002402580c0a10a11201c6001a80c580c49070850101d89a0000a4400c0d5114003175040034406414600d00300407540244030149061 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 129086834 1250 129085584 129085609
    0xf0c0708030c0a02060f15090a1e1e0603081c0e0f031c09150c05090301020c0a05060a02160b040c090f02090a14011d03010e030a0206161b02060315 65
    0x540001c40c0305803c442d81006600d92100080c07010007100c0c2072a00c444a8061207086d046885080c0440001e24030700015008415801c41806a81c031038240c0c03c001da5800380108110485c100d0301c0101044d880441d442c003500c41104d13004681d442c0b03000300d0010520034003959140c2c405882d03500c80d41d05010b0078400f00700d10003000d64220091622138445ca10442c1044100e00d81c1120068200b81c0304202040c1e0342c0084175031030f040c4244005109000034a058600340120305a03268503502c089408408208081a585016403140c0c1c1a9625aa90051860100d00038a24298100c440207440310000070b0302c1c1d945958025005500b030303d00c0d49036210164815180e1030440c08038215008160003c0504014044501070509a0340c5120040c16020000b4902c64080c0381074640c0c1e415208004c9000d4400394006102d42401c241500c2e610142c009000c0c0d80d0f0101582e074002070380030320070b07680040c28460300d950709030380765000301c01c0015102540800c0f105410180c15100c00e810b01514402030b540d01c08810a50 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 129088084 1250 129086834 129086851
    0x4180b09160806041109040c1e020309030610141c23060a0504020112091a0424020406020327090a050714070b0402190b030c0d110c060f0c070803 64
    0x41c440600700009280c00c0303003d4000b0340243e00300740c0d05c541c21043d607100391800840299000100c0300b40b540b200315410141c000088a04001c2c808070034032025400301c02840c040205404403004e944032b649a221040c0c001d84104882448880c0883c02c1703d2511601c0c015041d04640d00d0041005400e403141c02d03010303009500780034107404a40501c0b000ca800904c045644900761550400c0507250640000c0d020800250005509907902e003a0b040400c40e07218403005600400c44032584075440c2ca45000801c001c80c898544640304698403030b5903078281c0280200c0b001d0310410350245040044825504542103940341081100d9850030014441e05d8660710701192080c195000003003081d04202c0c0c0c01500118466400d040104805c1108070041030a01ca5010b03000355060303c05901e040000082c0300203004203600400c045181c00000d0211a0403000c001d0800955664800c025030806510380d540076102d2440300c020950440ca0000342d602010a035500e522140c0d80d1442841c0025682c3c0300882940125400c41 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 129089334 1250 129088084 129088111
    0xf0d050103060605010c020d06050a090c0b0315031b0d0c0503010207050a1e02180c070506040b150d0f1202160803030103060507051314030a140d0e0a0b04180b09 71
    0x8144640d5028141c01030001b0f0800307040941e442e4004ca03903440d90088000e4111500c0d00f0205010340c075a036020604c0c0179013280a1501a41d12000242c00650089d1020303080700c08030501c03003e114540400e01030203484244074440c034001500001d02c851004071b5102a1034003c0c5d120b400103000e17103082c001049024401c10281580030414500804000b02c0707140400d250245114070701c80140c40b003107105101c2e00341d482d580350b0056a500200c24098414614001d1050159909100400101200460141c001d441c01c40c47c845000c0e005200f1980c840e07100141540c5c818419041c04110517500c0728075000c1240c8107840d200c451181544215203802d0380a080158400401041480190700c26690070403064980a072500740713001d01c40c007000c0c4c0d40b07806019600710103410811030b1503600f00312800059034820070380b01104e586008180d40307541100340500007080245401d01300398980000d01d001502c8200c100c0038106420506499012101c1e04013180019a0362554110542e852308051881118250710b0704 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 129090584 1250 129089334 129089339
    0x9190204050918160602030d021309140406050705070218060a050909071a030408040b0d090b190e0a05060106030902010c020405090d1b0803040b0a021c0b010f080f011a0f0d0501 78
    0xf180750041490b54200c00c64407000301804a0f40c0e02008039240f0b01c0e410302c005600c0304495101c00e02013100940c000055140b8100080030b0060b00d000d106131080340221010003460b540ea520503203191207501002584540004106241d46103079200301600314402424041da4281c46070089044078034151002c0c070340b070740c0004010004115414808018007000c105803d0940c2065507610409004600948032031200104203022440d295910150a468000c1d040e10341078102046061601018011004801400d00c8440d0f81110300004440d500305030311800030030b526842d289048008245000c400ca040001c0080804051707580c0c0d001c0d1500401c00080035003a0f085500b20050500c42a503604020480084901100815440010340e40c3c001d403c01100521562201d41400c0288949004070b4030007006d885074600101c070f117540110f1007400b0a0300c68256140a00509032001e0b0340c1240e00000f0201548014401040c940080007480c0d150a041c0b0741c185981881d03000b17116008885641411503485004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 129091834 1250 129090584 129090631
    0x1612050d0b0d08070222020d060608010b0711090a0216080c0d0c0507150c140f19020d0f03030b180f131a04020a0b040914010b09091902040509 63
    0x501d400d02078110303082c03929001e55669895071401841e00c080d220f1100c003c41d010000741c0740d072040c05060f031400204545e9202204000401464540591000955601700100c0c640f80a0401c440d40759420404090300412442c0400400350310052a9811590f0207110000d04070000d00907016419100f200c034503441c3c0280f014100d15205170381e07001d90100f00361a00e120000c00c3c400300b142c8003564080e003500c80c208444004184d85040030321400038980d20604018848203000810901d1081008100351260b03c1001c1e109503508a5560f00d01a5001d020300b001c0344001420100030500c4c142c843e060100d40c0c64075880c0003c9011141100085100d4001c0e8200312039290740400b540d5000c01c100700e0b8684100c10a499400703800000c00164880a1500710120f0b06540c0e80a85213401001c1020b00b007a50746407038001440241460000403006141c1110002c10300703040300030503101011006810101c890f42c0b840c0041002c519006503807541940d0801004c6a06d80f295032440f0320071030114010031102030100a1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 129093084 1250 129091834 129091841
    0x14130615090902030114071b02031203040317060102060c0409051003020603010e07080a0c09030605040c0503060a14010506040302010c0305070305070507030b010303020c1905240a09080d05070302121612050d 91
    0x44051b00040d04030810580c40c0d00702e0031804030480d012000324907030340c03013880402d2501d118559079580c0c02601004000805a100d0040c40c251302c80c1202c0190613403903280040ea550b00c0c050390b044800e002d00b40001e01c251042940800c1c0d00c2010710700d90140065994012038010f07032003a00400c0d2201403010030030601036000150f15400020404080160702030500c8014005540c81c040108030680701c002003000d001c814082600503046c0202519010304119002e0402081c1c007210306281041c94200008242c03410000b96012a0740607100e40d0321344507403540c04440c44c0c1d0200c00d00f2424410203208200200d401085444091032150b1907641d01c55042d410041d2800203083c2d100381c41000c0141d0f40c2100d090103040c0f074100311803040e43d5802c0c108001100d04d81d0348030b4001c00c001c4001c90380801e10002c3d85501a9044089804000560380340d40d440c80411034951094510250159020580d5003038403181d080020038202a07155001d1420034115510380c11520900301000c0006a070110319031411208510 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 129094334 1250 129093084 129093101
    0xf2803061413021e0103091a06032506140f0c0c0f0d110913050604050d1b0302060610090503060f070806030f07090f02070b10060210141306150909020301 68
    0x20b156142151079002034030f64620300d030000304400f29140503050940d0207600041c2e04260301101d410f1021850180c140c00d800011034000d0720070300c91f10b0402c6010600840c441c0318000c580550500c03405050481c20b4502d010028a00302440404122103a100450034002c1c0c55140003480191074803001641c02c01c0f0042c904002e080b4442c400e0301404000113200054484581d250540d074070307503065840c51032360646110348010180042c09064100400c101000c079100045407410b03202c0501943c04e00505522003251440000c015038480303000f00e201c2d494000002010109280b60994000b80c0300c0b4086418400c0642d40e01090310340c49801d100425400c010b005a10071030940c018000200126001a500c00d42792050a01c3c20765104003010035103040c2e4040f54203a0380c0065413101c0502340580038002d10307031580c4203c0c40107002d80e044640b100700150091440c081c52103549165a9101c10101004c03460114000b20f40d019520b4030b401a51401c1c18881c0b00040c8282178002641021a00605080d100d202c0c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 129095584 1250 129094334 129094351
    0x108010c0302180409150f0902040c0206070801090504020303070c1e140102030f1c020a0206040b07081006120e06070509041d030418020f040311100e0f28030614 71
    0x10f0003a0030084203404034640410034125004607411003541083d401c1d500700e9000411150f41420b03004004609103400031040144250350403c4103031220301080780c46040658a040002d600000104407203403994111541090006003034078601080350b510f03500c40150f40d07030140c0c0d108034401c0800000c0a0381c6280610052140304460403000c84a0b4000170344a2080120840010b680810305000b0f144402d00d802c008500d00c284215a5a404d440020b035403040110750031104c810001000801c841d105500c3c041c00f070500a2251000c40b401d02c0000d460013607070510b81c1000035075260020300d281c120801505010300001e403a010781d41d68291052000b9a0b81044600070f03200c0b01c180c03c050442030000215403c0ba02103201e0a152b076400101664040d1080109524000101103400b0050140b405000b942e40002181d0441e0340c461548000d859114407419801c0c0d00215145ca5014642802a012415032502d900707014203007a100300c5004101c0c0190382040e11103a649a42000c1d4402141d102a0340040d42c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 129096834 1250 129095584 129095587
    0x30606030c0a090c0504120f12050405030a0303050405010b03100507110f0303070c03020a0c0f06032f1305120c10080f070f0c05010c080a060b0703050d020c0a02030a0b0108010c0302 80
    0x440102d00400401d2040000540e5541035101046200e134003980e018008942d14002034403028209801070718400d020544807602c25503101c0d80c20724000c2c0101c40c11180081c001e0000c00149442c241d00810300100250340d02c0d500da11940901d44c0d014001c1c602c94144014002650782401c80d07004184a40d9210382c100c0c198045500d090b1a41800404d03283c2c49442450481d81c25110b03840c00300d080404440c4000d1501240000118000c04c094080c8008d8038070a41d0100034940644c40c0d010f1803550034061704812103040c0040a29501d81035802403038118000c0b007130350409a668502264003100b0408950106400c0300707190406610b0190340c0603c00300803030710745081242400030746901e07000f4010b024502030042c80c0f4000c50005010342d62654480e40c00000030080c0051110b00138203032507030440307110022034501507012840303440903002c1c1d5501d5600b41d80c1d601e05080910f10360500039404140300484600c5250007410050703408010700d20789948034180403106d075450644410700b566603800c0d0100a0500 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 129098084 1250 129096834 129096853
    0x6030a0c080c121f05030a030e040b0103090f0f03110f0606040c050408070605400e130602090a0e0108030a0e010c11041a1203070311010903091a0f0a030b03060603 72
    0x200492854010b0751207002c8000c01401040041c0d038a44d099803006806004007220b20b0b061640102d00c508281909540c14404c031160180110110344070100020a018500d040200102c2c2da52075055122610138101802c050500110451401c480841d42118039840401000703803d05003802400c4064481d030a20b1303818a41400c41c1242c444071580a2102000404181c004140303035000c103206039820442c450075569103140c460200714081e500c2003108240700311400000d600242003041a20484e8000340d100311034442a90b880010b940a2440d40e80e00c00d603005000f040d841401d0314030394024100100150794035049404041c0410700c8510740c10741808044000030000c100140c8900080440846000604604400c1400c0341640020182034111115451403000758030004024691180070b07440d40342081c0b40c032086180c02e8850000c40200002c5800310700b0480101148504501620340c41000c3d828504251503c1201c3d41041c83c28800103038440b02c0307a80843c2024071005810200c10f6014268498 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 129099334 1250 129098084 129098107
    0x90a050609091b0f070b01051f020d030c0e1207031a040309140d1b0501020f01060807060e060d0f090209070320030702010b181e15040209040b06030a0c080c 69
    0x1000b0a03d258a0302c00300e601510a02244080341c0000740c0c0c0488454a600c524148141003100900405009000d680c00c00c0c090702a038101d52000141096004003c501f0003618128090810100c0075401d00c80e42d400621419620f000f40e800c003003100d01c00100102461800e00080d000311000d0100e00b0b00d007409082c0320100740c0c8464000150b81d041180c510f417100502020984641a2500261031500011204460f69401caa0102c040b07400036802c484a00281401103030881b1010321482d85250b1000c0420803116014407d4200b50120080a980c18001038072125015680b40c55141d901039030741e49410100b1494074051460304580e042c541004040342000f10b40c00880100b0500c400c44036030100001d000f8505c00d4002c100c1240d405040d160240141004820b8510415910a5080c00601000808030030801040d54850b06014440e0b8069400147c1030100a41c8541001c90700952116811211902e4180045001e49120400020420408131005103080c002030564455084200500c0a400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 129100584 1250 129099334 129099349
    0x30f0d030b0105071e0206190818070e0117010207080a090305071502030304030c02030c0607050a061a180a0609020301151d0609040e010609090507150e0901030308130501020f090a050609 82
    0x24501c00c5500f1205da04980000f071118003850030890305c0125007074400c09240703500040440c050070340c003603042044038440590240c582c3e10300d0180300d441c83c1c060b400400811000c00480e14640c8078a100040c41c1501e580c541031115400a00710b5804103100e12001c00400500b004580c004000c1803418008058800b07000948a220141015040250424a039010742d6401e00c601c4070f10381c800415959a6404520f0013030f4503046030200549000d0b02d400300341100d10800d564482e501e80c0004010310b4143c4040000c1e01e0480b6405003854421aa032140c010540300010710042d030290080742240d10f042044c1c1070000b0703e03002005810038013070940082102c02ca62540801e1b50300d04034040720301040000c8800101130040c02164441c100b924241401b41041c44800320364282501e0000d2080010020b01c00c009a07440c6480d480b501d904034219000410220740304040c1c5070380001400c1260f00c0b0702c2c40183c890a0aa070845480c9030862480011144ca00c5d1500c05002c10043c070701030382c85a040103280030006114 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 129101834 1250 129100584 129100613
    0x70501170105010807030e0102040609050103061202030a0308070c0209070c02030607090e1b07150519060501050a0503090a120504140901232b02090609090a031d030f0d030b010507 79
    0x600200c1004900034a011f41c004941d01c0c0c000300c0003151100da50b883c1c01007001c4158410759010031301d40800811781c201503502d0030100c260003600034910a05103a804603034000c030007001da00410018240b504016510101c21030301402450351152500c0b095801050f00b81480604030005100440740204000642500d041303500c0807500c20903a454482501c48000e8500c2a4440104010134041c06044180e0495000f0b50044000c0c031403010030038840340f1500081700c09500446003c10303000e0108040b0903100d0401141c2c021901c034140d40300e80b08585e03140003503440300540c0d00c000b1801c0807038144914140a008001e40400848150340c66500d4850142c2e60b81c1d100c080c828400c8010f2010344a00da844141031011a115500012003400708414001901881d0004c000c91140200101056aa242526a841c00741d000e01001e000b481640e40c2c0c06407808092109401c0e03042c03460420160b0240e8007803101000302001407000d0803e007201888014200c43c800180c19041c0013050040b000803450b0320414004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 129103084 1250 129101834 129101837
    0x91d060103080f1c051012031b0f050f01090311070605030f040c0e04141b180a0626060903131a04090903020d08060f490507050117010501 61
    0x143d6403240a00b01480d0312844180101e01e000c080504060b0100507881540708068880301269001c1d00c0d01124540041d54110140c00076403015880024401e0300807a0300700452060b940460f032050503030f440508140110540320007503590b95245c1c1d0145030300301c25a5800000d4a0000d040b00501f0045c3c0134003540070207003d4413140486440001d0401814403085000b03800d00d0a8030100d00c4c038091412040ca000d16080c1c0043d41e000300d081d210401d00c05004400e003280e400500303001603071080000720002118000c0542c084162030758000204000c1d80d005104044606500700f40c143c116401c8164278202015160004a500821908500313a10b0000a0700644101040c2c00168104261071003805004a41010f02982d01c1c22450b1420907400081c3c015000d0980e8a4030402c035510001004401311040245035000f0b4442e4a0902d820b05219015a0802c0d00b650029270355450342151110010b21310200011480d008020030300c0134002c080000d640105003d180c4402140340d605840042c400041c8034460 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 129104334 1250 129103084 129103087
    0x60902210106200a0501140a110a081303030605090a09020415030519171306080708071209080f040314070b0c07051c0605070302090a0b04080304290d0204091d06010308 74
    0x2605070900880b50580d170004003d0000e01891003510501600030341d4003842181c03034004281c0c107818150050b50b500603410703240c0d42c0956541d1061000c101c1e0400030304800b003596520000c03486075202a25035014070b07400100012104d9440c41488112000711070751128080d1444010000100009514200000840800c44041c0c041c0c0c500310b84d0b4a1001e454001a8001c04905000c0b015010b41a6100f1503066a0300e43c0e03a0f41c0c403500401c0d5404001507990b0000111100c4100e000c0300c8441c0c00c410f144501c5990304501c1c0a481c03503220002e54100350812a40000b01094403e44104c040002002620b5000c420038a03190300945440d55814a038411140070740b40c00c0c04500c2454165101c09800c240c0c0111040c802d51510680c0240294042c1040714880c1c04400d5000c03542404d500306035070070b40d8058401185494103200c52a1181c041c0115504035110035945500c0d02c402d02c030400b52001012604000d602c030340c18401440141c1d81030a504601c001d00e4010348050819000929504480e0031140d0385 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 129105584 1250 129104334 129104387
    0x906042a0909060f09020d0201031d06090705040e06010b03061c0206031501080108150103110a051302043b07030209120a0203060703020a02032209060902210106 71
    0x240540c100400950304034005038000200c91419030805401c4520685040090100a09600c0d084550010b4080d40240c03056001c2401135000b50321041844203842c91600b901029103206070b14010080300c2503011a0840c11007040036040c54050803211010b031902030040c0303605141003400303036000c0244024400c2c6d44403404010b6184d00f50007240450303038024111079940d1415003140325440440c05246d03400604090b000042105010412260b07801d058244940c50780d20319201c1c2e1100f0600e800081d580001400400107040e51041e13148541a458100f000da00c9920300210320440c81a500d8a40c007201103901d84041c05108a00e6140c2e480341c08540740a4501c3e120040c2c00c400038019101c860750014080c2d00309a456100001d4089107062088040f00d041c2c0d6140c0c4421000c0c0d01840044074091f84c01800a0480540328108900c640c0010070054007140e0764501d01385050300c509920001203280d0016922072106608015a0a0510040d040002552401c64020701d400b032890f07003d072a95400080303917 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 129106834 1250 129105584 129105623
    0x3050702060423090c03061c111f111b04020304030306030c120c051f0c050309030a030302040e15010f05070602040e010605120a0c1706040e060c13060206090604 71
    0x1034901821144203070003903075083c100007204030144201c40c0324810300c41040061010700b84d11040368414200900305007125400f90001c1c1d2110b044807541101c04140d04c8492080c01c0c1c60300360024054803c41c83d8035240c0448001c40250545c40b9016011501e50409450700114200c04d00498640300425240103980e03949a0504a000f03201a800042108246c9400080c984d803290f007001d41842d001d503031000052a078480c108200000c08400605078080c0b039841281d01240600114401c050056050b00c2c600003003035001070b08010601c4002c40c0429800300d010b00c41c07a40149034007507200f16005207800d03042282200103820f940314603a800c4200440014094100003081d01600c0051800001410107543c44050180c40f64001a2002031b00e10041c00003d141040c00c0d0180e1081c403c055200e99113444644030002000d0360307004090303a4025482d50110032502e9000c00c00203100f80180b80600b62150003184440406c05d140354010740c110f601c21410b100401d000072034620341195005070890039440d0807405 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 129108084 1250 129106834 129106837
    0x1006020f0a1415160953060f0610021005070219060203060f09011d13082208030f1603020c09040f0b060607030e0d060b0a120204050702190305070206 66
    0x788031030f0084a0280310341c1401c2d81e00301c4180c00c03895031101420b80e611000e4561140d815500c0041450356a20708016164071503000001c607100e04501e80000810580b05070900074800400c03200195032004041020000c0e40740503580c0c12000869032400c4482d41e0000007035450070b0b0b02800802c0940e5034808103c00d54001c2003800d08090440003000400300c454207200000f50000c5500c680180007105144505190030600681a110031100c2e401090300050f01c00d0400c0d031002003115075070300342d00d00c521000316054001034201e00381d5048003c0040c00e40311010304071100c2c0b04da0081e159a801407082100103015041943e400040e07403194201650741c2c5050407881c0c1504200c0f0300b9004a080790602041c02a40150203984500800380c0b604c950300c840c014403035103214038080500080d03a20030f9454aa0315090119030388541c0902c10100700c040c0c12000044401c0301c0c580c002050030070718000300821420b107402519400a46400a0714840314011440000140100790042c100940040c1000031036607402c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 129109334 1250 129108084 129108103
    0x7231902061c150b0705070906030503070b0901060306020c0c03010b04110909060d060e06090d02070605070b0601030e0d120b0a030209010b0a1413061d06090409050304050303030702061006020f0a14 87
    0x1680043d0580e600c500b0112180d025100c04d83c0c0d10b0080300c2e00030404a42d030740141c0003229809001140742080944030048206c502800b456225520b600001004c80d0700d5002415104121001030001020001c04050031101d12110483c0110b060055102440d00040c050310090201551090b080360354010004540c0da030361000041c001403a00400800c6804000303091845804100111000c00e089480181d9640740e00e8030403a000110304001e12000143d40225040d002030040c10041091851010301030f003450024050080012002240400c000c0d5440c014000346120075600c000c0014190340100305055014020036168800004815481500c50400c45c90303003c1c1583c200780e031201c0584090a0325a2090301c202c00024113985c844844610b001091240304100043c040c0b842d2000c1c25090002030a40500d06485901050000281e0381e00c0600086104804542c041d202c2c920f001115240032a01076005002150b01c200d480b040b100c600041c4449107150030001101c0320040d810519858205d000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 129110584 1250 129109334 129109361
    0x15050d0f020406081003020307091d10020c010b06030f0402011407060e01140c12060f040b03030c01090620040501030902060c0f071811160807231902061c 68
    0x11a40820100d0154080c0c41912402d035564001900c0f03d5215202da0603e9001c040e501d40c00002c01006040d20a600845141c180c2ca20b410741490354041c643d908140521108004880c0c0000d80d00184c09000c1c440e402e040c140840d801811820280d051545d07200008000905010000144002d104406030039a800300d54498014020b0b0100c000d8600d000e4091142003590070000e410200b40006014410b0711503403d00c680e42d90038030f5500da8042142500030b00100d00d420583c2c3c2c0d00d8031140c40d00d060008150208488001194403140c51030000b08448203501000205400c032002a0b240451080c216022507109180c08a42c0c51074070f00015400d80315000305480d80c3d2040c603495049220f8089807500c00ca0710282c00300d466003030b0104650015141d007000003001c0110200004415880d8008112004601441c926828046a517680c0040c0d900d640c613000d040000c44444103c1d079000c00304a030040d290141103042d01d400d441a40450900c0c000c0c40218020304210481120919007654020000650394 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 129111834 1250 129110584 129110591
    0x809090c1e180904020306040b10080102131502070e130309050907080406050603010c021e0f151801090f0809040e0102160204050a0e07151e0306090f05040b0115050d 73
    0x448100d26166228090016104a461000103a01c0c030300001204e01c82e07a00a406480160f07210f03a034055100d24000c1c4091450030301e03a030780480d541d8001d101504045c50505100bc1e1190300b00004620407500324400c600c11507000001c00e00ca1860910741003070300000b440a20b07081ca032419107001d83d04291035400458000300d403c070800010030b5105240781d009600480007005107442c1c1405050985105844010240c1d20850031018510076151541e03842c1440b01c4165081c0034032641c0d07050f04110340b04c6d0390501403900f450306104d00c40c42c3d49e0990320401040300c00200300d100c0469441c0c444d0709071318200c00341c0308e007201044244603074440760450500b80140700000c56980c180c80560000c80d000c820001d0340a146000c0024102e80d10074450690341c00d2a0390010500e40c0d00d004d101810b100070200101c0f080044000440c00450354260618042082d1901c000c07034414201001ca1046070502031090003024201000c2c400450744050384030f0f0565007031000030b00703507100b4001094900740304001c68407100918 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 129113084 1250 129111834 129111877
    0x18080f0f0717030a050612060105101b0f020a1509051e0907120b2e05070512190806010c0206090406050612060f0307081f06241202070809090c 63
    0x2c2d0a0000c500c00ca01c40d40040001d40c0340e110921007203d5007088114981d40c00200148410318040803088114681d83c544100035102500080300152107030407044400401161440c811441d0810f10b00002c1c1c00054802208501c006100410700c524074440d0500034000c080e200d80303c501c9036008214600b8400703400385409091601c4000c0019128140010240d4034021032042c3c1850250040c1084002e00710b085480740801e04081400d03007940302c800005028040003280c0c0010310600080c40f002024000140c1c46040300c12441e00440755141c4800f003007040640811013035a07004080c20741600c1d01560308585405000c400b04000700001c5e089290300c0764020075003000003941d07001101c1c0318080581c2d094901c1c030707000c105140d65941c4e01d019a0803950010180d80c441c000c1e01c135000040f6130028034004500250b5034610a803820182d01c4000c0f000840144003020300b9a005502c0c54605402c400c411458071b861901e0340b40403400703000510381c401d880700c1c0042080703903a007401613860301c6071070b140e60465014 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 129114334 1250 129113084 129113123
    0x4080a050d020f030a0804110103022104030807030605010c0b09010609020c0f0d0504061d03120d02030604140601050d020f040b04060c050d1701090902300118080f0f07 74
    0x181c1040c44006218002c06800c00f158003201780d510f070214985545549440d80d941d681106402095401c1c10141e0034407040c0000800307040c15080281710308241984600349424014400b1030f00601102c24541030a07401c100383e0340c1c004504444280c20041c0401d054640940c501d003d080b00b41d118443e19070000c0b81c06400c4200228031840c625003182c084034200c000600c0c00b5104ca000b5481210049000c800304800c20a43c202c00c0444540002815a80314054120034600c3c0d41c0c000b0f40c03a204070940e0201c1008158103040c416000440d0038842e4070100d40c600a00020724610880c81d41c00d5a0030303000704d01d001002c50f42e8020742c0e02030b0080c0540c240d184d03900c4d5000146515031007441076800b4420984034010381c6005a500e2800710b010f00c0812421071b030811400102800c45a1030403600680402d040c02c45080130242e0240c01441241401007185000d81c0340f81d401d55600c10942d0f5003605071040c000340021100400c44051040049005468a001143e00301550050100c00b03003010880c0140604d0f20b5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 129115584 1250 129114334 129114343
    0x30b0a08240f061005071e0b0603060f07050702030f01060308120a200a1e0503011403011a040c09030f0606033008060402040b07050705010206090f03190504080a05 72
    0x3001610303009070482114014580014140c0e600004030540801003140c5042104005404041c01e0500c40e2801035143d8400f15803441143e0842c00401b000f00812042110240f00300c0d41200088004020f1410b10108148810001070800320900c58001419011920b09001c940d00501d03a20000b0810780f5030788d04140c91540e2141280c1050404280001040940180300d0354014480a808520f441c25043d03842c001a03521001c0c43c2c00521000702650040b136134040b110312047d02d96a41c1e0321a200d515000d0b802070906480710100f807281e410907003036003044440001303001c5481da000c480224000120300c000b600c5c510040d401c05451000301181c00c009004441c4c2100b0201d038803d030301c4000d0407070083c0d0000c00b201c4608031074a01500c200e42642c6180c0340c850318fc9980c00460080c401440e040d40c61081e8003507644044002c480c0c80d00402c208100315a01481442d5101c60303c0c2003d411b016800d40c040940b04d2081c0b070364204190b600b900280f4401c07031048003642c01070050b0100300d4003040313101d0a085664 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 129116834 1250 129115584 129115603
    0xc0e060a090509010b220f030305090d1202010b03011d0309060d1107030309031b02030d0f0201020d09030306030c05010305010b040312020a080a0e0306010b130e0901180312060b070206040510030b0a08 88
    0x20305204000c1c80e00d0386010001b00004841c100e202c403c5105007103544c1126180d0003110340c2940105041001c40108081c810000202051a000042c0040202c4141825900a142c40406041000702c90400b1850044201c2c1c0c6194001c460059650400c3c1000800030032035070302030441a2402141450406406500c121001406621008400303000c10b0009140510b041c42c1c000e40540100c1c1081d00c525010780407104240211b80000f500700101103a40c07504855030380d5400c1d00005d0301c1e05010800c0c0059038900c81301a01c401c1c1303410310042d81080d102d6583ea100794800144454445004d42500034401c0c0100111280d00c0007900b035440140140041119104944107846401840000110408108100e07403d55030340d1040c982c1175501e000880c100d6a4070041201c01595220700b2042e5a0002aa251120341b40c400c3c0c40f28011048130b002c511080740d095030440441c070341c0c0030080d900160396040251003c030340f0f0844600544c072240c910110050310010100359045290014086116640811070009 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 129118084 1250 129116834 129116857
    0x40b07030c20061204060e0d021e01020f0301170109060203070c060f0504170a1b0506010e0f192d0209030c0f09040308040512070503030105090a0c0e060a090509010b 73
    0xa403000071009107150b52221071111544907200300702d0724404007210030040d03070f100340100000990f001c168102c09041c000740a038944010b0308010300141003c14901c4010260040d40d000840c1840c80e403242c001458441070050b60360101c100c1c4c5108484007c03d4004401c0d442d23004034150744a040c202d2025046201e008001c665050415030300b0728804a60b4810148542d0b0080f0100060005c0400540e80e150f110804120400101c0740c05410098030900c20507400d42c2c800e00040100d58982480194019809010300900d01041c20031300c243d881c50f180b40c0200941c4041000141c601024186681140d9520501962031b01c1100f0700c8480c0381c080d81d001c2c0c8202071081d030076070745d1520300b950030001100c0000c1d05807503001c1401800709011a103e880a55840f5201e44110380001d035500310502820340002c0811a1a07030b000000511440c00c2500c001030304840e044a080c800035012100140c200f032900c540e95401070a010586070140340c07040c0c0d4010001c0401030050012961540c6030300720582d104891048 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 129119334 1250 129118084 129118103
    0xe0d0c24030504020a031e05010e0606030115080616030e3009010804080f070503032505030603100e10060b07060b060702130903020319020f070501081608060303040b07030c 76
    0xa00d0a4007900402e48540d5008100c88040d40c01c584c2c1d804a21202820b0000c50504410400800074609206007100a0b031000010099498000101403d440007904009540207458408004801c0700055440c1c0010f000d0090b1346040610301002c034000c0040f04070710f41c5684668100ca138901081c5001c01090034002c00340c0b0240c1080f152030241228807a030660540003540c0c290018000c610103401814040e80116201890440562102d038510341007a00e50a600c40035540c55108401c81251804020340c5031801d00c0390031032410100098907084e805240400d201e03198003038020f400b103040c800c455540c0da001c5070410270582c941c100340c14185c018403400c880b00d5140250480103441c107101a01d0170294000c0c524251b040382c4800102c06400d443d4801c40651000744000c5012000c49210340e01d07110590760040c4019055aa80940b92803141d40c062414000c492080c8411003044079424031241c4e003a030038030050b21740b90440403070300c0d43c45541d1141c01030f060007007600010140d1041030440c5040c080c3e404d05 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 129120584 1250 129119334 129119399
    0x30c02010f02013b01050106050c060709031203090f02060c0a1104020c031c060b07080315010c05030421060207080c070f120213090c08012315010e0d0c 67
    0x140d080f194401c49a11380400003040e078407081841c501a030561100c890b0911004148074440d0982520002e030000b2020071000301d00238410010400c1600c0e070041e050b1801035240e51460b01c2e00c1d4103182180140303104058070b60700700740140580c0200000f1626409400f1581e0344c08842841c50300c900810f501180c8031800700c0d11140e1541b81034001ea902c1c0310184405140781900b501883e4801c40c0402d07078501840c603200d50001551141c601c0150182501552084c0d80c0c1e0b2500d032601c9100590305181081c1400b103d036281c06c0201c0d43c0007003507030265400100ea410b4034074691110320b0306c0340710b415400400c581c0c00000d1000c01c00c81044080c112452086044a080d9034540680b000826240e000300c0011800305400803003d031421400e4070350030300740ca8900050760300101d07210742c2d598000035085910079a45400e244034035000e030350701e0b02d40948882c0341d0b6060550506d002d140c141014030504050421062030103600300c9580780b808035070003e0303408a50071200701d561f882c0e0780404100101e2400e01150016806 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 129121834 1250 129120584 129120587
    0x30801051519180617012c0403020a0b060301020a0c170c0307120e120d080604020405100e010905040605030a0605151305010f0609150f020309030304030b040c08070f0308090d020a03030c02010f 85
    0x5550f907558000713000882c582c2c02d01c880c47c2c2d0300310301e02984000324000211149103000384e0381400b10b0007280254041c000c0d400c4039041003900c14102828050082e84104600c200080e0300100c40b0020907030015050f00c420b907035041c00105502480034240024000002c54104100041018a6402d08551120f030030030945002000810183c43c010149070340c00c0052441c44c3c1c144240e680ea54003600c0100014101a16000407a81c0300c822004c4030b40c003103484000c0c600300c0d03582c102007880024401200e040c0412414070011035111418424004c0030036464201190050040b81c94504a0341000780900c4010780108686038040c090030310030140036000c07c00303001c07541c28480c400750300c156802240181c0250a200c40300311030020b007421080c401c50100340043c40044d50140000c00046000c0c03a032a0a0a09060500d0fa064440310307804080c07103602c10381e82044010304a6403028101c98101c0940b035100d95040000c148251a003400003980700f001c1001c080100b5400030000240c1a000782e95600042691b10390 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 129123084 1250 129121834 129121847
    0x10801020403051209031c030f1103070207050402090607020d0b01030309060c0b0718030c1409060f09070c0309050411121e06120304090507030c11030301030308010515191806 77
    0xb0107841a008454a004140b5060005101c403050140407914241d410000081a910b40070000b000080e0701c807008250740418074050740445204480c070b2140b03181403c0c80b000c2d40d9a0060f21076a0301403034002c14180895903e0b402a03598154000d401004106001d203801058030303109000403404602c441002140e0103200340c0401d0038a075408a0310081c15220b0800030340d82d501890b10405000c00c6010700100016444280c03902c020160703050000c1c010540e1100304801c0d070400a017041e00444d041c0c1c110440341d0342c500b608150480c0441c10011854811410112122003003504086c1d001030030718030800400d03010b00000f0004484060300d69102510303192480e40c0003c12600e001001820040c0204055103007103182500d000310602c2c1100d140650340c5c0404801c0d50b03130458401012a54030740c3d2020a4a4109040e1070300915290b0242d0b103550b040d540c0240c00c401c0180280d5000741c1d000c0001c40e2002411a040341c40e6041001c44010b07880c4280d460040501808108140341120b102900094881c090079 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 129124334 1250 129123084 129123089
    0xc0b0301060914060c0d0807260103060e07091401031e15051e090c0a121a130501020c060106121505040b010207030c030b011d070c0311030c01020d050604050108010204 74
    0x5440c2c50406241140540b004546a110749600690802181207003d20400950415007040c0d00d071045180303080d03600a0300d01d5180c0e14541001001010402e01101107000101d41502e611100014034600800d662a18109158102d550170a1030040c01e103048180350b1000504070391194881e041e040302400143d04001c000e16800a140904515400d40e107a07541e030b0003c2d07620080018030340c0c1c3c04840001c0040200c100c207803410011034018081c8220203080451141010b89041c2c51914181c4040307640d10103081c00b401d001e40804100c0580401c40b804146910140056000402552a82a01d1110708c5d02c500f000e1042c0b9000c02c03101c0b45215002542405010340b01c2410700e0030621000d29020621014040c0c1d20b102c10b045001e80400400000c002030b6003000554010034800d50290b041c5440520f1402290445182c01c102c5a8100b1a48035880740403001d605500d03191601081c124101514914040e64032441700030750002c00c408010511540c4000d01c141e001310360500103a41d036807000500702e00c03503030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 129125584 1250 129124334 129124337
    0x3110103181203180b090c03031c0c050f04140103050a060513050411060408100509190201050c0a150905010614030c0118090911010323062103030403020106030c0b030106 75
    0x441c80081400390b070515041080a0901041014240c0d204400074845840300702d42d441110780900241d01000c004034030034000e09400852070518500300240c00010790984802840d40c580c083e040d203c2d1321500c00c0e10844100403814984440d00e0788081c02d00108060301850009141800080e8800c14500600088a202905143c0780c82d07008500c82000c1d1100801c1030300c02d44200745134140f80c0e1302c405000708003e1401e00b001c0c003143c10b8008401070940780060910000e40e44543c44200305940c18000c0b0122061382400d246e952071040440082c14200d020f440030f408880b2603041c2154441c0243c100e02c1206210303400801001c0e4a64101c0000d104210020b16090780c80f19144444dd54050394404140045000911b4801c55640b01900d007912070100c01100c4d500020140f021142d6094001c0e0000c500d140c03000c01c1e03c42810f079034441220b0600100018070070001600c3c09211200b0318003803442c50034040401d8075507a00c3c06060190203001503100c00c5410450b01c010006e00182e81405480c182d4106 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 129126834 1250 129125584 129125621
    0xa03091a04081c020405060703020115060e090f190536070911040e01090b040f020a1707050405030105090601060f0f050724150f080a050613030c08030a020403110103 73
    0x5200f40c6060524035000300c5000340d08000c04581a81e4550280c040a0310035400812900e8401d911a00601480d40c080c1e4140070b0780c544980540e07540c151407141d0105015804410310383d40c02800e04035006a14a11200403450541401100300c118158500300c903030908144190701d200d040032184000034003001da4409170021300c0140000315154112007040c4400498850401d5203906202e10340d13034001c0c1e20056075a0398030030f5400a2070502c1c1c010300a526150500840c1080c0f8400405031001d21000d44a400c0e141c00c4c5000603a6560044060360003402d0090001c100500d8214010f81d43d8003000e003d82008294070b14110030707000d489042640b03c010b1107543c5d40c506000c900c1d62034100010504104030244140c1880030940200030f4412300d960344080c2601c0c00e81d01440d04090306c00c034a10316004404035401c82c0b507609011039000100300b9008106190b114071903110368201100e5150310400c00411080c0000244031100025801034025280900c40400050149000540481c0e1841e00c028000040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 129128084 1250 129126834 129126847
    0x605030c1c03230901020c0f060d09060f0e0307350f041802030711030310030b0406020f0301231008010e071205100f09090201080103020d03090801020a03091a0408 72
    0x2881c1946540e00d446400d0514008207504400544a240d024015002020100e0344140940e41040172450141c016602e0104030040701c80419a0307845915440c10b15583c071405c9800c00c01a181d8007503642c00001c1c0400b0002030003600d10b01900d82e80704400a8031407018101c4119030b0390311601d811404404d508031049040c1d4030403d000d0102c0b0f80280905080d0428188030000f12000c50340860105042c6580e001079a074a040200a40b80004000e24004070360300c14800c020f1101542c19200d01a250401440f0f50241d640e071520030041e100b01c410000b00400c3c0403000052041c3d0300660090110300820040c00f04541403030a001481203400d00c00000135050f80c0041080b143c40a240e182c0200180c0342c06080b1580b00948601924016980c0c19038450019030100581015015154058041e0300c1040c001004a0b4000030094070060101910038840031580c0300400d030040407810300810003a03000755104c81c643d980140003421925003d44444c0e52141c11f1100c069a42c0b03100c0c42c444c5a01503040742c2000b9 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 129129334 1250 129128084 129128119
    0x80c030609130f0506010f15080f070e040b061201171203061c02030706120609020301080304060e0111150a0b010e030d0806030a05060c03100b1306081005090a0605040605030c 77
    0xc40e004040d902400f080c2c03e00000304000340102c9000c1d00d0707070791100800c0d44d18140d0030003038841052480c60200064441408502c035144030056810100302c0c502020150b64000c0002c0c014001c3c03003032551f40040300081301075825070100c44850480e492003a101c03014050390901c0300e48a181400f00540c0c55002000000d034640b03800320024054a5822184209488980c2e0200c0c0c5860025004200426040030075604400c14a00465000e041117007400c5d429540f4003000b460303485c015400b0380000d020340c0c00100500790344203200d1581848584007c0720824000300b070b03003070900d40020f4440344082428110400044d502550f402540c49502800419025017121011180318401400b43d641c03601400d424800415410040d00e03014011017100103540c0c0c10b0103c01d41d8440b070180d41c461904010300f4403c0862400303141c85114202c0740356040110b1690b41c0e02c0800b03040c11450390480c640c400079500a10126408540c0200700380e0324140c81c10803800f5107400c105503491140b9a8441c0d40b1130403251542d03000c0c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 129130584 1250 129129334 129129361
    0x3061b07020616020301020d0905061302010e060325050a12090f030c0c05060c0313050406030305030f101205010c03060e0105330c060406060b09010f030c0c0203071401080c030609 79
    0x484a0343d11100007000d50343c0000d080ea80071101e614822500d131104c00b801d0180034810986c1001000b01d90b180480c64941c00130709080c4070703050402d208100200c00154140203101e0b10f20305c17031568014000c600705038410f409482500180385c00000940c5a40c003488a0721264800c410301c40342c0040c1c580703e856140390780c01c840c000070441044a4400302d40d90005001e4945002601002c01d1031005561103500c0d00b002c2d41240701117903201c04c2c41241000350403c0800c3d0000212a04400c1090009a50b96946c0844008106460b8441d07440010f14004ca001440819400b1b0402611665000c0c071229548052038440c2c88030078028190b10244032114440070f01d109030394800c1c0140340f2079a1040101906000e155160f04859000360981d005007041004214142c4a1800a802e4885029081c101e14500082c80444032030b44103000d166807030510b42e203128007844030b900346035a00904640d282c6856070070035000344c1104545140407407100404142d2030300768917090700d10516029248026503503c405800410 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 129131834 1250 129130584 129130597
    0xc0f27160513050d140115050910050d02090a0207020d08030a050f01061416020301020706060f080616200f07090f0203130f08041208120108031201060e01090b0301030b0603061b070206 81
    0x5c0c0124118002c0c82c05402c1c09011740741c48103500c4185509140070306000c0d0002000b00010091911003a00380100e0f65484210030703070076806448203c9299200c1c668840244500302003c1d500442045460381044881c20007988592100802480161104080408000000c3c01110081549048940c690701e0840c400790a00c10454085080c0c1d034499600441e003260302a880c2681c0003500ca403020300408480c41c00d01d0b401000c1c48001042d413842c1103006e000403400040000001c2003050f0099115081603154072145100959040e244142c0f400c8504035aa0140c902c035001919082410341c446610300307031080ea84685954030020300080c049a50304c414440d08080101c941040510011a00240142c265031a26203d245100d545200c000e900102510050344084213603401045101100b401e5030f100039045815a060800d40702407001c0c01a204a034668103ca5901d00004c400002402203604d001c82c0254816400c0d00d8264840e21032030040c2c040082d0b13004811640401c040401428030318002c200 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 129133084 1250 129131834 129131843
    0x10e0402040905090120030403020303130204090b09150106090305030403121403090a02040506041e05040312020a02100c050f030705031005120d020106090e0c0f27160513050d 77
    0x14050b190a041d4048400c10307140380c00143c0d5201c480754000840001402c0409810340314140c00d526155600039582d101c01001200207500744e40420b411074513203030071412940d940a85449094603184d0100355880641c0300c543e40140094030000205180a0213014040d00d81140c091450181583c646603500d0310031240c4542002013581052200b0320010000c0d44c0a460750801902c0030390045d004200c10380d00003600792449540307010302c6281d103240c0040c24100e00da41c0340040801c80b96910306003a03c4442ca0002b61001d5940006401c10800c2e034040f41c1703c0b8009880000401c01ca14025104944601884802c130703a2074a030800100d09100e00502c00b4581c00000000341c450101d0300c5001240305aa22841c86c1e1804d980101d0390a080141c082c041c1d04082d0104c51010000c40e10035520403660b4080098150f405807401d40096101912403281980c1607d0307040a105280e054240f040703c64402c4111603205000e00224440c002c3d2a1040007210301211450004801c940e082c003003004590409141d0403503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 129134334 1250 129133084 129133087
    0x10020705011412010e04030207080105010e061c0b010906050901090c05120405010b032d0a050c010c020d06060308090a0e04020102030304230a05030a090f150311070506090703230a02010e0402 84
    0x380d003840c40101403806007600c185d02240300d0519140103440c000094111362a941d040c88014441c0300029003030541e221004649080d04503600c0581169100c48920000c0c10500b001c1c000070601d4100340d08103000b01c03070f03007658040213603a80c0d10303600c4040fa082c95160400150301049070704400446849400d070040e0141000040d00c0383d800000919000c8500003050704000b0121600c00c95203203003001d080412840c04040d150600f043d03555252030fa02145069414400c0740e007042400d6440c3ea0440b8000030b0380c089001c2005944030308215006402c4000326600c200710b0708002040d408000146140190741c10b030011425a226591250300e11013075100c0744181300104411911000e5010402c0d00d10950082d0051691600d02c4a001014120380b6040721640d800c10030410000040f6000d43c40182902c9494009070034680080a421030344500c040141142c481c000501030320003004580b0718100c034441c00181d0070703400401c070040703040c001220011070094102c80c10740070255021744a1140c01100050006 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 129135584 1250 129134334 129134347
    0x1005070624060e0402130e04170406031407081009020c0705090a02040801110403150908190c03030501080a2019140f040905060a050402010e1305061810060c02130f020315100207050114 81
    0x506a508240c2c80301000907207437000441031150070301001d44c1281452620ba807040c6060300d201c0c0307400d845e54070403c00381982c0043c8400c81a8818000e00d00a441c004062980e1810007469040c0690001d0050314035a5107041a0052000c02000c112821268000c00b0400030044000a0900500e80d41000f13541012082103081500c00007000300c42101c03481c58855092255050600804444058000c0c07440380c0e00c00d5201c5008150940803040000002248400d00b1510300f0b40403600c00c0009502111056112042c042000401085502e0a07850300396030711648002c0200420090f101a0107002c0c0a68101c803000c2540540b09802c4264018018181800d0070a048008644080f020603122614259544c4c00d04c0401d11b081142c4148038a500c908044180c24080f030609040031451146800380152030b01c4e21021500d401c1d100f4415462866000c100d02c00f03076120410040d42c0b048460507240142e4036050003051400c4100240802201da0052907090f007080b00543e95500c0b1401004000042800380 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 129136690 1106 129135584 129135623
    0x160e18010507021018050f0d030507020105010501090605090102120c0304090501170c10020709050403050406030b0102010e0c01050915030403050a0f050301051005070624060e0402130e04 82
    0x445c400d1010389949068001c100040c018055a03000581000c0042000035810a440d2402d0020342e64200049080b510b0900406020880340e0f60306000f02da00c1a80038100b4045c040c01152f604540e000030158254028644c1c00300160300c005014082c05a80e40030303843c014200d070041c10201c0750032413400d02c1d00c41d040207030700324090703280740c0140d1220500c00c21094009100700d3b0010000b40c245414010300503402400b4140100782003c440034800d510500c40d520405041e14003418401e01007100450301d40c1d0003000d00c9a84440032035400c00000f0a0000114003691003501d4440d510304031020040c000c451a46030a03010310405100400c51610307601c03040025140289010340d911071031480d00c10020501400b0314403451030501e0142c0c0c080a0212514800d80d41a500c0f004c003031607401020401a4403807000e00c0051407528a104115030140c00350401e410500c00d4418031080000442c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 128956834 129136690 := by
  have h0 := BRFrame.cov_init 128956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 128956834 ≤ n) (h2 : n < 129136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
