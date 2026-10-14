-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0578
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:32:50.589816+00:00
-- url     : https://prove2.me/submissions/2d166ff3-9493-4cc0-bfbf-6a9cd715b0d5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 103776978 ≤ n < 103956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 103778228 1250 103776978 103777013
    0xb060706060f090204230f0316060207060e0906010f0905041d0106060201020405010f03020c15040b0f010e011505070f0b09030a0305010509130204051510020d09080106030503030c070c12 82
    0x1240c080040d10350f9050084070245d501e1000e045001c6034050188038031041207812090b034040030310001a041910104004009001c0c0006044482460000040c0c1000c0540e0088400c000c071009160226448807282c01d60094005c0c030380041e0103544080107d50315a050341001d40e00030b0900f240c0c84104151900ba04100d200d1100080141d04d07981d00c41a1700f02d1140344511804640b85180099100e4001e50241ca030450860080da003844101d040c3c09103d108040f907013150b51240340802e11200c0600c01010501601c007d40042509505103090b9606240048002e5010000700248110420a40c0d1210f0b484803a80107840c004c190034401d140907165048002c8000019103004000141131030302c101114003e0301c901c0188021045103400f444060840140804400d200c00142181c003070300d42e00d01170880c0c2c402a9020305000240d642c001083c45400e540550001e0b07050400030300114030040200c941103008400e500b0395824561030041c0703400f81a42c0c080c00d0300710004441d44003030149420f181151202c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 103779478 1250 103778228 103778249
    0x90201120504020306061908120a021b0306060d05120403030905150306090a090203010905063d06051605030a02010915092102120c1b0108091209040b06070606 70
    0x140c11203640001c85200301e0b400b0358540d01030000300340c45040a9400349402c0340d10208100304180c0340c0004e02e181c00e0202d07210301104000020020562030f070500c900b6020032039060040c004c6103080400207984020103041140305003080d0308000708001c1c0401080d03203d040000d0b2415103440e075904018010300c400f407044901a0030304800c0d02005000d01d1044030301c101001481c40340191100c000141c000d140421041740c1640d610802d410104508104542c0b01c2c1c1104d036152a2119500d5200c207020465100d08002c0407010012060321002c00d0088507800c2c0d031200e107840c0351502c11041802c541c1c40302a51029040c1c1c0400203402c48000d40c10341152000a01803240024540503a1489804450b80329401034445034404804450410030500d504800700340d5841161b0b80c03001c01c420411141e5100072151812648a6152154408100d80d5103030303018542420700d01002c2c0780c070820a5441d980300c05850600307a0030005171850315942c0d543c0b09600c08a400b41c0155101c0625150040080415000b0040354a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 103780728 1250 103779478 103779497
    0x60a091a040e06010e0408180409210504270b0a0602070905060d021011010f020412050d03050f04030305071403010305030d060b0412030804080f0304030f0f05090a030b0703090602030901090201 85
    0x282c0003d062030483d1580c021808081e07850707031511996504200c1d003907030b68854604440d01d0644d42e00e004084040780240c0c1c0c40b04454207030402c403030401a00303951010107200090100300401d0601009003902e446c2c05581d410007060207010310070b004181088082d948001c00c00c4c0d01207841c1e81d0000e1184180c8410090400140c0c64403010048008113440000350b12508695000490700d00c5442e403580360020715000450050800444881031741c2158102044401d100a039200c103000d4204001600d031201c60504001c141041c042c01c0110900042025040c184c40f440460106841070092b404445881c034081070710703540c41c0d240c40c944a6000b0364599401606081e0302141c3c1c03501c031104a908944004c895864029820b40d400d4401080c01003003980c1c0b00a0502408508111034402107100318860f60390004403c0c002c14015162060328464002082003c2c00100380039151765201c42d00740ca8000b00c64a01991311400102d000c0c1041c4400244400d0003c400d00010400541100d24014802d03203070303640758 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 103781978 1250 103780728 103780751
    0x1a070b060d0209190608060114130621050a02130903110f070614070807030c0210030e0c0f1924050c07050409080c0304030318050402120403030203060a091a04 70
    0x4016074041d02070b40c003000e030001041c5003181421000000142c0210045501940c03009010308010b001d90000c1b2450054100e1050b0074a031500d4008900c0b8100c281c02c01810307082801450b840c04c1c1c480903503c0601a151145018040104201d00d80c0640c0200040b010883c03400440014080c108411000f0070200f6141c035031032003808a2002c690b81c140d140100503040c43e00300200c4600050030a08024020200705000205422500500030180079440e261003409039403051111000749105210f04241c82e150141c40507600128404000c030340d048a007103950340030f00c07030002c0e034000d0214105491144000100082c1050810742d0000c150101401d1032640b0b542d000000d40b910711802241107202c0d0010f020521640c50154080d014003401691040d040c45040d130360451845d0702ca0341095011031141807240b800ca0804c0b1600e400581415681981011000304031b44280c600043d200030149500800040e400c4c0d160801584000c0140700b4041c0004560308002c06981d01c6000c00d0300e0b01860500400c41d00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 103783228 1250 103781978 103781989
    0x81b120604050a0b150d060212010803040617040602160b01150c0305032d0c030a06090606020a02150c1002190f0801060e040207140d020723011101061a070b06 70
    0x80703030350003201411010042e0f40d160344003103000418100e8401c44030308082c2c0454582c258001e80251184c0c000603501c0601800c81d083d04101644026180c1c1d008001c203101c800c0e44440090304030104100c0703080f659107c0b480c1070304c0680240c0c00e030441da01d44214081c40c1403201c1005020b041f038900c141070307135243d102d1000c01f1a0801401c480150206100700081200d6084121f03400d2001c088a00014a0350105400c0a40e044401508d01d90009130b00032060003290f045600c070701d900608502c8010800646801000703503e1b2070380210064862000300b00341c04003c01000c011070303c00c80e20035000c1c0d80d9240134500442009410815500058080f01140d00d034855000340748154070241d10ba19020784603031815100b00c0709030044400b0283c120b07400340050000a24141010101121031070042d000b412440000246441ea4682c802d40091102d05081241c1c3c58060729403283c1c082d82031a01c01000b003415104a40541030710362100100c8002d0301c0b020b40c0c50f442440050700702944503038030312017032034542d10304100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 103784478 1250 103783228 103783231
    0x209040506030111070206031801020f0304050c030616030b01021c031a04050c03011701110d050106021c09050f010203130308040f0e01080601140111010e100c050301120219081b1206 80
    0x13000608100b03d0140985055000f031903104a6000000c484000f0400b801c500360782000204250900000c0140410407006029210700d0480540040c9024588500c06409500d00b0141010505564421060181c1d100b4400801480611000e2400241960070020007c180981008013842082d04202c0701600d0507001d080e0007035480395401800c590078442500c401b40d04024a614040d980d032120404500304c290081d007800f91940000180c59072421708040d040c003807a02182c5503000180d14410340c0554001110307600340c030002c1d07a100341d00300b4a20006070702d9442a2900d04100c024031718400020040c0e04001401561407480000e011240e44480340c14804000b030040c000141c100b20014041007030a544621340c05c03d014505130017940e690101c403d0848000001705846500914519070b1406068092480d09041e107181080c13940d89081d020366078104041d1b01c001d02c142c0c0d607014550841d20000340300b003015040c40d10030b07034104281c464043d11035103011400c902e0052002e50f9a240c200c0e940401c405 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 103785728 1250 103784478 103784501
    0x7030e0901180e07180b0d0b04060c091e06030b0307030501050103060c02010e0706080406090f14060703050702030a02060103021009030c24030204081b03010204090f09140c0112051e090102090405060301 89
    0x2401550014417010107445580c0c0b1040d0099001040000410354170040c050145000d81d1000940c001c150b60010104442e0760011400346030642070920b650114101c01e00b045920b02d140000c3d078030b10f00304002800c041703c6500c00340466003480c1c00481442195031000350080210b4008200002410004680301c460a101d000f01080d0580001804940c075074111004036845801e2030351420226541e0300d020200700c01d5180c1000c1d480708040080e41c58040c0304040d001202030009504220a1400080d40c440e01408002c0c020f404514818131510b0151710700d0005140e100b21100280c5880b8030310b040c081802400c0203584402c112280c811000e009108a42c196101100944100c8018441c604007030f440c4010902c1c2c0641d401c0000045e805450311030f0342000190040f0100d509a0720b82030903810340e0f4003040f269029400c542818012a0b8021b059040a042002c90104003940d943d0440704d140c407141c101641903050b4401c2042002c2c0d4040d40142130004c0121403c01c8103484040500d4222010300108 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 103786978 1250 103785728 103785749
    0x506030610030f030e060403021305060306010b09060a0507111206040507090908161a1302010e091509070302090a03030503191e150503070b03061002030708030a0207030e0901180e07 80
    0x400f000300f440f940d040ca10b0a100038000c2e40c42c0981c1d80e0701291602c1036002c1d46503c8269604140455480e040c85482e0060a000c4203603410909548000b8201d031090321090710601c03038009a0030040100b00030895441c4800244041c0b20100c0410f501c54a40c0002c0313070100c509020307032a00450000018803612000c10f80102d030303143c2000300320140d0101c203800d040c0056411407008401000081241c40c00c09104910344242c0e081c40180c40c0c8009089401c4989070790f842020f818041101c443d10142484c1110142103484421a484001c0260000d1103131000349034200c0c003a880044245504200110302410720046102d0403020502c244400321001c084c0241148a2484203910720701c10f00c0c0c2c0000003440080c9400380c0c1d41c0380e92000060701e0003070a98000b80d10080c02000300125403801d50103403506c0341c4030342c009149041e009641c0c81c0540c1c80007c0c28100015070100355142814400d06c09140c02c0c0700060000240c40d61548110112621054050100c05007000450300240a000c90040c0c100c1c1c2680c0f11 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 103788228 1250 103786978 103787003
    0x15130501030b12070303020c040e12160201120c0815031b010807020718060302030f070e0a05040609080304030c060c090605030402211608071202010e040b01090b0d050603061003 78
    0x45000c0c2458055066003c2d146410021a000b020b000101c0158820b40090195428407814001590502c0342d808415401c05510848003070f21117801c942940040b44c100c51420700c12480107032210401c5041c5000c0e0680351016103003000340c202c098140200e94010451f0720344420081019a1664050a00010180c0c80320448000354001d019241d08055a0700641c0c1e10310741c585800500029142c100103517070584645040007503050500006602c4071800d0060003545040903070307800300004003074520070170380d0399880014040c000700f9849280040c0d40400720565a06103420b0080c02441e43c00d009440e103c3c034001951207201e000700d461130100e403003c0e12240d00b196190b800300984442500a0980c428000704440038240f841881981000ea9640f12070f402400c0c104030f441440c1c205641c000c141d4100c0c0b0013645e800580e800590304104108200c4000c00e5042051004a41d4509654041c00e0545408241e400001c0c0b000d0f04158800e0070103404817489551610941d00a403070444c032001d8001c0503c01c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 103789478 1250 103788228 103788239
    0xe060c030d33140d03050a0f050712020303060a05061c050408070203070602030c07090b130906090c120501051303050307050a021203040303022a190623061513 70
    0x10001c0703907140300b605940c0d40a03200c0180100245002a00015000c1841d84000d104400b140f201c101c9030b010003540d00340e059884680e0090110710451400c4428003900d01d15410300301c1d10400c100c480e0139500c064000c00c1014a000065620b810a0b01e80a216043c5400045614100101503ca901e0350402c04884010000803406000308005030068421030320400129003d030705c2c00c00c0524010700703840d802169140d6209803007608040c0c880e040b141c0c10b00c0c14110341642c260b650204694905410750000155044145046030007449424001401e07400d90707506c000340524210500343e29041c0500b00901030b5540300170b0b107600312900001c2d0040218a081c4041000030f4800d0f405420011b800340104c555078844810740d041c25800450301100080c1c0c0004104600403488521110749003803229440131002d550088054440d003100700804039404082840c4130511840d500720180050f801807034500f0280901e0800d9114043c2220300c5800b440c0350b4020780c400d442d01c0104403007900071000d240b0301d10107040c803 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 103790728 1250 103789478 103789481
    0x5030d09020d050a03020307150501060c02150c01060602061e04020312091c050c011d0d06240803040609050d0c0b0711041a010306120b0c09030102130807060e060c030d 74
    0x4000698100642010b810002407040103903c440a020b60000c0d40c50b11910301e006150143d40a6118407181d040000400c012900034a03030940155040300c108001741147e40c0d016000d406420300b150144d41c209040001c441b9000300b072690060766812504440b90358135071320207001c50400350342c0250540c3c041c00d00264030740d900001514040400a041d150302c08001d0f007001c4d2508034000d100781c880b508004951900b43da040002100c0303800102209103a06070803030000036680c006103007014124035290f10182528281d0182d00003d00c0c020454000d07002c41d2250001035594015008a20119807400c4000c5900e203410707940c00040d1a400810241e0b1b1038200713001d21071150000d03c021216441d0b20154000705590354001c10f8000c50900d6451041118a500010140c86c81684031900c100312412045011135100c58001d0741c8140206406070341c81c00e200c0d000c1382c0284035260101011200322040400c0240780443e680c1c0032603905980f1180507102c1c4004120b40ca200c2c24000c071001c1c5d803040040900c81c4006 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 103791978 1250 103790728 103790741
    0x9040201020106050d12031a01120902061603080901060e1006052805090405010b0f0706020c0a05060c03010320180910020d0606021b240c01020d020c0d0c05030d 71
    0x41c400421070382d40c0e900100b00422200541280c041031000c40c884101c40d0b03d8412803014a0704d1560407442007280c03100182142050240800c04161252004015074403580c04450444408000003a6514094100206803070420b80e600746495003480c1d40003450002c1450079074040c40c48071900c00c0347c1d5131030010103840310303070080281623010740069220034400c100c0c900c520b507210065521190346d501f500d40108400c80e00141c0244060000920809003011415400c1c0e80b083c0340d0203140160354440440c2000d01d809d2240350001d14a110321340402c5004a440c90146040340d22900220401c000d40b0440c2d0320b840c40d0700035180343c1c00151503071045031503074a881126a0003011490546c0d90403004800058243da11000403003140c2c80c0c40d10b0017045000c3c0d04111811042c81c0c48154181541608070004840340010101c2c4c508450305118280c5000041000303c07450004e01c040210355906294008002075009003804502034080c410380030f082c29019243c1c0f1744180354420059440e0030004842240200311 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 103793228 1250 103791978 103791983
    0x10030201021c17010b0304060b030109030207060c05070b04300b070807030b03120406020f070b0306040b060409090c03020108060102030c0601152609011107050a0209220c1419050904 80
    0xa40f80d2819680c03840c00141c0c0c5001e46080c11a950740d03441c003401e21406807034071142d03450f02982c904801c80f000304c0d5002c901c98090700da00d46008020021a42041072400b01030303422141c1c0700540000d0004590310090500b4000003503141c400700c99004904030400c2101c924040c054526401c1e440000d010384e10812070300e54045142d06000641d00b5034180420b00c0e10008104c80740d00c011001a0a0003801e404104070000c006804004202d05030a041e041c544602010388064015515103441118940e1502d0a45015006848081245450030705000009440c41c2c441640461212404241a5403000c0103e408001080c0020000b80c1d182c0403a07400503400070050201009883c030011441d210074100e0034251507054050481d03c5082402d11a421100003611003070070404200002c0c2e00003000458888966601168100b001b541c41c4070010f06401030141e1010a4a40060524810050020310030410343c0c00c1c0c0040307603000406030001e1000c201c200a54078001014000c40403c414070703080002c4c0d0303401031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 103794478 1250 103793228 103793237
    0x61801031d01140403110c030c04020d0905060f060405070804030225081015060203040305120306010306090f051005010534020d0507150f0e0105180306070e040510030201021c 77
    0x101c01444542c2110035103e5041c0e103034100c3e04184018980d010009210601060003d001c410040f040000d568205420509014a03004618990204640d620050440340c0100542d811842c2c02060600c034000100c48241c4220701d0070021441180c41035203100d205981c1a002010f5801c400c1461000c003801103000201511840310011070944018003d0040c01207508101007031011040c100c100132a065a01322404540c07060008101050002544030020004500403650b21744a08004a000e05555003200821501b80412030380644031660280e442520300f444178650242e2034200444540c45011034031859825103041510700c115100a4009189514100a00307411101d60b01185220210441c00c0c0c071140c000c40810040000d25103114403038014a40b8021001c0c0c218410090b00400002c00080d040000c00720350704040310414000020b0942005045482514040d600101a221400126402a0f040202050004000040003802d07260305030050604030030300e902100344255000c3c8900e030800 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 103795728 1250 103794478 103794521
    0x10c1404030f21050703090801050702030403150b03010c0c020301050601170c09031005040c0611060103030801180f060807080d03140609070c1b0e0f040506010e06060409050901150506180103 84
    0x3e83c00102c5802040103031038268940da43c5080c064091a203e512002c0c969040038108072015034040100d4083d82d900c41c011401091902d45010000c000507156940c02d90b1900c0348880030641c00818903400c15100324001d10007680c4400045450080503c5c24020002089011805107076120001e09985003014003103a000c00ba800e0b02600554030140c80581d900b10110310288500e641c092000b484a40504004104a500d0b40d580200300900510500d403c081083d12030040d8100b103a04140c8469018110511000d9140c99441c0c0e2200d81c80d00c5014450b01c40c103400d542ea61806402004002d16100c00020302035a6a0000c0c08041e0100400b004204002030070344030f001030510710340c6a10300403550049240060609032601c1c00480043d00c03a8a080c0008030800000407400500729054a01c907800034001030b1039010110f143d600594001510760b5003480208601050305600c2401074800c0100c4c45201282c1d90000d02c01140719811001d810204900d000d850103502039040701241c1d180c0380072074002c903 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 103796978 1250 103795728 103795763
    0x61b0f03021e0318010e060903032d090d0f02010605060d020d06030804170c042c0f0d02010213060c0507090c05040e090a060e070f1715011502010c1404030f 69
    0x140d1013150729140c03c0c56500c0c0f041c001e0f80c0e401d100e0065980c00c004e001780840c1c108a8078684e035a01004026004480f0800c21b460340d80242d05114501c480b25000005c200c03070070500d0380c0941703503250004a0030003d50f100c1c440b1003105105000e800103e0344003074252450108d207807103000c0107035003c00c0001500c19290840080010340c0440100010800c034150003900c1210280e000382442560208c1034443c030300307184103003440840184081c00300714161114030080211a0354400d0500c505101e40c00c155009a0201c14855038064008000c440000c000400c112611a074060f07441c03010f1020b0241450348516000d10003600c19501c2040100341500f06941002e40e04c20000241800071694215213070065094a010400300b0301030b8903082c8291700064810b43d03007040f00308d207a043c46030700c9403807101c2000c1c650940c46d018060101c01404000c0383c600385195a11801407000820700e811042c0c0041d0f203092041010709216402a00854030480ba5852a081c030f180c07100b85c0d03a942011819240307980e038600e5600e203 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 103798228 1250 103796978 103797037
    0x603050c130b0d050702010603021305091011220f0e0c0c07091a0d11041e050403210507051602040f05151509030a06110705060c0403061b0f0302 64
    0xb05007155980360ba5603a0301c1e01d6902581d101410200a5a0406ca010310042c1e55006603585902c010002c001a213a460b00003c5242458030356585801d54a007000c0714a098440354003c01c0707031901400601c09990a100c25162004415105180c00d00341818010f0104090300d0011980184200010a0415908203401802d00c4065848020242c0d45c8010320401c0710b03404a0b04850012007281ea85c45c103000d076610741241260040311070f01c0c46103668541496400390401c0000c00000c2c2c4407032041201e45400e1801a001e20701c400440c1c2c0280c09141f0b20b40100c0605401601d10580b65035454606181c002d5004c04815141203d049034801d0311001003030741e41d8009104440c4030303900c12100c194224508070180810794145904041e0340c100104214038168030001400c09030301c1c0d0b01803000580c00e0300030700141e1518003500a0040c2240101014008000d43c00700c06002602e00480d001c104500d452005445030135281f8010402080d03035402030303130310407070196018100d11140528041d4910f00c00131003000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 103799478 1250 103798228 103798267
    0x30f0403030b01091d07030b0f15030703021303080702151315050409090b01061103040303080c09010318080406140301031a0403090f0906170303070203030c0903070e0901090b0708100603050c 84
    0x10681800f650030081110391600802d104584260b489d90303041059040410813544d014800319943c4140000890150351095044900021205e05104c0200e03840b454150040e50144806034881d05200381d40c20011701e0014215000401d504020140d01031030075030134844203140c403075194092107400e01c0001140541800355480d01071003080100d10b00d40c1003410240c80d802d03d071405540140d009000610000c0d070002000c1d40c105035000071003905c4900d001c00403400b80018030f03542d01804461401000c1000440c0c0044d20580300c4648401c0203501e0109503502c1e8902091101404d03a00d1400050361000a0807820a608240285440c0045075128507c1103990800d40c0c0c80031040d599124010450b1252000c100592180450043d40c07031400d11400007075aa0202401c00e40414000240b03009803954204003544c004c185011269036035160625950303000f00000c6001b070700c16141e51800141814440c5004c0c5210b6005000c1d1300c0c4003107051000c120020708000b0f0076100c20a2040004124488100c80404c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 103800728 1250 103799478 103799519
    0xf0204090e01020c07082d0a021002150a0203040b072318090603030414120304050a060801090e06010b1602031011130807050a030303091e0804090c05030f0403030b0109 74
    0x9a0b60720311440c8038170b1a0207031550184010341c010005083c031201c0e810b0f96003899089048011903101420000a60802c11083c0c0001d40c01800301200d4821250040fa0410b11030702c004040b11003d03601c08074100245c0c4800c0720020492204140040c8007035000308224804007000c01c142125031602c418810010b42d0111500303002003040601500e6140c0b07800080254030070026400f80d404d0501c0c05607907002d101031745842103100fa85c0880914034050010401d9a00401d00103254603c61a03176000f0290001c4000e0161908040c245144001c1c46903000560364121307100380118501d00b40d03413035a090b0007401c0031076000c81c0d00d8002c447c1e0600e4a10550302403a103288002d010580d580d806282c21a07102c040c8a940000c0c0542c00c048802c02c0682c0d00c06a1160440ba018103001c00e0000c0d40703107031040040b10300090710810b8480c00035060301840709034809482641e80461003044500802001a601800f0884a20186600860024001a1281c0c0140380703c00010306083c101c440d01e40d1366900ca1400c114854 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 103801978 1250 103800728 103800731
    0x15070605010f1418011403030d050a020a030501060302070f020907030f090503030f07020d08061306171606090503060a090807080705010c170c0910020c0a0902070213021c0f0204090e01 81
    0xd01040701c900c41d030f4214160003250201c80000016103403c450540512501c0c940c40200098022603131028021140302e030f501800c0400191034480b200ca402500b01000e818000380c075200c00400e60314081c0c400c07220250b4210100346d583c100c1581c200046040000d041c40304041c4c481c90001000781160160070703c601d10503c00340d034691528900710382650000500c0340007154842c4c1000301100e50040750007500140180c9041020f0340300d400007000a00400c0e881403074000c0d5003000c2482c10003c0440c10100c000f003038109054002e40e0f1072201722010803e501502ea807640048002c00c0d4260901e6011104c507500c03480340c0c41d007003181c5501d130004030390001003081d10079946a1a0048c02c26910103c01d042e0084200740b4014607003803060031003d060080e00d0341c00d401007500e41e105019540c0204411903004000900340d070022034403402240040d41125101302c0c003808030318401e40d101d00d45600030380c1d0340589607100c04101e451031070f02e804010300b614260940e071441c1d08100200791160390740901c03c0010f034442d00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 103803228 1250 103801978 103802009
    0x608060c0328110c0c030c0a050a030b060d020a060f080108010e0c040f060302030a0b010e010803040308040e060a0512030405090f071b0809030102040e0402090604050c031504150f0608070302070c051507060501 92
    0x5160411488500d03a40c8100d003030700c3c81071000341d96141c4820300394cd401400800041d503444000c5056500d050b0000382d072220f0300c0700b00002c540b80d02c00784696410140d5aa0240c0c00d036030b104182400c1c4d440304000300c040f9406c10410400d6509259010a898006130f071004600b03d40d40346c01180c105150b040090b205602000018058048203c00d01401816110002c6180c580b4580310299180900c1c0107140040c65001c01040c016034880c0428005004c0050100d116480b09020140c1d40740d00500c1200d0280c12040c0c002010300c2520070700c05105126684236844911051110b56003c40503404045521402c2440505520348003480540060285000440c09500306401002075211009182900ca1420030081144804051b000e50350003d2241e207840500e4007000c40018050001c6200c224031800400000051581d209000341c0211942c0c0c1d12459066110004203c2c268410030304058048820040e0410441c248140f20754014145107101c60f0412003580d4420301070310400e03402030240541c202d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 103804478 1250 103803228 103803253
    0x61303091d09071e030b071206060201050108100902150f040f0e0a0b0d0f14030904050a020a0e0a0e0c130e1906150806090601140d0608060c0328110c 66
    0x302202c0074000d0ba01584c4080c2280e502801c9000c07509001c010709900c4410082030740c841c040c0c140038900380c485034801d0000603181c5100038001c2100b4402d6003118803840249480d03810313440c490000c113107802801c070012400c2001d000c4541580b00040310b203189181004000b07000000e10800c0006042c0807500348000b41402c60048040d21024a49688510042079684001404a29626031140da1041d4a03040180e10302450303a085015011f622a002410902049181c4000340c4c01880c0700c0b40f090700c83d410404441700c2840051203260007205a0500f07100082034890403828043c04e01c58201020702c0701c4807610b46079a4111a44c00b079801c135120300202444403014070418001c02c00034040d4030030a140125482207008000010141015000300240f00108190380d210701d813000807982c08200407998401440c4d0701c40300200828131a000940c0903003000310311080b24510071240101104100e445500d102d03a100124401d62089503115103640e103810107026045a100035001d00b100b618082c081d016a540d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 103805728 1250 103804478 103804483
    0x4050f1b0f0604060503060d050c0310090b0c1c05060d02310e100e010e340b03040b070306080d020102070c050910030308071715030d02060603061303091d09 69
    0x70200710701c41c62090005001150384882034039440102280d03a84101c0925041490400364028011030300350162207030b000300c01606500000326880c803500300b41c140d036512201400598050303094000d00e034400d000740f181122080d030f030840c540000740245443c0c0e60b0790445d4001004a501e122080f03c02030038014030b007042d83c0130941403c806c01000010a02c88407140f40d641c1a2240e500d520704d9520103944134000074482409511800801c800c40c0101e0304c145084c5403141c4941c0c01c1c1602c00d20042c04090801880340d407016521001107540b20382e80c0c2c0317003151a16540c1c005411030041603a001c05950782d60020f0f5034a000c000c01e1554050680005966a2a5041030401c10005070455805441600c060080318280004004202d0b9018a043c4515480f0f00310110b0b41da1502c06400c461040a4070144020700e0180c0443c40c0c60080120101c98500344110426a12504112040c540c16088640041c1501c841d050080300d0070341c424502480c10301d4807180300009440d0800c0894600b51030820070060280401c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 103806978 1250 103805728 103805749
    0x3020405040915050f0f0705070302010e01061e060306060206070c110d03112a040e250608070e0f090a0e1209030610030c0605090607020319050610140904050f1b 71
    0x43da0307820f0305c3e1600c05518405203074050041420000d00041074414140b00b0b502221a0a110400030300205690705c00c46820b10040d14210428074469108c0000e00900900c01d1408648142d00a043e886c1d9400c1001d0360864507281050b40c6c051141181c0c0b10300b0340d0703034031000e0018a8840d031144044400135819052800342e2a07410340b80c401c8980c5210f03103070012403803864580784a0100c41c042004944078200e58202520b0841080d07051303c00c200014011442d00c04854141d56055a440c003c3d6502c1c0c0d001203584103510300490b6040002e5541c0b400321814050142a800b03098040d002c40c220000c601040e1400481003104509840046281459490140001a00041c1e1012414052401e5441b6101c108803184600400d00000040041c0740b602c444d01031720021034009040e034000041408824907486200c1c04116140c4c043c0c600001c1d48141200c000c001034170110a005a4080c1442c801d110820501800a891070300c14441c3c4012800c3c0200001e2507900244501b040e003800502c0b0520890804 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 103808228 1250 103806978 103806991
    0x5010803070507050907030e0a0b091506010806040b04060b0a2003030405151015080712020a1b060b090c070308010603050c0306040b010c05030c0f100c08160302040504091505 77
    0x1c0041d41d0100c0c2d0001505030a8500071201d19049495000c1c040d002000c007801c0900f09401958041001d0111181c5844c1c0708001c118180d4220b200165101013040104a032102d0120320903501003280b5061583c05145880303005800018036548170034402d152908024000000520a408040c01c0340c452088a040e00706200740c003c42c158100b0f0341c1d4864a94401c0f8181401d0103208800140d804803840c09000f00514040e102d154020488610007411110704846030400f00e40c07d4486100e00468502c200d810380e084550304c405042400054858045e41c681c83c3c25103402e504c900714045141c0e00c4c100c0a074081e07002120140d965011034600640741e803405034044000d0610344010000e20750780300c2084943c0074108076000a00c0901c80c42c0144e543c01c80c84200030304076100205140c1c10748880044c840511101041c00c03200785400c001010010f95900045503400984800e02242c0e0391074030300354595440360950902500346522100403604407083d00e0402e440c10300c0c0d24812206c90484504c20030783c1108 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 103809478 1250 103808228 103808233
    0x270601150210060e0403050705011e1a031f1d060703020406120501030b0a0f2409060b0c0304140d06020c010c121416020a0605040f05122712060405060109050108 71
    0x28a044940380c004000117001405000000990504200003980b01a80c102c807040c03031000b0400f07480741c1b4240090554442c03100c2d01401d00d1442d01000e1070005000c052071451603000b0034a002008160b5800380c000100c20321006418186650484041807254503c1001c01d99030050701ca914004000f00344e030303c0c0b061101013850700d030200600114081d980250b9116180b150702107148118413081600508a0f0281d0112898002e41501c548035150b01d00c80044461294046c080c01e501c0301c0c051201445404a00d00142c0d0042000f0451000d6100b40e618103080c0007460300780280415110301c0d040e039000c81c0d8900e4450350340780941c0300d855412461700c161034550620304010808814654440c00180940900c41902c0c1030b0102d00489482044054040c0382c4c851740c24001c3d030a20346000c15041c1c2400c40100c0320782c094404040c0c0841d100c1d8042d9900d160320307040304018940d0104002450f00901c00281f5402602062400d16040c40820402d40100e115000900b21580f6010261044aa040e000160340340c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 103810728 1250 103809478 103809491
    0x270c03010b07030e1513080624041505060a05041a0f07152903120901080a090f1703060a08071406090a0e01030305030f0618270601150210 61
    0x1072034000151046590303d400c049a590b035040c00000e50a4540c82c440512032040000e0240d00b1441d03804840c4100e071704440845031181c0b901c030402d583c014000000710f03813111400340d180301c414031701900001860070300e050700055030544682c045601030303110810200100c1d00000d410880400398a081c00d4100c1c1c02950207030b08251000c0300a040b140318558004d05149543e01e910140d5003029413001c02c1c522116071200010000700c200070000c2d55001c2850a02c40d0065080c41007144040034200d403800001656079002650b14504c185c4014140c079402640d05145180103800010700703d881c00d101c01c00b00c0c0f1842d030340c9903d04041003001d14642ca4003d481603401c0810700308080c90f0b582140c14040d2200f03d824645801082e80803070b0b59654207501445021049800010525030400000e5000355a903942d101925580c03c418030088540d55032a03c2c04020324000092400703038841a0400007056850440c0c800c1d0f11306551301d146070200a07004652942098101556a540c0400190314910134450040c44107 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 103811978 1250 103810728 103810739
    0x70903080a050d0e01050108070806090c0a0302060304030c12030911030f060a02090f0d0b1e010810050c0d05070e0a1a0906030c07140c0a0503030c120901090302270c0301 75
    0xd4001c0c044001c040c010b0104046500001a0700114008007814000b0040c40da955000c4669411030307880341e02e00701c0c0500001f141e18048041400f10740742001510b9601c60500d15424461640e0000300250100b105011420340090000300302221124025900811482814100000c0c80d03400060346030300c02d9001c40381d00c0c60002d40101c2c406502400b0403034010f840d030380158081800840703011200740d481141c01003076004201101104034020504103911000c02484d40e401ca41e0710400a004481c0f40760b100c41191018010240c000c541c0c0849200c1031a8106144000c036941900d800780d03030082c04980b001e0700102c1c50b030409507074180050081c400421a031011075582041d03e446410f45e201d0040c1c2c800000a4850640c8104a500c6030f030348940345084034403030100d03800e88034420210050311594481b8000201c61a001003a6494112400003a1410900e00341c0c60a07030a9201d1181103041c81240c1000101503684d1403685180e04413040e485030410401303000c201126000040514111200a0006022 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 103813228 1250 103811978 103811993
    0xd02070f110907210b0a0b03071b0f060510170601090c0201090803010e090c0a1502010b0409030e01080604150e010503010b06041a0a14040909050705040c0c08030606070804080a0b070903 82
    0x43e4404813401c1078400c80300407110380007601030241c085420a410000c0010f1100400c0001c610407001d03a594580f09503907241420714155090704002d091508102e004201143c1c095104642100c4800a2080c10700d0b81c80c0d08058001590f101c0c0500c203a00144010040000203008211140340c04c0d01c02000303540c041c0e03500c01c003040c001801030700414180440042c031002810018144c3c80c000041007c0030140d540c01a55284810411024005500b0b218040b0a141003500940b038940ea4103072120541411058011500d208004cc8000c3c0d22035102c00d640381c0b600a10070404c00250140b48a00b0a903581400289400c0d1040410151700480c0100300c02c00035081e4400c10040c0e20250f004c581a626200c4a008031800c040c0312103070001c000000900001ca10320594401100c4611400a50b00f90603690000c001c02c80d9210503506c13011460100340c2c640040c2c01c2000465100744010710b094180b0f00c3c4c41d00e4189654020f6005030181d40e0040300301d04140650740c0e841c01c0c1d1040e0070345060300c3c003a4110b565900 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 103814478 1250 103813228 103813247
    0x100906180f021c021c02030903030106030c08060d0605070c06020a050a02071a04030209040f0819021c0210150320120109020f0904020d0215040f0e1512030d02070f110907 75
    0xf0040d0b8086054a40116111422060f20840d90000c0d9102e062840d404c0346c0340d83c000e12400010030b2400c449494a103015407a900d104950090402c0c1c041c6d051502c51a0252000a00071010410107800c81400680c042c8058100c140084d500c0c07a4503030f05121400f80ca40400ca80080302d544003007800c2410803030310b0700c0d0489003580e034183c40d5581c407a140d6240901c0c1c441110714004010500201d0100d16414120f1748030b0203660100d1b4204d568100c0100404400010030b03040c81001600100400f0801803420380107440d205801c017550307813001350796500ca4460610100b5544042100d12400600b501e00e07003003001160542c2550020840e5001580c00941d2100301801d2183c0100310107000a002c0d0340e038058444c2412a00501200c480c0040c00c846030b8502e03401401151505550340d50f0100d40c42910380707011449440340b102c07031000c052051410043c0d407030071200d500c401b6480100213900709022140040e0021a204200c2442c00c00c0081c6003600e000940501554010650b49040228403a480007171803 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 103815728 1250 103814478 103814527
    0xc0306042105120114040b040c0801030615050409060b09220f020d0b040f021c020306010509060409080a02071508090c0118050a0b0c071715100906180f02 68
    0x614421450031000c0e9401d00808014901d028260b6000142071918171070020220541282c041115400036802c01c4200d603401061007000408910050000034030b140d2184084084601c003d4440b40c1e501c100040036540d0300c041c1110303426194050000781d828500042a0841601c040c11495055035083d00b0865660404016103040c030380b01c0458081d503c1e2400402c002c1e0780c012101141c1480c150800c0408048010300803401006c0c021050300721900680d04008146500801900c941d0f407812003044607000380a0b0002d45c0c01995242c80100003100c104c0200111440c98015001551401d000540651b407500403030011700c60910200401802c010070340302c034855400d080c01248007034a07512810f02000d81d9040a030b001140e418020401c000034001900404a03984200c070701491b200c1140b080c0005440401c0c1340c15510085d5010342034130340502c619600003a800e240300c0b800360360341520000b41c9545a0100300d0408092101f02c501007840e0044a5207901030980540c98038040b825402d0b841400d00270398 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 103816978 1250 103815728 103815773
    0x6010507120e06040e090c010519050c2b170f061003090215120a0204030c05010c03020a02090c0712090501210b0607030e101e050c1507050a020c030604 67
    0xc81d0407034014030349920110009010903440d01e031513010480c14150261041c4d440b03440746401c100055840b800c121140713240108039900e02c3d00d080541c00c0d82c264000740200310302c600401c0d0070f08818800e103c40c5c4401c04100040e20b0b070008003090102a1455101800b07440000b01d4100c10070040c282a0300310141c000000352007039a030a10a80404a000300703c0c142c0000e510070340040c0e1168103401e00c1e502074070604648a1041c60181c41e1071102404034400c070302c001020300c2e010b042d04100c1503000d80c0086412034040e00503200614125400581d00c6402100c000510030750124071302050155030424802c0c845803504051070400d040c074002030700c140d0380d2100302c9180000041c3c11086008660700503007031803d03000d400d207501c4100f01c1c40c0180490140008180c000c02690488400e001d1040e1101c1c031030384008a00031801e031000c03182c2c12501c951180000501340e01c12006109800070114010130310450107991107680766402c1c1c5500904140c06a401c191080e403001c810710001c80c0e40c0030700f41042c1c0e4034150803 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 103818228 1250 103816978 103817003
    0x2030c1e0c0615041503020a0311060c070902070b07030209090f0717090102030402150f0703080c070203031b1c02060109091b030507050406061b060507020c060a120c0806010507 78
    0x20140518403580c180a8007502400c000c1c44428110160140c0ea081c1c0d08075014004070044d00c240e21008941c40c0f202035482600d0003010004689102020342e02d040000d46901c1c03820034001413151914a081d4403980c01c1c00d41c002003110600c041e00142e030350000c010349010b6203452860700000c1c04108002d04451100400c0c900800e00ca14007500003100301000d800c00500880c504180c1060007500300b1a402d90082c2c40031145034401c561703600112188104415612824102c0319101290150001040da0582080400007100565010805085500300e81c4400d149407503c0707a004ea6081c032500c00c10001c02c81120000152445401040e1281586d00030100058000d019040c9050b07003065a0b40c0b42c601e642c488580c08000e2040c081104000d41d9016602400304942e00c001c11191410400f0b01c00146242082202000403090f8100715000007040c8110b407100d00710703103001441940c0900182000714044951503d0034071058010020310a4690a00340894640440060710b03600c5440f1000700010401c01 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 103819478 1250 103818228 103818277
    0x160f231b13090b1005010306030305030106050c0102040f0b030604060e06150306030c0a260d08070e130c03021305030109021c140706080702010b0d0c17010204170a0c06020102030c 79
    0x81d64800c03000780c418441d19842c0d0805503990101a01c1a4200204110f00400c0039400782c040c10f411694181d07074061443e880d10310304640c2c1c1d41000500e0880355408210004c0c4025035100403401503d00d1002a942d45d05000c010403080314501e5001d5200c0030a42d80400603150354811524000010052030255656500b00000307003454110b8007105d601101e4400007040e00890059910321903d01061602c4820308080c0c5201d41d02c0075081c0782180000e014100240600d8481e1400c0d00342c059001d40614001c1010100c10015110700111a13070000e91b02040030f000d080380ca0b0380b105000b840c040d4020814a41036401042d07003003102402000c070481d1080c121b0b00c1040748551143c826424524150380425840340002400c180054a031400190f007800c060344c0c03c070b2030701d1141045103590000440a5082c030701640402d81c82c580000d0b140d810b550a00001604120f1400c240341d848991902425620501d03151a150b690441c1d00702c10110ba105000700b03d164881d00b41182c020401366004c5019000440c0c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 103820728 1250 103819478 103819489
    0x50a110d1104030506070309020909010522022106060f01050301120206090d0f08072d0b0a06080106150810060504051c05010e010906051b030408090402160f231b 71
    0x6030f20040861080208109046505a00c0084441e10840e220103075503c072400e40760300f0b1310790990303411442031505100c040344200d1034004d0071005440a03140c00d8071007004000304070214505240b103000303e4009a040012500d4000810212a01c09081031070442d41803031350807000181c11145c000d00440d40015840744503595900c80c2d03060b82f58802001680e8410700c1c40e00c00484d80221008440d44007286041c07190000c1c1e1064040324481583c04110443c0d0a16124016900f001825011105556170000714150350207004220180c1200e500140c1030000c0b8180003021060020413200e1450040c450070312480d40d101b0101e504441d401c4032200c00c1440503510440140e086500000c140e90b10f00a510080c00b60103410040145006410800566607003406c2e880b4805214805001d81c0d171303010400640015520741c0a445c5042000d08014103100e00d6031070016100d040311078291402850110780c541003250448009030110b01001c040351540c0f803130340c984950341d1042244130346480d904040c0c010b00e16140c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 103821978 1250 103820728 103820737
    0x308030f13020d0c0f0b0403050c090414010603050a0c06030513080901030b040c030905060601030e0307140f0307050a050601140609090618011806140604031b1d0703050a110d11 78
    0xe040507043c4126240c442d000000c18840d0742040d1a46500c006440b40000c4281c80449030494040c0c241c89000034100070001d04024000c03645060304c803420704080c1100b48150805184a940100802400c03420050084595680a40d04041c2407004000401071282e200c0d0061a61000340c041d118078035000142d0140a21b00c1403281c01a1801d4070441da0240d00d50400c0d92224055000e403400e89c2c031452b00450940d20401ca5003ca90352040058500240c01841d9036000003040d903042c0d03080d01c502e410209045a0000300b064070b00f03912a000c00000e21005025240c010500c8070050074108004030003051080c06501052031140e100e000002d0015101c240f02320025152800c80d4100643e140c41c0ca440103480b410100312440c600d1319401151215110004103c052030042103a400d007443d542ea11301c44500c15201c00c0c801d40c45242d0001401d00c210318441c1070000e0400811110514045000404651009119402e82410903110242c01260003040740c1c100d28240742d012901000300d2440200070f204 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 103823228 1250 103821978 103821983
    0x50d0b100e060d091a01061d0604050f120307030305070816020c13330e1e04031b0b0a0509030a0807110c03030c030307092c040201030b090406060f0605040308030f13 73
    0x440040906001c0e400c640c107050b120191251101003200c151480c1004508d030224a030440c0c0100b00900c03552510303041d290802e4a00900d1b100590260702c8090341150403070001180820b40351400e2140c200c1c1c0224600f940040090080010811401002942c0b0014402c1150295520070402c0810007a580c000d400c6020341d4801c0702d00ca00f00f00b45003801d45240390351030400201400200106107500602c0c0c840c0e0045c1c00c5800900c0c807030b4403003c20044504402800032400d103c440310b0319460501d024044241142c1c0118459595450010300e10b2042c1e40c001802c60320190010010250700982004070250085c0c10b928002071000f50f901b04103440e100c4d60400183d4907110110b0503184052000000714410007159480b01034007640d43d13140e0901071070490804140d40100d501e18050411000f1645903100d4014076010441c860048080f0b80d203150f080c1c8003a036505407100300c14090300c10a0002480140003a260052405195489014981c04041e00980050710600c000c56140d01014885202c05034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 103824478 1250 103823228 103823243
    0x30a1407121205011505032403190b060105070201020a030305280614030307031715040f0c09080c01050a0c0f12180503010606050406030b0d12050d0b100e060d09 71
    0x1803168007908098a10350081e000508000010031750445010001c140d0940c02d845460035515440e4030500004010b250000da40c580c026141c40c155602001201c000c500b00411045ca916001c0c1050954080000d143d2410300c0402c114440050364001619811b080d0540384c00200c503283d40d00e064000b501074035074400a1805510300c2c80085101da603c52021190500507849401c1c00e034a00740b680b240201c10f405030124040b15407030f21030242d45003450303680083d40c4e0300c240005981107070000381203405001d0011401c03030303640d51000c4c180307034000311000040d064800051414402c8400020301620500b1460802c0055074012101000300303204028245581c40644c00c08003030b0760044018003580010b103010842c2c0a201000186a04041c41810160380d0103550b1186400d00307004003074001e03109498026802c110040c40c2a4045110a0480460700780701c0e40c2d03002c0d50361a4a581c094140c4c2d0b11026103a100e840c0c4840d040c5040c54000c2d4000441010544480c0d45a103501c101d41c0340200000d100180c00d00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 103825728 1250 103824478 103824503
    0x13151e0f0b12100e150117060604051002070b0a0507050607210e010f02030a020702090112050a11010203210703060b04080d03090305282c0105180303040909030e030f030a1407 77
    0x45a14901c5c50140c14280e9a600b2142402c2440d10055001034503c140c121008000a01550804403c1207035090810300444490b50b50711024894903500021140001400100309941004810300000390084c3e990300c0c0c20903100ca02c079880b202011600f0317040d004650f80c3e99036404844200a42000b90f0015060208545a15000e42d440b0007030b6000748401c038403c5440500102d98002c154094003500c070b0b00b00d0010580b1b030130340d50b85000350b035540f03000c0050540c4800e01046240440002003081c00c0c06d03d1a2040e4050704104a01030f06481031a000340c008041c05110034000d1180c0020b80c9210a40c692901088110003410151a68420710b111181c0000311440514103410300704689001480b050b59a0a409005110310340786c8004090307241c4401c0b02001a0144110341c071507400340c1180c2e032641c00ca2070840326070300c00043e00d59805588a81d1440d40c9071642e1307106050300130000c0e000480c3d0030307005003c2210904d003000c1e88a00c90101d1540902c0311441a080d111511301c016a15031960050038503400c0c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 103826978 1250 103825728 103825741
    0x1140324032d0f1c0305130206070c060306060e060d2003010801020a08061e0d02030c03031209100b1c080d020705060906090d0e13151e0f0b12100e 65
    0x1288103203240341e480784910403d1829560002944503c1000407051090000c40008001c9014000280600301c9480412801802603a500710040106510a170f0050983ca403030006e014040d210711340e20030002d003d2508004103041e1199000caa103031041100000800c000b00681e0751140143c001c1280c2803a52001c8008151048158000c04031060755031107807210ba550710b80c01c00600d000014040004d41010340c01c0c0381301070308000c12204030305131004041e5028140c40001007842c41e00020a02c43c424000031003808000102440745400c0e9150720756062201c20f01c0340021070074030000f6181e4990044846518002803000714403d90b030485845076001d6507203e010b41441341d80c40b0400d44100d50a80980d01c0420305900001551840c0042252140b441f4030b42540308011611242084c1c481c061a120358007507040c5000021010040d021303184007520f00039060700c51602c00395403d4000e40d420281482c07092001d0ba0382c040988250900c410245807440d80c030280c074046904801e602c03c40d9404910000d0110 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 103828228 1250 103826978 103827043
    0x10207051e1f0609050c1b06071d01020705030d0905040b06161203020d020403080c0d0e0a050d021302040602210a020709020304060906140717060a050405040503070f0b0103020114032403 82
    0x8032000d01c21200b02445500290785444071026149a80412494ad2504014032419001c9500c01719050040d600314541d0340c400b203414204070102c1800040d0031801e00380124502480b408213506030940b4050b0406d03d02d00303480c81c1d4101113074402a0403003c14103800e00740540b00703070100d400f5882d20050940d01d0303595a150601c9144c0106c40d041c0c07550b010700720280900a106030894580c1c1c2500906c1207007014903040c10300c10501010b103c00d03a00449011325140c0205400d000501c024101340d4010a40303802100d282808a0100b0381400d400d0060400401070030b5540000c0d00c0040d00c000c1034005a89484901d8040020044420002d01035801c02d41c484034560055041ca0388244440d0712121441d440d60460070307d441c4030442d5000c0d400f66003048140070f203040640c055688684250100c80c0352036030700d80766015182e10f1146c0468880c00d10400510855034000d150060800344c44426a05504020481190401c0600c4000c030f134101e000c1c095400140e80c108000c06002c80e05007400c000c130303806404c500c04 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 103829478 1250 103828228 103828237
    0x6070b1f09021803190b060402040e04050d02150c0301210b04030207050907050703050708071e06020301031101030509190c0f0602010f0b0102060405060a0e011b02010207051e1f0609050c 82
    0x140c00e028541082c20140c1000703e10720b0245003040b0880e04d001442d6070b50f220254840030348101c3c0c00640c02c0c0004a2f907203034260403a41c0100c0c0144002c2c550120386807002854688441018546020b550007881208000c2c003003580d0544480302d40c0d0f41221141a001c45481201d41080549940d6440e0244024580c01144500c16148240d82c0b6607400d94421100307803414800c9210041c0014020400302011a412001409600c1d1140004034001c82d051040801c1c030412101c81a904194004010001c11408503100700d015002802d00b427001d4a42009003646581c0303102d5a042c0030140010f80b907802c000d024407041d009040007403601c054103031b00d0b08002402844c0324441036000c00d142c07609013a0316600000b65244503a0b40040188190381d2084a01d174050700740b60f017a8600781c1d1740b0742e401841210001c98103002d0b207648a82c0010388403240d6040c003924011004044c000c4081c4000f011110141c0301040d007a404c45420010344580c2105406218020002c641c0305064041c42d005c107000344c2030315010041 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 103830728 1250 103829478 103829497
    0x10021206030c0603090706080c04094821020a030b010801050402120c0a0c080703030b091e06040209010903020d050f120901050d0c030b03060103110a0f0506070b1f0902 74
    0x302d190303110075014003e0b00d101c1038503107540e503038070180c000c0100d9440392141c1c5a0103201034603c142007031307961080407054a05c2403c0103840c03001d000c070030060300d22007000c507440301c1e1070035454402c501400c000440c0541804044500d4100a8241000741d041c040e1103072a480542e186040071560b50420b0000200203203000900e090002d1030541c00042c65140031300a031510041001c0100c8403e40311081c01c0750b1194400c41c6450140240b200200e4003207140d0300045d0020300c2c040d403400300302e1251810402905402c000c0807407001202048250000d440e0040d200d50313100c44140d80069403101c0240041e1145081c50344005d51006050344400304000010a140300d5417401c1d4002c480100a04028030b00b02c40c05401c02c140d0003c0c80034042d10a8054072600031034002c000303174240050729400c8240131a0900702c003600306407414941000c46041c0c07401c00600b214010715144411030940c505110000d0041c1c0b02e40d00000d0240249000410a8042d100251802d40203030b500300003140c1ca40c0c54150074003039000407082 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 103831978 1250 103830728 103830733
    0x4091b050f04020c0c1207030c06021b120604031b0b0117150f130204060308190914030312090102130e0603060711100509030c010c030b0405090106061b02031002120603 74
    0x41c4000c604090080c1c80000c0d003007101900c0c55410000070320400040c20402d021147c419540000049540d12901101034501a4085c0c010b50b00074003d02c40040051000700e60007026102c1c40b400d00c1d03000201c0c1e00d0ba0030540c1890300d115041c040802896030015460800b80440d40080000501d000e84140b1803410703004034006441d8002038000704421008800c5a0302e4000f2241080018120815040d510302c109100900018503561691200e814540003007015651815030600c0c8039110b9500710100d030004040c0100c070000210315502c04280c803402041d80200310410f5060100f081100c003034040d01c044500f002012212559611160002c1002c260740050180c000c40b00450341a62052001d0618500c000d0010310b07041040548203802020000c2510109000a00180301e15001c00c0c040c103103a8051680d0081606401c2100300021078401609035002c507807421b00204805034000c5964251090078402440e0304880341e00100c1e00300030700c81c4e541006045c40001d40b00c2690741e61000441c09031405408 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 103833228 1250 103831978 103831999
    0x201060905070302040f170a2f031b09040c05030307030207170c090c0a1e0903030314010602060601050c0307380c091201090803090105010806070201060f050f04091b05 74
    0x303055080b88214000d1100c2007030140d031b003030001140c1c0c6140303003001d41c11080c100c0721484401d1722400409202d000207404170010304840c01c0f210488103a204400414110058803048907940700c14072030700c5118419980201518400202882001420a8001d050103426a0341d00d2613140750013502c5144034000c24600b04045020704591800006240c620380101929000f50f6480303650b1000b8083d0800185178040291865001c402080d0f5104074850a039007a45800c1c880d83e0441c44c014054a40001d0441da284170f10a004000c065800203140c1c1c0c004200303080035680c48243e05209821440f40c03102c0a080481100d03e500c20350b40703a443c2d20541c000001c2c98600030001d140900c5102c51442641c007200400c000340480c42e01881c080c0041140d491340b04c0c000040940721541c501145400071074810b109a5500c1d00104040c007002d02181c0d0b032019503880200a440e0410400c00000c0d602805018000d0540c040b07040780c6030326180d001844540e04111900703000d28840d8034100014105015850048040c01ca = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 103834478 1250 103833228 103833241
    0xc080901021305060f13030303060503101b0807110118060c0206040201020c06090d1a040b061002060712060e0a0902030f0106060c1205120c07020a052d040204050307060201060905 79
    0x1c00d0394006030515005520300e6282404001164000705e4001c98040003c100e02e80380080030700702d840001c510030f0328040340c02c9207018105401e00384680ca00c91941810041d001c1c506075600d2000b01c501d40401d091a0400f130700c0e075140442c2c40301c440012150701980b80c07510b00c1d8030031560340c81000480303885298148010709100808130b80303402055500a0141e03004c084000c100d031500d2000b8040d003003000b80c02d1f0708101203292030b91108050301007018126001d0303c0c410701080c0000c0c540c1140d0b1002066984141c000c001c814001d5861f14000c0000041011440e04000d0800241d0025402818414008041130820f02ca0510040c9110f2074101d200f4811170091811006041c000c68048401a441d200d41005d4152141c9400c00044c0301e1140c1005004c20100003490750302032886020748141d0907401e455052500c1486415001d54010350712442504e0207070100200000d40384003050500e481d4407884502e03c1c5001c20064002c40d0841a0305006855011410310360562040d41200c43d907940130301c110703207586 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 103835728 1250 103834478 103834481
    0x111206010f27050a0b03030a2705030a03111c32040b070501060b070b0f0703050c03040f0203161805150a05010c0c050402040905010303031a091303110a03030c080901 73
    0x10403142d006020300c0485500c18a00c0760302c440d600404c001c2000c20380e04e40881c00a07085a02c13000c1c81201160741c2c20240700c10440701c000c5c40102c500b81e000140e861241040300203941c490100c80d00600b0040d1300c2991143e01d031420700c4100da1244d80300308034030a41c11f8800c0f4058940026642c000e044500c8200610b40102c3c000410308091954850003585403504000c88410152b101090545156403900c00002c1c094160398001c0410500510040e9000e00305062000d0462078040c154604050401d4107004090811404980c0c015520241650484120b0f201080c100400301c99840051072000c0c0c0006540701400345440c2c207180c4e030b070801008256180403401040d410100003181d00b10410400510455004030b88018000703000ba03151480c00e0b0760380c0000601381d80c041d41101d40d0242e1250010010140c060164000240c8403890300c0f04488240f0340400e05201005200003a5902e0f0801c0140a01d8040e01d6000300c9070344101d0035580c0c14211410040d0203403c1c00e50707034a00040c407500000341e400b0381c06 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 103836978 1250 103835728 103835759
    0x601030c08071808030a02030306011115010b0912010608100b041e02210702030a0f020102030403140d02070203010e07051f021c09091407030f02120112111206010f 72
    0xe0388a2031440c1c0c4034210119507020000a0034001d8250041e03000c94006400c00140c0b82c0302e2401d500456585c50104001000c0149200e8210b0043d40310003445010344581c0800c090540b5290b060a50300c0d50711103000074805045102240401d540391030b10100304024042204c450000d10705030f003031142840000038007046481d4041014010445250401e441480302e40040c01034180718010000c15040400654180407026a40034001d070f80005056655143c00000c41d040c40c1c40c10780000c504514094901803c02088890004c03461000043c451003010095030503101c200782c01500070040c58000707082055a51905000b05031207824007200a03003105103101c0e0400c0010800c0d1b0702401a02e040300c106601d1100705902c098040c4081000c001c21500100c0c800c6e440340e2040f401c00e51b226410051001313000c407000d6014400640d40108102060300b91810403ca044038448071090651600600f0000d204050351045640e000d80e046d44030780040000000c170a4180e031b080c40f01160925503944503070b8656555 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 103838228 1250 103836978 103837001
    0x30b0315010b180913020307090b0603150103020c01060e01030b011a0d0504030e150712020d050412020a1a130803190305060307150201020c0606040e0a02100c021306030b060103 78
    0x51520042c0302c2c5120040103084046141191458a900418009006000202c07481c04c03003091500e0b0f01c00203500d000c100100040000e410300b04105003981d00403a40c00d00c0020030011400700c0804004425034800d41c11100300b444400001c1120540f500c07100c2d400001d0a1000740d8080d1074003800131030f0602124011212044215540c0c0b468041003402c03601c05460000e1058043c0940c4962003402d9807540740403c1030800c0304801c4199105124074000c046004200510402c640c0100c11841680f40c009084030180c5150704400611740d40c4502c00550703580120340010300940640c5005002c03c1c0c0c482d0018003030a41098107860b0b4015155803803240d9a00401080303c00c010803488030950020300070740c4843d40005028040c3c030111500c510745100a07504e401140c0c00142c0d40080e000d07003507640501009800c000d04940c1841609004011169120ba5088002e4070508803864040c5006001d022945140c0d0b5010f8400003a4218820991008000c05d110956803e002400000c1c082d61180c0f003541071041 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 103839478 1250 103838228 103838263
    0x10605060a0c170d14070306030c0611010e01020a0905180c030a020d020702040e0c04110c0d0315031e0201031404020901090506060c060f01140603010312030f0216030906030b03 78
    0x242101012514140c800380c00741d61141c079003c064110a03001400502001100c0b110108003a00c0449401c20108030060842c0700f018035264050002a407549198000c84410f440c0040e2034403000704906d401072090880b20003203036200155170354a01d5080303600f500c1290001c54442c08668444001803036903000840382032014000400018400300090340c040c0403210040c4ca4014200f89440d030103d401c44486440005c0603505c00405d001441c50680550380403c000104000d080007140b240c1542c0c0c03840c100009400385600d6904010941c18140080001542c1004803604180701c80103000c054035400e10016070001341040b03030440e680403081758404e002d80e0f805422950107030310340740400004250140241d03074811030402410714005001c1001c2d074003a00340c1403440c000e00d500d80000c54402023000ea032001c0c02000305000410206a4a4407440c0502c4210304021941174a030751001c01c020f00c280040c10301211101052103042c558003000d58029104079072000c0103040400c80815aa44a004103400c2540 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 103840728 1250 103839478 103839487
    0x117070504020a030e061302030616020c060304020114042d060f0f180306050a0605010e030a1205070f060e01110405060f180a0b21070c120c060204080304090e01060506 74
    0x181415401082c9a045520f00020042c140c1030440e401e146c0241c41040c50f0740c40d00c1c0114800d43c42c0c1404143d030082e05d414078252600c460410040d4548501c40c03501841800d004c80003900750f9019803200540403161111003070396140c8694860284259200755a4040c1e500e80d42c250342500720b580300f100240c030119202c040341102d9000044801c400d4000b019010021070504094100c0c50a1142c580514030135003001c102c84c0750581040044072840e0380f205040010030901c00300e00f81c4000c1054040c0303e41003600d01c0150100090103403000e120390400180300007500c480241c14850309034803c000c1034540760024403010000c180d80c0c0145000d2402402d900000030894045500d1111005160403d00c20704050400d00c568070029500882941c0b0141e100c0700002160004c0440302044000c4545090b0506005410200c1000703201410452004100c06400000c4410490044928086e42079000e02c2c15035981d51104241d680b02d0b042480323544120780c2881c0c041810104180601000d581024140c035041 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 103841978 1250 103840728 103840739
    0x601030f152004030302190b010b030a0209030d2601150e0a090c0c02010207060c1e050c0d0309140105030c09010c15020304050a0c0504200c03040f030b0f011707 71
    0x161041c01038168040e5902da8100c0750481d00214540c41080301c440b580c0d252840e608000c0d05000721001d9000c41c00104100f640005130220312800d05594146e40490745076550400040b0003072040343c82c81941445402000d68145a00c5103e48101440c02c0f10401101690460105e020600030b009a0034600503009085a20f54410340000c114100018004040a076a40031140100c40075003000c07500103410900303460159601003200100078075032450602c1d00c509040e141c03200c04070000c40804414180d004c03007540030701c8000c01440e00c248400420507401a1098503001c0d080b40703864412240c2c440b20182e000d02d155801742080c1d0b48621880c440035403501e03030f662004440f004103128040310741c0b10840c000360f00c644070144055446188100001c0c03003641c605042104401120740d015038407a6003024014800d01c280780140b200c5c121031075a407180d110304d114214142140565008001000101d020000600c0064010301e400350302003215407100c0e40d8880302441d0a50030340c0d0070703604031036441701c0c004100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 103843228 1250 103841978 103841993
    0x11040203060f281206050f0106120f09060e0106060318030c111f050c01110418051b0a05040e0f01080a080c120301090903090801150b03100302030607050703110601030f 74
    0x604180d0b40c4038071608036a03036240f81156118140c12800100f40c0d8094010100a441d03c9482e8026056802000107985420300041c942c415103000004e2150f228410810803000940242d00515800541403207110700310450503000b04031a10600002a042150b151155034500b01070116954056507096100c00c05a1928102070140c0070303e01d40c102000000201142e4103905040904901c56518140c0d41e03003026045600351413500c4069507915404200412a42050003c840448458080c010034660380344158003201103503003030b1801c03c07070100050140203d5030b0041c0103000751262008107000d541c81d54461580071003024041d00000d41e100c1480e900118034004050000e1810f20790480e0401000c500051115800c2a440b140d40a629111b50504140d0081c01c1e02c00500798404c000c003c14102c2d08039550681a817031262081400000020540320052400c40e003002e150007500b12050b505050304c1c01000b81d8001c00c01a0000760401074801c41d04030000c41c505040ba0741140c04103070818900d4840a8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 103844478 1250 103843228 103843249
    0xd0206060f13112a0c09010b04170c031e060c030405120d0e1b09090105040b0112020d050d02062d01050f04020d0510080f0705090a1e110711040203060f 67
    0x40400c2c1051080d0700c421050391256840034440c0084080c84801c4d1460500c1c64800d6080d5118070030b0001c0401031140c041c45005450403600c04580c5030400e8245260b40c24141030640f0209501401291506034011610400d50480f03a0a510308803051641c5110b4012118002075400a04c682c202c850016400d041d00005070464400004002031303590b0031250520b181035400000c030300d00c2c544849441c1605142000707015502c100200002e01ca81d01d0b01c2d41d209014000140101b003410680000e0132819500c3da4946148500d9115007120008551904003942d1000c08840c28441803407030f4614000361400030448a0945030783e0b402960324076401c08040082c1d60701150101500b00da4203004c600d041d080c4c1405004e0059424026460003c0e04100d051800c0002c900c01d815560360203102c040105444500c00140d00c1028840000b44d21101400c00c000c11201400b03d54401c2810400030b600060507481c0207000c032078410701c9414441c0c15172105100036800b0850700e055102406814001c0306003800000394 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 103845728 1250 103844478 103844501
    0x9010606020c040902030c090c040f0312030b010206070f081f0b04260705060f07050318030124050d03031104060503070e18060111031b030309010507030e0703060e0c04020301080d0206060f13 84
    0x80f80ac1548a10394204003601580c029150b20141d0250801e01540510a800c9080d40a00c06080309207001100506582510b0303d2600401c4003140c0010446d4100c3d10007100a0701c178810b01c80c0f4406035159601c11660b0801c1c00350b0b04180001d620400940c901d8020345210151034070000d00070503071400003005441c3d0091702c0c501580c848100b2000b400500c0500c01058000300c841e011340803900e10f00d01494211036684134080360003414920f41142082310f22003004112001140c07442d1400d03c083c0740407000743c24411082094004041008a001303a04a0051442a0016511000300c01c0001080001c1e286105480544000d1040c021545651040c4003881c12180c5140441e4a0001201403912008101d071050b10700d40c0c3c001000b44190030b4030a01a1942040203450180211210000c01944a94140c4001010303155208030744139140c5001c1c46803c6404030001c000715141d60b590b02d2410303221140c0c4080c2c50010b002c1d00c40040c0c00c51601e80d40c150541c0c1800703800412a42219000a4010b1100c101c20 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 103846978 1250 103845728 103845751
    0x717030c061f090c211a0d051002040e040308060a0b0a03020901110f03040e0f0106092711040303170c1e0d0612120207060f2609010606020c040902030c09 68
    0x440c2240e51401010060115a640c140c08114081c5e20b803400061310341140c04005040102c1c0c003000c1c0d07060500f4a40601001c442c645d181800790314109281c62040c1c4600005140003080004d08031814041d043d10990080d1a080d416036100d4081007819510350045152041d01401aa28485d10036400b4000c044411f041c40a1000b52070300c40c9074600318010904100701c1d4000a024046440701c0d00555802c903448000c181165414044050160209400b85115000030f80710804501050401c1c080c0c40209918010442c482c031990a18a45512a001c10740102d082000900a0150740d6a00c0074851180c0000f003d0414010032080c00a0003208400540440002e0002c040803101d2485500002c0102d5120a1140481c1c0e16207000c1c44001c00800e01c0554010b85c3c420004170740c2055451400b00c01e039180c2410503040001e540e501182e4001110211103414500b04a1a46015401042602c0050b000c54003100c0c030120800060340ca00450083d090f030840058907059081100d0a03540054903003c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 103848228 1250 103846978 103847041
    0x30f110901080601080106080307080d2007050114060904020a0e0603010f110c01180b04081b0109050c120d0203090d0302120c0c04050c03070e09040201031b020717030c06 75
    0xa40d203018280c11100340d6400220041200701d400748100c400a00e040b030f01031400c2c5960b6841d1107855000e07246048051035128200078403654558207007540d1907801d19418580300c41035800c0a0340201901007034900082d9030907020841c80c0c03030084e003543d114940c018001640ba50500c0004c80e626100503040b69010740d204e180c4e8407003540850043d45031107400c2c402e2442c1c0320b940071003019017900e003402d029805104250380302030081100c0f0021b05503c83e4200c00400e5a41401c0070ba64a54054810201d020765481e220300c1701c0420001142c03c03e0150300840d00480202d900d41c100d66107d00c0341803020000b5074800c1292108030b00303001400300c805038064015074501081c0009014500c0d80038880105260700001080c00c0310703184c40c0c415a600b14004408690840c580160050940c1c5002005544200540c40000d002c5a1003a002114049203004071058204010700001c2d542c0c1480c3d010700314440d4000d1458402690300002943d03441c544000c014105501d491149261601441188085072100301c01e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 103849478 1250 103848228 103848263
    0x70f08090604032402190509030a0c0308070201030605040b0d0f150e161509030303090609080d0e24040803041b24080103030e060f09040509010c02060c03040c030f 72
    0x60250000f140241c3c18080184d407521042001c01c2481d1145040b032503c144181c044031707910f41041000a003890f09041e6641c1944400092070040c2c00030b001404246082d4001c81000305071030103041018402e88043c40300b141c0b2102008155000400902c0d0807a08988480c008a99410300035980b15014241e030044920340e2021280583d080c0315100c21150780312448a03c40140c03d245880c00030301100c010542201c059840003802c0c20310a2001404140d150708151086c000c00b1b500c0560290f6210034010741d1442c103602403901508895907141014010f9075004002c05181e2508442000080342c1c1c08901559655541040754002500543d40b05003158600340782506204001c1001e44920300c4025200da102200a088009c2011080c200b00b02c40c00d001080065040691414080001c80b8042e4641d2400701048680c0c1c0280d01186a12600303000034450b040700e043d400110340f291a41d09513034440ea40c0b4000c0d9041c1c1d1106590040c0002154803040000c510160710307100f134644c46003040c410606001c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 103850728 1250 103849478 103849489
    0x40906022104030f0801080d0c0510150f0504060302030a0201050c12040801051503190201050a03020c01150303170c040909020a03051c08070e1503101715100b070f0809 74
    0x6800580348445101d080c44141604810074540050342031030100da5039814803041d2511340022804030014405592040c0080003c00d2055001c4c88552860411520902c0700c41c0c0512184680300303000c06c2d81c00e49440403d107810980113420659802800802140354039034011122640800b5603c0301a005600d003a10705e0f600c40c4002032000b004000c001181074140b07803640283c04184a0f00b058800e0740030308010348581005400500c10f60ba02424060744404685409030040d100342400d00c1650752070000c031039110072010f540310001c0d0f0340255125070614100340e02c012202c110030342da15191101e040c0420400310b8155000140080c0c805010150307801c7c3e49965403484c10700c41c0040345240b07010302d4282d0100310354814081ca9110b0f08900e001d80d21000c480011840603890402d039001c08203030010015849140303000b0b1010092003800d04045034805050b980e80e031110340d4060a1100b803000303100803407030029400b80080140e0f000c1c0251285480c0721550742c050b031509007850464129000340a810f02d203a6aa = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 103851978 1250 103850728 103850767
    0x9150c0b0a06091b120e19050304030605090d02031804020f03010603021809070c030302070203070302030a03051207030c0e010503070903170a030f020708041511070308190903020f04090602 83
    0x10244040340507400e00f0b00704025500c05259a4012501c00d41d00d0705002d0b60300030800b11604086450004040c4820510305040c10103040f82044445100e4100404115002000700100d0340101e0040015840c0e030b03002d417600d90511000810050f0300503c070784604480310f840107840300903004100610f4110050141181608260300130b03008680d012411300c114020b02001e030346020350708481c01c00d294504603e01802c11400c2d4130019080560100380c100454800304400c0c4051500202100c030045406d2034020616405494014102c0400b2800711f44503c0c001d004000d841100e40d02d030008480ca0070401160603400081814081064a40c000004a14551480c0c0304080260703500b5940c0303d4080d200503058607200c4820725a180e10400c010f00110304000143d4055540c0705111030304031840003e00700d07207004c0c1c520308450075402281d000108100c5140001e1600c040f070710020304440d2880351030545d034080851101230b404ca8000402d881d040d1415502104209225107001820200c030f80c03c07a40700c41c510 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 103853228 1250 103851978 103851991
    0x90c0b0405030f07210503070203030d0b01120507092d0b09010306080a020a05040c021f050403030c0c02030d0e03030f18030105100308070f1718090601030c09150c0b 73
    0xd001d01250509202030250508043d0060440c1d6281541c00e5080401c005407560005c81d0b807115a8003000014800c0781c507c560014100e80d11031128104207002090720004240c003048900000694460301c50081c0c502c9582c1c1c6444141c586464900303190b0981e0301201201c1d003403200b84020410b01084104c200c4000e05015203020340c03074002201c00503084511a40010740941e1124142400580c0c0300a100e0050b01c2c401e03100070544512400003a45001020200080151409003a01d1803400583d07108034032541c003d5030140103c8151079003d60303100007a0355002c4c4d0541c1002806503031080c003c00a100718080041e04880c6400c1c1558404c41654100030440303d00385a107410300b015140b070309000d0306412495190305c8000003451030341ca40d4440c0c880c94100030711a029409550f418854280e00315004444c000c9400c035076480c0c40320a001d00f10500c41401c2031040d505640451000d5202e84070307141c0041540d40b540d400150074800340c4960985c0564a8008102d041142040014240c04010b401100c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 103854478 1250 103853228 103853249
    0xe0d140a030206180a12090807030305090411070201080f071e120e240402010e04050412080c1c1805120309010605030109110d0c0b0310140306041212090c 68
    0x200c514009041100c060000701382c038041d4135032000c4a540040361082d40268445010f06d8a0020348400344c0d826081c50388070240724000d038038000040c0748d040341c000e04409008840401030304400c0f0100740c14502584202030f0002c2c607100001000d800078600d071240c22904908040d803045040c0708083c0807188083d0790800c00288078208900700300f80e0390f02802c003071020f0210240c010340c0c8401d50620080100302030b981c1d012800700700105040d64010703240d5001520008d8070074000e502c0c2c1070405550f44946000810002159400020b00151003402035071114400800808101030741200c66502a081415820401e0704184c182a40040c0081080402120358003040e2501c0b454901010740c2100d2031a40514003e90400c1e2010001035410040b40141e10300460340452006014100b40c07045d4003498002c18a003000000501c420354004845100856405c040c83d2521a4424018036480303940950b0001c142c1c10368480040b003c54085c080440e40005500f80002d40030f10291a80300500c80182d00260410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 103855728 1250 103854478 103854493
    0x50313051f140906070e010518130204051305060901121106130303140408060a020d0e010903270305030316110d090e06040c080a02180301020f040e0108120304030e0d14 74
    0x82d05030070080303503c1070003900a0180361800e108050480b2000a514a04001001480004144400b404010b0403140502004a0700c0c000d000007038029841381c0940b5100f00c90040d40701060410394007031030f071240201600c1e048640c1d181150200c05054222003c0392140004201903000e0b403141c40c0030b001e80a500c5100030b004e403480c506014119131541e040c1e09454a000304801d204c820800500550405450381c401030391100e52511050080c800c5044502c5a0350800400e03c0c149035104a400c18803015251010641d100c1401c9070950315610b40c8001400c641003400041c503012103ca02c441c5460b8802d003885000c1240003402d0908000d07102c540200411000d180c18040621181200c0d43c0c0003809507810000040ca50a02034036241d00109809051034001484420f001000b43c5412411000a002551920400f02403080c0d0358002c2d000f002c01d0f2001d04400040c6103e00060400c0003000c00706074151039600e55490407070b40c0b041d900c558280c0040c80901590002400040140700100381030b009800310 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 103856978 1250 103855728 103855751
    0x6050a050901080a0f03031b0c05010501050a080a080307050909090a05010507030b01051e0405040908040e06060712050703050f070305030a0b090601021e01110a0903050c060307050313051f 83
    0x124051900309038003440c0490014840203800182c000703410341c0c000e180d00030120014641200a85090000281c01c02500000140c485801248410129105a0080c84260f03250024401d0315804c80c400c0700c00301da00401e41c2c1c0000c64030b080300442d00b1484514000d803800c20802f0109400c18070a550108090344040072b1001404000e10805070010303518607050240c1ca5443c0300007049800307008002c40400c008a041c0700141c01800c0304840007040050824450307130065042c840c210340c0191080740180c4946000088892074420104c0740b01940c4200341420b0180403042c01ca401d45c021003812800e1040c1000b81d07985841e001c60180036481d101340d807036950b00d290000c042c0e0140c6c1d580700702e00d5016039031590a0000580e00850b22841e180308800750641d40007580010a03014100c00c1c8c0d02d4148002e80040c0d040c0c0c0950b441090841520300907000c0301c0c400e09000042c420180320480d8010005602440131410400c00c8031944c64100340503200701c82c0840703201140080100390341d24046002c50390b20806c0902 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 103858228 1250 103856978 103856989
    0x102041e06020f010b0d150b10020c1906090b181302030402030c0d0506070c30081b0a080a02070501060905100b04050603011412060c040306050906070906030b04020c060a0605 77
    0x683c1e0309500b00a1000110301c5010999014401000411004040e5400c0c480038285a10922140c03800500c0c10303034582e8502e20003948880d500000300d40144483e031010090010080306550803568259a119860381c50443c0c2c110741341d04440e0b5101102208210301c00c2c0f00c0d80d5042e86240011400c0c0c0c00041c0e41e0305051040500d002c1ca800981c600520b40c450440003c070314089040c55100c1d2803800d1802d804801841c051000d1068071842158820701c6c2042000d07002424602e9400050441d1120314894982d4120b856039100c100c0180d401703100c803c02004441502c22003103680c0009090343c015041035003e6456030b0039220150480d490b555035450400c00d1001c84208154010600c0114061401d070806000c035109100c14020b100035400d58240880070b036210304840c03032500403485080e54101d082c2500141942d90082c4420f6a540d8201408541420004070b41b85004c0c03092900d0b000651440d04100b070303019000082d1306650161b401d004207120f1441c14024107100d001302030800030780c150410f020410f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 103859478 1250 103858228 103858243
    0x60c020a241a0f10090512010603020405010b0304080301150c061b2006040b06060708040303020c0f010302090f0f0102071806051806090703090503130b0d06090506010504170102041e0602 82
    0x22a5030b815192501c0c1c80e03411001e9a070160076260300e14039100c1d40d20291042c10481d402960880c8040300300c1d0b0300a6006501c074200782c80c030885003071202e40d030780f00c40c44030642c0419200179040020400042103c42d00103503d40c0130304152800c1c0b02c1000c030010b440c0c02046a40311908400500390360104c07145c285074450410403c20341d01d04200200c10b031b04041216a520740042008020a060f100481c1103a0384401c103842d80168031003549603540e070b240e240c025107500003280c00c14000c19554a4423103043d8080e000341c41c508075001d407d40c401446003204000e90007580c66841030641c042d00001084411220f1480b204031104601d0102d2420720700024020005404d07071503440003410b06814040b203070391180206504070011f441c0210315400c0c2800c0190440c0303c0c1d4103103c00c204031800000501c14a6aa001e411800d41c0744a040200c960b5400c100000da030400c0b541140081c0c1d04000038030990110b00004d50403000b00d180010304107900d030940b41c000342c0c1e25586d0321656000b01d103000700081581000f5a0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 103860728 1250 103859478 103859501
    0x7020d020607020f030d0f110c070f050906060a030203060d02040501080a02030708010c02210c060703140604050c040605160b0f010e090d020a02040e100c081005060c0a060c020a24 79
    0xc016410b0b0b00384d2000c0d10390041c0b500c0c1040490f159440081a103a19070072505c1c0e6162900c81141d40d03030081e0281da651b1843d45114800541050550000701880d01c07442140c8102c8025007183e103001d00b4000110020f41c4001c001591044520b060100561a1481907901901c0024000c10b110411382c010589445a60703448407285a04003402c0024995003c41c102c1d90845c46000d012140807a010410750381c1c6c0c003640d00030007000e209a90400c0020340c6d150700034250210803006110910744407041800b058a40407103000f50700c3c1c00104020848940b04000600206070484204480910156100252414280e038525403809000d4018003511200490881d0040b401d84010401c07a800d10b10007a44039201117202038811a91000d1201c0b48420522150fa41680c02a0f401c1001d03100440b0090020041601c900920602580c2d000c141800c0140c226817181c0c800c0401045c0300b001c16900c160107091a0b10407282180038039020f202c00a802850b41c2007059080c0911101818504d551403000c40700600c400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 103861978 1250 103860728 103860733
    0x6060305160b0f070b0403021f0203010501090602010b01020705060a0306080a0b090c03031303020616060e06091902010522080303130b10030308040201120e0a0c0f0b070b1801060e07020d02060702 86
    0x441111070f504022100d106038402c5591550703580e10704080c1e0509080181d8901000c441140322604907020342d0003141664002d0329408034241d29480220f081780c4600b10301e01d01580c4041d0080c0568500319000d01110401485e0202e0301640f0780203014142144079100304c81618070700c0140b000c022014003016111120a030300440c2041503528800740386010f5444068002c2d140010103800e080c0b920030001420680044052100c0e2001c50065544d4003000c03501522540140509008902020755810308800d405075030742410720304400380c8070861002e05080c0f41003942d0700ca40c0018a490050014503c101400d11083c2081500c60a020006400c0100444d810a41590342030000940284d94990400c0e02843d10043c50010300200344010950b100000d5018400c00110308100a054500305044c1d44411420204581c0e650210200500549000800390241c032000141c04140841e08400f5402e0414000316036160b0340c0d140c02c06000700c10b80d60080181c02c4194000c11564040026940180c4140700 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 103863228 1250 103861978 103861987
    0x30906010b09030604030309061512020306010e01260c0a0810060e0106090603020304030c050105191d0604080c070b070803061903050d180b0a050406080702060705040302010309060906060305160b 86
    0xa038035800014170090038103955512480a01485a00c080f41c41c0d0408440300340116142d44840c403900701c0c207d41c102d02c01d11a90001059208001043ea4103c40241115100070b00ca554070140c41040440d10a45e2a8403906000d00c400d591401402c400800401000e480c43d503400030f18180c15a1883d8000b01c01c000040001040041d0b80080a0022a2041d1400688903115031608903503403040e502000e0a41d40c20704041c00002e4400b04500101c0c4140d04204020f80b07402d00501d12045a200d0f00c080c644c84d00001c0001e40400d8507600180001000f840540311100e4031504a018150400c420a403401e000c080108580b904011902c0310724600040d0071855060700d5540c030b0581d5080500c50b0340c401c02500e004040c800e042c00000c19006060480101034948802e11401070080e04640700340c030000f80c10100460b000381d001103140348c010304281e607501d8900340c00c580054010340034001089600d25070f602004804943c491107660095441031001d40950b0b408034404c0d660740c540c039400c50070340b40a0030030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 103864478 1250 103863228 103863247
    0x51906020c06090402070c08010c26040b0c040e0f0402040c020102190e0a0e04050a030f110a030c030905091e06010e0918010b18061509101206050301020f030906010b 73
    0x5100981c07401c1180e000341d80e04020404a006405101c00040a44040c4440414103001c1074004180d000040d5417207642c04052901201030018002e079440c14017107041808540415195400c0341d900800c81c5450074a401e507500d001c03484040301151031502005c8074000340300441c40c10380501111502035200a504040d200c2000711581c09175125a5001c1c8048074a441349030f83c40d00c009a0700142080384d00b80500d8a0241802612004050011800540c00d2031036000501c0c0102c0b0004240c80100c401011801d025aa060b2258075170381c441a01404010100011550391380203016200e0b483d0f00d8000a90718841005000c0b420201808a5040c42103d400301e00d02c989440030b070154002840041232540c5008030f82207500418004050681100019501041d40358402507058022031060711502042d803500c42070136440740180d1301c0352540509420003e11540e4801c041800903444070250000741d481e1703100c000a08a0f4091264203103c1000071081107032408050203080d0050181010322031030010704e503 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 103865728 1250 103864478 103864483
    0xa0504020a121e110307060315050409031d0f09090c130e0d1b020319050f030304030813020f03030c01150503030408070b0304030509090c090f01020c0f120309091005190602 76
    0x3c84040b0500b03010030b14003030202c101502112160041d00703813841242c0b5800b009000e00155090485600000800000c1c0c5081522a200302680c1550394481005902d48146154002070601d00368020000841c282b8940d45e4961040c1c0038100000040611000c400d051220b01c1400700c1034944400d14028010904003408031301480319031601d00d0310240480d400d8076024460071036040041d41520500200d001411a100c03c20b40306580650300f11030710303040300900c0140d903480101c40050004e000e050229841010b40b6001d94640b0f80300605950320104c142010034030b1600106103241e1560f454048010001141010030000703842c00754051441c2908002c042c555a910903c111140c0f080000002804d05200740242d95860200400000c090f04058000248a820001409118181c0680b4000f001d40c00060884002040030b09200d4104000d181000190501d0560301505400100081c14060796281c1395544150509841560702606010521017091281e4066811030f10448506103c000c0c1c00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 103866978 1250 103865728 103865753
    0x70e04050f04200a0801020c0723010906030902041b030f0f0b060703050310080d0c020406050301090c0302042304050102120c0c03070b190c02071505040b0f0a030908030a0504020a12 80
    0x42e04812940f4414110200e40328108a0b84007440ca1752002c81c4a028001010620703004888580c6500b03841102452803030304005e404002098040b0325040b108001450107900b0503034642e800140005002d00d543c0350020520078002c50300d20f00113561030703034058a00c0c0014403600c18850100c4100300800500c0d600411400e2103a8070003d000e1020201c0050b80103600045584040e050000c191141e000980c1d0000d040000c0d1202c040b8421400d0500c0807542c3e0405204104005402c134584220140c6140c09000040c072800c03051034884142c1c01020004d1030341058010340180e210750300060b60b6a41d0300c8103941000740c0240c99201803000402c0160b03400c000c00002d0b42c0c17481e0741200d0700544a8689599490000051801a048150030201450360080d000b0544808039420080c43c1009415401e4007140d1500c164014004040000e0160007050021007005c1e292022340c5040c005540d080c55107600070170b134000700c13a4800e13800e4407841000110305100030302ca0300801006c50307035502c00100c81e038400082a15 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 103868228 1250 103866978 103867013
    0x10120305090906030109020a14130b0f01030b060c19120207050d290f0a05070203040b0d0504020301060f0f150503100e0402010e060c1005130807032006070e04050f04 73
    0x7910700400c0183d513082d07018900c2217900070050264195113030001d100c80c504802603940319119481d00403025828030f0250560451008055464441d04d0303d00540061645030f1a540d0000ca09015281d15510204803c0c03400c00c444031030303140000e00c0b80e10701400800e1040201500715080007104001c43e803900d904030260242e110441143c040015042e0340000060907500003034030034110050081403551904001d0049103800341c1401b80d650f45450076a03483c4039520881c04024000c00c62501d05030b902d030340034075041840100003060481d40c4443d60450424103412034226030555000c2001032000b2403070302ca492081d260602c1800c41c40c0180c540c08910740340744103180d00780240400081c00c5a100d80c40d400355403e8003c0c40039441d840c003180b54a5482020070b01c03c5507a00c0c504004a0012034050b290210025400381c2d001c1e1401c0c00f01d41d011a4107052038026103c00460748503a60144400038004180720b14170702d90780c0b407026001c040708010a40d00060681542d410720715051001013503422403020716012 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 103869478 1250 103868228 103868239
    0x20406090207020105040e09030c0703030804110301050f13050f0105070504050a0617010509040204090f080915070203032d0406030903092102040c0c050f07080f060c03160909020705061012030509 86
    0x140c5000c1c52301d09610480b40e0441c884d02506402000705600448924050f0740504004c001080c002802d240c02c95030180c0340d1100101c2003100052034406001e44036000d0500c41d00c00c0d622141d04000711035080d0b441c11743c0c1e480302040011070188180c0c104002c032000207204a2808240b011002d104c2030304e5101041c09158001d1140800007425512030340c2184d664680d120222281c03c0c0c465041410713040e00140705903841584000d810f02019040b0b2000e891a56400030050351400116803004e004498071340c11411054080107071390341d6444100601500040100d07440c049021030451500811046c0c1f40c1d0000d031045103488008649030880323501c8560a540e419140011480c115410540b00d01d5019840100305204070143e1740050480410000221001e03881140d803500260b00e00d00d601d88400b01d0300c03d50010400d200103003081034216411540d2141c5414407524442c0c0750740c00c400c1617a102c40420340d0542d001034284514506120718279001009070018400e200542545d0080091254144261040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 103870728 1250 103869478 103869481
    0xd11190807110306070905040f091502031e01030b1005120d0e010e0406030f1106190305430207080a020603041b0315050a06031a10180207020406090207020105040e 72
    0x8402a1010b560070315000301180e596103055500280031192600030710740686d0070030408900443d928011181995844110004c11605d50b2a05100a410040aa80d032141340d00340401c440c0d00ba0104410b003e14059540a2894070b01003041065422440d440b0900442d900c07400c02050101c0850040310000132880c01500407c81500100c0312060040221907110340340c8480001002036180c120301001d881040b02e0000000424108100c41c0110510701c48a0300303c4210304c2640f00c2c4290300850f803100b20b1004007104100c84d90607090046050203203200d100c0081510f098001d00b202c260000c52503c0e9840281855810a20200e488681d0810001d002d500040041410060400f140788982100480d00440440d960708003012800f0b48020200b221900d0140410f480c60b00c540a0710064a800000900a941850400c40d904113001080d100010b0449003003c9880c0304411400c031884000312802680f1801e46004003c05c45085a10460110344100308190061740c2103019102100c4181038210130030b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 103871978 1250 103870728 103870733
    0x30a1104050a0609051501140f030606030403050403061401060324060f0203040b0d0204230303030636070f0801080607030903020a080f070b0108010c020714030a0507080d11190807 79
    0x580503941240704001e0900081204546c003801a081c2080000d1b41c03172000b814501207081c0764a00c00c106051070310361401c2001072a94103000d001107070084d100c0d1030401d240580d60746802048803860f2014420417042c00004100d001d07858003841440742d00500101d0f0402114801d03104048540c2d110700000c1c084800c0d811030500f8024004c0da0010102985040d0340d54402030350010084d1f0145c052032844054030030403100e01c042660ec441c001c0800241c01945141c03150810014141010f410b561b110324507040510316800c4111041c4500c85407031440030f91107414900d50107041440500001410004d0041c0104002a8005140740d00802d450900041c6040c2d01e09007281004550503020b05800000156614401e1030000186500d031302445030b64080b070740c0f030b925080d00344c3c1c620b200301c01c005a10000b07040c0b20034500c110780c0c0494100b0040464450b10110307611141045c01d01d03071001509411010303905140b950403981541c4000b1a00000c1d04140c080f020030301014040f9035001516110011600204 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 103873228 1250 103871978 103871981
    0x806010813080318010e030412020f0d080c070303080a0c090e150a061d0d05100b040e0f071d04020d0809040f0e060714040602030f0d0204050429030a1104050a 70
    0x88070350807030328460707891404d5085119842c40f1600313980ca040d8030703000c40315030f400300702200703403020f0703034200340c0d004400445680810403021103070f11071141e0140c030f1165004001158180203050040018010b0a41185035080103852030500a12040c1800d00707001c00b0102d07603580045c090f4165000b000d09a9226110000012a0303c180646002e07003000c1c100360301140d40d0f070300111091110502d20b0301c0c1407074003985041407080341c96400a00030305680c01001c44605c0201c65801c07500e44a00301a00009e940c481c0c518900d440e123008051000002d40044005100329503030345801080c4100311007103004803420310780c0c0452000c075420003018250b0348010502c0714099441e0b030044028406024003d1080242c001d110544908045d18400b011502ca0804054940428400e48085802c5e54014504182001001d0307000e07640601c02c2081c045a0030000801e0703541e200d1081010700640800402e041d2128100300c4052695641c016500c65409204100c00068030b40380d10901410056402180a8440540210 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 103874478 1250 103873228 103873261
    0xa050706021305030307150b0607080301230604090e190f02090415020301090c0206070c03020d0c050309030105011217040506040605070f050d02030c070e0c0712090e07030b09060f0108060108 84
    0x40e818000002ca103020b12150801199800d5287d08040118500800401801e4400c482000340303a03a0041c001084402c505501e10580410103415500c003001260b0300240c62075200390041c07000550313581914200c2c440300304110441007140da010040780300c40700c0d142c1559681202d400248251000c00005040115803240e09411064101c815526035858421800c09850001e81c03400c01881607000080300b142c803a41103c000180c241e0050044011104d4080b81c540101400990f82403008000c03a80d03064400b44a020700130301c0c0900c0344811210306841c0c020001580d84c240f030b02c52a0801d000030b115550741c05d400c807000c03668107080075a5200302c03d2134501d49040c0207182c06032450044103500e1035515000720040c03107200510710940b14003503211102d200007a00240c490401214003071014200150b8954400700034001d0314103120740c0362035660011844060080701c8201c0000e4840d942004603081400145400140440b5828210400b00740001d010f0103004103098100300109000c920182c4080c840320 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 103875728 1250 103874478 103874489
    0x30f1c09030206073914300f03130807170c010507020a0302060712030507030c09140307080d0c0302010b090105060702130b040f0e0601090608060c0a090e0403110d03020a0507060213 80
    0x1d402565105d0781849082c5061701c50380d00c40030441031035030380d582c07900e2003100d00d81d00034100c6c5154000f140c3c003440119041c100032001c4140d20078901c5d01103004000b003028101540355040c03405407890803d2000760414240c2c2c3d200c0c0343c0d1100342c42c010382c9900c40d021501011300c58083c0380054880c055800040d192518650029401c8a0001403810500c9148400741910340c1c140e490030702c02625410412030884160070401c000007100f14000348540b602080a0f050903a034010100c03004181c84e0310005090003004847c00010500d002000420541c0a025200c0d5040b0101c880e013140750714000106002e84036801e07000b441801400030440003014154000307584180041c008019501c5c880715180b0040403082000c02440c4502d000019502015008520691b0318180242102d40ca800319905101d8100c00210418800c950201081c48004024043d00c0707140659111010250541c1a40d420000211034400030903004010b0142107a4101084614080d480000103a0311030311604c1d4018160307a180c010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 103876978 1250 103875728 103875803
    0x203091008040308100f03060203090a0c15080709181509050c040f090501060e060f09220f0614010e03010b06030106030e07120302120306040902030f1c0903020607 72
    0x515a030607400146075109070b110391565111522255034413030f107160161265002e0130907900c3d01880060540d402454000301c40e4011240060019540c40041c243c01d600102061000301c019460a2a0312040030764001c1c50f90304003400d0160404840413200c54142c480c3c1003096440e204800160500c4800c0b0000810000804000c80c1c2001c4040341c0c10307503005200341e4406104031040410140950720031681250010f031100784110003070205000981c0c10070410030803c914248222500e540300c99020401c1c510b00c005d0f201514900100490701183c4021408074056803501384140b003804034442c885400840309003003860781c4032030a400085c00341020034440c680118000c8000107503950581c0101004800f814291000c0c00e0316440720488031046400b0290040e445003003502078001201c1c5c01542c22040161000c038800da0f40d078000c07920300501d9030002002030340b114162400c0b103000c1640c0480c07100d08500c1c000203290300d0f5400180780c03030107050300c003034040c01ea1500d003038081c41c0311036100c14825170941e0079 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 103878228 1250 103876978 103876999
    0x504020603010303031a0d03110d0215010905070c0b0708070f080708010e0c070615050102010b01020f07050f1c050f0c0d0f020909031c06061407020d140304090207350307030507020309 81
    0x80060110278848514540c0384100384201c99003500100b01084a000303095900d002aa01c0c0c25010703005404041c0081c018805000d40c0ca03404a4200487c9a1003071800d13460b00103c500301a071004081c150000400820000309800740f0650581c05241711381150115003801c0d000380c403442120341031403045003002080d8610f80110300a480c0c088403420350071100240c0081006000250041ea2200c2603407083c1c40301d50b08513040502061401c04200c00c80b206c1c0c00740c010781300715220000d00d11007001012401d50f51540f00001022441c1010044e000c0d40c0d51042c1c401413243c0c1c5256030f400a5100a0a100900c14100b207800240304007001c10a44414050010494030f03920381140410000300214025000094220b060101c00d0700500030440e01c41c1c1e54054240910b840f900d454010900c40c1105007071080b030004000000360b03800180060041c03180174680c0401d0200903c8001d5138602900c07407002c107400342c82e001c1d03d101840400e8142d0354071031902d003400708056445040c02c03410b503c02c131028281c0c8030340b0100c07 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 103879478 1250 103878228 103878233
    0x1f0303020c0307050102240a0f020a0513090c0210050a090b070f03060b030c0d020d0b1302040f08070311060d0b03060a0f0f050415090f08030a05070207090504020603010303031a0d 79
    0x90312010840042c0c00703072542c01d520f50004a0312410f03440e080500e65982850440000708512107520361081c05900300184900b410107a14050fa4080d401c00000564041900c1002003460000d03d00100b202013400c00862080c49400781d100d0050094040c0b80302c0e40e90000541803030550b0005030b031560f4070480f0100c1038580020040d16020100c42503c1c0003d180c1440030401000742c0c42264010170036405c2c694144141e1110784006135201d03c1c4034507601500c0d21007054650f05c13184501010480001c0c809a100ca050501c0540c968085070702c4402141e001950400100b9010b203030100a050381582d00e15615891075000380301a1201420540d014487d00782000040310f0b02c0d41c8800c1402101c03c4040c040c410310003843e1000d482c5d040e40e01801c3e0f42048c00d00810303180d809903c0811100d11a148407214034129803030305101c0d50811039600307003400d84a40030458160b43c14040c00c0c0c06441215810496414607401203103131b42c00140002002c1c9a981d603841488540e02071a444075040c802000740d9941c40382032 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 103880728 1250 103879478 103879483
    0x40510050705060f09060f0414060f01080c090115110703120314010504140601051e04030f02100804082704050702010f0b0105120f060d17040806010b03010b070b1f030302 75
    0x141c01c1e00e040c0284400703c1c1302c0c144120145402141244010880b9490700014441d14040c041c0080321415100d60b190301c007018040c4406841480040c00c607140c41c0d89081802d40c1081042e80d2081c7c806c00d4003100600030907114290100c6524014501100b180305160074507850a03080350005821801000c40d039113806981078010001b00c2d1181036500180d40d136580709202c1500d00044000858460b00d100040807544501c2c00781114040c1410035801161074208044440e034000d42095808945025480d01541040111450100c00514220001e460243c44000c6280a0741a0991100d00c264a00382c0442c2a0301028004043e4010000c02081c10564000b078000c0580c002c078010220f0414242188540c000c00c1038a00141c400e034501c0c084c2d50344010170f06144840007480300b5407249094528a01207041d10030811280d04020080b00da58a080c00c1d6494030b030501c141c1c80050340a504100510140f503003002a1502d95a10113030340141c64840c2c554001e000c00030038011a42455101c44004140740c0e00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 103881978 1250 103880728 103880737
    0x80304060203061801031505220503070203061b04060f1806080405070801020a0f03020c2b110714130f02160b0c09030604022101021911070e0106050a030204051005 72
    0x1221100300c61540701301d0350180c40b502484040c0c8903149880301d261880d616504135940c00b6440d1000b00005480100c04070700d19481c140d0b4291140e90010503a2011401c04100e004c0d0013103072102c90003d0003201104007165902c164001c12007013111520091182600494454449685d00c0c500d012943d91640c030001c01c811800c0310b042d90a0302c1001000906510107200302c5030310348625a1844020f0003012025006584084030000203445000b68030001c02400c8a1045882480c407010410001701d900e1005022003603044445c421070308000410850781d0f20079040740240c508155103451100d13804100b007200812504052000301c500004242d401190701800d00c084051050034914101d440d14a1003c81c54003c907000a034060b405040810702502c6d0030340321498020344010051101c468201d007510b0036a005003905034a40ca540e448584c200c15049030500c0340009034a00140580d034070707120400401000c18499a024400b00082c501d034a03034440d40480d00501030207004e420000c007002000424541c003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 103883228 1250 103881978 103881991
    0x22116080a0c080a0302030703150b0901180305071401090806010e0a09030e041e0c030b0a05040e0f1204030b010b0a080c030601020316050a021914060a1106070c0309080a15051003080304060203 85
    0x3804107003032b1181000140d080295809135083d18280f404074001521000c1a2440e01c00740000040e1000000400400c0010050501010701c108851071388d4001400e11b030110b030403180d1150090001440445072440303031307590300c945024030104401103581810388512007c2000144c009043c0764110121100c040c0d2011811800c140c020010800240401c804071549040656881505500c04012030b14094114030700e03004080301910f400d145540400e910340211407607501c4800001003000c0043c4080c2c8d2222038014060210194075150000d84001c1c002c184c02401407481d040d002c4049001641308009560004505119a0105a1603418903603514004141c0c207d01c203140301e103020f0b00d5006481000004403a4180c00340c1d502d661030081002490307040b119200d81007001c0d28100c19407444003000001e006460a0702c5180d000307403a5003002410105140c010380d2075644100006000107140c0d12010114804900e0001660307141d04102c0140c900f4564030281100802005104c10701251340d00540c05001e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 103884478 1250 103883228 103883231
    0x80706020d050f181906090804120c0f12030e1009080a08030a0f090c090216060501180509010b01020309012102070c080708071809030c0210022116080a0c080a0302030703 75
    0x8907210400e45e13440814801c014442ca8a0260b0000092513642018120601c1650001d080981700c003950f030f0190071800c8080e01e1032240c520b41080890039804804000e840e400014001011440d203000d00540c12480842d8010100300170500485071090550700d014120550589500148504000c3c07000d070415582c810503d4504004908154207521031100c159912a510080191401c51940300075001403403515500541007100c4000680e09200b1240602990700c0c01100c40d01840d5256400c44000a1158130703540c0c034240b203c1000341c1e0004240c440c400002d00e005640c00c03442c0c048804d501d4880c01e004010450020031101c0030000c070350000c0401c0c1d0b18210308980c02c050307840c48169500d0310342c1e129000d02e4090041503403521407040e40050030128003c0c2001030303d0f45103d60229a030511b01c0c17034528005030000803d00440c0007038103283c1d040e02c00302c0d404200c0c2401007030480c4135110040240001c2480a0010f05c2c101210301612010307050542041780992a4401c071040900a58400c54480d00040e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 103885728 1250 103884478 103884511
    0x10c020d05010f09031b0c05012a060c030b15030a0c030f111e0a210e0f0106050406060c020303030105040c021f0902090601030e0d12061802071407080a080706020d050f 74
    0x190058480514650051f5580f9201403801005403010701e50b038120314515818400300e403a04811030403400d0b95511f110710300c00201150150f100030308903164040503a101c4c03900d0504040c0c00115100582c2d8008a0b10040050003a540d5402500200300003618480d03070600700191001200f4080c1c0140000d04246070000c1c54140301c0746040c0f404d51103548480ca01080c0d4212550203601030b28044802c1c80100740100091303110380607d4442c542180010003402c141e45800c0f0034415070425010b03490080000e410140c0070250342d0382c00aa1640414041c00e4000c0b55643c084c1003d40d8400c2149a841d078010041182040d503e40c8000800340c4082c0b54103a025081074000300d0401d52091240000c050318003000b504c1c00c03041c420000c0391900e9200b8520b0325901d4540c2004162031600403004110100e80c0a070050350380c03242d403a012059219442891181d40c100e0f01c001c10190901050306109a544a0840c540d103813400c1c582100280101d501514489207010100424074020044041c01509079400c20b0141 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 103886978 1250 103885728 103885757
    0x7140a080a0c0f171b0f1305010602010e0705010c0206070302120712020c011103073914040209060a03020a120603110301050c0313020603060a0801050c0a090e0105010e010c020d05010f0903 83
    0x184101c42c0d480d101d907809420719800001701d4000140107a6801050003044558240004110751601e000e2402440d580700c004002a54092181c035901c0803004c03000d00a6903181c0360000e001c0c40e0b80090040d00032603001411030708043c806c2c021031303074000064295a51181218108441c62061518040300541700d040c1d0310700320a41c0103100b140c042c180d19070025444d000b0a540c0740000744002801c1d500302e4012180e0140a16480c0710100c450602c801d640c0480f28907d8900101207034410101d0590050b0b1040040324440c0c0c031500c04940ca00059401c001d81d442020139812116000d051031035580151800c8404402c00246200082c0010400c4000b400030741c660b02406240341c03206031080b064800492105400608010024503400301000304200f1748903640314005400d40d4801c0b10320000c45ca00006083d51400d401134000805415441c01c001155810f0a0010340b03441c041e0080c2d241800802141b250841d0b07074804000310350702d41c4100240141c3c200c440140c005004052007c4010070a088030280300e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 103888228 1250 103886978 103886999
    0x1e0304091b0e032107030c12020102130e04030f080c041e080c0103050c0901030b010c02030d020114130503030114030a060c020309131b11071508010302100305070207140a080a0c0f 79
    0x10a02d43d11000490080341c400704c41d90b01e6404040e084007800000902c100c0403030180e046a01004109030000359644000540580c660190364000d010403240d500280004281c0c81000c3c01007814160518808030703158a20310810304d028992000700b584d0000f481c0c071000182c1000244d001c440300c201c200d60191551000540c1611022560010036410501c01d6030074540c400c1e0041c000d2100b060610420a05ea00c1c4c0102c6d0510404182403000f49c1c0d1280c043c1301514821503140340d0b0210f03013120000e031503508642c0c0b900e40700c3c4418850317801020f2215002084c40e40c3c0074030440b02c105a100d401048074218849010b51217400000c849403003146081c0c100325240c1b1a82c060f007800410001c28610000c29698001d03107001140f01d4002c0307190700c144103000c1920341100e15040041409034035202d98541c5144100000200d405520380101810b100030f100c100c0b03400003441425a00328142c94075009804101090100c0b1241d4445400381c85800c481c07c017130102c00c1500c1000d0310b030303803c5180c172003a515007072140d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 103889478 1250 103888228 103888243
    0x106050306010f0f180b12010611060f06120f0c09070905030a0b04030c0c0609030b063012160213050f0c0304020d08030a02030a0b0108091e0304091b0e03 68
    0x2d0108031001c0040701d040313100c1c0c40e4182d248852070601d540030407a809048104030302c0c650006120307403500003074401c1c0c400e0000c04942d0040c00c00380b904071039804940008540b949006068a002e03140d0300008601e075940e81c0c2c1001c0038502004002c450848800e5400707d50b49100c010003490041104002107041d04c1c2c4602c0707000301940e5000d001049030305010742e289038107514024002d40070841c80a1043c0000341c5030f03061040041101d41e468809040c114240343c103110b0809040703035224141601c100e141800789030308690360460b41234958001080c3d03c55050341c20b10141d50360308021403a0000d00d90140d400701c0089940e05074000d0314036007505070718604400125142170313408041c80f60703542c030025804043c00ca0095600078800380c21884a401541d480343c07046e030010b9445078500341d008001c00c00d14031510310505018071000d1800c2c1941d41001240191560403038055052019180b90070f142d5203840c20001c507001408041c4040144480380c45400740c0011942000710001048035569440c40d1400241d9071 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 103890728 1250 103889478 103889491
    0xa0801080607090326040e010305070915141305011502070f08030f070c0803032d04080405040b01030e0f0f07060302040b0405011115040803150303120601050c0a0c08010c0801060503 80
    0x80303001e1130460f1911224030044060342182c2c2098200924050412a0042d200500e15414880f607294154038019090100c2e640048011a1030406007018408400e0819004c560030070000d480d40700754400c00300d14150900282003d03814144800080c00e1442c0a07904201c84106074261040141c9640c281e003c44803407445040c5d9107030b0041c00000d80c0f04021600815100d8481c0014584207030381c5010301811504100d403184405034084140151000c43c018040074140c03804c1841c40340602c0e103566150450b019500645d070085a4401c030441c03d59000b80d111082403104002154105d10aa401c029074841d294156018140038000700010054003c0c000d032019145004801810682890011200300d0144683e0440a21074290141c11030402e0700ba526005c1d60184a52594034a480d19006580b103c00d506410301a80c810849864020410408940c0020003443d00072b55a0310000e00e840c0c6058504000030305140c0740c410780044c480310154000250b044407610385030001d80e40ca035029201400100d074038 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 103891978 1250 103890728 103890737
    0x22701080c03121206060d091104180309090b04090204020412060b0307030b04081e0a030b1203041809020d1403030601030b01090e04030305091905030d0b03160b0c0316080a0801080607 81
    0x90441c1140c0c403e0525620031806800141002071007034918042d20352368802603600c2c1000c03e005a4450070030b40100c2c6e204542030101150440c0440d5401081d090141c1b1507400003d64038888c0489540d0f868105108050b002807088d91540e45a0764420790248000b4802c5420a15100b5140036604000c2100400c6a401c81440101c07960b507921030580c03a500003041200680785250102840c0c01034200980410700f1255030002d0401a0030f000c1c82030803508000400c02d00e500c1400104505100000100010f4103021804140503100d071001c100c4d0b580610320000c00308245002c0075072811800002640c4107407004d0b03800b800703011803041c010b40e4041200e0160143c1c031042c5100040200340250025030b013082c42c030021640d0041d56080d4162590702d14a108035840c0d000040e036944641d000d40150404040102c014200c58902110500c4c40020144184410490b02040001c9108030034426500d40d030340b00e03040521121400345002e00065001443c8940072810120010480303140018905200c0d00d650384a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 103893228 1250 103891978 103891987
    0x15060d1103010b04020403230f0c01031109090106170a0c0f1803051902030f0f0601151106010b0c060f070f0c060605120a0b010e13080304022701080c0312 68
    0x4524420303110440d1000d401d5900c400d01c40c0c44036119880144019402020190146070464010b480071000c0d0b81880c82183d4400840810101000b05203410f00403c2401d0015100380c0d032010a1049001d105605070b4410b04820000850a400102242190204041c20410b603545c82c5000800c48010800d854005820183c003040c145024462009403800461032240000d80d40f0f0750360f24a00b00da41800412940301c0302a80d0811070500300304c400d103400c6521010701540d58002422940d00c441c14801e50342c0c030600c001070f1681c501c0d0269980c0903a0600101c2a03440c80c0d0b071520054861940410a451103500c035407c0000e00407a0303013000307290050544e66100e5060a44c00c3d00125410000302c0d40a80310320b81d90b603038002419031318500103c22020300704000d400d410311103060011107010168003050308004010200981e46086110303c403c0c169000401e5612500d5500100c2c100f0075219002105489281440540b0b11030044a640e0488030140d0449904a1030b1009250b00d0f4427444210b2148085e0500 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 103894478 1250 103893228 103893233
    0x30f0c071502030622020a1d09041118101a09030c132307030c09030b0c031b030a0b030d030213140f030604030c0c060503010e0f0903160b010815060d 66
    0x4008507013200c0010034410609500aa504840e85c0e41c800d03240780855800641c009406401c8041d01204a0f000461908800980c40c00304541180082c4020074012040f1411040f66641c003020a0ba948a0700484d420503140210003c1c1c02580d150168584a240364003c07c000a040c142c00c0b5000f800b40600909255480041841100c4922030800009180c42d5076480b1b0f000c1d5010031621881c0e02d100d111819450a00701c001504880c0c54000078420071503804000d1004c43c2401c54140d800c01101000310b03559941c1c00080241000f05070301565403030318001060055400c05908101e0352158110705440b49552098003d0b82240708441041c480003120190821503002166a80014200d01615210090391410002070900d01c089504801040802d03c0400074424500700000261107281070061655044c15a91076084000070000218401c0031000519142030a20946880d6000e074503000a402c202031400306c1485100340101d02203849101c5240c8a4081130100c0e0030b01500b80035085011114841c0c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 103895728 1250 103894478 103894481
    0x40203060a02252105030a1107050d050705011811030d0504060f0309020f1504090b0405010b070b060a0807120302011b0c0f0503130b12070e03060624040902030f0c0715 74
    0xf03e405480240408040c40c86084060704040c03000b114960741c0b40e0b80c0c2d203000c2074041d08503000022514050310052000200240c070000d41614079000904080c0d440e00c07680d18045000d440307503c004d0f1b0440203042c1031000401500300e55018259400318282c0d01c5040d1f28140c201c540c0e00940c480c8200041c110b01d1341d140014043c2e441000407a0005d018094045507610100d82803189900e015a280701e130005003040000814403440c0d5040d90304941c01c4c041545015811a5540070340b52000d020044488007203422980c0b800403640023415110160ba00710b030340d94071101c07103c060108019405542001ca01e0129080f91001020382500c0c1a21444d130581c003503403a115070303200c0340540449680c44200420014086681038000040c4000800e80c0d0765050384419050201e88040d00d45801c1c4134420100a072956000304003c0e078400c2c807c0c0c4080c00010a403004c6002880a000315280c80c42c0400a80442e01d116140c004502c20004c010407a141c1c0e40383d11703140f000c60303115070350740a810120310303504550042040c0d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 103896978 1250 103895728 103895797
    0x40314010c0915021e1c0207080a150e06010902031e040b07051c020d060609051c060f091b030c05030f0607050d0e0f0109021003020903120f070b010608040203060a02 73
    0x52044071462003d40c95540555442d0645000300d40d1b00c143e04420030600c052200e0314000e807551000e000c440d403130010032035681c045a2000404c00d500390130303031081d841240c1d0740254985d5004200b06c0b1680d503503c00c03421000b944182c0b4041c840e8018503007400607000068002600039980a04141d1050769200310840b066080103101c101054101102c200f0b00c403446001801c0c0f40003440c00b001a1880c0303080b1b4003038078001d990740c02140170318110012814000c41a041c41250160001c001242840301595010014040c10100a10040d10242c10041d2140d654a0600c203030303031055441034040d5032214100355540d50031046185250344400c0c0050042c1c3d00c12009030001c1c110b80c61010484070510720240d81040300328150b42c0a035a542c1c42c003010640c503000b1002e202c5e002c0c131810218540381314000869100c0303d03c20908440340303800144154111045c1800ca0b0b00503030b00b02e8940f8407203584649005280354000c1e10241e00c03e20840012640c00c6203a4400c6401c0b1401c5050f2420002c200700c501010090745 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 103898228 1250 103896978 103897019
    0x601030615051512011406030a0b0a0f0e01031401050c07120e150c0105150f0f06070623090102120609090a0c26010e03030c0d0e070b040314010c09 65
    0x649041c001003d484900107814010407a400107074464840c030000711071266050f13100c40b0020307004c0096042c09890341801c884e081411440045082da840b4008030ba40e40c60b503a806205020300754031002403103039400c100490507244203c468281c0c0c6080c0c012005d00341d0700c007138541e0301e0074100400c00070000502013540e600707441605003021890b882c041c0000071071140380703200c82e2600018000389000c0051000e11800d94003459400700511141384a8012822001c4410142405507030349454003ca030f942c40f1001c0d509000d5008005005821384c008038034180c15031720a03803102181c1071800400d213203034818000d5820b110b06500147c81c0f04c0e80c0b048104803c040c8003420800e043e000703204520010a00e8240540040c2c08440500c0581002844008aaa901859480c101649000d000c01d140020120490b070f008a402006191180e42e06d8800d1801072520482000e1503210b000d00010700101c0c0200548112402103c02440340c50300250b03440c0c2030b12814080a0300185642c001030041c184000b034800869036 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 103899478 1250 103898228 103898261
    0x1060503090f0a0308090d180b0c07080a0311060705040513020918070206150d0b18030c0a0b01090501050405040f03080a02091306080c01020d0f050a0c061a0118060206010306 77
    0x14200742c2141c204034980c9002d90000c4c400c08200b1030f4100c1c00300241920103405280c212011804001c4c902a6412036010341d1f800300c04001100d19102500300003140281c200003041d640103116a10340a0100c0c4804604d400140c0110b000040d10180990f0549040341c030083d040300c4d414811000c01c1d00082d406040c1e004e91100c47c001000e2980007100100c644903503060340041236070b402d000c030b0740303a40110031040300d24415051001103e002580c0c0e10101138014a0b0786021544a14a0120a41c11402101f03010a210720400300345030113001e0a11041e5049507074001c400c22050f41c0f40c100b813009840d000c99000d0200c1c2200c0c3d03c20b600080c03169950f2940072110303610041c00c2200c40d0780050402c0b00e900e2401e514443d240c550a00201030240b11300441d1040900061980070080c1e00050140403445000c0c2091040119000680500910021110710360244080104100e000b00411100800a003e2800203150f03400d0011803c1c9850450300507984150003d15881c0c0c03031070703a4120250843e06a40c54003407 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 103900728 1250 103899478 103899493
    0x8010306091718040b030c0f04020c01091a0709050405060303180303040515070c081504030e19060215070f1d0d061803020c030102130b07020a0803030a0608070b09090106050309 78
    0x50000c001501c03d88040035414144000514200820742d910300c01d6039407181d00940c5800c2000c2d500d80001c2800b20308269070140e201e14200d0304a60042c6000480900034140303800e02c2c1e83c16551800c004511454640d1240d20356540c481c0c00303000c11120103d07490742c0c042d40304225522048401c45403142c0c10b000020110f81c60540c81e1004140c3d825481581c01801000219a00b81041071a10145000d031218a0060000104010701040407010150014003805032100e40c03404951545801c80182c038480481414016607030720002996480319070211340013106484081902184242c01030403182d68203585405800c40c5910018803401d00180300c071940102800d180100180381c0f80100407108601c0044400c14003a0740c1400384c10304410311480391181e48100921100780800c44200713811f4400d2401499114003451020a100400c030390003405492002000304240408a500310f5004d850602054074442c5548000d9004c1a0080c0324800b5801002680140109445440510ba000d0040c00482c2d144 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 103901978 1250 103900728 103900763
    0x813030518040e030a080c030c030402090408090402070b060f030f070b09010201090606080105101d0403050304050a0605040605060a050103050907060503060a03060906060905090a031d190b03040308090d0801030609 94
    0x803580f2581d580c3e4030541020400055042d00710341101d07845108950981c0c510301e000c00b5402c1e5140700041c00244142040e0010600740124801a6041072201038400c43d0b65404038100000300120481e40140300c0d0200110318600340c1400f050402514800c24010011142452650303001a0802090541190342c1c84000c040402d400d8042c11004019481c00001d1504001460b00c189140e01d4000d864980341b09540c1c181500049280305610580500d0315a490b0b4503945881800c01c01c2c282d0000c1c0c400c605007001d00050014aa00041c000c1c00101d0b4003520040e600e40c0158140e07242103421b28060b40091001700404c80c011001142d200c900104400c614030340340e5881c00c00300c6041e03000568046984240c203002d003000501c601504075031500c0080044000d2603400030400c00d1551801e402180301890302c40d1140c2c0700c0d01101c402c40032003003040216050b29850103003003d0b00220b800707500207108e02020604d502d0b4040f50492070085907030ba400d622607003946c45000c00340c200c0703000413103001c40c071000304000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 103903228 1250 103901978 103901981
    0xb06210a18060c08010510020d080c040e090601091d030403060b060f040603060602010b0607120c020f0d03120b01110703290c0a02010609060b09040f060504020c0d02010c081303051804 81
    0x1024400c4000083c003404011004001080c140c0080d806650010400c82919800141034114000c00c0e03c2d220303400307070360b00d104d552054000e03039000c0c400310000407007071148944020581c1e6060300c102c0c04040051182c54a0000380d1082e810b07190341e00c2a04200b006001041d0560494a13411502801d4103141580e5002ca56540d41d00c1ba42c00f110000b540c2e902c0c03e2010903030a000b1446104411160681821199190442da04411140c90400d100108081d0000c6480d480d506106401c0000c02e15a40c40c9981d0401400d140c5044045c50710407441c01420750fa5035030085500380c410402c00c000416419040d641d030b01c2e440700e007103114490130707889001030410003040a500c0c1d00e842081c1b401204c0d51141c0134444040d013036035815008411210309084044c0b1929070700b401560b11451044501040c2c400304480507100510071a001a5082800040c1031a20f045001070700710400c1c04980d008000c0c14208240803101c1a500341c40c400d41d0f5a610b0007180021a1080e4054424404014468503020100780005030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 103904478 1250 103903228 103903271
    0xd060608150a05070806090a200d02040302190305070501050703030b040c110d0201110a050d06080a0609170301030203070501030e0c0306071808061006180306050a0f0b06210a 77
    0x210030303990040412040d14100c0c016207801c0b21035801c0005c0141441030001c2c840f03940003028040b001d03668607000385c1c5a0800c4215a400580e50718403480d0b4a0b5030100e5000040d6209010a9000f9419403a90252041c103a115a604076a000000341011a08040044505600070f041c2038007015100c154208855896200d403d842c80c2c00c0b51101e46a144101e001c260800d5540702c00d05055901d480f0014505012290403200d43c1d01e6103241c4070340c0c0d42d0b03400d2082600420a0342c10502c214414107407440d04010041e8403107401240160500c420032003c1d44400b00f5148400d0100a4058100b9501003080707500a4100d10400640e000a40e0782c0c0e441400302180c6003281c11100200040d003440c20003998407000034900300103030050102904140c504245d503004004054480e801c20001100511450390348008141406558032003000d000c2c40c241403604002903c030880a1500c51864124070310301c986008021a1400c08100360003003c14604620040c902d10401072203400032a8490700c00880c007000190004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 103905728 1250 103904478 103904503
    0x20102071a0702040501172d0601080622030c200d230a03090e06120601080a02031504020d0209090115030516060905010203310b19050301050604050d060608 69
    0x80b038440060340100400e0b501e06034000d514402181001a08055002c180000e0b410010a004421408a660300d9801c10380440c0c014102c03806060300120f082103000c940b00b8001e15000c40c64050600a0240c845250b02c0c2c0c0c100c0060108582200c0500003c002c41c0c4028460f40003007100001414240b0003007109050b4404040720260141d22164640c11921040d43c11884c41f0700c0001c085c07008550381c0c05002071451740520250024000c0000c1c0c015501e581c07845c4004903c440a81d40c06d541e559080c180e0b40e607a440d4017284207000b0b0070040e01501200c05d080d90302ca036800501764100c0c2d04458081c0450f000014142c68103a5403206459040c841c0340c560017130010740c8600d00a240994520200c1c0b00d0380ea40da904407004200307280c00308101580c1e0010030365010510036400098080d1901413500c0f0708004100c2c162141c4145a03034005416100400500f0aa41c41d0200902d150031103040120703441d1001b4040c5a034458802d02082c0500d06001c1c0481e015507229000c001056500c508280e864040c01e030307a08 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 103906978 1250 103905728 103905779
    0xd0e03090a0b03010b040e090309040608071523030402030f0610240c1e02090103030e0117090d0c08120103060207120503070e0f04090b070908071a0a030902010207 72
    0x34545420165080c100a00030a1240c605550414140714901d02c07545c40340c01107151184021510790081441152030360400107004004140d61181441c3d10303400e140c8501e03954485888060580f40303000300b02c44031342078034020340540441c0d007191b00c00c024607000504266010b10454594032240601000503d0148007446a4100001d20f04400784100c0d0020b100c140c100f21241c14661b010301c540184e4041c0b0803660004c078114110780b200d060a85a2010904081c0d1b00c0503d40b40000705154000000a880c82e000380d84414807103544120025280d1016106184160b1003201d01c00703c0e4612418200002601c11703c403030380c50030310041c4031041001400c0e00151815540040d5150800010421840c1800c00c10300700a400d5103400b00020f8051400583c0c036500440702c01c40004100c2d03503242e201c0c82c06c00758003070b00040c2e650410180080152116014080d214131404e0301c0401c94100c683c403070602c0b030511101003e19040210380d08501404691004034198811505c0201d49544a80308800703144540824 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 103908228 1250 103906978 103906987
    0xb0106090f060908070501080403140a08061002030903120307110f0705041407080a02070c0302100c060b030c0f040905010b0d1101090b120a0e12120406060510020307060c02030d0e03 80
    0x3090004141160b20080922150b03c104106244001c02c03000112842401d000c0c00d15520303400c0035503030300e0240b0385a140c100c14001200316426030442901c038007641098403400e568244a200038bd80c0d03440f502108582c16803060101c500355034180740c02580d10030001e1030150045004400300a1030310b500d01c07403120074541000c00140450704241c03282c040701c840320300c040c10381d2030811030780150441a001c0c0100c451140c0005014043c804032100c076074011a400f60500f40308048100e030040611603980c1c1c048641c68202411015149400102c05d044004d0003010700410314030010801000b000300c520300f11100d5407030719015510b650b1041d55082f03d09000b00c01000001d113604000400d0482070ba0020717000c00a09129030b583c800101088185c1c0b01c184940005504c501c5152a1868000000c10020700c3ea200010a1400d440454803214000c510490050208548580401c5107001c0218003040c0140d2041c88204040360841d0082c646c80c10681c01a01d00e0030355003242110980701c910882030b0f041d40c0000b5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 103909478 1250 103908228 103908239
    0x90a06110f070b04060305070c080a030212061e0918070803041805130f0f020406090906050603010b090403050a11100c0e0a0302030d030c14030f0402031009020105030609070203070b010609 83
    0x2400030700300e011002a290080c144006504240101e02880301016a03880c0000c03119030180b0001c603070890304015a5034030303003590901c010003039403100e03200300240300c85140450050700704101d22040c0480300792104400c1d85e060805202201300700401651080a41c00a0850740032000c1c484c2c40040c00c24040034590302c81c200304c07480ca14022440c0c218041d461508080140801c0d84204014030641c1c0701c2d16103030025005007402c6408013505800694804e280c0100003c0080241d03005407030092045c082446680c5d02c1404042c00c90b1940e0213520b4100c4440300010b000244a04020504495107040144040d01c0d90701549150081445c11400c5990390740d0703840002c80390040103441d5030340800c4a00c021600e080d6400f01c0c0d01c1f031000407601814507440d0f48580b002a0f0080340360039103002410305140e45070f05c4e0880314000c501074141c0382603010b0b000c0c4002103614480075014040c402a010f031030b001d1854484c00240001c803a8002e00d400110b0000340031000c0041c585401c014000d000d1030355070381107003828072 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 103910728 1250 103909478 103909483
    0x513020417060f07180515070501140604060e04020307030b0c1204060207020a050405160f0207080f0a02040b0102030304030e061c05040317011e03080c0102090a0803030f100819030203090a0611 85
    0x941454180001c0c505c00004d25920424000240e0310180c07001c2c500d02c1c00c0c1100c0200d1600070460014525400c1c10a00c0005150610740c12b0f21442c002c581c2400803035035074020f064030000107542c06500340d080020140b02080c181c1e01c00030341100f071900003245006840d8100b4481c2c80c40540301210070940000b500019450203652a00203090119810086811704201c0d00c55014840718604084c4143d040715121140d000b845680024004003082d140c07421240c0c0d1a05440d01c500282c228880c034035020503c101948008180d0b441103500d030b100d00410980980c1080b1287e00002d024425007413000e151208014054041d143c040c0c2c0c440e07258030703c0301803c8905012107050160440400420030152003804030512078080f20480e5045112503030303038030002141b090280c45155002504007461600004665400200a40c071032400c00010155540f500c03488003002210741d220b41c010a42c01750100d202c0c2245034003000e10100d886401124689081c02004c01c404030b907540c0c00080840c1e100207101c00d18900a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 103911978 1250 103910728 103910731
    0x3010305071a030910240e01080f01020a02070b09150a0c0c05150d05130506040b040302010f022a0127020f0f010f0c0c03050a0c06030c02070e010513020417060f 71
    0x1d10300d046046150508640f40e549002100d254112074035007107400c2040b08034a000d003c02000c1180303040d03542911542c204e48511f0081c07182940078880c00000c02c2082d1418400e554041055901800a1a1405106204a40040b5021540886a00d034032248810381d070300c001e000000c0310f80c907003942021490a10008501069004500030090095001402060305089130307403811700840005900c2d150000c4001d5020800a00140076124003010b110622440074a0a403245201c5e500a00c4104103008117072090b400b0340108020f14101348489055840c0b0000d042900740046a0000100884d0701580641d070001e404140782c00c0004203981c000700750700701420114110710040c0ca100006901d2900000c049480c201c0b1400f00b0400015449400c006501200400444d004000c0303410500042c01c1c0300c481d03a0040d01c80c403408a0b1500000c0a15103001182c0e0000325550b19003441c0c107a0b840c0500303106091402d1503455481c40c0e030800001c50341c0a214203c200c00413250b00010046440d01d850b103400509070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 103913228 1250 103911978 103912019
    0x5060f0306040b0121060c0302070b010906060917010216030509040e060c040e040804030f0606090b010c0b0109050916080c040b01090b0702040b2205150114030c03040c0b0301030507 80
    0x200304108004103140b0403ca078119031081c09001115800c01d555510300503002d150041c0058140201c80340324aa01d90003030454a07009900850b41d44e66200101c80444040d4840ca00c041520f1103001c11600303030b213401c40c0a0b803891036000151411082d42c8038500201d459910403004260040340e00c0200341420710031040740c840140000d1480b401d000c15a4186801180301c2c4121210b900f200041c1000507c200f03541c02542c1c421801241718449180c22005804e840c01030240591501040756429841095840300468100e03c0e0a00544d007041240c0c40980401030810b4030714072035040c0514100c002400340000034540c0c0005001440c407000d0406c4169562651120704029080d6004d2081210b00402c441c0900d03070403280000d50491010106409401d20b030381d580800003103000300e007501c5107194010912074030410040603100780840e001503072100385006c4c4030602544d05000150610cd40e01004640160041094900c1c01d59211403900480c0d0090304110b9903508404001c00c0030241e006000c900560 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 103914478 1250 103913228 103913233
    0x181603030f030b060f07030c021c051501120f030306120803090f0a05070e0703060b070807020111030c100506030a050319030b0402070b06060a0c02091302090c0403021f05040f0905060f03 82
    0x701c00300014440d0084540000d401000011441e04248c02000c03007243e200c0e405003ca41e2150190104602d0440e00c8050135103407800385c10320190b6004400754466041e0f80301900300c8803401c8030075114040e8240501d60114203060b50303044086891100440d030f1691b0280310780400b969078a80242c2c01c0d82040608480d400d031a61000f51700000040000c183d0b4000e44d840d0b9007800035503942d040d034101d015003825801141180700004d004400e106c8158000d04206000ba2101c030251180341d5500381e500c0c4190807030b00c1e28541020240c501c01500307a81100e9080f0300e006040700c40c403102c0b03516101c0c00c40d4810044d03150804102d240202c6196010b008c2d65040c98001c81d4110304290868540141100d0001e20b9180306140010b80304070024012101c00036000d4024012840900d04059181c46025045005a200348842e90000340c484040b0021101a66400b500b540034010312501801d4105c0d148282d90010b1010900020070070782950210107004000011000c116410f089050140103031350188980d010343c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 103915728 1250 103914478 103914491
    0x110306100302090702151e06090f060d080702030303070e01090b04060903120c1202010507031103010f0e0c0d05070f0e09041a0c04030203070e0a0518060f181603030f03 74
    0x1000d90315180803250180d0b41640c0c1907680010403800e042c1014404160754a502041c45103ca07600500c02240d03081c10340038603101ba141d800c01c008808200712040d64000c484500040d020707040c42840c1d01034051089100504103603095000a003146c0084540800003841c50140b0102c540c0d1205c03c50008060025146107010700b0403200804c0711400e400041d100743da040040a1043c1d110b800c1c4590001e0b0441c151030074244041354020f000e008107582c01000203040c04460725003400c00400301e074102c1c0c0b410072105601034030705418039203152401405024030234010300070002034070900d0040620400d43c5544008103070750761500c050a54a1011030305401400d415003000005913a0401801035120f030b419801000d503440c196182d10a110b0340c1c00080d014090a0000200e41c5014200103028140c0c10106101c03940c1c810803d4110020045400c44640d1300c0b240100750840a24040a50000081d01e06c01160307071000c40140e864030200300351061842940e51000c01c10306500c0171246410840515092240 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 103916978 1250 103915728 103915741
    0x17010b011b03030c0e090907030c050a061707030213030804030215090d030c050c10030e0f0d0804030e1c0503030601020606040203011409060406030b190c05040b120a140112110306 79
    0x6801e81c010285503855000c20a400c2c05144078034101440100300c4c151910300310060b03540780c0600b44822155500076140105841c6001c044e42d03001c0d1a0b255a80319049801c000924480200240ca40400e040e400c000384010325091002c4140614080c0821541d510303d1807060183c056951112003010b24418416217401d6503c40b002c4588207030300340c03800d00e004076100e04000c2d042044810f8265801744c084010488120341542200d4041c050107420380306101c80112a0340e0716014402c0b03d01000030140400280080e006011041c00c0400192044108001031b450b1200301440e00181501c00303510100400800350381c100100c40d44044103450030b60542d494102412080d4921100403446001c40700c00090868503141e003c20001d54001c0c1904000741002580c1502c440d100000032442c1d00d040c6a40d508407940244203c070225204024110302d400140c0c4012880d00c0400f0705502980c9468255a4078001200305030a401303005400040c1039420300c0c03864800d4650b18803480f418060703000003040104 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 103918228 1250 103916978 103917017
    0xb0a052511040c020f031305010e0306040308010303050f040b0d050a150e0114062205010f03060b16020402070b01031b080c060f0f070c06090e1e060402091917010b01 73
    0x1980141d0b404108040c034081e041c0d04206181e15180303818800815000711b03e004507614001240c00c283c9a106d02501030100345a1a25011070340500402d0400c3e0041000a1003080100031021983d042c0c0c0d820540c0781e12800100350b0103c10142c807200d4403041403000302411441007000c9402c0c3d6400b5414420324080000c44100700c14031039803a55040105403c840c40d103c800850b0043e46051142c40640a0100c4103e102584540210b0b0b0004d000a1034000802d4040d20409041d00c4142000500f05809508041100d18001c18202d07006a002d00260780060903400b94240614883c00e8400760b108100c0e42d006010701c41d00c0e88081c01700c0d404281425440d80341c6004646092118040e00c958580040c0603d0103644aa00d01c000d01c0011428000500e155200a1040c1610340c035030f518074003d448170701e00c500e1800c0342455513054038410400461180d1400b90b004001c1c91070040c1c06c034090400748174040b0f41c3c1803929030b00000403034000d604241501d00082c4101c000b820002d003003c0e5980b01c1008244030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 103919478 1250 103918228 103918253
    0x7030305090105040308070602130602060f010e1e07031422020d020105040f0b030105090a060620010e150612070303090909020d0807030507030908010501150c0c0b0a0525 75
    0x505000c000601c5200c264030590031140610341001000e9035a400d40d1401c1c0000b540090320811010894010100b00d11381301240c154003d12801300003000c13a03406c0400341d10301c0300d1380608071074200195100d001210f00d107005d007200e00ca40141c1d203002403c68107196101411101c0149281c1010861561904211040c2040500c0841e01540e1400741c001083c401a01c042c8030b035802c00c1d000306292150015007050107200075070503500213507003040594070381e6110901a00c546006140101d100c0c6034180c0340b4503200641452000d80c0050011420980c884505804c143c0780800800091a00c4010090079003040c100c4002d0f49041000104102403075520b000304441058000c5180031501e03184074401b955217030a44081607c0e0403e404507581c4a462030064580d034000c91040f400b0550010001a50a10610030300e4121046808000c410031031010b011111f1511050040f102c0d041e0908001c20310050042c064103840040b511003960703c501890250301c02c13840c1c00b1003210701301c0c1204007040002400b900440 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 103920728 1250 103919478 103919483
    0x8160216030b090f031c060b041802210112020102070f06080601270b0301061b0804060c0c0801150807150c03140c010911040e071a0c070308130312050c0703 69
    0x800040e16006841800c00b02d5110f4554000d200120b0060034507180f113046c002d01c0c019415810820542d8074564440c69004520072409045a900101c0300c5110543c0c0060050300301c1d00f03007120752510416982150b1103000307070010a41018501d05150865030100710680c00340c6103419000c1007051030940018003842000f0704540c10032809041e01ca104c01900410f400c1240c08000c40108200d48070030f121041d81c2c10900c90b100c0081c8000203800114030040042c07040301c1d900454428035060509500f0f80f0308901034101141d540040e5100020b54075020710980741081c1c1400231440d0a58988402d01d0300d1301ca625001075050700c0303144508010858202241049542c3d15041c103417a032000c2608c80f08214000c080003450309508004420080202c0e514258002c0302d0300719000c02c0204104e4103255511403150007030100100c19080c0c4c160901c0440000b8180d294225011a0304440d12130740c07410b0b103d4029800d1a5150b075000a41031042280d0300041002c03020161030024103081c4170081140d61440c051001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 103921978 1250 103920728 103920743
    0x18050712140a0812010b360406090501060e0328020d05060a09050115030c03170403200f0405040206030a091b0311130b01120506030102070b070816021603 68
    0x240420410741003280507500e07590038180c500401c058204002c1d19441141600e0501286800100c0d40224040030340340b0b40854100040d0b41c142e441c40c81c1d01c01c6a001007804a0844006400380701e42540c85004100180c07078451008a9a545080805810b10706a0207801e4032a40000f00400c0002003010f0140200048443d0001201c1c101c03400803c29480e44030030003400c14040d0004114071a0201d4022503116441280204403030254128100c408030842d000c001c21000003018200702080443c00c400d000e2101480c4d0441c50300e81d503075442020300b0718690050400c92207044c0c031403062440c01e00d0812030a12002d0714140447e01c0c20fa4001815840000c180c071203016502d0050409001c030200383c001e480d0071102c0c450403450b07860381409441d01303c2604442d80b0543c8943c81c5125100040d0140c003945000c10384034030942c5500d005603c405020003e02c019090365091140c00b011030b20607501a40154a25200c01405003000140c1c4008000303521400c1c800d44d800503000541e40c7c59600d14420490783c10100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 103923228 1250 103921978 103922009
    0x5090705090d080c0a02010207092f0d05330109031202070323070906080d050d0b09040303060e0906011a090109150302131a0f070317010801020d180507 67
    0x2110b410481c94060a120404100403a03520030000b40348440c14000d800b1100150b640d10404016515005100b2a00c0d46106054411450840035083c000708035120380d99062031441c40103034013100c80c11194800c2541014007103084542048015205010040e090480c080341c45c0400603094507000e01c40107240d001504a030b4807180d80b080c8001c00182d907014014030800800042e107442440e64080001c600c5004241c000129500c05118407012075001074040d10b071100c040c0505842a400580c5241705450f21a06280d14a903104c9606510072031003502c000450382d003001e0900d802e0744c6006045040982c0902d005120320070054204035002281d07500f01540e224161030048908070344c1c0d54000c0c0120102c07400301800150300741e00a051200c1040e00500852580c5d04401101200060703004840d580042003020301468022005182040c00f170304000303541400003d001c408030301e0245d02c840300b107950100d41d4040c100c11030701480004050a0445030541003082c1c9800d61200304511946000410703814 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 103924478 1250 103923228 103923247
    0x19090608071403042907081e042312040b04140d03020a02060903010b03071d0603070f06121b020a2001090b090a1205160605040602030a03050702030405030a15110405090705 76
    0x80daa4444081e8050b04404c081c14a0413011f4200c0c00c05442031002c107944690440c45980b41c1d03018842c416a040250707400c600362a00900b41c01031003400300001240c02154012000c0440d25002000100034048040d507a441c9801d1440070144000e9500301c0c400d0008004000200350700041c00810581c044460b203981c1c1d400039000900502048e00620303010f0141040000c0c03840811038213180b0340d108000b0443d507a0742d507050406032182d403d80120807940748401014030000740700305101c000946044400003010341d500d10352141401c040040f143e005901404115003009020500d07180c50714807003030005c0e03d680b09440c00a0b001b0406400390324880382000c920090f25036a800c00510003040f040d94070080b0303e101070410035194450150220129010448006a00da1041d8101e404032090742e8055030401d0303003841040b0050103000c0e10040842c441888086003640c1d0511034001000d01c03604503039910f091100900d0083c3c404a890701da9040a0500003084141c480c041825480000e43c901103980755441c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 103925728 1250 103924478 103924523
    0x405060112051b0415090207021201110316260604060e011a0f0717030f0108030f0304030c060b1009060809010b0609091b030a0609051f05040c051909060807140304 72
    0x2d00710500b417000c0450300081c040c1d12503000784005030080c0d592030582501403016600b40d810034610b440e11440100002003010101c406056507000b520710702800c500072501a0020351f030310509424946241241d00b0700c41d180c03800380305000060010800501841d03241000c1a0702040c400c40010307a024200080481108549030111081e0742d9105140c964200301c0d442051485420458080c0c0e040c00030340c0c0001c1043c050010540e8402e400c00300b0428910343d9580e030100e889011903070080341d5217915208400115502c1841e03408040c034481da2a0780e062460100f009000b94000b801e440c12503450500128800c0c0c882c00300b11000d01000b076416110a485000844190324940c5011214151010040c000c01c0700c50741c0c00c10021100c5c0d124051080e0f480d05005441c8500642a01b60491900b00c1000c2010b400c154110304418842c508005040c81e01f142000320300c00b8640807000c1d0000b55200c00c207110941e00280703041d0300080103242040b0036070305a11285009200140c4060b2a0440c0d1103044100100b40 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 103926978 1250 103925728 103925741
    0xc090a09060806011802040f12050a14060a0612020306010603020c25030201120c0c2402070623010305030a050f04050d110109060309051c1b05060405060112051b04 72
    0xd640e000c02065030350700d880940340c0c14203000c1d00c600800720f100d10800c1c805042c000d0340c4c11f03901c80683c001aa00e1804c0001840201302040c00c131154003490b488a03000c65082c0c4031201c079070340c0100c007c0e015a00c1c0440d1144100c0351190041c10316080403020041c00758500168650548049040041c0d403101c034030a56501d4036050054044068030600d40d0f40650301008206401200e200f0f13201d00240301202c1c441c05c0251103c0040304030000708500240b2011801e25954030310b030070311039102c0e00c0c03101803507945001c080ea4441082964202e1711000e1003154018407061258124440c40e5450640d941103980b4680c580c032404036040100200071410040c0d0005241c119030003808000c10400010f011403801d04041000300c042c0c2030208078040030000301d132402800b500380302c03580c454041c01c405240345450304840b08800341c54000300041900b04e81020383d007071454561983e0007031004021601e454a083e03890040160840d410a034071815451001030b400140c03031107130503034003500000c020001c0402090003000c2c03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 103928228 1250 103926978 103926989
    0x111902060703090515070203010c11030316050405030334170903070b0301240e10050c0309060c03042c0a05060d060c0906030f02040501141806070b0703180b0c090a 72
    0x103501145c5402d00454000348210391003500288090048030717206442c64480303107645000c0e43c1c1042000804408021520a000703a001e424101d040ca40c81e00040392641d0001440b00e00d42c3c1e481150801407411881d94200946a50301c2000e4050000a40c3c40710010290390f03004000020011800342d1071541c00740081e401420303a40c00080d40320361755500c0d1111000f010000143c0e94420340b01c40c021407940709980c506070b0740e64040d0801407001c3c004117045990380e0180100829601082c030201d40c16594a03001004220b204200840d116402c1c4907000980204598074000c1141203001940403003010001095032000408100081503a541d42c0032511a98035a0001000c09240c4508034440c590001241025260155810081c1d4440c13a071300038080f40f280d402039902140c1100180803445607280c005010021030740021081180c448030200345903420400040340d05c03042c2c102c1081079031350b4144140d4000720203881030f54260b607645072a03c03620028080c005122031140080d11401310385464481400805 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 103929478 1250 103928228 103928239
    0x70503010903030219140922050106021e030a17090a05060c0c0d0203040e2701020d02031e04020d060f0b1201090c0515030114010309050d020604031119020607030905 73
    0x1a9842c00600a610600124a10700c0069074428640d0380b0502d841600c090200b29800d107030002610400c041c03803010803401c10b0b010038801e00000b440031090040078000c01c12a0018026a07082d101940440101c811480760940c1c410b1080c0d50426601158003024114500e0700400300d5282d41c007078107092500c2013201030094820b10007400748650b9000b000749070811001c0c2c140c1d50180c41c048412078481c81144240004000c0100103d40b10a0202400314509203c0024401185458030b803282d017a600940c40980180c0e601104000c1140c01d02061801c5034280305050084516040e8005484180010f00c050302c040e94407240e401c044045944407048c00d040c014003143d100803840789a28003804804a04550b450401d03003000903542040610813401981d0380703502c642940c1c02c00e100002c04450f0900b0140c10107441c0e04070500032610600c048004007850394080c01c96071a03d03090140103141c82c0700c03540324240c0c00750301c0c03c0c0b0042601c1384c02498490703030484460f80c0d0307001c0340e0030220b8455505d03400503039000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 103930728 1250 103929478 103929491
    0xb090a08160e010602010608060c031012060504030806040c02030d11090616050c030c010807030c1b08031015090b0304080903060117060a05010521070305070801061a042607050301 79
    0x140e40a003004102e41c010a070960305681c94070001c03400c0e101607110340c9449500c2440441c00018038440030716842101016410405640c0f2800c480c1041d0800d03200307442e403d60301c2c400d10003810350007001e03554802e2058405200c103980d078060003950b1717206000c006401c1654500024040102c100200d45544100034042500c1e903d0307040602c510b81c001c0d1b6104480da482038070952001402c01044503544040140c5034100e0a83e40c441041e4081d1861030702e0b0078200400c404d040c480d004000c800c0000306601814065841c1e2401c00002c03110200581c00c44501898404080d03104980e0100c80081a5000f03e0340d1130780c4a03181c0740f0380400540a1156400c0e45802104004039542d480d00300c40d5216105001c00302c40d010341f039201c0c2c8001201c40a000b0950080c491b00128001d0901c402031000141c501081194a89035a07921400c1c1001019002245540d4464804008001d031070b084401c1c7c0c1d45c1120003110310f028641480070400c46100c1e50128007103151929050346407481030290100a000140092000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 103931978 1250 103930728 103930753
    0x10e0d051308010612021903050604030c1103060c0301140f0a03030f02070b120103020d0302101b0905010216050d020312030a0504030305130f02120102070f1b080607090b090a08 78
    0x141c01c1011040810790180780d00003060101402038504441380380c9024090b501c1c0640a014070004c01e19603031488941d0001d40040000e5003000090701c0340303010355034416003421145130404d10030b441e4001b854031a44c00700c4140983e080e00e00c2c4c21241124a076070300050f01501c0d02c2000c1001051041945540088070600000c14075400c68002c99803120213500362001c103500c0d2407151843e4058500011414440f580050005080440c06854001e001740110307012072569403c000144d82a81c1e0180c00810451100c054156400c0306000000c1d20090024109040e1401c8000d105486a8480d07a449041c403d180b480a544062110442e460180580035a0302d141401c0030102400b0700751422400a8503200001d5500c0701690801d100003079114108481d0f06c00b0301c0d000c200d44641d044d0710ba42501e541c20800a00014000c40d0111041ea1088216005220350340d1101040c051456005420f190400710800c040c25501c450598141c1d0182240152191806030228100403c05c0e000725105100e4000003028 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 103933228 1250 103931978 103931987
    0x90a0c0807080a1e0510080303010303020712020a0b031807080f0604021005091201060501120204031101120608150912090d080d020d0e010222050303070201031a09070f080f04080318010e0d 83
    0x300b055580001c50031b1940c0c911641e96644000d11014006130440b141c2403008508030200a0a81800100601070498450080c0b5803d640291414540310750081080410f404041c010140105650000717400403084900d440b5448980040c030081c4280d4a0290007400703d4010380a0300d9501c0e00150030414401d01e0346200c80d00030305030f41c05031501203a0069620705003044240200c8003943d60225142061920341c40040d101c1c541d4100300102c28980381e00020443c0242000042c0400600c103c940040c2c2c1810850301d800c052608403403006003101045964016140c10710b824070030691081c007083c1c2c1c030884504400024020b006072a204541800d41c407500d00340f415005458a1411328100005004d81102800d290540c01d1103095019002804030802540c042d41c03085020340c1000d00c881c0c0429603520f0001e0b21209044400001003424540000c0301c1c10382c0244216840040328240700e0590401e51a502d09a02000f8806076801c1c1b144104825410820340103000c0140b20b0108a0b20b800c00090170240 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 103934478 1250 103933228 103933231
    0x1a0d0f051212070815010c110a0302040f33030f0813030303061401030903080a02070206070c0b03010e0c0c060610031404230705060a030902010c0c0e06090a0c0807080a1e05 76
    0xb80001d4200000c17a400c48103544403132942010584580180703043c0342d99904a2560604207607648041c2811000015071568010300180b10105440043d505540c850441010f002941030b005895a8481c24000503030501c82c90501a01e41000403003c43c81c0480c03801000f80d1264011302801414000c200108068154000034140ca4034080d040401c40035100c011400c456415402400007210540803510380344441c0d00800b1b02c0e5002414003032a114080d01d412054004940c0074008005002004000e0781d48130000d415001440c04c00240d1034041180710150352154080c1c2800d202d0071900c0c5e06406824081c0d4002900d0410103401e58280c0c0c80d0500389030300c90762000c891888900e440d440424849540200344c48050310b1000341480d003010240d038006c40040c01c0156040b4144030180c650340c0042800049080001d1400084d121014a0104244006c40380d0181c510b401302d5090211840311b8540010303003940d108481e4903202c00d2070303076810300d018004c0e020121300c0e04030340c901a640703034503140a0540046 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 103935728 1250 103934478 103934491
    0x30f1e080c010606030b0108090d030506060d02030408030702070501020a050c040507030605031606031a0a0e09011e06080d0807051c020d020708070204240b0307181403011a0d0f051212 81
    0x20081681b844d4010764440800f120704000c1c54110b0440201128000d620080c2c0005020b8031003070500d5280c01360030040b40c2c0306031803d03a980304000c002c02c801c030780d41001414098002031018055101c1541c0e2080c4e41d9656180c03204c0d00c5541c648000458a601c0303580040c0c0102802000c5440306d098800002151008034000e203030003e82030032400d5107445400e40007094244000b4040c0d805e9140351062003000e488024140400035501c2d0164500d62024000341c2622009041c1000501203281000e407900d1b0080140c13296040c00009420456069045403e41d042c035540f411a0301290200422040000d01c10541107504072440030403c1c0c4144101c5601501d0098400e8038100000c40050001c0780c008900c144041440e0150700300248007030050840996000201030419944c200700704000040b4510458220301d0140f41481410102d61501340200d03415000aa0544404212a0404122006075940740942505160803160381003040030082403250b2504410880d40300c0003001d0009004040945c1c0c01c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 103936978 1250 103935728 103935731
    0x3030d1d1b0307030f0204020f0a020601170703111c02060a030c030b0402030405070b070c0306140a0c0806031e120f0c07080f0a030f0215041b0609030f1e080c01060603 74
    0xd800880201e505a07200400041c000c090951035550b031203c0c054074030201203802c15001c1c851b8092880048018162180c41900075008543c14a0107000c944159880400600c0d0f0000d941000403c482c031851608007123064031800443e022429200303507a2130340104004e4000000140181d04903078503500c90103811056076400d21952a400c41000107a0000383c81c0981070f074000090400011020348014400f4610407801c21181e2a07032074944d08211041c2d03a103000d0014004108100001e00c25205601c1c9000d11410031356004e08100c0b01007503890415050180c05400d440b40c801444e80d00401045140002c150300d09030341c0d502010800c4440f42c0007005401d0681c4140351010a4040002c14064007101003031006022840c4c82d51002c80f110b0b41c90056003000d5001c0e01c07503103200740941140c010748244c1c001d04081c200101c0c0080c0f160010885070f1701040811640d50428000034451004164886401040c0c100340c1c540c41200640e10304040d02d900909141000840c20410403040d0041c40444900d901d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 103938228 1250 103936978 103936993
    0xc1207091419051018080c0108060301020a0c02190306020d0f060b0403110d02060c1b0f03121b0712060e010c03060b03040b100801090503121003030207060e03030d1d 73
    0x20300a07403510307050074584034288044091000f07081c000c2d00c000d10131901c0e00d044004071044400001c581c0c465904054041d41100e5a4880b00d035820220598202c0e005030021443c000c8006401041e400c181040280b00d0410200c1c1d08800a00ca4088280515004401199030706095480c0783c000f01a0140c040b4240740c180071000880002500580e011a40c10107080e240d04243d0b801081014a4825030072039011000340604151101c0400c2a98071241031a0201c031200c7d8012000c10002a000f40f90452080d030222503042d444640900641e031800c8036040d807540b07a24544d096424205900394000300c9503410724801350030070f105041d0014001d03220010f000700400d100d040c0c0201c0c03d0b14400e01692900080401c0401d001074103003621994031810000781d4140044d00d56012a082d41e108000c00d0b111540007154804001042e09420341e00154280703004014245140c0e4003039201c41051107018203000c50304100c1035040c1c8091003254415141c5903010842044220f90f050003140b0b2130215009548640740 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 103939478 1250 103938228 103938269
    0xf03030c0f0a121404140a0b0a0309060b06040b04060c11120709051506090607060f150302040b04020406021504050f030403140d080702120703050405060301030605060114031e0c120709 81
    0x250f4540400290304e2031589000d0030610500550030108180b541c01108045000489111030005404119250398021070102200e04141c0700391003404510b1880b0f01c4003084104114840403085808031081402c1400300007810f414251095405141e0858110800c945088108040801e090b4151a0300310410040c9171070b442045003200d0b903441403498201c0020054103101d0714203840a030020a110f80004201c200055148509480914004043c401ca40a00030300451615028448002c002980c04508051134807000a650720146154100ea0103a0b841c04102480303424004c5042c170542040072207a6495503403030300b5125450b1414414805000e912201c140380351140903a940a043e26038000d000140344c4121242d890303880484100d083c4035040200083c191103030406140290300442c400509460f040e0000340c64141e0100c4400c9423600d0410420800300765039809401481c6c50002c0398441943c0b0101a41d40520605c00c024601c00409010000c1040d444003070581a5001c0c0301c0e2082da82410750 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 103940728 1250 103939478 103939487
    0x50f01140301090603021201050402010c0b2502010209030111070b0a0b0a0b0406180602060702120309010b120c03190317060607060e071a072114070302070303080c030c090f03030c0f0a12 82
    0x644009001030f0306371440c000491100ba1916403c4148426003581400090950380703002c0244c10110300c0582d401092000300e5207420f104540308003507a01805072030548113688010240c40010804520b29654801194258071401c0f0030303201a101504003540d4a0341c44036005411240d82c100654001c40001d500410a41d03c04501c95029080c603400074214498618040b9180360801464a04a59603070708070641c066860068151140180710302900503030f01c4c070380c080c181810a148107141c0c0040301411100e000940c440952202c001c40804012019101c09000405c07921902c14003810550911441070000300b808680384c4d00b150072050317003032550f4001c20b42c818040e40524600a0080c5101c07801c4422505080b1401a000c3d00036464110241c14107817283d41d0094001d400700f0740043e84103200500c01c041c0c022040701c0e0405080000c040c218905090100c040344140c8070054000c10000c0e09006090314100300340d4105100d00b0302926409075401100da0b50314408280c058074110094486960514080e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 103941978 1250 103940728 103940731
    0xf09020c0c090411041e05010b0a0f0e03011401090518071406180d12020105010e1003060e1614090a090201090e090c0402030c04060305090d0504050f0114030109060302120105 77
    0x201414a1501100401c1002c1a00800079186240180b000720b00369603640c41a590400c4020380c5020280307180a03030001c1141d90507080209420400c00031102e460780c0010070300b00c40c1d100e03d143c812a940704010209025003918801410344d9030343e81c0001b24100d102e9402c800d1240e12400142403c4100e4145015510512881404642c003011a00107000d404c3c900004c040c1011840900c8215101c21404550003d41100e0190b8201403643c0b880e00d2059820b010b410b0061060405103030f00c0e820070104191140f00c680c40020300083e501c8030348031070f0100c0901c40d50014070354030700000b146607030368015006018111650291113070545030005070b05e181d0180303e418400c136010780d55280e6603400d000502444090107028000a4443c4184103580c0d03940da400211b01c20360340564900d440d00c0ca030000140548102030560f40380c580103900001000c0e9441410b403030880c0e03000c0781c801c01094403020061340c03908890604005034010010003c0384003e4182c11004c11248260f4200070740a4504042c6803c0301ca0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 103943228 1250 103941978 103941997
    0x3040201020d0e2b05030309010c09060804111003142e030803061c05030a02010614030303040510050a06030c030f0201020606061e0a1418030705060c060a0207050c060406090f0902 79
    0x1101440006501107a0031580c4650f611302540104000e081d0315030b2481c0d40c00444143d022a919004245021640520803c0007080c82d4200409181400ea545160303061405010500030300384149480c5080e8860b41000c6510301d09000700104500707101c41a0340e200740303c400182140d0010144103400c03110500c0f102808483c1c2241300c80b81161581420400030752440030b00d40d00d104a49044003030105100f48020840008107400010f041841c029400a82041c211728961194200340304000c003041c004207a04442d402c0380900014559590b6000b40c1c001c002c1a04084d00590842c4000305c00c110a12283c007207814001d808076003c1d40d43d0001004200c1c03041c1c40380c4144c0380307040c0310351023840307020f4240601008ac00c00e0a2500c9402c0d5282403450702d503002a0440610000303001945601c0c4d003030610694018140940d861490003105c140c1d4595110070103880c522074680e0014201d0140507044c0800310300f942000b00390b1070f40c841d41d600b001040030f08035008050b0444011080040c44a50b14402c0311481c02 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 103944478 1250 103943228 103943239
    0x304080a060f060e130203060601031a09071b08030a0f020c0703080d110d050a0e06100e090c030607120e03090f04020703030f020415140901090e0709031703040201020d0e 75
    0x1010390340301005002030350b85421440e030b12a90702065078042c51645078882c030140e102d4400030100e5401003601d02500640314605142c40d000c85407240031030101418420b45426280340105071104c2400b12b40c0c00d001d03050030506103c00e84a9200400581000441c05aa1254400d104060821101104038031a040ca541c1c05a400380d0020400668600050003940d070750100700081d1f40c00f84003451042a8451601106406d0380d800030006001580e120300c07060035000320014561454480c3c0c0c0581d42800900810f950605518000b5804050030030805251100113400c3c0c40250411140180c6003820942d140009503044c40500504064004103484104200a112209103c0d094082c44025440080c081d001c06407110b0740c8400000b41400144010500d4004030320040049907002024400745030101104134a040140644030703079020340303804240c506070b09690000c0e0307d5003441556442100d034802090721b4003200c2089030042c400c1c0c001c1c40c0310b14000c0c4c0907202c00b50300d0803070111000d00100300e645a204 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 103945728 1250 103944478 103944493
    0xb06072918060f101e09050c0703120b0f060d020910030209010801080606010f030b040902040c11100b060d1d0d090501090e070801060e3114070503060603040c05090405070303030509030408 83
    0x3101e1107201900400c18111714900c0030340f6040d81c1019140112188603110780001030100425501c450b0b04000c11100e207004120101903900000e80c81022018440d100d003002040c500c0c0840070341d504403286040000c02d1040b448090304400f070080e41004165501240b100e40001540e4400446d10a100b104142c0d2244082e02205400703900800020b402240c0180d41c550000e401a00c071840f4802d1540c4403510f076040e0448510030b5240c6030810505030780c003080b4201030880145440d4142924100d1100000c007140c0c0d02c04d0b004841005032207d0b100869648500102d5140d450340212126040e00d20070b9072500d9206880b00c05a00b13100b41c041d6003a5000030410300040115603c03d040c1c0e80c0034010000d2840b07200d00700000000a101d00c0300741004d62028100000c0c100505980d01c1400e0001601c4a01085035241a5002900c6800000c1c83c103406a080000000d040007180d48400014080040120461b4141400c2c07165540c01a40821000729181c40c0200d084c00c4400000e40381150302c40b9000380b425 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 103946978 1250 103945728 103945739
    0x1404060501090c05040b120a0e030a11010b010302090102100504031b0c0e0606030f041101140d150609050904110f04020c0a0b09160302060f0d0e0a0309090b06072918060f10 76
    0x440700808060b251950f42d00c9d0008800401d100a0006104d0396486c001401c00c811502c0e4210350001c25201d050500c100915801c698010650740c54603480480001881e548506080d00e900080241943c058952062404200520800601d080e50014490010740da910503003071128038842a19a075202e00c887c040082c3c00100c9806818004900609d030000780350b270910f81158050b42000c001c01402640760440c0f024080500f0441d880200100d00d04103480c030f45031201040f4101000382020b01400008081400340740ca0720020003a08000141c411513581c1560703c9500d86420440c9811541ca09400c0c0124212a000103682c040484c03e030708404503542d242d9820048a54414a540030000c601031118881c0c0d11010310030001f004504402611000200b450020000503c41d0003c04105290584201c815210001a84c00702c69100c3c4c46421080d2101c40c07613961004108002144041c1448100300c2003c0314410404003a0507040111190b41c0c44072072440745103c000720749025181401000801c42e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 103948228 1250 103946978 103947007
    0x1f0f21020c0a0605090f190f080d110d090b150f010e010c020a0f180912050702060904060303090918080a0e0a031e021807120b01031404060501090c05040b 68
    0x541040101110b400e540c4954503002030710340490701e9107416008011591458101402003408000ca1203c0c286500c5034140e81c1c55941201801029103108000302d02c0d09500d0311203503c20382183e6900180d40344c44402580e4010301500c0e990360112052404c410200c2d0f0003031014240501c1681c8010b0680c0003610aa20044a5500d60400c40c0c81c1008035440a010141e00c6c4c000d48000544031020b01001c0da1401c01343c0e07007103000060340e000d048200c1c50a1030580103e04142041c00385d000f41c52615030350750056400095102c4c01100203295119181120010800d40c200c00c0d66011681c1f44c48080c8000c4609800803109095112000303403c44e601000541082403080500c800c041c0001044401090b88940798210101414200103810f00c81841400c2d003549801c0d0801c4148000c815246c0c045032400780d400500305080d810f83c2204060700c8800045d101da01a8016958485025050b641d842c074082c142000502020301c55019080d01d0030301008a540d01c079108032130075610105011490420346508400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 103949478 1250 103948228 103948237
    0x6010b3c0d060321031103130308060a05030d0305090705010207080c130e0a062004060c0201121d010501140402030606040605070516030503030702010b040e070504090c051f0f2102 79
    0x504490b079404011000800031320319421108900c903000d441c0c510302900c0250407a1072814a25810140034010041c00d07804403011114072503070502c0e0000241d106d00010070180101504030540c50b0140124500031941c0c540e024601c0784c031050080b0f9206680d218010385e203071000383c000c000c41030304092814001810102800c003202e401c4001e00142c2c1803001000282448042c06088a034641c036040c0291500c0d0041c08608244c481d03116406141529041c8080c00035100442c00a061122403052280b030b8410680c843c4007541c00b03a00d6444000308080580034000d202c2400b40c0000e502080710080114200340c820340c5d1003440c000d459289801d00780720058550b034200f058211510320841c1d59418100d01c2800c50b4a002b18442c000454030303800c2291000c0e0954505856190155180c40d0310b2642c01c2200107044411910207850000b0b611072741d41400d00c0000c007240c1046e90040040740002c2e00c081001c5900c1070300388001d66202e00010300d80010455500401410498031030555603c4c00310220320590081 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 103950728 1250 103949478 103949497
    0x803060d020a0602030a0f1805090a0b0306100f08010203040330060e04031b050303010b0a050c07121a061020150105030d0201090506040609050f06010b3c 68
    0x14806000654005042c441030750700890011380010a5820103641c00100460700b0b1000c50801c0c0034a840f1204103c0c611030300d01d1003154420a5420003280e0744280e942e00c001481b10001e8150b0f80f2030b2429214441c01c1c2025413141e41d10658030400c1c00a140700d030600c252405103605541c1c03030b42c02c2c451364041d0a0015540c018966000a888100c00030f203072a851198200509121001e01c43d04e103040d007400b03409007a842a4405501e008620054002070740401200e0540d112205c0340c07034035041710441c01c8032903005014800502d4828418081518044d41030400a032034400c0603400c0c010ba6401a400038201d8041d1203540d0800c0001c80c00204903401400109600c800140c803103040503001e80d07103151424200902000440031000c0052007507003030a1010f001d100c40e146c00244070008a0340d90722035484e60010310140c655a540d8200c1c0b401c03c00306010182007001540304541040d61183c22030303e8254003089034804903441705c40c0c001082044c1003441d203e0101c2620744680245c0100104401d181e07004a444 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 103951978 1250 103950728 103950739
    0x804031103030c070303030b0f0103020a0f030203131e05010b010203070302060103111f0c031b0203030403080706110a0503091b01020c0d11210d0e091303200c0103060f0f03080306 79
    0x552503c0c1008000002c025406581c1c086a9043c90f07a0502030141d8021040604060040107400c0c6020380004401c41c813180c1915006903030399183c21081840d082030071002370410002800003a0942c521004120040d40544008c00c9000e0300c010069a580c41000cae40240503811040040020508445400e68030b200060b216002c0a11580b00340c0c0101c491448481c8003240b0b08003d06410306521180c0d41c288040070b119130391086c44080d00007036541c1c01944070007450035000086071010481c85420800107101d458481c1604d8081c01c0bc00940f4540003110b8460091180b001031000104d4a8029507107c4001078000e0180340c0341d4041031100b01c115018084d99030144690021819844243d8182c0620780c01c00f45440010300050345903070601c8180c6141104011040000400a50311164541d4011a0300442e807481e0300000e1405540e4418500d1a1200e81c502d901c4412009440220702c0e5580d6030300c26a030401c150341d107036480b040c42c80245000f8011600d15541c414030015103503900440e0802e100602 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 103953228 1250 103951978 103951987
    0x51320090d031d06070f0c080102040b16051203040302071701051014040b280e06010e0d030e0603070e04050f040b070c060b061317071503050a09060f020a1b080403110303 75
    0x4030300d150b032002c2d0341246ca04443e51007100c01e11609880140282420400035498140b504904109501038102c140744400082c070003400404c01b04020200070444184025922881c4c2401d010791142c900384a540010040c0007080d0000c1441072241c503200b202516416080142006101c000701c400058041e030308159034040c944130949d251000081c1400c1340c03044d41c0541d120541071555201e00e4a41c80303050740000107003e100030790381c010860b01c02d0104140d540450007022800c0840d100010f02038182e400420000038820140e0f0301000b214001030701a5020710a41c0c031405942d004206e0700301d401602e101e0b030442c085884144114504c50420b805140046019850480001d065a04c81c1c1d02e42000b008580c41c0c1048010984080001c4000d000310241c1107003460030441c00f18089c44684200209996140000c40d901cce0b540e0b00030803180307030050710800c940c660122113600250301080f107071400304180041e5140c1103010320024030501717948900a1802c4c10700c1c6a8814021000c4086102d616000612 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 103954478 1250 103953228 103953287
    0xb0a0309060f0c03110304051c050f03010e0402041a01080a15090204080d110613121403090c0901091a040f02120a02070c06050408030a18051320090d03 67
    0xb1a81d50281c1d2203000510765070380e110050100c5000d444940003031201882040302088011580720b00d04088076014110450080200300c40030b04c104a29035496000200020414808107408548924801c1d20100003200c60110b0340d001950307110b41d605000070014800106000b141723130850501c491010800703084454591440c8816600710740c11180301c0380c4c008054500080da000300e51101005030240506241d00303202c00c00001310300d541c080c0600700c000800e040303126061185607001441400144119180c3c102006502c6e01e4600000115106042e544000304841c03107c3e2041c403540e941c200d0f20024030501e085050101902025000604046d402c1c080d18001110016402e8498040b8640040ea91349551400140204a41e0450303c10800e0a000c2441071540000480e03d1210603401d040c00ca07a505001010f00600c1c6680050381c1060b83c00710000e080300e40075008440030801d031081030360040205482c5100d8600075803030002d610091700031005e40400e0044c01119007103854220507028580312788 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 103955728 1250 103954478 103954481
    0x320105041503050417120103030e0109031a04031404080a03110703080403080309010608070b180307080f01020403030e040b0a03020d060f021803010b01080c0421060e06090708010c08010b0a030906 86
    0x666181d02081d240c504000070030a0644002407944408419a030801c2c1008613040d0010005001c01008c0c000c6038007000600da030144120b00f00030f652050010b4551036014044043d0303408186c1c1d04802040100840b50500300d07086050b117082e40d101c503004010091058400b01d9003510441c00e00d03416405030362004000706444d170004102440c0070b52140d6070f03241410704005007142d4990303102e1181500145014090803844a003102c108403c1c0700c0d1401140c21030000001c1c03c0c6580e5070b0090540344039a4903007502994040d006030040324080c0d02c0c1c0ca803a0703104103c1400107032074482400b55404a0300302c000b03000514112146110783c40c0250070000349000b031201c00300100e0b4800340c11403c0c603929954056800b49400d00a8000c45642071916a0150900003103145a90281d40035601d1501008000840300d01c000303012400406803c0300040c0300100086241e607032200815508007100740151000494199014021005428032903a500d2000b40e00c0d04480d0203042c3c1258501408050b162800040820740301d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 103956834 1106 103955728 103955759
    0x3080711031501080d121416020f0a050a020a0803091e0609060d0b0102010518030a0302032e0503061008060402061b0313050a32010504 60
    0x100064184070042c0303945042c84540b5000050084400a059201c90300b0706c1e120540002001c4240748140c85161706400059808800402c100700901da066600e00710b100d01c1035030005d040b40340b4014106120079000703440540c4040265401c3d440d001c1c0119000b421010002d602d0510018046103940d00049000c0e42807282ca100500d40076122a0300700c481c8403200508155807490800302000003020110718181c01036281100207141c81b01443e6040c0c0036034030036900640c18045190403c0b4041c0d800100205288808042007040c10400e0000000c11610200100d042181c00d00040c1450030380001c055040b0150007150800103107601180300c40c0c0103501660f100fa40c0c3e1402203140b901044a180c43da480e01e100c0020b00c0c004100016600703009035442115000159541c880c100ca0b0120413003001034030030380da1300403202e14400400b0a1521411006041081c02e0a540e45200300c40c4450 = true := by decide +kernel

theorem cover : BRFrame.Cov 103776978 103956834 := by
  have h0 := BRFrame.cov_init 103776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 103776978 ≤ n) (h2 : n < 103956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
