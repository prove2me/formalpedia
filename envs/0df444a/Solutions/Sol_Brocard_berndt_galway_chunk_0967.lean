-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0967
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:33:13.580989+00:00
-- url     : https://prove2.me/submissions/79ab1d20-da0c-4464-927c-944298415128

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 173741007 ≤ n < 173920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 173742257 1250 173741007 173741021
    0x7111606140f0f30041e0f0c12050706020316060e10090b1b070203060a0510030c18050a02070c1a0708040b0702010206092a01141803010b040c08060603130c0801 71
    0x480d900208041e9002500710505504440007032580700d1410305107150900e480c001c0c14640344603000701c0c0d44169072236507584c14504c5540d00004031510311610b60010031031700344074542c06020580b00841c1000000c1101c0d100c1c24811240151060355208811003446c45c09000951030b40011840c2446001c0701482d00440a09089800c1b0241c00308050001008400d14002c4800d0150014000e06603500ea03109800010a8003502402d41c0307010003c000000a140e5000b07400c010034001407803080c0404216030035819104001c190139861403041041c4000100c0450180044d600c142c021561040601a0608464410840051b008102c04600061380d04900740c0200f03030b07462003a825210030b0340742c0300e69682c0c1c1c8074035086030510410905018400700760200d804820364034405250405015030f000070010016031148035015002d4207031001c04c25081c1024010f4000c181e030191010043c1d251007410080c400c000207070040380700319800004108a081910a11a040ea41100c04140101d0b13807400300c40d00810207 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 173743507 1250 173742257 173742307
    0xe07092603160618020612061819060512030703030e100905070305070918030302030403140a0206060109080d090e040501020403051c030e07030c050118090507111606140f0f 76
    0x100454080030440a0602c480085d83c09032219041041450300b01d4182d8074002e06203900710707010842590401840c0d4070307032a00405044160704104030213005c0700d0007541c0041d000a4007540d5250326031001e0380b00001c101c8020541515002560074000e9042c50b0034042c4540000d0041d80c207249001c0c0600501007201b4049274884c00c00c071204107646086042c1503c0151940031544840c2049100110b400b80d0011603002d4401d00c0c100c1e0700843c0e0180d2140c003a4005107004001644007600300121940c0005005e8003415194008240c10f0601e03610040c0000d01901442d010b90b4240808941000401d4040e02d01441d405000d8814442d00801a1460104001d2078000064203104526464041c0800e41009880e08071341c100c242c0906000054811210011024900b1411400c0c0084c060b41548110342c00390f2890703a00c0000442041c055140360104040f031341989031903006030422840780c0107501c4940c01060448469240d110b81050390000e0701500d1842d072802500004c000d0721504542c4d010340c2c90010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 173744757 1250 173743507 173743511
    0x10c0210031b1d0a06050403020d03170f0f07020a080910020f0102031f060e010c020f130c020715030e070e04030903050313150c0201020604080c0c06040306050604060e070926031606 80
    0x6803038100183c1998a2042c00c5c040343d130820060000d400e20020301c580160003410019003032103d0200c8499160b43c1201c1c811320050ac11821702002d4081403902c00d4100d40c980c8028000c10055485640141c8034145101d813103881c0541e440390740240240300e501e4415810000840d1a4a442200c80301c080d40c020345203800d240213004000c40c20a009400e07884480e00107070748100348155690700f40132040b51031b00d200301d911911020391104150018061218480d0f400c0e4041c3c5111072030105203200d0320000c181c140c0c050608040030b29010740400540d0304111010341d006800561540e042c1030303c0800c0c7da90409032071804001880d00c40c1e0108500ca003001c032043c0c2103814038a000d07260403c90b40860700400c000d00503003104000c1008111400c1c060960601c0b00d80549081848201c0050350a0b40300343d10403551a611803040069903c0c25100300001000f290a01400914081e031008000400d5405241724800050885004130200d03441e020003c540c4000271a03075a4004501c1400c5d519040007002c0307401034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 173746007 1250 173744757 173744807
    0xb030313050108010b030708070e040207060207200607020d260a0f02060a110d09080405040e07090b03010e0312090c0a0303020610171b030a0b25030605010c0210031b 73
    0x10b5481c0044070b10801e032030782e5030310b20f031340c0710080d04442c00407490003c0c4bc1d0081c3c00340020b03000703d40d0500c000d00405200d005102c0c8070380c0e641a08286508449500540305a40c00c2c0304400143c0c85008003619a960320203e007104d02400f0046420b40d0400c02e03840c0b00462680403030071001c80c80c0c01c181071320703080011a0208d500b00d40d140c000358810b480400344440100c000034012101041e102e0741001d180d051007240c0c81c504054440001c202280c40b2045040748a40c0582c0c010002c80d4402c0c8540000104264000d105591030354604940e01e218001c00f8800d203881050000d000c0c1c03034040c00682e0b244c0f00d000740f0300707041c00d60382c0e040007035540c0000e0750000d003800d20282d4000b030b010701002c4d03100a4120004019081d000c0542c055400060b1a9200301c6406000c3c203480354002070726440c1094450413129010307a00c01c00030f03802c0c20340c40382c00a09035510506242039014011607070407440f180c0c80c40d0350481d041500151b44000880242c840600c0503541200303600903483d40950080d5a144490000c0a2458164 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 173747257 1250 173746007 173746019
    0x1e060504150b060315040b010207080d03020a08180304051e0315090610290417030c0d03060b0301090902030a021e13050609011e0b030408040302130b1509040b03031305010801 77
    0x24442905d50f010403001c4c035602c0e4071280c14243c0020f105c600c8140142c801d080d80d01e000d49401d050907a8002800283d00088951019410800054001c4003c02c0e21110032850603807d19079030300c9140109446034140080c41c4010400000301c03085456005410b8601010109036031211128064824064078090310000400d0000e480318020b0444801028240303035060808040e4801501e14118034a44040800c80410310b031404000000b44603010400440da100b003004005810000e0120f55103007050308141003003004c51125020360b415141c0925001618181c2440020328190b51801c1c02500203208003030041103248c040100070400030050b54448030810540b12108203c8030100c0b403495024a4460060084042c101c0010308564140c503090700081392541c54484003600116030880e0100030004003441141402c2d000b0099a00001d00b0a0002a900500207140c0e8400100283d40c10700700410080c01c01d41e42e0381c01c0300c001741e400170301a80da80f112040c2c01d007059106079000e110302080c4240000501 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 173748507 1250 173747257 173747269
    0xc0e040b0103030509060c0114060a06180b090a0e04050d031508030301030b04230c010f08190908090406090b0f0d0314341406131e060504150b 63
    0x416540411900c1840c0c0c2980d400741c038213401c01d0341119005902802803904d041024440e0706070269a042c038603070b23444c80d10100300f100320840e5030498400c015220560050340c03001d0b640c1c40e0041e984010035040d11803842d500858000c249a50110141d240381c0005c2c08107210000c03481e02042159642e05001041558400d80098405807050040030342c410401080441d43e001d0b000303030700144110b0307080450f001009030a0036201001c680d1a0525040f01a4410300d640c2c00070000c011400c1c0c80d00340368100b0301d481c3c01c0e650441c001504049400645400100c070401024804480e411800180200401a1900c0c0294001d2241d0310788035001790a0048910498039140540904907941a520540d1507000d559140c242c03500211103142030f104000501080c2600a00c4206644e42c6004c01d188454418a04061403d10380d0480c4541680e08600e00380302d11600000d40343c00c407881c0c01c0030038910b10350034918448250307a020840241c8002d25140030f000820a0700c0b4258a1601c800c2c3d001408125050010401 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 173749757 1250 173748507 173748511
    0xa17180102120a081b0301080706020c010e150c0a1b0314061302190f061716020d0507030e030d030e1b0a090506310e19080306030a080706090c0e 64
    0x2d0464051100410480c450401c81758420350a8a01003001c00701c080c1c015210b85c1003a004401541c02c03404044c40644d074108502c0e005405c0900e081070880c458040441d0301c03015000c40c065900d000010b40c140c0c1d00001048004405035000ec1580040c4494500500c03042d407690104685541d80b10151081a0350000750705401241104489010320078030f5801c1000944034400700300444600c200001402151021240b4000d010b2a1500d011001c1070620555440381e00400b42c80504544031010100f10b580016250800f00a50410b00d0303a809250409035005e180d00c1050581c0b5100749528bc00100d0352540140b1421350808080380d21504c0c00b8601d04404121003035030b0b80e80002c00310100b00444125504816001f40c03000e441c080c0810300d0b03d1108120150f002c666140300942203805200350241510442c0004803080c400b0300350490088035540c211480307190002d0081000803010a0b0b0694040c040b4403a1190f1142c0c80903541c084d10b00d072030005800040025a944c440030040003e2031a51f0245d098 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 173751007 1250 173749757 173749783
    0x30d020610092a1106011517070807050f04090e030c070b12061908060a2915030601030b0613060210050601120f060f0305012901050307030903020a17180102 69
    0x243c220200349640410f080341680d060080140c0760202c0340d6444401c3c4150781c080c4c8a4102d41c00c03000c480c3e400307000d400040801d50f81c481d80039100d400c0002d0741e58005899904002946025a540d80200901907103501654100c000402e02d8108000080180000101101815882501c075040da64421018450090040c215024965600010390600c0e100c444c45800a04c036540480e2a1515041c1061030b11208840406156646601c0e241003041e07000c6004003141e0409460288407001c10000c580c0e007102c0910800342d0034001001045090303020381c008401d00b01011b0541034440c914161035140505942c4100005802215600c0e103c1000a029951143d481a1103408011001e070013084003d10114007a00d80c0d080c3d445402103499103680300060010340c0560004076040040440300411400c0b0340d20172644010114001c1001ca036001802d1725401a40c0e07082c00070380c0002071b05060381022000c0000410402020403c04c81d820042d001500d408001d2420b00ca0f45050010016a13803180089489 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 173752257 1250 173751007 173751041
    0x302030103060b24031312020105041a06031f090b070c1a060906090a060906140112090b1612090602030a0b0108250c020307080c190b030601030e0309030d02061009 72
    0x1413000c3c0c441c0f00000310f410040c1808049284140c5448440900c41c00c1000f42006035101c6061105000c420310020309c0110900d103501905040540029540b02d5070300b641c40283d941000350200300d502d815444250166080110041d4526024071300404000740315404135444048030683c1b0707100700702c0c01403854420040646046081d0b11214100407031000d0042011110302d13261400440c1c54645405110024122070352413210502e8104001b6120031803440c1c0381d901481c5002030807004103015420031500880d0550b17256503070414400044032408903080f41c8203052401c1049070340800130550700541c81000a50340c1000a54141c500450300d03404103a500c840c01e450040003c40c14110a260f0b464090049400e100e03076406055404030b0308140322070303010a10a803c100805005414114610101d41c6001d902104000d4184400090340b40405058281090b50b038801440b1220401c01c05c40c1d0700244020704640306c10305600c50080d42c400c42204c40d8550210040000a03a01c0712a024038100411030b0541d03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 173753507 1250 173752257 173752309
    0x90c010c051c11010e010e0c1203041d04020a050603250c0f080d0509030a0903030e0a0b1603120e0309090402030304050a06050409050709030803060d11060a0302030103060b 76
    0x1103601510a80003a501401600d0051040851245110011000c680c44400740600c41048490840e20010740c508071030790501da2004043d80f0081902900310108903501491010003540541c514080c41c0c200e880c4c26100720350002428149080d49600c25882260b414216907100c2003030149030b0105403500180500e8601c000780e00c1c44264a00001c00310360614264051b40c020b51900045540d008030180d0b4a0500003644419407115409440e502011010045103042901c010082103002c9920016040180316208605156940710b40c0c14004e003000a00e0944442c07a013054110a04603015007100071840c5220300c2824404e950003864101710140000d5802d00d0035034400e108413600c00030000c0381c0c54001080701042d01d6036110001c202130034030b503550f0a0b02d460808080d102101c0300030380f02100b80080303503d023000000e1900c0105c03507200c80d0907500c072901c401e214074103416250ac00e41540c661201c00402d0b21101c03141d069001e94101c9028001c14400d40941000707000d07100c82030088150441e4000c80d2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 173754757 1250 173753507 173753509
    0x10c0c110d080f073807030203040614190507020d05070f02040207020619080f040c03031b0203010e010b010801050d0218130501050123030f190503130906030317090c 73
    0x1041c00074040c06001254640050160402c4040e8841181110700c5500d09000c402e54410f203400b507000043c440300e2401200d035001044883d0851004061030201a000030000b030800503960060210080d50304060121810b141c52260600c07070240707011603803880c9400d001508092001070760b621003c2d40f03500c40503c5d1911030340381d9049003100c010013030780c0054003044100c0060f02c1d0301d8000c04d640b0b6101c0c0001c61700803100c1c940003050020041d09190841c43c0003414000401c40d00e002e400c0c100e0b9814146910307008100302604150411030746000c0e601d0752800007008a0810190030594101000340c0e40c0c03001030380e00c0d80100002c00354004006504014945104403110005100d0345400c2a0400700d081e40021a50791020700390b81d8260840404500312281d0000c594035110000300202d14101e000e030462401030a080c9542e46281c4c1091404d507072080100005200c824001c441c0c1200c0c20f8a40079003015150071180001e0300b1684000c03400542c1c00a10201e0302c01192100b40e002d40303140000360404085200c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 173756007 1250 173754757 173754769
    0xd08060603070315030b010b030f0907030302060c0a031b0302180103090f02040509030f180f0f010f1b060f0507020601080307050613020a08100504030e062805190302030108010c0c11 80
    0x290300d007103510342c0303030031340440490880344944d1300030300101c0c403065620720b071030800c3c6000c0800181c400361b09544815001d000003a004103000e0b81c0b00150003181602c030304c0c1d0030a04a010344542224403148940aa00180c8116850380003024044043c1c400e070003519610400440407144800c1000d0043c2001e0300341540189400d400868000752108200c0c0d0070a0007161710040151b20920900051440a482c000c000781000500340d05d400303c044802d6210f5071000d10002c0c00c40800003004000708040401c0803510b445021000090964021404100010345141d28a0090600799503140c0588200000001c030382000004031101640d10001070306c0d26446003119464596905502207038000b90074200450025030410a0b00c022126005010495090a0038040c2821514012040c0241d0b410032002c201c4034020201c0030454803842000403024203200008860070700810030b00d0000c0c030b104080c84e03001c100e82c107070041c41c181d030000c40080081d81c4030b070002034991840b4448002c0102002401000140c07400e0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 173757257 1250 173756007 173756021
    0x90109060c020d050f130509100e01090c0e09070302040b070803012301050703030b040609090b06042a081b04060c0b0906011404050403090b040906060905032d100510080d080606030703 81
    0x78011b6205940300c0000503421a0120380c403d03e400e21400013080841e00c2e0562150050070403040070030081d011404000c004001a4000f507000c1c40141d8041488148654119002480e0a151030b030b84402c640c1c5000240e0782c0c020f1040c134841c0000143c800503030a030707010ba0314014110161161480c00300c259400f03901410401c0c0405030320079610700c00020841414000e28100318840d405200e640c0c0703004800c200842d00c07141c404101103418203009529690410342075040c049004d0410756020f965440c0440410a07080c1c401164003200407d000892542091032204000d20030400b10904d03a07a400d5660f07990b940c0034411000980d4450701c0981d113508095204a80050192400141542c0c03111840040341d4401e501c10040c15664810801829501c03240701c40c05010300b1400b400c0458640320700e061542040d500040039090030514461140c2d1010400718041144200e410f00c1140b0f421003420101c126540314091090062103080b0103018891004c840c42050002c10007070968803141c404400911013 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 173758507 1250 173757257 173757277
    0x301020427180819020604111201020706180507060201180f140f03190509090106030b010c0b0702030d0507050a09180204260d020a0f02060306040f0203090109060c020d050f 76
    0x5940320455030703111002c80050041c0d01070b0921907618606650001200c801d0302c00910304542080c0300340000507514992482841034210b072402c1f41000341d45107003402032050030b40040283d0725200381400088454400040101c0c0100f0130b9902440d07a510050b801d0f1030122101c192003c100d154660300046266200340309250250140c02000c1800020f002d00d4140c94801c01c00840d403010500301690403401d20035800d15803c51a151f824101e40c01b0100b0000d00041c05001e05064584100400a901c100207140c41c6a0f088a1084903d042001000e500ca0b03104408040ca11820312001a00940c0140c0c21203821031426540d1401c440d1601188106104071805100000c680030040080c074402c1c0c000b200104d400320ba542c1003c4109201c40482c2c940806400742c4010b5402075008400845c822039404512250142c6100c2d80c3c82e9154000074009001d2001194070051010003070080300001540440d07a9103100d004200944042e0394401c0e41d52302d20081031200006c2080050354600300c1c2c907202900100364 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 173759757 1250 173758507 173758511
    0xc0a081906022b0e0607020703032c130603030306050f030604170c100b120609190203161211040515060d14010b0a0f0306050105040302060a09031e020a050301020427 73
    0xda4080080f45280207490540011a260000c03039000d042c051054036004001800100840ca02e036070740c00340403084520b010302d0340741c0c0c9640d91280940200060041c80b03548000d048001805d20b15a03035000600e4640000da000a26000d004140c0c2c1c1006940e92080754401401042c1541d01d6554110f25090207080700060034809001b41040b0603010030103982508036400d008a0414961024480c03048a5142110920f81c407010500c10211070101d4007208c1c0d21010381400340901c1c198008a890149424601030b844100e200c03000a1049a01d801481c504d8854100d4166810144003000160758041e5052011151440030307040c07007490104000c045440184501154418038201c41400c6e500c000d0303001800c00c83c400680d03000d400d03500c408401c205010350300f010030080d420040002c0c000d000d5408024010000007581c0300c01e0500841c05103004546c41f04601c10f550355803100c28200403180c4071080707020b0000707001c0100d040e16041c001c0c0c400390303401548000c40c1810f402890703100d0040200e40d4400456 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 173761007 1250 173759757 173759797
    0x4111206031608102a14040305060f0a1b12021e0301030b04140715120f050702070503010b01110d201002300c1b07080c0a08190602 58
    0x38003408040083c000d40028020015240400005549144910b28101080c81c4203000203002c1d60800c0f021070b042940752000268103450040e1301c59109a800141040c801c7c10704000000d03107804c118910840701808280403072503810305640404060500c0c2c01d0003081c0240300b01d40030304210358098500e00f103843c211180c0d0140e011400c0080d690080e0404d40303080c1c02d500c00300000d000070140810801c001040042802501d00380c15641c030006440b0560082200100d44280c602d07480d5041001150010801001036080c2200080c0d654455171040714003075400c2004030300496008014118070b414040000e040701e041c844404a071800e900d11040081b10f03030694440c4c0d102010030054411000a02c3c100140c1e500f504182125904034980707001d00e10044101030520701a960101d19540021148100c0e0351203101503c8400301c0442c1c001e00d620400c1c842e0f400e00140f125000900002600740c1980d900c40d0180d100d9440588800600034500c020083c1030000700f00046440c3c0c020710b444516089800380754 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 173762257 1250 173761007 173761033
    0x102010f1802030c180411040e010218100903050712050111030106050a0801091802330d06060e03060103030f03090b0c13061b03030504020a03020904050f06060411120603 75
    0x640ca00c9101030790320300c5401c1d00c81c02141020489a00303495021914150801d035030301800402020004c0c001021061002d0003400340e82c56580200032181e030428001d6444041c050308010061018005543c491039107099407000441c040d00d03c4d542640d4010707000d040d1041c14003518032421035148208a921b990303180c00c4581d240380420065030107040107542e05507440d081c2d04d00090000506802c12301c1e88501c2c00500048203040568000704681e81030700c80701c0003444642e4030014008800f001128060036018402101150000300404409549850030002d903520b40d40b0840ea071005401c00e0a80540c000310042c00840d00230704003211200300514004c14580c1d0301e640d50042085003a15064070880020602d044035100c00003460b40034110760710303000c00616004e01d00d0030b90600b20181c4c041c09065441001c035040d074403401d0a41c405990050224607039803c242c80d10581d0340710803441d10669800341c980454203074605800303080c00d20300c0020402e60070403088030048105a40090862941880b440200300f40d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 173763507 1250 173762257 173762261
    0x13030212030705030708041e0605071e0c090606030e010204080a032115051336050f030306030f0706090e1f0305010e0d0306050a1203020a0f0813080c1008060102010f 73
    0x170b054401c02c60140c5680c1b8045003060441180412045004512801807021a41c40f10540d1041034124200741e04c814020501c211110400b4030000d001c40002ca50041041452500a40c0450b081a6010000f9612050903c0e00f00e002d00d005125458104401441c0440d102c2c0c2503200b0401504100041140c1200948100f02d4000703448030b40b1041e1540c1d4081080f468041c1e1951680c1007e01d40600a20000d17480d0341420424030420152140b0f00e031003108003035a0000101c80710156104040711007640c020102259250030840d40d40e84688517900c0c60340751150003c1488011201d0588800c140c2c0760601c0500c11341040c00610107500108842c40da8036203900012031000c000e5004000010316081c0394480503042c00c1c00c0b0012a000d242c18150100026141c0f0900381084580c441407075004103000e071900702e0406041070009400c0394000b40c1c0030401d101c1800c00a101140c138800c2021405503a80b100305d80c031003080c0780c051607001d41207000c3e000701140100f480c03035031040d01480005251a0001c2000c01 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 173764757 1250 173763507 173763517
    0x90509030f0c0c0f0306040506010603150801050c07140f03040e040303092a090e030301090b03010b0312120a1b0806010318151820150d150b1303021203070503 70
    0x5000d42c0800f84940b414101000402142c807810303000f5050b280740680f01d455075410184510001c042c0e5034030901e681c400114078400c2c042c00e80c4100910a034141500d081c03803035410007001912540080d11400150103030000300380c403e020301c203809141401d140c56a01e1a0048006200340e0a040d2501c1903003000606045036203040d2040301c08920b41056454801da14408100d0700194465172501140783c0d040707940003040d241101c810b034101041d403018400120f80905038201c4695094070600f604920206040e2025201810001503065404d43d10010480c05036031a0900c40c0114807000f070300d003010803072141940d075910a2040c140465500c0b0b00f06505800300031403500079a1016009225442ca000080c000c0c2403098400d68441101c0501d140c850820740000030f041c8000d070000005501d5a00d4030760445401c4041d402480407510360100c9001c2202030501d40240194100464401103865118a82522542d00342c0c0e82901e0000380c1541d003440060801000c0150040c070007030185000050307007000101 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 173766007 1250 173764757 173764777
    0xa090204200d05100501020a021c080307021f0b0a05061e0f071505040b01050603041b060c05010f0c0e0d0203070b0c031207140f090f040617070603050c04090509030f 73
    0x39039541c880c1801c2e082124000340081e00d83c24503000041041307a80c006460102903404a400a805502007041e6002066444500502c1c00c8e10110411100c950086003050a82c0d440c80b030106e0412803041d20540865101c004c465900066007001072000c2d0820388060400c3d40d5031045404074003103080302c100900d030300104100c1440e4100052108100550940c194244508200342480141015981c040030100c2c1401580e0003418080001010302c195031020041c01c3c50550768400d011a25258003d1027071004400a480755802e00843e96105a0984940d141c20751243d40c034404002c00000070455503407500c001c1640e040c0f084850104000019000034601c1495080082d6500c1c0e031a20204606e0340c3c4010030140030310804400040c1440c0300340049582002181c5162a50346500780001080030802000b25500f0a181100229007450302c84256904d0304080d20881d15140d80e83ca50840964104843e25034601c441070008101e0a0801e800980e00010488103882c00d201041c1c40c401c00325001a074204c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 173767257 1250 173766007 173766071
    0xd0501060f092403030f020304090c080f1e0105010e010509041104050415030f080717131410092c09010b010909050609070804240501080c04140a090204 67
    0x200000415849800f003004104890655401100d41d25425110254400507060010b083d0324a45194424021540507240301b0400300401002d401009091001c202d905046a060031702c0400c6005a50782c0c096070900302160b00302c8500342c0c01e000c011610003c03c505494140801400640420f13074980c010041090707064242c00e40c4907485e1100b00070a40e00e5441b42003500c81056041803000c074078550031074012980c201c0c3d03503180d50f0295842d2483c10300e141c00c44c4617012118085418003c0c0d40c0072074003901c11900000349400000e00702100b089883c121610901c1302084021400704003038281801003075401041d03882c0840c0c3c814403442d5038508460085400980320f075901d12000c2c0c02036802900c0c010181407150010499850030401240301000090710250501500100040412852040340c0d240d490421001543c0c01d2410404000904000e0081611a0242030356072001030500e8803c44000c800d0340390b100c0304140c881440240c010b00b6203c50582c1c00c641c40e144c8c862800e281c40301041c01c400c41d0200703032 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 173768507 1250 173767257 173767259
    0xa090f020d060b09060409051308030403020d09080c10030504050708011805070b0f030a051015260f04140109020d030e041503051f0e1009140601030c060305060d0501060f 75
    0x200404a50003600512121001032004c82c449481e508151030a031042003d000549450703020001420742c9141308014540080007040104066001c6140c000e1040c0c1342e200c032038146440d1081c1319166003c030080300c1d800c200c0c143c04580506209410440c3c11501039401c3d103a10725181d40240d82501c0c480e40c1d410103411194081c250410904100c0751006002c00c82d00d46080014603c04001184400b401040c203807510341c004aa800e5151814580043c0500b682d400050551a000034068111800355414012a00080c0196001280b506148102c000090400b03070b60355250f4a44500505400542400f90340e504200001078407080b08000c2801c0c000c0e110417850500b10b0042209131000802d10449a00b10207000300001100002d4001c9040c1d00c02c1d50a915030400010110b00030501d40205080920805458101c00c01c590340c4002c00313a500600462001800111020b590f40c982844000c10701e4004043c01c1110512036407100d900490000d003141500485511803e09544040d000b8030415252140 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 173769757 1250 173768507 173768527
    0x607050105130c060e030709110c101b05030606070201080403020a051002030a0f0b0d06050703090c030605040507051906083303061303021002130810051906030506070c020a090f02 79
    0x80d0f54000d01e140d203082c0d001c0302e070a0070100c2d0b03c40c5920301c52000040d846da00d16024010045040c0c5400000a6045825a80d1303080910300141541c0c0065850010014200e40001e900c502c2c100c1e440307030001600ca1450507030154011100084010400c0c0c0460081142c01c00016206118181361403510600250301d0f0305003040300d60229000814903040e00c520b0960b81c2000e9171034100f0803d04444e041000040d80e179441c510264042c0001d440020445002c4980c080104511684041d000710301031012510280d41311424000400480c080e99042000c62440070001a4403da0b48254084000c11120002500c0310b0800f03000e2080894600302c44401071800f80c0c1007410b04024255100a54030005030100f601920040d4075450107280e411000b0b9000228a000c4460341901c01009144180842e074090743c00b140014002c0400b980c6100d54204000195600f080701805a54141c0e6084405007106455503541500c54240516049811800150340058424014420b40c02ca029003c2005a034034181780b8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 173771007 1250 173769757 173769773
    0x5010612151a030a062a020709050a0203010609140d060207081207051c02030c190c05060a29040b06040815010b0a0e060c0307080307090501121b0e060705010513 71
    0x80c041007011440207900d8855a0b000900c00991340c0e0403200005402c0c03980c1041180c0007031140a1481c20000340c02001a01d1a40014948100c6201c020300f00650713191829920180d200a200384000540c01540038015144c184070510f0a40a0007055101d0301c05d801e1703451300e05980200030b041c3d8036500041000e411551050082e950300401618000d4a411030b070001c50001040e581c482c2d054040c0e404000143d420100308121220020502d8200702c2014000100504e40c610850f400c503014040e02010417101489401000c016561848129140151040e00440d0b00c40c003000110303500c5500c0d0700c940d070400d840310703c020406007040c0d101500e5150320007280354100030010f0307001003010726013044041c1020780c1c40f4060550111040740c68955400800d14410310f113003c1c2400103400c143c0d0000500400307640202040c3c4c215402a00d070340b8860b03241e61154804980d0b60805034840f0359158881d8020a0303101d98401301002500400003810b04810361582400c4401c1101c80e6040911101100414040301d2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 173772257 1250 173771007 173771021
    0x1e0c03050609070f0201062103090906081f0f09080a09060e0d0b0601020a080d0f0b010e0108160504080307110102010b0321130905160e0d110d0501061215 68
    0x2814144014107010300800c8041800400740d10421403404150b5401074400c5d08001c0c01440760942044020304226680b901c8891000300480209002d18400521600b050150000310350100014281c082d4184180020400070a4401d200c25590740803c00340140d290702c500c0c80c695004850141c0c540c020820f001d0100415a01302405106026007000810ba6555030000e640c0d41c2d0100f00c4611a03100d82006078070308444818000e0003190085004105941158865030101c04010303000d11002c00ba050056a10104a264071400544140001030101d542001300c1100c9914134540701307140c00d03a1001311500b103401c0410300722203408501100c03244940e1309006840c80d000c0118080c0070403e82c0c5101e00712181c51000507132400780c500818040c0301c007000b61800f03200409078803005100c01d1800039016420103001c07002541c0400c00320b002050450600402c1800707080d5026902c01441c4031081c040020f020340f0a07800301c03210b40d02c8620103c0c15611000340300403c2803007542040340349524103103494180d401e8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 173773507 1250 173772257 173772281
    0x50a1508072708160b0904020d230405011503020d12050d0c03140703151710020c06100e0702070e0c07020a060807110102030402010e0d0c03060527030906030402100309061e 76
    0x130902404200101341c1142e40d480e07012240160744101000010010780740c4601090000f08008444059454082842501c42c82c07203a40200041c0d0601c00c40c51325412428040070b500001040506c0b00014245101e20140030314a061142c1001c0b42941040207440105071107030b0020341c81e0306040345c269403504a10b9030490104e0405111040007204060350690307981c444c50302148008030b07181c2c160702c50510040b80075941c00181135503603a803c1c402c1640c0d02e07441174401581410361444000b55080c00300c21000d00803800d50703010b4005940303004000310300058042c00b0000e407000200601401a0381c0c640d07800009240c9a25540b62074500303443c001d400c2e0022003c21101c2079004104200060f03070300c45000c0104030000c07540000701e80b00a0600603020640c1c0c1e0001004035142905005505411003910329411546400400c04141c00c680203a440340540322101c1c1d084042400031034010316040117030b0441e1400902c0d0000780420b15407540c0042d40c42c1c6450718010b0303103481804a00600681d000781d41c0c2d0712071 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 173774757 1250 173773507 173773543
    0x605060a090927021e0a030606080625032304050c090c0412120302070c06110c010c0b130f210314040309030308130803150a050a1508072708 62
    0x5024400b243c01e8944548020711030200c0c2000300004d170040e034003604010031025014880300f40d128a0510000c01c881e008091441c80350000040b160006480c4948a00c0317018000a1080400820b007035014002000800c00340340d0306c0040f0340e08005140711602b407007103018030002d1400c400c004080c0650860302524a00891800304820b100f14118250141103da0b0710019454060044a030300310024010000d00130480c00c40300200080140c3c1c440040b1381c00c981d404043d15000ca600000548035084640700c010700d030040b80d80005045105c2d240c026400c080c0908021350f4031102d80d41d11b2012031804905a03400c1c1040c4100c03900a419458442c101a140c00005210b1060616440180044190b80b2000b4100f000040001d410108036000c003c40c40e542c850a011f4507030422524000b142c0e03a00901e06401200c0c0341d00009140d142070f0a01a00301e4042050007400840c5450048941d02c3c00140080309200125154000e840c0784450500e40075141c2106001c0c6081c148002039080c45c1103d103544109607 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 173776007 1250 173774757 173774801
    0x20f0105040b0a0806040f02071a0112020d120203071b060801050126040204110a03050402130501050a14180403322a07170106080109080901120605060a0909 69
    0x4804007100c1120f8110700304050326644290010740503003941d880c2164070500220741c909c01c0100260724140e003d540380c1240d1829a072144045211203488890295101c40448000b034017151802c4032000c1004010304c141d034942049504d0b07281100c945a0b00d451f003441d4954404010030766000300100d01419007403810004080010103486410f103411034242e10042103d00200342107503107952160500c900c413492400d843d5050103c01400500c411541a80070f07104035910301e24015254401c0c1c3e1f05a0714024420004241042c030941c1d100501c0d006183c0e004030100d029904000341c0d81160b80e102c0d40c801e035240501c0300704240c0320100c080012200d016983c10b00000d00710854220405a4281c00364641c4100880e1080411000642c20019120620ba020300c110206000312011455002e84141000034000907980c1d601103422030b46c0004018003a0007050292084943c421189103a6001904401062850321000010718a5100b454a80c0114804141c10041410640104031942c002e05031004011 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 173777257 1250 173776007 173776019
    0x11205010f290117090c091b190e031203061915050c10050709051e01093303020a031d1c050c010606020703021503060f060d090816020f010504 63
    0xd0441511603280100750300b00c440400c2d910036940c8540700c0c0314080311250103052605850b62100303030494076207014400c038400050070703400c0b0310350103404051490034021719140548080c00d407140e83d80c01c0081d08110580b00c554410307613000c2103051114064012107680d43d003410002c00c0594407080c55118a20150404d013000300500007506035610f0a404c0c00c1c000c3d40d840e001c8114a08080810001007001c618000a000410380e0192044003034850646180b8503242002c010609112003002e541e900298142400384011411040400120810407080d03551040600003600c240b913a072038a01d000080d070f0210f00e4030070180d410701604482490040d21040c291015283c01600c4a034440125082d2480601c03110001920420403540c0030394800c0c008202041d00c491009448070700c1132000360310414503040c44107000e4403078030200e80c00340e03000070004180c0900c1e410501c400e0760001c00200a4442c0d560b071880021a410350001c020a118525a420301207900b031042005400b4217810b42810014140014864 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 173778507 1250 173777257 173777291
    0x30506010c0c0501080a02090a091a0108010f05010c020a09050901090308061804020d1b0b07051218010309020609060d02040f0b07150905070f12050c0111070303120f05011205010f 79
    0x83e18028a40751032aa51050000e0010740325102c02540c000e81c009030002038031580340c2e10580610344000c420703400c5c0d10400c01c01107841d0482805003603c3c486842c142041150300442c0300640041c4060401c1000300d948030922011214200c621402c00d0b5140c1d401ca03401c0641c0714004961021007142c1c0c42c01801003100484010740c1e0004c1000740280d49041c0700310244029882c0c01079042c00c4580800d90041d8458030500855080041c04580c1442810001c032140000c0c001503c140c0300c01400da46440e81070500045000e0041076400340e0308100c0c2084811060344800005205031035450070056a5546031503c620600601c0398024000311405005480c00900307400712059501c409210702080071070300340c01c280b030421490703502421241e010340f000016813103060901c48403a01c0c020029944500142c00040d9604008008204a103070010380c4140002400394500304140070311a5000205030490058900c1100d40a800082c9404001e84213402040001d000e01400b140b00504140101000728881c0300c5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 173779757 1250 173778507 173778509
    0x100b0109080c0603181c08060f010e010c0201030e010510030309050307050303160c0b0406210b09071107121407061701030f03050c0607030e010c0e0604030327090c030506010c0c 78
    0x212410b000800315041110001024080e80740c031009682c18071000c0030310540080c4201c160403012400e50340c00101580349c40d10500c3c1000da8180c5482c40605028801100c220341529412418141d40b130860b600c52160920a46220b461248050079009085040103400036846a010724440e130b00c45a014425a1404010380b400e0301030000305520420282d10303210464910f83c2c1c0010f50090000314000400a5000b035909a81c2441d4044012207501d208003400b042c2c4040303021040d006221300000c01c000b42d11031010b246041d041c1100b40d44ca00c40d00c43c0e1021020418a22003965100c449071502e0710303104000d00c42c0c00d00404d06403c1c4007005000c2c1c0300003440c036050305102c080c107409050881407051502400443d0207903403540d426142140703008640503005010050118800f51702e400d40e1509568050310040d06425030023481c6e98106031456804a03404844102014011003196101c8020581c407500c600d03019041d06140810b4110708000300408459004201c41c2c100701102a045001c2094904440 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 173781007 1250 173779757 173779759
    0x1101170103080f07080d0504050106051302070203070302120307050f0c0108100806070f0908150108060c0705120c211e03070e09070e060d09061a062d0309100b0109080c 74
    0x9502d81541742415404ca016030760440c0c0046051104010410206603c800d0a03140c0407102d03491001e5046150104901512070020340541c8150820f00140c688560003103114040b50048030b29140665031818180240684020101e0b482203c00da0151b60f00010081c0d0303c500c86c12500c00e001d528210300555985800780000050020207429101403d10a10003003010741792600c11111034110340303028941c59807824400e0740c3d224050800420103400100c030444542d02e412000030804ca10b0340303003034004485d4000b40320090b9038420b96800c2030360713440300d0a19500c1c02000e0703070007a546441150000c403c91262281141c07690403400c00c1049041f5422000e41400c12109884c02c614030740e0391100981c0c1c240d011040300d43e072000f40410750380300500150b0004400c082c8100c41c140220141c80e900c640c108030388001183d030b1200040c00f81d0a00c54a40c030214800030350307a0b0100386084c0249850b0009142e802564110f445410814136030351132281e0740c0201840c0c2102881c1c4000301500d040310889e11034041c030801c9 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 173782257 1250 173781007 173781037
    0x11d0d03020909071209140c01090510050706020306030102070209070c06060f0f06030c1701090c14041d071403070e090f01180c0201060b0f030f101503020a05070b0103110117010308 80
    0x45502030f600c0d402541e810b544121f0142400c40211501130b510f50f80c01000c00d000408045001c1101d060080701826400c01580387d0b2800d002480c1c2e40c8034040c1d08003c0c10385800d50750900003d00035a654080080c040c07840c94903414800c40306400c0040513a03030540c10881100b000d038441080340d01140c54000003266194030f800220051008800c0b200c030044000c1209140c4518000844d24419a501c072076680003203034403001c02004403052810464000d070b101e20343c404408016548c1f04201611002940204245021914100003001c1c0e800aa0820b079504000a5541c1c81c0740380719403c21304140741d00b15006480f1803075558500000007000c06600c2582a114646502580b400c842c000d40129014110560206880300140405400950070032034880700441140d17004160360320b51120240f0152041a410070201d204c002c0b03020f13000703544498900070400c50100700460101310300300555406144a03c000b00c03c13000c4044001401310144c21410301445840c0b86c010400104000700300c41d07100411400c9 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 173783507 1250 173782257 173782277
    0xf0c04020d0902030109080912010605060d0e03160c03021c11060918041a0c0f180607060f06030303050108150f060307030203030c03040603050c0c0c010e0a08011d0d0302090907 78
    0x40e000180c101e4102c000c2d00756080146000400112070007404480c0f506490440b0618600c203009400c0e5100e03071140d9034200e001000320038250005074118480781d44406007100e00d0150b0728403030012440f0509200b40c0e40c0c1c10f810282401189095003100085202040712401c03034403100e854429100d0b1340402c5d500d100b640f00050034036141e00e942c0040101000c01e00740510107403800c0d041202010580c111751004111791000090f6218160310160f84021410a0166003070018442c1d070241e03401c1e003248100d039100109108200c0040d49070702030a01e00555025000ca80c4c02e01e145409000e5540603000140241c000c200444007130b001d50310306254000006024030030036440b0840828240341098001a4043c0000154041c000100000510483d05640d030104083c2c2d58943c2c038a016030148a6101145030801d1310105519886501c04600380303071000303003840c2c3c199580d50401070855000382000c482d0351061f8040030f00740b240284a01501031615040035481e103801c400011380d98400c002d11010500004140e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 173784757 1250 173783507 173783527
    0x2d0c030608032712010e060714030a020304060b120a060506100c022b050303070e03120a03050601120216050709060311060a0c0602213115060306050609090f0c0402 72
    0x3d0700d0b650780f00c4064240141048400e0850b4042d0114092104c164410000030603080c0c0e2007040c1d14412140291304d21800c0d070b154004040082e40c0047c0c0140c80550301c0d0388551030141d0ba04810072001100240080400b9103c0b0314050090361002410644a00c0d00510151142900910340e00300003a0704641043c10032142a600541c0c0c0001e40700c2629130100b5803101715040001c00002540502296107640081c1010700c0105661144042100072001005000300c802060090b00426008603050500c200088100da909200700c0e04141e00070400d10400911342d4041c05410702c04ca2010304a40f180a02038030381152a4480d0f10704960070030a0240c1c00011790541142e00c50707200600303030541c003071000e665440c05001283c0d051103400d0301c1030b643c8590100110303880c4260745840c100c9404a600c1010500c0d8880b80210300040e081000c01d4a114140703002c0d40120320f00301e206e4400554800d410000d068103002091260204000300902110fa21099010040d02e00008112048a0b1304490259031081d80700 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 173786007 1250 173784757 173784817
    0x1f050607051207030504080f032107021e0607090503060402030d0f090e0c03060922030e030c03150f010609031106031e04110111011406060d2d0c03060803 68
    0x465014a4440b010440e2410141e100008108565062003182d400628114100352a441001001ca24a1440030002070500790310104c050346c0300e4401d0041d02c0b02000c03d807440d44803a41e20001010b905801020420000c00d8010600c03001803c1c09074010019882c003035003c05c0c2e4601c140c1f403012007030056800d0f55644c030910624031880641008490040b07541003446100082d0340099810510a480800001e4800030702c100644a485400d032441700f100750481d48040c0c034510381d010a440c0d00350061070211010754804125240e0b114032820034440d0145801c9241280700d45060f04621300304074100d802000440c0300c108030003010880454105d640d83c0c81c1e400c1f480780e100c416062100003142140301000280481c400050300100e10030b880708101c0002001d4014200e4403620415805410118042115410014040c0651005c0708600041c211a40154110381e0348000080004c0c40c601a80720a40200250041590341603041c1000d1006504003010142c9a0040c0b6000c48121b085504a00001000c14 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 173787257 1250 173786007 173786023
    0x1f050a260708010207020a0b090603130809100801051e030d141308060412080105060a0809120705060103030e01020a170702030a060f09062007020d0c09050f040b1f05060705 76
    0xc40031035955580d00c4842c14003075041000c060b44119060b000004503085610211140c680004000c1c42c5195500c1e0845000c072001c400041d100a00f05201e6010f80d6107600c0c2408502680355102e52000c3d40c507007420422055100c039284030121805200040303071a28000349451012050381012561300001252100140c000c20183c245103540b460f00020700c422000c501d19005078003641d40d40e00c0042030480c1c01d8402034028411a0340100c4104a00c0304180e10410380c5503088170b040401d84007980f8030100c001005030080507013a502c6800c501d00401c101508070007090041c10023800a4400132040d51150600c20004200c004409000001c10f001159424072046410a030300940820002c0c0c9202c041100a00781c1c194201d6070940b91102201e042802c001141c40c1c50381100345035500e4001d1a07400e00c541c007801c50f4800c80d0401c030000c10204000c8618001c0b680f08050403281c1e80041e00c1c15040c514000314006d001e503c0e0059140034000050210145c4210698000765180d42d91100d45140c503038617007180 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 173788507 1250 173787257 173787329
    0xa020a0503070305120601020d0e010c0f0b010b04081b0604060e03101e060f0b0906091516030e0d050c10050c011104090605011b0303050606211f050a 66
    0x1400b82c00f01078204015122000401100700c00d265a00030041ea03881500011940102e084612050880d42c0720f0556154014410850070b500403030307242e0f20402962800e07001109a40c1020400f48100c80b0300708100104e004034408031990b00c40d40c21002caa0070780b04602450080001ea5000420942c400300010511503c035032408010b21140014132600e02e04806050440007410b00303000050421180c1c258006407552041000c1c94520410100090740c4e0140c00419000703103070381c461000356206000140c02d070464884001c0341010340924000700000d1038103400c103118001c020710190118200045c0c0820310001030708c0701614551a40c800b03941e1402030620100085d030070081044030001450000e4811510103100500c1120b80740c13001916010340e01425030034008440c2a413040800c2c42900829045400038140030303d00503000c0300e000d40400d072044001e910040c0300000c1c0101c2d807120342e41103d07141e40f5018110101c54204000a00c00d1520351040d00b080382c00720300700100500b801908808180403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 173789757 1250 173788507 173788513
    0x5040f020f030a05010303030c020705060319060b07030207090b04050c12040501020c03040f0302131b0806040204050d03050717040605040303140408070602060a060f0521100510140d080307050a020a05 88
    0x9041080030024113005d00044000038245042c80a103d0700000f90982070322401003000c4e08603130342d0002c42c6101c0f22282e05480f8185031075180020300604000018030351030b4020f50180c40e50390b040200401c280c45245403950700507480c02040008114224054400d51081c0e2400007410b42c40d1402c1490180c0a00c1c000a41c60340400600040c001d400c030b400d0711040700e209070b8290f8254072088803498210748504040b00c034940d10700300070244544c0c420510341c3c4d03015500134801401c190304c0d0300124241d4000e981d0110040f5600180c2c92040c071200c032411200384907608092602d010300b40240180580900c2c40000d080c040c01c5403c6101d000304500c2074401800c102000c8880581e074400c0000d54401c13003030700c0c410700700c5203046e03004500692041d10700c0080c0e50703002d000b0304c030704040c54030355180c094a1282e40c0c04128040c95446c8610002a402400e0180401100150f8a14100008407401910000f1240e1080f4a8800c8001c0010304841c1660342c8074644e4200741e0780b034401030401a401c0c646120350040042c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 173791007 1250 173789757 173789761
    0x30123030c0915040e0c09040f0f0f2307030c09091403030f16030605030c06030c19020d020705010e0f01080c07060203090a120e0a230301180506060904030905040f020f03 75
    0x10306004003000c3c090700116001d10001c0001120303103444d042d03c43e07245504500d48000050101d41c4841907404428400d01c1d515051602d2911a4020740c81b1548044855454a0315180891148040400c41e000e41e0040a130185a241d80e0301d80180007510321400b5801519005400280100440405c080701250000ea0f9600c1ca0704034204010600f08813807194510001c594010320380707482880389005a42d005002441c400e00040104a65134000400341280b00408001e40410030080c00c0c4404802c0e44282c005281e0050308000107410000903810640c10007078551204401c559402115540440c020300704000e603600d4100079198a40305944028041600001c20700100003000904410003d02a100041020080100894422691743d500326071161749882c0605c0504811b2100f9880d40200c0d00303150100000100c00f29007551302c0c22000c00309940d48074a070744003030050a200440c0c1c40001107525a11a151a0b40d0140c002e00c024000c41c0d010b2640d94000242c840c0c0d80354100e55403070500a43c40d0f40c983c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 173792257 1250 173791007 173791021
    0x309020402040b0306190e0708060d05030d060609050d03140f1905040501120216060510050a0314010608030418020d11040905190b060f16020d08030417030123030c09 73
    0x1d42c02901ca07240102200c40d1b100940c0e10016928005031904080240d10700d854080e81141c0303883c005055940c1c04040c1c07845010001d581000142031090760b211021919902d0460050412040c40c2d03c40c5000c0c031120340c00c210000b13600c402051a110749494100d5140e50100c44075038158001e40c8001c001e4825110354074070030950440e01500403600309030303a41c0401e01e10020300d140503401060740700421100d07103800010020b00d40d500309e00d41c0443ca01c2a5481030640d208001600f12240e58819213000240f5116680446028047c2c640500b04120003035182510706000e68410b0580d0f29000030620740d0200f090b0f221304106030003200b60f94101811868896403500c411070300410081c0d90304440000d00a5203001c44400901400b07075408401003140d410440c2c180f07a00748aa0340305250030108032400c0804440140d40c0c00d581c00080c00d000d40340058030f904c1c1c94617001d20a0b42c000c408903022000c090004000030040c1921080351a04500407010402c841e0002091171b02e20303050845540100c1100402c204 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 173793507 1250 173792257 173792279
    0x118200a080f06010602010605091512010f0b01020f15061005120a060501020c0103060602190807050d180909050a1202011b030b241206010504090227120607030c030902040204 77
    0x29450010183d0300c044e641d461040e802c840842c8a0700c5c0d000344014001410b07049424410385d50642001e002881d660044c040c1d001e0840d0034440495400542d10341c0c098501d540d0400034030351320080a000420040c101d60100d4409604010101403103195050402c24015100303a05071259040000c0d2110700034240808500c000d4201da000d0113006200e40240f54034550b120f8041c513811101c894001e403145a6800603100f4004005400a4415003130403c8280c0005404004040d21403c0a41c0c88440d5400603200c2030301d402600c0c0d8015031840342003416100100350b000ca030300840a6030025103012103509501059000d40b07140d0740e1280c0058910028a041c594154100710b6058000700c5080040031141e0103010201c005107401a0f02100041c0191485071401050300d94016105061803030400366580780b40c1041e80d11141030048000944424055010002000c1c6d02c0d0261080750705515a10007034812554680d00200181e08140d1a9904150400c0c000c1d4007070f01d54913401030829981d40e03464000402c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 173794757 1250 173793507 173793523
    0x4060305061003090c0501050a02011112012112080a0b0d0b04030206010f14040902040204030506100812030403050307081f0f030c05030307020319060b06070b0403110118200a08 78
    0x8010802c200c1007003890351003807044440059100d140c5c118100d003000011035164110907000003d41d0741c5c801441303450181c0d210180285551060103c0032660420551100c515080035000000c890707017072081c10001d08100200700702003106207080d11880d0798158000d405400c45641040d048903d0b009014203210a41c80010300c1940290211401644e89402015004541e481100d1001d001d05c00030080c40c2c030b000d0b007011051500003040581400d840e030b1121414440103444000e00481340c900c04200d01d01090150100d4541c00003005820341c680b54078094110300c0028003442c1041540310001c1ca4010240303090001003101c0d0003514510f10384403c05c0c8108011307036010035200086040d8002401c1d20700001241e00455016010304100032504404044203821000212041d40c0c40d280090515210a8082c2107114010040c110141c10181405442d2003000c2d041c10380759034101007090035009080c0001c0c864160f40100a03d4080031a000b9500381d032007910b54890391040110000003010040001c0742c070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 173796007 1250 173794757 173794759
    0x90703021e0405030712060f020a23040501051606110d0e0606040912080705120712050601021203180718061a0a02070b220801020406020d030b030613080d020406030506 74
    0x210020028504005000302d203d07080d49030348000001e010004800c031480c2209031080001140c8010b41c01c8049060745c10190f50f0b80300140303160068800302d02c0d6600a00c1000341d108003015140c9810100020850b02c40c03052480c00141c021070b0124100903207540203926000443c1661519100200c4e0702c80007602540e04d0b61502c5104030800302e401442c00e441840c072041d5020b02142c400561000007500c82c00c03801040d64040c800305100c11a0001c00700c89032a0320560459440c59844010144040b084450140c4010304660014149548010054007102c0d0482002084030f120b01035a4212145030000d1500b15441580b100904440c0240c420782004042e50709512170024140205840e11100c1d002d1380e504200181d0107940100401c1007804002c04801021019907c008490422003804004250340320881607980003404200c2c455060210401c01c1d2086e00d800d2243e4007015000030380c0c038030f409444a0724581c0f041d0106000c101c02d0000f107030203030140c0c0c400c255215690384030040c0003014211030032 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 173797257 1250 173796007 173796037
    0xc05100203011d090a03030c09030b0106020610061818200d06050607050c011d0607031e0509010c0605070512040f1707080a030e070b181005040602030d02090f09070302 74
    0x8a403001c3c454150151159502c90002c0c025001aa181140076100d410030410501c820302c2c80210108094003041400380070581c000b0081400d00c0ca80170488180310354084400c10000c407031003190301030880380190111ba0f003880d202d40b0305a800340a079100900280d02040d5400e0307107083c2542400244140030b4040f801e00102c00704101e0355540140b048510a50000424a40160a40c0445980900c2d45480002c0c1c04855600840c070030300c8045451341d031060100b9800302c0d91401180d0443d00340c402000c01e64614929000d4144030325640041c001c013050031030080142c1e80300c10019003d14072a4050740c43e600180c03a48140f8909140c10a0540368003869810750394611941c9201c004210004d041743c0c07440d64801a0240341c8001d00d44210000c00c0700c800c0c03007185809411030004440d00c020001e4138100c690210b03001c0d200c1c8034000030040d120b084808000c0500005103c20401c0030303004010b440a81411050240c2d51790920350000cac40304124460382c1da5001d00d001c4240301e441641640a4690505c0303070120 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 173798507 1250 173797257 173797289
    0x100914040c1d070516060e01020903010605040b0609061806070311150c0301030206090f0405070521010b121801020406080a0f06030503190509100f080c0c1902010c0510020301 77
    0xc03480808404030122030082c86008034078080e10940043c0200c441c030340e88080c91036005690340010356a0451061081da9000b042c40d111604d802e1281800500007228108503002d203031800300d442070144204892044402041459000d41001082d83c104800100b001d0355804861401910175405c0d12084550351141d419981c03030924801e082c4038000c0e0221100c0c10306681c03842e4200309041c0c2c00000e043c1d4004e0164141150390740c495019280c05502c0c1030300c0d1541c0b12803400c40c0c042c440050b404290300040e142c0c08010400c0621007000c560081e040f813a07144101d41d0f242c843c0300300904010341050720692710000d400549994004022801640c02c0b680510044241c5980c0c2d1080c0c0300b00c0c6c040070f401030b001008002d03030400e00d8030100d40b11910203040c01410700c05030100207018402018002004201894045c42d041c503030020000347c0c0104c82c0406541411b41050f911682d402c01c14206841c205d54400200c400c4d0782c01400e11011136540130b011100350380400701d80080039400a201c0c80003e07100d1240 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 173799757 1250 173798507 173798519
    0x207021c08210c07060c020c130203090c0a0e07032706050712020a1d01020c180103060e06070518010e040903030606120209060d050a091202010504120c02010e09100914040c 76
    0xb030481c015054503c40d1810102552600001460000400b00c15442094042c89041c1c0b0740700c0d043d104118a50000680300d182c090300c200d00740390100300c0161054000b80700a009200107250455040b2000e4a80094805035520028943c507070320081140c3d07180b510b29100c40400155030003480c800c066594600050340e92510700c0c0e078186c0c025130b40c642000c120454500560340c0e0341c11030341d1880c800c01441120101010000445c41c40622a00095494400180144140482c1c1c0c05295003511903103000301341c2407402e050002c1c014000c50811000c1c844003244000d130143e11030354082092042c01001000044414600607000341450f104450104043e4500500140c20510039201c42e41409010103160109406001000384001040811100d03079944000303000c41e606001c0d00410312036580000855092a06040210a18401002041010f00d02190b401030764084c003100b56400080d2555000c82d221541c0c14440c6411903003001544ca403402000481d80d8880d0890300b4015401002d03081991600c840d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 173801007 1250 173799757 173799817
    0x30903040b0712021c0f0c03031d0304140603060604090e0703150c021209010207090e01061208040e0f0112020105031810091403040e01060f14120105090a05070807030207021c08 78
    0x40300380004201c1d0006118078460040001f00922440303850005584080c1043d00b492004000c20f40b040590301c0450288444548114800c02140c01180c0c19070841c036004001881521a500801e003690f903c2e0103170002c08400411800d40a960301c414003080701241e1070841d800815004620f100148901616010000342603012500d5102060b80500032044c240036510020305500b01c40e80070250742c3c071031000a003504203800d841030051040c1c05940e030300c515000745110700c030300080d00700520349002500401407a1501e101e100511a420700f002e9460f540c40c0e03000c2c05100801d140090090f0b0240041c12155908168800049148107000500c5a8140c00c14555a80c0c0030f507014001d003d0030071200601810f402010000710b4481e003840c14084800710002c0c890403907000f6a41036030b80040c1031001880a8079020f0340d41603010720030801c1001346250050000340070b0071002c0c140d2400e043d80044c0c40f42c03d41d251400d9000e4110a0500d10603400300746450480d0b201d50084d50120100121310182a030810409 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 173802257 1250 173801007 173801053
    0x50f220b070f0908070306050108061005131e0504061e180201031e0221090a1a100b04080a050f070e1512060721060812030903040b071202 61
    0x51103244140e80c904805a8055141640300d00500084500c00560341204120340005140304010108495140800f094035118014000740740802202c0401c0c0b1054039007450f0034602d40b140180c0807d014590b072101410869504640760a024141020002440746581140341240032403276117180210300c640e215a0484e8100d140400c0c0002421640300d001d50320903009030420070064202030003007000c0002108120790141d091080022104800704801440c0444280c2e84a2984006880014042e982d17540b032144441c0340e68024203401070040380c40c000841071510054a46001550341e00c0340c0b203040b0352703580300c0d203c00f011078240c49075111404d0680404207410701250b80008112003240c4400c2000107110404409850b04040c2c000e070043e0740c09004001c0f042c0121016140c140b070201c3d0b07001c2c03490000c681030032420915500742001006458030001d50b038031032030300214112a1291921803030f4030305602c903561084040001c0498001c0a1002018459107002e81603003c4410310442d41c8141641c02c03000c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 173803507 1250 173802257 173802263
    0xf0403140a1806050711210a0b0703060614220b04091a0604030f03050703030b040f0e12030c0901081801020406080106110d050d0216050f150c04080c0112020706050f22 74
    0x500300c52010745083c800c01107009580418007441c11fa500030105189080c00b507160546e40f03200f400041c02a80c83d0544500d03006044207180500882c5040d00803440300c1d02c9442a00c4619158180c02c0400d00242035081c500a400d602004507940c1c1e9450702143c001e40f1507407080c92a40d400c0d41048402903d4185d00f11000c072940510504502c1c141c40e00d040d215600021826024180c6070303e0740f8540c50380c0d98401d04003c40715250300080c8080503403556501d000540000d0702c0d02d81600b0002d024a01740280b0a9a5080800b440d01c00e101c1d50701c01d04155940100d88020501a60004c1804a84282c014866606035642d503a01d402c1c11180c90760350103036282d00310301c5800302007201008240c03c0b1030800c0c0c00030b10b5032506514640340305441c203a6440d45420001c5009000c190003107241541031001c001d0480f41c1240f551aa56030800342407000641d1540e0a91280c58140010503003034142c00540f41d01550312650300a001007009242c285405028403404450b40305105514814401f0b03096039074203880c0300e2550 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 173804757 1250 173803507 173803523
    0x901020717013216020303060411070204020d05071806080402060901030e070f090e07150c0f0b0c0403060c050c07030b181f0501051203030f0403140a18060507 70
    0x2280c05450001c00000380d8100819540301d5030358800500c440242d020481207184048424440349010403c1200f2025000d00352022600a81c000416800002d0b660014800c950010b51003000d105609068411001c0080d001030010900350000e40702c40c0d0000c0d2007100103449418052607850381d4000004c4160290300c021130b00180104002d0b04000303002d00074001301810005101d81c07420526501e0274001d03a01c080168404c0309030611a420403405162009160b410052002604084401d0007034808c0440c10402c01c911060540184034607070105225803a001032189407581000a12000260701a0009840f45401c040c40c0b0358075644200c3c1200d05100140018100490131980d074a80302d14001f403c0301103c80c912000c010318180060200210101c100b0090302040320442c8540019944141d1100e48680e4022111030510000030048075400490303c0c0480b66680d41724a0103031a1090301d0350300b40c0e0070b11501090000c2001d8005904002c0ea09400c04540300196585030121a14813541800070312400f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 173806007 1250 173804757 173804759
    0x806030601061403060406120606030203010614031005090307080304060c0905013b06040803040f0b0f0f0703050409050c0307020f010506012a061404060b0604061b0c030b0c04080f0309010207 84
    0x903c400043d5421a5006001180482e5182e044102100400d6000d4884540da10f0301081145800d1107081c000b4818108007801900354840003a480d00e0301c0e160320b80703015510341001981592007072007268400b07603110760029120300782800c244004116441e0150040f0305040720205941d809043d041c0c4445501c040c500c1105441d5205428454071100c5140e5080d80014403c090603503120b802070009008041e00864803a8a813025074844518142e000451040c410003008402c41d09480031682d580840355007041d651005807804076040e02c20356201c180780714500030501440603050381c010b50140300280c1c2205c0e4880305810045080300c0050311001e011074145200001030640c0700e0184011b408030700345000e054245c40cae142d03041581e00309c5004207800c500540800c8100881403190850707c5400390b8000c0d05160602501802e420000500031080340b60308200c09003040001171641c405598001c1b000448c5040110a492541d08a03010701000f600811036081062840003041c1c541d00c1005038014423a003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 173807257 1250 173806007 173806037
    0x1061407031b150e010b0f030c060f0d09030807020c100912060e0607081b091305040203030d1a03010605040b09131506060203070b0c03040309030b0601120e07030201080603060106 79
    0x4003025508810b181d40e8039400c080040b44194450001c44141c012000c0b9031680006515421284080074240c4100205605412103460006100e4040c490075550a640c544a41d0b00a5915018401000c615a07040070307000020160301079120740c041e410603021160007250813002c01c0700400340582410300107040120b080041a103c504a120441d0092000090f50100e0484090500c1c004480d0315011a42d91024004403201021901c84290681e00700507080002003c0091201154058a26085500c0704041000c2d590140b003151401e0802010400c10406115010f01344001440800c034131035441c01e04002480d040a0140380e2071080001c18a80d0141d4130f500c0e510400714948003043c0c6101e40f00312400d0400280a1140002805142d0020354507228a440d0601440c0740050400c42c0624080c818070000070703000a000001d496201c00b208200390350b5500100d8485560303803d2100d01074101000c1c2c050194012402400343c9000b1b985846280d540d040c01d141c1d980d00300313104000004024820f200c1603 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 173808507 1250 173807257 173807267
    0xd0b0402090c090406030507060e0306040308070f091d0a060902120a05091e06060a0b04120609020105130b07110406060c06150302100513080105060f060309070f0b0a080106140703 79
    0x441240c480c2e890342049083c2020a00b1039620b80c000b1905a805180188403054010300c49070039000e4110000c150720310342590000d11844000e003c010510880301d0300802d07c5030203031049102410014001c40401405042c51307011110b0151405580c952800401252080c8203000f2030380c090846128444180c1c032044021001000000d000e0740c150301034200040091040e0707003c980c0c0c0780032407a0010140781c10490b040000300320040e8403071a02d0720402c210801c1441c205003000031080e5000b240010300d210703243c00140c0701c5104880d211410400404e802080008222020f008030500940310850703420b01d840140821103400c1c0c0100c07000b00341107800c0c0e1000510070350071a641c0544400d0040903403560325404289000301a09600300442c00201e44100c41e0340c58260114020300100300280310900340f90700810a1700700618003440c02940000b000560025003080340e0302c001c003418000f100c02c05584404201c000e4006880709800a4588000003900718490041032001c150b40300000340c542100b503a41694 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 173809757 1250 173808507 173808511
    0xa0f0317070203060103080307030b061603050d090b0711011107050c12030d0f0b19032303040b0d1e0203010311090a0e0a03080907081912140d0b09060d0b040209 71
    0x410642040700c0320050300e05001407030080d0f00c81c0003001c3d140d0500f040040c0c01c0d90800404180504000d02c507117108160101150505260142400d80c2c2e43c3e0168401c04000c1c011701d550152609112109002c06154000481130b400e152060003000300c0c800b80c03204501c25108409001c1e10b10790010450441c2c600c0c120310454039640d804022039142070380c1903011209803402905000c014231380e07a10a14516003002801c1c1c41c0820462146242c10904554400d2407411500c1c000c01c52800b554255500200000c004880192800d241c1441e2140c00e5030354403d014150014125040b0380e05803c0005041c2824000d50b810b80360300c441941d100303142c42004e0044e400c000812052041d82c890560100d03450050003411290b0780281c1d00c0c110f40e850003a031040d10302020750388842c40f2a4009260503502d14414140c4d08090359001441410b4841601c00071180902030940c506106600000c80c8d0100c0c1003190305c11a40745000741c4200406d50b403650204500410032200140c1007164480c001801850002c0c6507036 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 173811007 1250 173809757 173809793
    0x20f0313090b1f020102040906171203060103150e090f03030c040504110904050a0f050108030a021b01180603090302070f051f23030906011a040e1504020a020c010e0a0f03 75
    0x4410181c04221141140d540f8040001d030758001020310001c00c082c003400000d00249084034912090601c0340a943d0031044105d00781407040031011640903032007500001691129184140314150711030020b03410149050301c1602c8580f080000385055130744040162849400c0d00520f5078201803801c02480040d213003400749021282030401142d47c0315074441c0305450003418083c0700080e28150240d040000c40c0d006804c18255544284444590075038001502900400014180d0010300b191600603110402007008020545040310004a00c165041c0c0c02202c400703020f07608658070541c0d52101c0c1068030316107004e507a40040390144086061002c25000e80d82c2441546000d082c040342034001d460795140403101404400400005000c42100d041210381d001d4281441024003903402a5190007492289105203101145248001502100b100c032031600c10b08400341065507598101e60b002500c0d0321454440c40d011131800d01c01a0450b0030310011200503100c0e20000540b0325421502d48441c8100c81c45c800f8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 173812257 1250 173811007 173811019
    0x60f050307090312030c090509090307200607032604080301090509100c0c030e03011109100c021e01030c082404110d09050d14030106210c080106020f0313090b 70
    0xd07001c0f21130740c2c504014540d0700040c40c902411000304204c43c69071001d4072480030a0244200c055010084610095100b500d81105c20000386500302400000740c1c0c000e0f4000408915a4107041d0050131003424901921804c04588010340282c044101d0143e4001d4401481840180142c9040d0360040790440290002c4403000c030b40180118040d5070b8291803400000b400545450109500804050614a001c0303000348661810021a070301d1500461090710700c41c503a104200d05460313001c1e41d1032243e010380103400e001071407580200c05040390088220150000c0c0c60144a030010600c01d0100c81d00580342d090090403548035076500d204191030100c01c1075a000d9559102425024808001031034003400c0304501040c2d0744101d0403d00d040c42042c031091001d0284081d5020381c81c101d50b804490560300039091000c444081400e00c035006443c1504450a802d01c0d0030350080443c0c2e00b0421040c102c43d12a8226406604c04070032045d101e00416001c0c1c08140500f40081c0301050350784c2c112500b1b10b1005090 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 173813507 1250 173812257 173812259
    0xc140a2d05070f1701050c0702010c0f0c12151e050a1508151f03120507080304050708060106022a0303090a14040c09050105030f10080307030504090c0801060f05030709 74
    0x40da802c000c0c40303901a40c10000700c084200a0402400d10f0080503d510034020030251814001c240c0d0103208090300241001100d12a0b0030400504070354024140350051180050182c803940500c020b585d124405580c00d2070314890155121480340200c400300c3d0072400d002801602c0d6010048054074000c0c0000c0c0846844510a00080542c1d05010004100786802040e202d1109c0d44001d107074034000743c03010b9240380440c01c0c41d0b50001c040c05001c0017141c2e40000c50520910005030102c815000d108402040e050000041c8020310500080303840a585990701515101c1e66603031001da91320f04800035441c242c82d150b0015100d1410281190360500071002d4240c0746890044000200310b191035411001820000c082c146503981401d200d87e454140560070301c007541d1410540040d009000080c481d0302c60202c00c000158110109481c0203008126003002c42e0b868003032501d400f9210380c2040c0074aa43c1742d41340c0b40c8250700d0103102c2d510300d40c1210301c5502c80c0c0c41c0070308110204441e06c1d400100507006002007810 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 173814757 1250 173813507 173813513
    0x603090a02150d140402090702070e040311070b0309010b102a020d02180907050102030f0f030901061505040602061b04061d0303032d01151101090507060c140a2d 71
    0x403501080c07044c618949141c50140b041003100c21b8050030940840d80418014001052185d440c10f0304141c05041410846040009071860003145400c41d1182e1200802031210090054100c03c411002c12030300c40368000a4000100d90104c08030080d804500003080e003044400e00f4444d28141c0d5580060042403447c450f03a00071540001085074200740313214102d000c0003040c04041c060384020381000d101031454503001c0d81440031140180364141c014a0030000126900707131400d41c8041c0003068401000c0440d0100400c6c00b40103508288224400b43c0120350010740c2e20820300c0052034011148030401c0e820141001011103204400074501c4a183e10b00042d9284140e8040020714481e07686420703105c1c02400d52904200c3d0078a4440400707031408000303200600c0804140d022207030504030a4900781110302609005075001d008a40005845401110303404141075a000c22180315040c018680382c080b47c00400261560741d980584090110300c1e100d100d01c3e50400b074039482441348c1c212000d0344c0e00000d01c180d1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 173816007 1250 173814757 173814761
    0x606090409020f0d0c0e0a02040303051c0e0d02030a020d0504051c0804031506050f010203120601030c0c06091a010807030519030903080c010506010e03010e0c0d06060e01060f09050603090a02150d 86
    0x510640710170601c1c003001c01500c181410031580c00410780320b043d8101407030b40d40d000d050760142c01d8043d2040c41004c401043c90250030b038020321000540340708540d1a140b681c80c001c1c0d22503000400080040c0112406103103d036008104850807220050101c0014040440500c03080010301c02d0304881420081000001140200307d00504400703440d0300011f0b02a10705400c00c00341c029680003050540d007040c0440034150a0b030000240e4815002e003000701e400c00403120211001c201041c001400395250025000512104408130590740903d4141003040f80d0700c43d00301c142c0ea21150700c030040a03540001d0b135409062900c18281c034090b0b8424200002a9902e0b07035a000400d4000c80c070b4445060b07545004102c02913900c001140300101d025002042500740c031000d260b8856041c07140c0703d402003881c222542c04102855002400920b0300d01030500c481d58541d60010201d182103409940040d01c03060000c14140b502c1422240140901401800c08080c00e070300340b2806e6408080100d0310101d09000c00d80090400d8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 173817257 1250 173816007 173816029
    0x3040302010b100201020a0e0a180b040f0903020c090705030f07110a1203050a050609010b040504201201150201060b04050f010c050123130201051b0a02040c050c150606090409020f 79
    0x2c4d000503894907030307840300180991940d80f4040e11031b40401d041000b10310b22070a2400c407141d00c8000c2c0865542c035113101042c050b00600394510582d52406903154181903000c1108114620100d0356002c09841d039034421600da020603506503502da0ba122002c1150701d40212490075580100d101a2040c03d4907a0711100303042c401d80f101200100ba01d60041102e02d83c520311071a58468000c07103a01c00f0a504001e0281ca260140b0700442e800341e0f9840f2207010f5106c000e00f002146210a42c4003580da034a503040641d0302d4800f002e10508204084801c140b41845006004e61815200d000c2e02190600c2c0c640010400b44c000d000100c00c7c180641e030000e0102051080c00b031401c581c038961020383c420094480030514100030062030860840040d650250050380c4c8007048070524441e454520442c0f05152a0080c10440005d000a6100b441e21f0702d071002054029000d050044804019201f0300c100c0035000c01c17103480045500303580c0044200300c0c072401460a80d020798515070003c0c18002d01100c80da00410221741d55 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 173818507 1250 173817257 173817289
    0xc070e0a020d0e1204150203040e04050c12010504080a1b05120a1d0306150a08030705010b0f010806091810020d06051c0c3003030e190b0c03040302010b 67
    0x1d080c00601c8860b00407109030101810003024680481203490b4034074000c6009030021b03081c110b01c92400c65842003094074060401c1000085403410186000c0f5501c600b00d0b50040d0043c0d101084075402400107106143c81290042c03489494010018002c4441d02e10703070503210b0300d0512461501d101150b0308110740415004e040c03624a5886c0070190307000d000012020b0443d2148003640c040f0ba20720b6200469840e800c501000241080025000700141c210901c80d00a84039510000c100d03441070240c1504a07110034802960469122949800115036070303181100c5864100c2d80c9403000c503151203400d0140c420307007202441c1070703503d00c5801840c00803d99010706130f80d81724180c848506000382d00e491280c151981403e418400c00e40b40c4140e071041595000381c030890011144280b2800c261080031181460340700d641c21303000e01000754140750280040107140c1c4c103042c043c450031300305050710300000c40e81d0000c058001010354a41d560b00b03102c80d202075000500813011075485940d04000b603110110809080c1107 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 173819757 1250 173818507 173818511
    0x3040506090601050f0a0b09010306031a070314040f14010f090b1005030105071205060a0302060403050d0e0919020c01020c010c050d0c1b0201030207020d05160f0e0c0a050c070e0a 79
    0xc010650034500b00060700054800d0300b00c0d899024440c1d65002c6c10f00110303510514182c0c1c035040010300580052500345d1015101d81080346603035a030f9070703c0c80440c2ca12880054a04028401400e07240c135981c0e0000300c80051400d003c0302005804200f5400300a400126000300100c1e020224101040955030901000c4415804030b07403d1110490f0311100c0320001c0c100070340c000c00c4030b072618080007070260441ea01c0ca00c25841e9a14003186454075802c85a4014503005041d0660f20390f540d161480c0e81d00c0030110000c0008011000d81400341c940a03800c9805292080059521010848005d10007035014088501c490740d420810012800740a0050f10441015626091344560180d000001a9600d8500b100100080703c0803070308500c0b030300e860001c0d19a0b8081c86c0050321045184041041a080003a002d005880362805403400104501c55030803d48009140380000c440c0e43e40900742c0c07542c0040d101e0a01640042c8600e600072441a009403030340c000c1020844090b55521901408208416154140115 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 173821007 1250 173819757 173819761
    0x40305060112050a030813020a180b0d02060a031d070806010303020d0201050421020f1002301503030d05010308030601030605030d090302040c03200c06060d08070f0303060b03040506 80
    0x104080c8012401046a090740c02002d1600b951101e0702c500103040c1c0201842685408104d440c40108442003d1503405020b00603241d1301c03940096a003180b80c0c0803443e0741c03078206450000b8500b8500c0441545660180049041c0000f0010a50250900c0303a00c6211040881a031300d0500d040030480000281000c20203003070154114200282002480c03c560000c1d68109801d0000003511140320310745a2b81e030042c540400a11081c801c0303051202c400140c801034420b201407038118a14982c01403444c050400c00b812100b10000480061905448190110200b034110020740d6007a080540000006401800d40f1f02d01078000e5450800c0300c03400e0304140d03081040403003001419601886940e020b86011002403865402551000f0a0300c0e0303090200034002c9071542e9403030309003e00a07008040700f420011070846400306252030003480d680103058a900c881c4900310102d002402d200c00038101054001c10000d14000913501c6130b1148800c2e145085040590361080058080040b9025500807882240680114 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 173822257 1250 173821007 173821013
    0x320703030c050412020d02011106070f0e1002152e09060b03010e16020c040e0a02040f33150806030c060c1911150705190f080d1d01020403 61
    0x607040800014103025041000340008031030180c031a42220350440f000c0d0310605240c80101e5000c180076600072494494801845021030304000c01d18180c200a0b6618251490b04400300505a00400040000340e0084900250302941324947c0b5544140c2c0e5444040d03400c0d00a04504c15038041c00a2490218842c10400f400301c0ca40c0740c01144000c0000000050965042100081d04d4490240ca50761500c4d02038109585103e00a01810300040d00c000c00400200c4550001c80761202c7c3c0e9884100c0c49a458010b05240c592450310401c1c019611010280c0c2a0460781d00d00780d0111805405140044161a900000c11900503603031500c05101c1542c03120a5401e190050502c2c04000549651088005101040000900080500c10800c1c4042d501000d0000c40c02c2140040360b0407013406411240c4440b4004042020100411506205904407540c101408072400c01052290300e0041c07078001c120020002082600b4081c0c80c0059200c00d0010b02041c0e029216814030442c5400c004581e50049010424 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 173823507 1250 173822257 173822261
    0x611060a090201080a02090f15220f030807050f011d010e07050906060711100503160305041104111b070611030906090904080c010203040f1e1232070303 67
    0xc003060310401d00508859034000b03000c00c04000c150400096012a000c01c003507a03500d618184c020300203060f00300809910044401c0590100c1000b1500c0c2411a144140c40b06851291104841500d2252000c2c81e085545c0c0c11043e44c00007805490340e100d035002c0d6100d400c0d82071040c07041c801d140c54441d0000c00900e04c0444d0035184218050202d40d00710000400c1241c460044243d4030240c21100c05990346503520f4990000d044404a10750810900400140001d410500035030140d0390201c01710200700303000d403012000c2d207000300e0740107000005180c050105400d1035000301d10101c0886408030b0a003c8690601c8191081005001103a0307400030400b0092540c0003c01300009084010141d49444103030340202c0d0451103443c04050049000c038000606000c1006c055820f251032140080d5600d0516040100c2004145842a203c418098281803d00320300000c214018a1f44150b030114070820030402614500394510040304203001c400c10381d00d100d0705800e1084c4c2910b01000c1d01039880744102d04005003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 173824757 1250 173823507 173823511
    0x1030b06041a0f15030a2003010303210b0d1b140f0f0102010b0d080702040b01080f04030c051e031801030b0a18090b15030f010c091707080304061106 66
    0x80541d1400b10740502c40c0355400180001010261180c000c0d03d40e950f40403d106003005880c2810020001c4240000da20140d0011000c0e4090803210074011a256580c07007000c2e00c002c2c40018003083d10510443e05035800d40e4440085a00c8040002800d10100030200d0002e1502d402e0851755081c1039855842c0c01c5100c2180c90b005010300d1540032400c0540355010600112410318840e01c01d48603003200034107581c401d4000d071004800c040c08601d0f0121062411442c1e5400000d0101d202e2401c015a04007e075100e40c4075684502101c413035032960707500c45460960710084400d401b52220700548000d894078000d00009207080d141030310015a42c6040482d0303400340074010900c000e0704050a01261415960b2006940d00075600702400c0e008107541c3c80d0b1090001020309980081c0300034602010840d50080c5103881d074003241810303400c0c1c40b9810700b941d603040e00f250300d51800f413000310b02d803d40144007091064072030240c5030458134101e401c1c0307607144da074840d00c1d54009600000004003842050520b044080c88010303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 173826007 1250 173824757 173824759
    0x140414090702031e09030f0708030a0f0e06030114030f030a020d030f060305030304151806021c0621020a030b090c01021e061902091305060117040c03030c02190e01030b06 75
    0x18240280c04065100001e410000c04d0034091012039418200d50b0b080c0035540710004050111081c0c943d41c1e0f09915201c0e003207060381001061418141c04209409034090302e680500041880b441c50f820b2017000c440c0b10307209400c9581c051003203031840320220604200900e4071160710b40040c21a8040190001e0a68081c6c007007156031700c0d0410604200180300001038135002a0f1103001c0d1407801d4108140d1070020b28045200401140e000c402078000d020030341d8010701440044c680e00000182900b4604000e80321140320310302c1d54440b078500402a0440740c40c281445140300805881c6144e50301d480c1c05180380f1041d036070142d150700003c402488941c0c04121240394400d0034884400500d0060b4041501d5603001402181c515100641e00803603082c0540c11990003d400030039180c04078180b080024018030080b06c0c91408a4400c07107049440314038081845203e564400c8145212609640d0220b80c00051010120781065074911418140d8001c0190b01026008032003220005601d1401c0071041654003810007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 173827257 1250 173826007 173826013
    0x308010513090807031103070506011d2a0901020111030a1506110606040911030a030f030606140f0703020a0c03060903030b0d02030322080d030f0b04060605031303140414090702 78
    0x940004401e442030341c0c102601800c00e0303400c3c010070300210760035440f0341200109503010f1040003041189001450341403800c1c200d40300155941e5028140100008210482080a50b0780c0b40d000038032441e180c0042c4ed030990180f0001c1164400107115450b1600159004400c0e40d45a4200340c40c80104000140d00801c03040ca44240750600ca40380d115207904d40a0100d40c0102e4990081000f840503541050050590180440d19221400e0400900b0703107048143e800d00081c1000b200003030307241c0b2500d00a0344c010b6590812034582007848192000b980c4c000740c400c4096000d04007505020801403400c11000358028080400d2001c82803600804a0310303c07081440c4140650607450002d81c034000f00360355868051081144413071001030310100c41c03d001e0340d0201e02c02d840307040c4424800c6607254108040e802140807080c840c42d940c010810042d5a0f1034060140007032010300c001883c2c00a110b00391444680281040f110040183c00d03d8111a8815000b0102c2c010900c1500041418840451544442d182c806 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 173828507 1250 173827257 173827271
    0x21e06060108040b040602130608040302070f060f030504170a022b0c150b0405090d02060606030103020d080d0609021612180b0a020c1905090708011401080c0d05040308010513 77
    0x1a06607103020300042d20504c101800601000190343c1104c0752110080815003880760b44690082580074210350440042c024624005000c080d160300f01002c1d00d94a40312000340403041328084000b0b04005005544802c04580c2081c15003d00200820705000b940c1d014103c2d81c44d0207020180a001c0e242c80d01c49425003600d0f02d242242e40d1090785003211990000c100b42404600000f24000b4250349881903a1161a2405210349600c0000d44121320107525020384a041d5a81c1f4104000c80c0001d10029411100108490000941400003000c18050f599000150030781c03904c40e0481242c01407038000c8075403610520141d0510110b0a480044840189040c203031001c60202c0c20011055607110f00d41505070b0218a02c807905000b84074100e046200a841c4d2006504c40c68504d00a519107445001d01070000fa1010850051249040078181c0f00c9842d81c480b0081802001142c9010009240400d050300c03d004500c8004480e004030342c0124044d170341d4149194105410040c0d45404000c54106a5181c150 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 173829757 1250 173828507 173828509
    0xf03051c02030412080d051017010204080d180b040e01090b030a050705010f020705060c161a0a0e0609040203070206010f0f030f120e062115010c170c0d021e0606 71
    0x2c1124152452500008420b066a28000001d0300480350070303001e05030501d1b04000c0c1200318116080c00300ca1201004229038010035608600700e00c600d008184d1507400070400540d2040c003c411090880f200f036a40082c0a5585099029840d0001d40024004140307280040000806d14083c03850312031b5003140a02286803569590603074680441c85007906104034480f2080400c0e00900c4241c006000103008203075107500022540d89c80301180c80703109140d00f9241c000802d00703c921080400307507421514400e514100580c08190b408850130005d4642c8102d0410211006444d5400034501600e01c54000f005a94180014241c484c40749410603a2001083c0c403042000c06c404011252085400c08112400c500d1070341c0084850b50708010707505030840000215044258030b51b02c554402e004411754160901e840303210300040c030768039890b01170790004000c100c504000c240c4804038444011a000c00c801d03d4007a8801a150030a118110503502580005800003061340030305080410a141a5014101c2841c00c08 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 173831007 1250 173829757 173829763
    0x40203242809050a020a091806020d110f190f02030d020c28050c04020f0901050306180a150801020703050a1b0c03240b01050306060d060f0f03051c02 66
    0x6040840307064240032240c0610290090044000351040024480b4122a090050f901c2410580c03c0740181e82e20100007558408610030b03108040a4804007101c801020384508021350840e02c3c1110b111903136190109103404461008010364501c01c440292940c0342d00f801003400b03143e07526150042c4100c41d44101451075002c81200d0400080032001621004500d40341807900d0960f16490544011700f44c048891258004400105984110100c0e0786241c0c1c031a05200990180c00c4001c1ca180b0000c0c450402198040c0e40651303440380b00500342c0b8010550303030341c0103121010b010b60f0194801780d0746400988140341200034075005042c80800a52a00d0055580180326101e0104a1000c001c074005000c00341c80a40c0c020100280e40009c448407506840741801c009000421108881c05c0c1c801709454240f145250041d2081640140c5400e411a61030a0a02c1101d500160302040e41507a43c10f4041110386160490002820042070403078622415031510034604012002081e20030141c0c2002070104540c00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 173832257 1250 173831007 173831011
    0x6010611010506011419020a1e0521090d02030c090a020d060e19150b0705030310060e010c06021b0102040306060512061005010f091d190e060103111f020604020324 72
    0x340804110b0142e8601089092110b034000c009c0110039403a141d04100858000071034003e038061403e40b490b0040c800b490fa0b017220700c1041f100e000c80000b482011120324040c1078103100d541c0040c040c2d03a054281580003950314581128032045496011840300021101d41c85a08003409903c40c100300b06003002c0305003550940340c3c0700400c081c854964800392500c203aa1000c2000400710340d505a0384641403450a9601ca4100720707001c54002c000b503d00010241d20452015002c40b4040c0c4640001d03040d56200d00c1c2c065803001c0d08070303000f03200424820300b8296000d10050000714050078000a10394140020402104008040030902e80c3c0000180023428082540f0041103d00c24201021440b03450036017540d00d0031003648040c00c0c00301c640303480750040034104205030321902c2407514807280d400200744408100c5049402038041a40f200c0010300004905444a10240710014101c49100504403422541200013540d05001a0004018001142010468171a40d140b40442c1c0007260305148020403905000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 173833507 1250 173832257 173832277
    0x21f02090f09070e0904060c0e090c030a0e010e0d0507060c0e03030a050313021206190e0c060f04050307180608010606121a09130515010e04150e060106110105060114 73
    0x32002c1100513000302414500740e20b0140c002d808a203058104280140380c100c1154002c01d6041c4402e0415107801042030340708542c07150f0107a095440395440d0800410510b070400806659070800e0454100301044603030080b0030326984056550b102840e001d13003503e007071b0700421041c40345102400c00142c1e808001d54080350110b1a1058030b030707990f0141a1820030085072000e074102540f800e14125000021818030320540e042103d0911000034004850203d540c0000c0b4110316402400e0102250316041d0001d0040500c150701140c00c3c25200c90000782003920070b40c00f404040541c43c009045180315401680001c01e451002040340900e8410060000d40381000d00c409400e695080844540402e581c800a00e0f00c0c01400808040c6040c1840c42c0d5072486c3c0c0042950385c0d03c201422600b002d50350301b082505840009039404c0b41a210307652403011031000c0a10300c9003459110301c01c180b4009010007405000304125680e40c81c1840112888600b114405003255040005400d4040404a608011140c501130 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 173834757 1250 173833507 173833519
    0x30207061b020d14190506011406040306060f050306070c1101050a0c05072606041e08070b090303100608060a141507080d0c09060801050d060f020a021f02090f 70
    0x80e5498200c07111a0100002540202e20342841401d0040304c1085030181400030f8101c400b41111403480a015016500006000d0b0340114014030500090f9141d040c0d00d1400584070034102a1260355140030307900984c005400d01d074084081004545010030034990001c1090030700b03003051010b44d1281d824a16200d0581410b0060011300094000e12440d00525165001030a881e8559111101100301c210201d842d007004005e0501c912080c0040841c0160180c0e600107146000180c0c0ca00940069440141041d281d1610902c4100d02040c807110500d403054140c00043c0d6a2441c05041086211005400000c00c021850040001710346030b004040050381e4a50081701d90814803100050901340e1800102c841030341c80407480a08004810000d02050b0034900418132084442c42c8044560b10210f102e03500c001b8590b08010001420100c0f02e204a05015250224085002d8915203003030f80d10400045005034802c0044070710f40c840c11a008400c016442c901540b03001103410029600550041c51244518 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 173836007 1250 173834757 173834777
    0x8070807121e0e0f03030c07080d05040e040f0611130e0106050c1009140703060f050108010507020d030203060103140103081902030405031b060d0c0815060703050304062c0f0f010903020706 83
    0x40d84000c130814280d18020101e0359036111400006440c0c0809209111091107030341c9034040d045004a05a80582e0403030741d4500640c3e40c50391580c1d0094640d100c1c00340c814a643d01001e81c07480850710b00a1683d85200c10074259441d241c8444240003c0b0140d1081d010400c0078003204080400214400a80600c0c4080c00b0541d1842d6081250715100070f0a2010b003180302d5039100100300565508800c1d00154140c1c0c0400c2142c0c1d80c0c90312542a00c4048800c00b00507001551007e8102e8081c1e400307141c001e10185000036544820a01c02540c5010030380058910041c00324070118106840d40c80120f00d001070348040c1d1704040c60000800d40c0c914242c00780707080d121020306e4a040c0c191036107415261006051101841804c140620161403000f00345c0e18050000415801500181080300403140c003198599591861556140c480b800100307001190034003000c8080480e12a0741a01d4150114401c20b49030150045240e9520321528058419500c020030703905040054003c08d8001ca5031078215031a80c00d00c10000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 173837257 1250 173836007 173836009
    0xb060f030c04020a0f0e030a1a1905010b0306030c0a030314160602040e01080706030207021e0f0a090f0c0305090a02150c06070f030e0610090b01020102040308070807121e0e 76
    0x503071070540c5103070054404130312909041d82c410011440e01209450300d00b62540c00c001410f840b208286000740103a0664100c038050030710703401160f07030f40304e1141019560802001545041074034003ea212842d00390000c000d202c9145400d01030130020800c1180c0100c1490b1940c0d9001d0407030070720401c1c4070400d004080781c03518000d01418110000203034004030855031962900c0a0301c242031008e004400c464850200c002c211940203208503408542c0042c940038120204242a95007004150107140e040301411444003030700d07103842075100054000a40085100d80543c846c49040701c03c40200d01c01054140400d0001c12040825204036194042d101c2450790118404080300600c1202c00c400c07498401c0104100d44507a0000000d0501d030b806540600c03080c100f0011803680c0d04400e5030f0701c100610040303038108000007841c0e1146c4002c1d8410b000240c01c00350b03642c40d119290303049170a090300c0c505000140501000303050329858560810b6400d1202c0c0400300c40e16030f151280c03082d9200c5028000700e0f0303070361a20f2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 173838507 1250 173837257 173837263
    0x9200a050705030417070b0406231603020a02130b010c020f060702090405030304020915030c04200a0c0b0f011206051b03010305010906060501080105031f0b060c03030709080105040b060f03 83
    0x80d01c0d0402d0480f03a55513603034403501c040042c041c168900c80d40603415010400c1040e1008860490300c20395546400b1000c00b40b642094024407440b41c0c00380d000100044203101101501c4160218060b07000b814041009006129402407000341410400380342c0804502d5680c4c00c400161019601540c00c400c000c5a1800412482d20036010081e602846207070400080200000045124500c00c1e98401c1c403d46801c014103164860030540660705400a00b80d2401608080d03006030440f10f0030222849020f1000104101246e10a041000006603403452840034045064000342c0c001c403031059910103641c9010800544440081001840e8603201d501042c06038940164503148185001c010703e6032960b50785400340c005c18046404481080c207000c0000b980e90700070680b060403504091b002c0d004034032030b400e0350302c1240e00c020300d0700740c800c6a40e1001b0f09295100c020140c001601150300030760b9203003882640544208e01c26030042d41268140f07820440000d001204080d00802d0944d0b2420300400301c0b00c000b0741 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 173839757 1250 173838507 173838517
    0x2040b0418020708070c0303020d080f0c03070306030c18141303050304140706080a0c0f02100c1101021b0601090c1b022806030c180e1f06030204030c09200a05 70
    0x10244c8404134a0b142880f5441c40c41c81e00b2240b0a8088403111700305d0200680d01a80110b42c5070300044030400020f10010509402154001614580043c3c1f69172a691103c440002076049610002910400710030508898800d6800c050000361030003034149001500703110000f5034100c0c003c1c1000b00100111342049030310316050f20f6400c890000c0d00d4901d82c41e014002c0c2510720841d80750300910700341202c2800c254010305280100d0062076001e0441c0c408441c0d440760260018401c0581002213401591140c0d84c001c1c40600640300030301252880207500c0c10481c0c3c1c6800c01c107030080320000c0d2a1030100c0d4065070300f080104182c81c0444540c024540b900d800050450f411ba0b6001c5005014000120004030b258402d11400ba110951802c02c4160719000d0201ca814800d2140100c540f00c11090900138401003d0781140d00c2101c0218804240d1040c5445280921255000780c001c05d402050a0042003007400f030ba4005041a22420400e00c1643c803d4881784485090000a0624000940c45d03012440391040312 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 173841007 1250 173839757 173839763
    0x306010e0d12050327062d04050c0427060f0216030c150e0c091005031c09050f18060406330302190e01090302090f0702070902040b04180207 62
    0x44070000c0c2c40030054040d0348121020042054482454560303500c101440544802c01d02000f0180d135500d6243c010340c4100e04090720403060110190124180c1e40d400342c1d03c0e01c202d124602410081d40000300f8401510300080e94902c030259982c885202c1002d04940c1058000c0d0031007408186498a1491940240f081a0038601200c60f5003c0810516030440790903400507100e0382c0b401c10030955821076082150901d4030345401303540140b000c80c0781c1d070701d04018065084490504d0054220350343e680000d14000784003100f8030802d5840541241c006070803000703000041c9000e40c5c12322442050130000030a038500c0ca000050700a4102d0000c50040c0c1c5643d40508041c11002d01d079890342c658a680300003c0b842c00b8181c074060340c0280c1601c3c03200182c424000d48101183c4a480d594030100e031100700340c403d00c0800e5101810021114000405030307640c2c0c50518041e8415007885d850750f04000340001e06085194012031201401000200544131a04040342d04640340c03a070b00e000c501c44d213083d4040041d104590000d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 173842257 1250 173841007 173841023
    0x3180c031101050a1e18140a09051902030603030c0a0f03020f07030b010603050907051009030b0a090b011215020d0209011e200f030406020114010e06060a0c03051306020726030306010e0d 82
    0x454800c40f13031a01c2c41c03001f103000c460100d121988c03480740005841d0201e400001620854103400e040d6000c0ea0040c607040100102a01d04001541c03440910300f010100080d20380e0140c18165206054040c49502d04644d540c0d006421820b041d42c03900500154184214010555120009582e003503003072007201c0240600520040c0328150f86400100380c0c00b2540010b803420403405c4042a00600d01c1d104000c156540182114041c3c0c2c6011240030302d1101c85041524007030712070201d01040082070f1004040c040c0520300010b8840c540c00000402c100458140d4a1204000304144411141c004410310000c0201c101e49554100c40d440c1c24a0400150807140305d43c030300c0003150102d080e0b5019000101c03260700c25101803031f040c0c3c0c1e41c2507100010641542c071160005810860b001420744540d22440c0302501070b0901e41d15241ca20f90480070144400e50141c4010381004405012510b4007070344c1c1083c00c1c0555650a403824400d50042c50322031002074541414400091000c0713515407290402e00c000e5641112034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 173843507 1250 173842257 173842259
    0xa090e03041a071a01090c050c0a030f0545031203090a290f0c07030e180405010911010e01021015080d091e0810090303180c031101050a1e18 62
    0x9040050704d082c096001000d0810100300d2403284a00306a460700c1c3c0030b550080c02400b81d161015248a9030350fa14000c10030000704510302d540d4148240603880c226601e40342204410721041480d041d00d04410a03256030b560b045044105907a0000342c86241c0b07441c03036604c2c1540ca4a070805c8a03860b2601108009010a070510b00702d2040b468040c154140c1400094065a92030b600e240006013072440032144454030980034002c50380824170411060300c140c10080c00e03001e03400c00340d041601035075407084034100d841781e44443c0c2120810001c0c000b002c1c5860b8080c2042c03441001d1600000c0c0d02e414000c0d00707181c80b0300e940c7c00700d03107200704a40c0c00c02400500f203620581d801c11076003800c020402e9905e0b01038040aa28841d802d01110f07000c0040340b800b00c840700800f4006440500e0140c1c1d02800c2da500c0309030b04050b292130052000340302d9940c1c440c4450388134030045c0c04540d1640c0340c0380c080000c0707412842d414094103001407880030350488000c4c044401d0103981c00e8411070500d075082e00e031041140060f121103550140 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 173844757 1250 173843507 173843543
    0x90c030203091005010b07060510091a0411041214010b060307021b060901090308090103090210020703020406090b1507050a0803040b0106080a1e0f02040812030103020a090e03041a07 80
    0x100650054a0b2201a41d00e90320a02200380c0a58800f88601602c1c9003040200001181c820340c446034110303c07941454004103580b50140740c140e950a0000c0510103201c10300c081d59624080c402c1c41c124041c2224070760b0070946440700b08000b0b4030300c00714094608904902c0c0303c8801d4100794021100b150004014603101c2c240a030009540e50301e10b510000c0074541c180f400d1036071458900196104094140d40d070028403400c60360740a00d2074000f40301d224141500c0e11848001640da995204403034250b241c0c01031500707501c0d500401041d62400c0e030041200c0380c640f410350119070b00d400c0d0b854a408622900c405a90f40d10500c0c0581c508000300750098541c281c040280f004001a00800c0c0f41210100c1d82c0ba80d05d60b40301c0c40d81600031105054010b800f42c61680c5944200701209170025031680020080042c01c196035050030a0030040100816101103500000510461070301540390000b03060042410022410742c40c6c112a540d110718003e09200640c81100700c030000c0c241908944280d40c0c441610b14000c50351760 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 173846007 1250 173844757 173844761
    0x10209090a05010807080304081e010b0a06020f100b0a060c0302030f0415030506042318060405071a04030807061107120206061c020f09060102031306091e0303081f090c03 75
    0x7011300d41d1940909180060000000070550703003542d02840203080c2000203640307418a83c004821440c0c80f155240d012035240c981d5a10b40072401030034a6006000030a110400f424203100d01d01c68182600c519207a03c48007141c88400705c010941d842410070164400c4c19080c140d240d800307020028000c1240c0000e01148040216189844083c2151000d01c0039844d0401040305464a9145c120998400303224600d0417007060780d15598000162401010b083c1c6441c00c8440c1c1001d404031410344256010703140402202c0b191030140080303103003081d111504060a655814490303100700c1300082c046648440e40303d02083c40f880c0403180f005a10002003c0341d5002e22070f0103900c80c04c0480c3d4003885041c5000c0d607c407405008010881c0e4030741d8000c0c8018210410581040550711010380303001d0461009100d04129024034400000c00b800b142c0c0c071940041c40c0345c000c0e400351400711042c400c00085d440500403c0025006000b6940200504005260101740310192480300c1c40309501c0100400c1c14030310034074106034241d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 173847257 1250 173846007 173846009
    0x41206020d0506010309031b030915031d030307080117030d1a131b030908070605040f0b0703020a170a270309081203010b07140703030503070215101502010209090a0501 74
    0x90001401555240f900550481d203010002402085484102101407600c40c2c584441e118400d050035030700281c0340c0c03807481c180c258a03d60260101e907171042c810107d420f1007007141030381e01c0101008514601e0683e40081c10204e046c0f1070001401c0ba00114440091410300a5400029901804000c00b105c0c00e040045008074202d0154001c1d06001003a404070882c80c014280c440c002822000000b019410f4120001e0800300d01c2030303815880a1048000140d0540556400749000d21980c003a948072034140050704100c080c14142c280b41c030410190103015000f04405000011840070300a43e0390b1a01f001e000903001c070803041a015247c155080c01c154000798480d075072550081d6100f40c082911025880d6481e0040c0040034a581c40c2840100900c814a50040010300e1182c1c1504803071803d103d680701e02e0080586c00440210f9008010000380781da0400c10a20f06181d0350b2056100c038205520100058281c07401904150301c6400168101c40d4000d40407039034040d030041d20031010391400a038100020031003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 173848507 1250 173847257 173847277
    0x1111306080a06060e1513030c0f1e030f23030d0e0c06040311011103070f02100302070f1101032a030e060108070521030c06090f1513050304120602 65
    0x150008118641901c3c401c0f0400e5402a44408428107900c20400c035101402085410808804010b00342c0740c070505809950041d881419801889820140400b55180030358216408100d0000402500d190003c5008000c43c0d4001601c0300c0e148001d4101100e5071409104500c030607032a401d035050310102d00000281018100f00b402000316414150341c2d1910742200c40c000a40c00710091000740085140c8035564481314034141008698819580174180c25600400740540b001040b01200d5000e6040c644454042c01c219881c085242c02000c1e624646099118000031341a01d10891521499900a40c4aa000c1c08503a02403896514400c4580381003400b00d4500140c0040c0c1170811000d40604000b8085063302d0442c03020340455800d01d000d00070f180324444c190f14200110182003d0b81840c0c207000400a0020140207072186140985140d417500b1441c61902580d603100300c2a2901000005100c6504070032104280041c100325401c00760300c0c1d409a9009042125510f43c42507040103d01c0c0d0007840703500c503 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 173849757 1250 173848507 173848517
    0x70909050903070510050a02090a0b040905010b0304260903030c0a0219030c0603151706040204141b030402060d1b020114070e010e13020f0d0501080109030c0305030901111306 77
    0xa128041652a40070380303c0d00070442d60181d10791000345021a08050340c06030074103000500340710141000038030000965004180f0b0420014040c02403009500440e8050b040210b81c95155092596038090010400441c44224003244c961100890310240700311502030500408603601d075089080e110342c56090495080f032003403450305010b00a04000300a940e04498003c82d030421003502d040c5056010701074820f0081401c0801c0900030420010045581251180c43d5004101a24040c0f050000321070044096030341e100407110402c416200c01400103010101910080d603200d0300c5904c0858000e0196500003072a41d07041415a030202155103052110384442c0d64000e01c40c042000c0e210320322002e016103901c400540002c1411505500902c1c408036006406441410f0484d04e000c0b5820807038100c0f11a628618000084020140c1d20038007825015101c003600170000c4e551255000f8101c107080360b400a003404004000100358160a40c000e5800307804010b020740d910080701c417000c2c0c105082d1707028240100d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 173851007 1250 173849757 173849761
    0xc130503010e06060d050304090f02090913110f0a0f06020303040b07030b0904030c020d20130e07121e080706061d010303232106150f09060c0607090905 67
    0x11805005903a010b890000c00350003651200340902060044610713046e00d0354032082000040b0030400348200501001c0c205001030b1a03055080821000e01d002801160801d0030500d034500100f603101500d000510720403500780100d050a81d0128040c8060340e444265038007102440001c28603004001144258860145032189585140381901111401100341c2c1e0007101d800001000a8025039145103820300040082d060380010b45d84041480062180c19030a820703120841c44c070581040711407058899a400c0717062051200c0300c018a0340c0d13a0210321a00840f0410100c0890900c030000750851004940740484910320140c50501522541c00300e6401c50704070b072800d000000d9400c0c1500010385122011a00318150fa440c0d43c40480300c5042c0d00c0081d51607850307440e07200c500c544900340c01040e400c424000441581c15034600d281c400044002d005501a40300a01c120744080280320444143d1042d00d54020303180e074080b6011a445018030061180f0510034482809155504184036200b16001180c05000325 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 173852257 1250 173851007 173851009
    0x70810030213141e0c0f0c010c02010b030c12030f031503031305090a0207030c11060412050f060a141614041410030204080a0b060f030d0f032406030203040c0302090c1305 75
    0x1100540318000b903100a603601040d0b000c0030020046c003400c032800100c98285030001000b20700715112074203140c025030b550325000c110a0130144960048088100c450251380d0007108a0035440b0312414104900003500000011048410b030f104100b00f00300054212a201c8203900c6122041a042c2d010f01c84c4103882a13000120107182c01c0c021a1450390f40b560341d40c0c50307e452076950f881036000ca10781e481d51300100602000c100300e5191b0f2840400b0703d0240005012041c0c803c2e81030f42c14003070050300982d44c2505091948802e0f8002031400d6070405040c45a90303d5000d000030088409940d800030316201d40e03c0018000034044801c1c6009891a201101d044050140200702507040348100d08c24805503400c062109408103851680c1c2c41ea003c000501002c25500e4030100007410045c040140002091309032400c1241d0941c5032048011140d1189403c0f40e02e0240603180951640da24800c140c20590000001004c10026400890003558094080400b40c100150080c1494004401001420103188030001d81 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 173853507 1250 173852257 173852281
    0x1080a030c0201030203040303060305120d0b0a03050a080310080318030d020a150209031203040303090309081204050d05030d0c201902040203180a0c1403030a0807081003021314 78
    0x215a050300c40301460303041a0b005401075040107000b0707400d06a40c0ca074001b010170300600040b0211000820126580c5140080131021140250041405510340110510000300c00264524104e500300d40325907103e548400c00301c0c20418081c1c204c0354003030102040f000b803402807150a5003000303003084050f5810720340d8842c0b00726274504281c88003506501e5428240d013804104c0760b00520081801809a803410b000d09a10b869040d0710a4034100c00007691030801406150b400045031f005400080003900300f03010400400c0020340a00e02a540c89a01003402160402c10100100c40c0e2001080100b03000d40c00c101c140c0034000440c01c1a002e51013407892a84038a0542001c03450100c2480d40c0c011844610802c1c0d002d00c0000e4200610201c0303c4440400402010718082003aa2401c511400074402094203040e021202c00500042c0c1902030703881808445100c40d00807550a92004c0c0c545041d026a544420340850541d00a40c0301a41212000581d0048082030350026414252801c03000140c4d0788405605c666 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 173854757 1250 173853507 173853523
    0x30f110d080a020d0204050d0c05011103030405060403030b06070b040c032105041404090218041e02011b1e08032205030a030207050723040606180323030a170108 71
    0x10781c84600207000060660b01428000d64010310050800b5141d401090728002d8000080e950207140700d07410403096034040d850301040b0312700304040c600f9401e05076541e681c1e480d4003400090038142c4900545000783ca510054400880c0c2003000650b0700c1c10300342807140560f0b1850109036014503403c581c004400750142c80b00c0e04800700e141d840c6031409280c2080c205002551115032544140c5980383d00c0d0241c0d0340c5414500b00c84039071211000307040c103291505c0003040e181c0540b0380c7c2c990b43c0700360390b140c002d41e8115404062075002400608c40c03a8985e45042c0214031015a0080e84640c4c9411a200a20130b050000d9071141110003888441965262000000c00750001e2004040d41e00400414861902c0394010b400038038403920445240646400600c1d030804607031170403103840c01180f40d5038110764a401d0103140000c14107810121940000204103181c110800e0201030880c214030401507001b1900801c0c0391012054010030b076900d07081d02507030003084454010061030981c0000300c0007003005035002ca4510 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 173856007 1250 173854757 173854783
    0x90b0f03010e070302090a060914012c011e0f17070509060306270331051309050705150406020d0e0303040e0711010606030c02190c2907030f11 63
    0x140f21403442d420482c403648020111007030305458500000e041c0b601800741080c18540b150f5282c07901d6040451514015107040d82814141c0541000d4894054058820314103640b1210b00c040c50f8001418a000b04501550b48043c0003460607580008010042c0b0550104050507403040d200040c0d0b80b0410013400c24010fa403c258036804c400c0c0440c1e6240e2100c1d4034280d540d9507504802c000a2105902c5d281143c0020000b40400c0c030104803010311188a110380915000c21040502184a0408002c101c4843e148888481107e0f0f4030410320041c44410045c100080c0401403003284107a03c02c8030300c3d8a03141c00a100707010141c80340c849640c0c40356024410440740a00040c00950a0034901094030302d0081029000d80f061100920143d09903100c207020313800161516171030110761868006c000070710303062454400b6116151004c400c17a000a194034200e204070352402e003070205480681a00800d01c24003410301255000d100042ea8001c0503000520510758031900d444030021140c0044a00e03440d01801142d507 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 173857257 1250 173856007 173856013
    0x3010b130203060d140a0c0801052505090d0c030c06080705070213060e2e0f0308031b030f07120207030f110f0a0302030414030a0308070f0e0901090b0f03010e 70
    0x240351034418590180d41d01100c010700d10785001c1215105c0d40b481c142600d070550b040d0b0308407101030810b20a004c030f00c0c0301c002c240303e000800a5250101840802d40402c10409990201000134200b107130b480f80c070603180041070007007600740c0c8020507103041e4681c001d29100858030f10805d37120028100340140d003070510510454031170760300d40ba400f607081048450049611801e5183d4403500411407040c0c00700c103903100d810001d10481650f031a407274002c800340c2c04079540c0078030301080a60103010042c1d0310b8a4101c03c1325404452152a51560418011407488040f141607040002004002c0404c0551074028095103854441e041c0399908510440160301c1072240240108014094100718244034114410300d541c6c5480c1034440c81e00821140e90304000061006500607400800c0501c200e01d501d40f913403200c1441c11030040c1340c032844c103541c09089114020505402c0c420108241c58020b40604238182c42d0b400003c184118a40e1141c0d04000101201c0900038014103020b2418040c9050501c500700301e5030054401 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 173858507 1250 173857257 173857279
    0x406260106021908040e040b0907140f12030421060c020c0d020d05010f0e160512060403230406030609050a1a100302070f0302010b090f010f09050705130303020d0e03010b 75
    0x460000c955001421121513008110005680401c0804540514400c040c0c4000c01d00704400158503102264000078403042c400d550942d4585d44230580a104940c0a850700c42c0c260450bc06c640303055014580c4410090000c0d88049001ca04900c0c8203a00713250720a203c208442604c4c2d40e01242e81c0c00200320515004810351605501500d4201c2c1c40c404000c2c0f0400000c280c000112805805584507001c01d140e1076480b80b00c154014540c2070811002809050303d500c00201e082d8221a65544c4001e00050148884085c0d00c44030110028200200303030032000c80c055a81d950b00c3e14010000c240c18800c41e8402403410000c107460150600400510b00341c01545180f111800804004442c24605032650505908001250010351104d01d401845800f82e000051b0145040c8184580f2171002090081041c207408014410358400c029001306407002d284000500c0d903100038003a640c8d8031500f605010901140000007082603400103280b0790b600007030341d150b0500144a406060a0341e2034807196990101c06026 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 173859757 1250 173858507 173858533
    0xd050f07030c1407060801170c031b0307030c03080d060501050c070e1f0b0a0e0102060403020d08060f091f050402130519050a09020a020d0512070c0c0b040626010602 73
    0x30341c0b146a50b000301084808010406002440c009407580403a02040300c80004200c90f07501024001e0040c00160301a00600820100090726915800c4069004c03800306400c0c080716850412180014603031007202d0030122526400c004166801880c403070f07400700b400d0076800705055115401360340d14545280c00070210181008400c0000301c4000f020364000184010810300110005580080148082c01c07803203564107003442c00200344185d0b0701101b90565100a0030700001035400110300072204128586109d50303480319000100c4021002074071680c000e80340801d00c1218603000790b842242c0c81c07141c81d5101d031069075501404145d014400000e003040c540c1074020411403d241b40700f021120b114544250015450314001030b0308540d180c0045003070a6010035a0303580c0d150104865540300c0c40e6070030000c0c24030500c0740042d24610401001482000100c1c01e0340810881502c1160000d0300901620ba0388490711000014003400c4100f18144c40c005041e14188402f910440c005416a149903020346000d240f524 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 173861007 1250 173859757 173859767
    0x312101409090102090a09200f1c110703030f0e0607050a0809010b03030a0908100b0a06030f0b12010e070b21090c0607060b12010b010905010c03030906090302030a020d050f0703 78
    0x28030302d502c0d075502000003582583d50711040e1000b4240000700010580179074880310416888965440d80f450b8410441464803485840c16280030000300d151596a140c440486003000c0c00c0b524100011a14000c00e6070b00030150560824200e40e501c00c4000c0200c1541c0c0f20010b44c1c0c17854141d4800c07000c104204a146219131081201c1c6521920540001c42d0f1030507410007003442c60303019650120000f00003040a00440500740300c00361006c1a40c031001c1c003a0510000c001180c0031282e101e92002d16aa03400c52003c4450540c0001c41c2c80d180051032240c00b078680002841c084c15065040e002e15004001002c03601480b00802d503030b031102d082c90400003104107020b5000c0f107020010307000760180d11904050360542e5582000038581d1b07900c64440451744030401414401c1c00d5404544000f000e90501100e010503076400052442140c8091800700c1c2c10f400141005c0e0000c0c0890b03540130f02070608143c5158203243d00080103004a00d03480c0d003200c14402502c0000c40765405003000c003001d000d5007040b4000c00b0901c12 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 173862257 1250 173861007 173861011
    0x30201050f0a090e010801021b01023a1505030705090c03010512030c0105150a0b0c0d0e1804050106140901060207030821090d120b0310050a09080c0312101409 70
    0x203420840c02d0f182e00c030510401801001d83c4018660fa4001801580b2400703810941c41907a11190300035818082c1c00b14003e4040050340b00000c00003005141c1c3c0f40d40014500780140c4855040002c01c00c40651164074003044440c02d801042d010340715810303000070136040241c2042d10a2441c49811400c50742041e04000c2001901e50640c0b08901c0248625160810288619801000d050325404d00600c6410103009103400030b40c3c03000e445540c1c284940f80034442c0100d40c104400300c1711303c0d012500480c1100028010600b05036100348850415081004004d0154000300c142c84c2d03100100091000d50004010351078200b401282c0050700101c104200007144800075191844008000071080480420178101d0b410080700e140c940340c0c1c440003091181c02e40001d0081100e0108038401e0140c040d040c1c0c0801d5660441d400400f00e4259200f000840604d05030340041c44041e40b0921460355902c2442e6881c0c0d9a400c0102022030380c0d141d00010400780f401e02c5e041d4200b2240310410449410100c0b604003c1103401c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 173863507 1250 173862257 173862277
    0x30405060f0901030b0a120b0702100f0504060b06040f1a120f1b310e04030f080105031614010306050301060b0c1b062203170909070207030201050f 65
    0x1400089019612240a8000903a403456002d445015520004003510500007425016100d070141c18408000700402c42c00055412200000c50f0383c840450407440c010361380000c91141840c2955000307018180390480350046000b80424030210b6007500410845d8031861084e0202100d1510003008040b0742d4152380d481210850080d9824a00b840c0d2038481e411004030380400500c01402c00b00070f040c1c601455a03011901c02450101d0410509a4040c0c0e90100003680e86005600c1c61441801141c502000c80c1c0c0240038410f05030a22410b03e483c000d04014046405034002c07031446170001ca0f040c100001c4028100b032601500390030192800705102c1c001e482d4504150b04254882d0300114807030b18240292002461226451aa50341d58002d070301c0c0c10880005800801070031403049d81c0c1c04650f40d410507074806000041e041506a1000c4800b95523910156000030b0881092446580c1084520409003500d0f440a0304c01ca00747c2d9965a8040f41c5425850000a01050b824004030480e54541409043c030961 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 173864757 1250 173863507 173863513
    0x8160501180e0a020403020306180d14040f06020705100e10031d150a0c11061b13060f030e010203091f06050d060b030c0a0806010902031b13030308060f0603040602090102 75
    0x24541d04408102d84044501480b25600003804004508040001c00c2e4000c01e608402d0f122501c540e80c1242e11091041e0814080082c016441305180c0b080b0701c100e070001d020142a520f03589076200c1c030281d1180e00038410648a40d8030200c41180036800b611142111000052001c07468003000d0005034010104860420382070014491703079410001003005240c502d102d920440400c2d500d828585801601c03031401e881d90401c0f1645560802d41c080004410341c01c22102e2142030350281310040030040a005610712020b801c1503001001604c0358102c0c00428542030a55428001101c0d010f0209090b4441504c580180d90701c24020380e5618110460f40345501d58503031602040b4140c0e01e00018a00340700090099032030940c2c50044040c00e184c00c1001001400d42554001720350341c03801c500207464550511034030100b10740000c0000d00b440c0005100c2a030b44101001d11070b4a5a0151900c083d0525103400200e02044805000c034500340380c20704110056280c0105000d296075965500c00d0080d400c00d8099070f0642c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 173866007 1250 173864757 173864759
    0x90c030207120201140a150302060306030f0604030e030705060c15040303020c0a0305180d0503030a0e03130b07020102060705090607083a0f050103080708071a1e010816050118 77
    0x90018219100070502c0768000b261004410810b011401d0024100d44100380ca880320054000010300c0f2010101c036011242d8544a40d604401710b0f0812100c50017110301d034040d0000300004c254204200c42c41c9107200740c00301c40c80300f9112001c1c803149102d100342030299039100740d422034000340f444209203031b0040c0300307190140c02d048910200030710b080f4601e6022404584003280404140c0d1980d1200e010084044805241c4c0c04060307201d140d128030000d46100200c4d0b0b103924401c1c0900004208403036106261050490402e80c1d21880050780390441d61080307005000d50400b040700030f486002a41e28454000b0001403820702199140151640420340300d09045620302e10700b49404001244e0b030490508111a0858030030f9240742403170226900703158002039141c48d1000500201d45200251207656502200341581c0b41c40030b0420300d0203c028090103640c4c5a00d00400c1203400c2c0c111401205600c4104149440c00340d803246101507c4a854149040ca000100e0408101940c0700d0702c0124880807015605500070703 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 173867257 1250 173866007 173866013
    0x70915020a080a0504170102070807030f1e090603150e07200f03190c0506010311040b0d05010b3105071b0501061809030e04050604140405010509060f040c090c030207 73
    0x103030b04121800404a440401e0801c000410914524a8214814000c519007026517680600c54080d055002cce0412400e080039141c09800b83e609010580300900c081c0c0c2644851150061404442c0e01681001a084c8803080c80414040ca151000f80e8050604400d940d5950f460100c1e5106107070b050240308101e504180d44800d02c2e05102c65280507030a0f0010715070b5031040441c0c180d0307605403a210040030040c0d02550007020a00125007035054079031004540040c8d60b0b10b4800200601000d18a0b50350080400e60154204031056020a843d9801602d00303a000601c0c2c036140b0074809036040ea0344224551b0341031214481c200d4503841594080300ca400d05800030344074500148000e0901d01000c86550390b642c1c0d014050020300d00021080b120000b4410301040c030644ea001003041d004892500d02450300c81010070740070743d110f80048910950103451390b4040d14050402501804040d84c0c80c0c1c041c1d000e00c00c080b80450204403000f07486140c01500031403030b07940b130007482d04000c01c1100310341c0040550921400e000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 173868507 1250 173867257 173867273
    0x4020307090b130638030106030b0607021804030e15070204020c0102070c0303090801060f05030d0e0114120115050a050313052b03050708010f14030106170f010b0603070915020a 78
    0x141c01501c0c2140d403070a1800740006141c1805c410406924104451321021388210b5000b20f0341034881600c3e011405002c031401190050150f100c0095214403c41500e58003d6555501548540e000360750340303012521628240108022a030083c00c6c4900c00c1003141030301504190700100740072100b102c00145068900e44820400c56400c0d0022800100440c034108440704090180c40c0c050304c10303d0400401c03149400700103a5070350461914801030005d0a4030101003a03000302c03000e048178200b200d00b880c0e507110089a8440100002d0041c45c00c100d00d0840c2c102580b40c030a20131703507174000610b132946840d40e1101904486000b0300b0755001c80c0c041c443c200700200c0902015490a41c03c3e440a0340c030a00410140c2c00203001d40303000038084400c0009403801000031a407015601000c445800c5140c03c01d0700c1440c408030b4003410b100d0f000903140903d400040c40d226800001c08160208180008200b40c2c007544080040512040e13446100203215641c1c107208062040420321008002c41c0101c81c94580c00b90755840c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 173869757 1250 173868507 173868509
    0x509151203121e010e0402030a06020d020a090f03050304030305031302030718051e0606070309150903020a06020606150c15040804050f1507030509010507060608010204150804020307090b1306 84
    0x1607400224480365071910605441c0d4008920b0070800d0b80468403440e552003980030503c664091202c0140c007007025910b00340400080380383c00820541d614030700445445c020390301c80300c0c2c10400076051941c00100c201191104e841602d40c050041e526251840c1ca045903180c001420300404031b18103645801c0160f42c1007254400510495a11104148407a84100c0494000034207034050002c0c1c842079525032812015000358055422920107443d071039035003000c803810f461540110b0384a00da4124000703145a08418100b00b1070384226105c59626840307603422600c0701020342e40c00c0c3e0030600a44455800404040150000c1380c4141c1c100d131070000103450311408100c0280c5040e0381311480000c0c1031050707046c01d0000d000504016190b040300b2000c2181020543e03c51284003404008000c1440c0c1070583c0b29408072030a0581028050200c103440d140c80c2c50007940684100d03404071014400c440d0031107000302c1209200d550004c000c0c0ca03080e46404017070400341c00c5540759503910400c203403a0764503400e0321841100c3c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 173871007 1250 173869757 173869789
    0x3030c060a0b0103061d1603020c0106080307060630060f02180a08030a0503040602070302070e09030c0c010c031209050c0d0b043e030a14060601080619050915 70
    0x418000b141c2c0b400981107681d950490420700b240140c00714a180f00001e00c450b001303038078520018000380c60903004a0003030003805200003031035003820310014141314000041c11216000710001c2085c1c0755035094004c1c02c554244180381440280658a8802c0002d080c003003540f00d4002c540c01300740b034001d104600089a1185107450317842c2e00b0059845643d820194680400b50004400841c0b030181000c1c03003e89680801080144015000200c40003014800d0100c0801810007104480c02030802240d41e944a412042492101c1c4c451183c2e80d41040d13210b1030713007040826015112070786000c00720b02a810151100804c180d440e803241031101c840b5a16104281c040f400d000702c070140d1b840c1c1014038119a01e0340f0012142d8001a1041c0740d031014402c8c0c4010f00b05c0ca60300285811034100103400700802c0c1403903030340100034000c41031201d4002450000850020310650099940740703581d696040802c01c00000c104542c102c1c1c18611701d0705004ca8204160ba040d04800d0700070f088000c4204030700029070100c2080b1045 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 173872257 1250 173871007 173871011
    0x60705090117160e0a05030a0204090c0f0602060702010c030b090402010c170d0c090b0708091009091503050c090f16050423090a020304020f06030c070f1433040203030c060a 76
    0x71500c030b90340c40340b10100b80b40307030403a440c0310342a04c6c000000e9a60003507800c020340301c3d03507560700114100324050600c02d0052159034142580ea40e65000c0c041d4440f00c0490f0390f94095400d10701100c494610034812924100742c004e02c0e00c03c50b6100c5800454800ca10180e044403c006010078031040da0381014054629905c0c10300b03022940c1c3c100c6803c0109940d007140c1c00912450300620030320340000c5117002036450b05032064800341441000d20344200c903584c890341e0100c0c41c80ca00d424001584d0418440a42050324082c1086504c40d420150034004407090440d0105a000300d0500800c90200c45003c40320194402440c0c030509041c4c82e010191110825640c940c03944000f81c20703550303400341409a19941d108058490450648c5072a4003c03d6a8402207401079116020000004200030703600d1040e01c54043d04255804001d00003850400f0301c6102d012612803d512400001e4041d0200b80c6021004a8100075101254801242003241052501401c200d81c03500050003442c030181010042c070340c4101e00040340 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 173873507 1250 173872257 173872291
    0x1050c010504290105060a0f0203120109050a05060d021318080408010f0e0601140f0d08030f040605090d0e1005090603040c050a0f0312080703060b04030b0f07050c060705090117 78
    0x480f211180030002400006030820300100803695401098404002490130f0150381101600001c90079845891100184480004000301d00011190700c0984a0b03001c031031003000151161780070441d0f5a00d29000c0258800c0c1c0c4e80c1d4541c0b442c50150340240074115a54100e850b06041240e450303075010b07001070700008100d0b9910f41c0d0150003216107010300041059120040e01c500d50412031040301d210b0400d02107034000c8107100216441500d503400250300c25508598000d0b12400d28480c030000e003060580c4d0954036a41050b000c41c200c141c000c81c14000e54100341c1c0306c4a203500c00709018080210020402c1c0e0b4107200c4180081007050300d607480103522540c410058070742c1e41c0e810001001030720761194000c003281090440c8103000240c052030b0044010b0807a81400c0318195100707503045000d45002d4105940844000c0380000400c04111505030050303c507443c4504203640c51707420880c0c540c0181c0182a480d0781c0304a0200c1c25207800f5000805843c00c041c034000568501c0a200100803031f40a88403080400c1d44004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 173874757 1250 173873507 173873543
    0x21e0702030d0804030207060c03170117010522111804050a0303060b0906180f031009110904121115040b06011b12031104030f03030c11010b030d0e01050c010504 71
    0x40e00c05907180b103081209007418182c030700030354452140c0160380600c282c1c151890241400344401c220903040d0364090519a40c3c5881d540303010708402c2070903107081e90700b4a004a0403580400d8040d64104c03003044480850056aa1903058040d035418080b1500540422291054103801e521418411401200145541d40b801e1400078115213003940100c141c59030a00a80d004c95540d40f040319017002c001c0c0d484a1005c442140002c1e03181c0210174000d82d061052207041d401061480d0454072400c5c2c028648000c07070540307840c10300c0356409040340c000b0404c0a01c000c0b035030702d1b0902890080c0c485c420700c0c42c01c85000c03000345500c9004400056030290b42c0701c40c0700410000b086d0f034040038000102c0c0346168408910012039880300c0100d001e01c8030031000e060f10b43d03040da5500c103030480c00c0c0d600441d0003802034100c240207400c010f00203186210410300000c103100c1c00c4030300d0308070140250030001001a0081021500007130b0119030421b04002e58a042010070000b4801c001401d009450255004140c0c161010a88403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 173876007 1250 173874757 173874763
    0x2040e011715060f0111340e01030206070204020a0203070804120b0c1309050c07050319080705071a0c0d0c030f050603010c08010e0709150206010f0e0c0307030f021e070203 76
    0x2000402d00c008034200302d0305444191070319a400d0b400f802c000310101d814500d0582001d454a065160392070340e10b0542070f06105102425000c0c074225102c0c49030320356120302120501d840c00f4000030350040810880d00d070043c01d15500404100c0341c2441921b04060183d0f88030841944282d0002c20140580755240c002d002d48842d006800181e001d440700c1c500003c003950709203114401c4c800c03880744a6507003001454ae81c021404079481d250740300c5c066039501c12000071004e01c6103000702d1403540052110000180e00303e0081c01107810b9540c0041e06542e509400c000c0d1460040700003060031100d228144401c4803249200d0099014030001d82d1000f040c40300b01e90103850119440100b80c03d2090f0304041c5501a51030700221000c4c155100000d40300080d44c4c2d00072096a904903180e0003050b00100400c03008015960104005040c1c42d4100012074003541e1301c00402505110503503901100d01e5040010880040c0039511060911507125401b60034045500c2005209540a15101d482c040002905208510b414 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 173877257 1250 173876007 173876023
    0x50118060b190e19020408010f0527030315010c020612040b06150f030912041e0905010b0a050903070305030d0c26010b070303060510091d0c160602040e0117 69
    0x24208a02c0c05072400019000d14000505030241015a000b40c0c401ca00580750122406043c11000070b021721110130565500802040f6003410307038512032030440f00411080344000c4039a0203142c07005505545981d004100000050215107040c0024000500d0050302ca0340301800c11200f101948103030314582410050419940208541d02c2210b00130554159a0105000e50300030700040c0c0039840d04c9a840342ca000c0d2804c000083c82501080e0041400140b0030560b1402c4140007000e11246142607036103100d14815101e0070301130010007444c140701261500703215102900c44402c0003021944030903903d40f107850950340440b004181c4c1d55254a00c5140903a0000102c08840071910003071f80b035040c0d001e01001400041030017400514100042e0341d1007454801d80082000d01001061210012190b5030042c0a003002c030b01c00c581c05030b040701c1c0822451a03401d5542c40e02c502c802d000400c0c0390070461604c0004001042600f00c1f2860f50034080071550060840555000e0001103580000803a40d10264500d80301c10 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 173878507 1250 173877257 173877289
    0x1614160b01030b07020f0f1e0c0402040b0304022809051906060509010207140a0b07020d0803070504050117070801030201080619090207052a01030914010c030903031802010c02060304050118060b 85
    0x306e40f87e502c800251b0840102450010454000f0074041c12418010700101c00382e800340c00420042001315012000354040e03842100d200a101c50004601c150901c06c00310b00c050317500da5440301008804d10540082d903100344181c100b5032143c10101c0c8107404807a2584c2203040051000f042c080019601086054054003412500e881c2c03086030200015543d071094003803013a9200d40455a20110b407180c2e550760f207480d075201d410705440c0d2820100003480f030340051261a00140c22840e402c5200010805281d001e001543d60304155a800c42e00151000c0d9400760142d42c00c01980d40214007414100c0d1149800340c800c5050240c0d0f00c02c003034149149000c82680c88030700008075015110b02c010080b05c1c041141d4503001c2c02e001c01c0403204e500340f00d9402c0c040d038405102c2950030180c5400542d981640032040e1144641c07000c0140ca0303803185551444400104000340843d09908500c80589085009141c1c003511907400170448190844190780108095402115031b01c3c2c4413460320340c15243c1042900d20282c2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 173879757 1250 173878507 173878513
    0xb070b06040b0f300d0807020c18040204050c09060c011d0d021e031c0203040b01170d030902030304051005040906080312011523121614160b01030b07020f 68
    0x2003600003891100f6100100c8000201801101d40c4c860784100c200c81c640139101040c0c0b081c5003c6060003800b8170030220340c0d81e4014091175040d6995440c00c29200c41004850403c4981c10b0b0303075913a09100041001819544002909005040c42960740b90300820800c1020070011406a5000b4640b5254440740c601c0c0c080030f5044254650802940000d8643c01c14070001803009910008101c03150035840b07000e403003465480b9920150f0002120580040d40034520480c0e84440582ea0f0300c25041c003e0b07144c1c600000c483c3e040740c900700f0b031218440c0c3c1085100d24001000d9901e0f00703a0703a900003414620481c00b0080814004101000440c0c0c181c880c510041461a001e98640410429115200401400703094202001c100e50300d40744500c20000071444860800710145005006c81ca0007440780c100e2960b440044000100085840140c0681c1c3c044027102030b160000312140444000b01207810148070401d0449103c100000801d410f00a1a4020b5005900f1650075081c4003200030300305044540c1a0f50030754 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 173881007 1250 173879757 173879779
    0x2e1706010c0201080c04030204060906050102101a101206080616090f050907051210090c11070902030402030a062c060412050a0e04060b090127031b0b070b06040b 71
    0x40d0300924020391550b424030300340100b551400444c24081c09243c1001e90094501140030070451215840074003a218240c0848200380080350a98055507030200c80c4541d080c0a0008608660070b001880c00e4081500d41040340c000210503c08204964a961009101341e1200c001e00c8000000c681d20f0b01c1320400c6610f4004045820a050761007086c1080c4100350244a02c1c400103411180300e542900d030110103002031511142850f1a205184400c50300401c10b0a625008498a9007405a02206c0701220000b014058851600301d00038000e400040c0240d815020b1000d40c0d03000102a84118020000c4000c800355144d00d42c0c9081902501110800342440d601c2002408046101c02072044816800e5103802e07a601c00c0d049108032a000d020008103a04141444804540d000f00d26014085d030310001e030313114030003941240480078481b802200c000c21942c41e412400e10100d103c845881594403055102040c05a6881c17400c0001c0c1e52000c20b054401c007071248140100b9180c01c1c001c035480040100d031000601 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 173882257 1250 173881007 173881009
    0x60f0b1c02250203060108031e0a020115060302120a020a1b080c01091104050702030909010909031e0503060405090304050612250906020c0603130f022e1706 69
    0x26106039054940d44009104040080020940440b181d50365800402500c0900081d0216003600c94007200b01d1103809400e00101319404008151000d0a540400c03903041c211000408030f02c2d43d884504403c046540380d603070110b0510716544101c00244020b030b40042e503076455110f84c003000c03107000b515401800380100003821040754415000c03110140d0403d1080600025403a09050b80d214441c600419542441040828006c2848410b1480442502d00703000701e030b4034010200e0701c91003840c91055004042d50014800050554006050280720341030107000e1241d05101841040f10402c0047c001900c00001c0210764282030140c181c0040f02000118102401c3c40001400c90107983c90210b815540c2e507002500450010a8600801c1c0313545164000016a00c4d90040c10115603024000241c41381c0b1400c440c0b03908012048a00c24040722a07800c1801d44d0564071408103081052080c0e91161025a880001d2207800741e590f9083c10000d0100b80300105614005089400d0300d01c02400c071180740c40704001d05 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 173883507 1250 173882257 173882279
    0x30708010f03080d0b130f0c110a02100c060e15060102010b01030507050a0518152a030304080c0309030601080d021207111c08030a02030a180c17070308070c050103060f 74
    0x2114400d18041041e801079000306000710301b0035002500c07660074281542c1d040c0032154403d0f0b2404116954111085c000081c0d82523461010140c001e41012009031600003217403045c03c0344d1070000d10070a40451610080801c052505944100a20002c0180780600510b03680902c103800400c2d800303003001d1000389040007015015005064640007808400500c03611802101071513200c881c54020008c1a14030340c014680506030b0840624042d1414115803880140b40228031012200010400114907581d5565a400c040340c200c2559000123200910107403a4582e02803050f0713070291210000070700e4060b04e00c072802850908003e500c1418035400300a00400b090040340d0110907010261200c8015141400c00b050200d410540c015081c820301000740480746240d500154001c0d01000018040b10070314581a9106100455000b424407400340e80401c804000303480d05d0002c2e0100901941d880302c1d5070381c5802111740d1011408175540d10a0340c005010540e0141300d00310103040384542910486052003140d540e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 173884757 1250 173883507 173883517
    0x11707090b0a020c120102120906010312030f0f050702060604050a060e16050c0724080903030a0c030605060a0c170a021504020a05060d05061311091909060605030708010f0308 77
    0x26440d00001c040703494a000704000c000c2c0e44c0380076109000d07800f00c0e640428000e40085203a040390b0a500008103c003500c0006a240c107030303604a0307010314001a5040c42a801091082a242c03921034031a41612051b070000d201d10703845030249402501161402c0c004110841302c004020324440b07440e000b000c0c0000c02011f030301076034000160b00400341049200c00098440c0c0c011f03800b41800d6403141c4140403c2241c40c400701b5031a154684500c80040c0d5926a8080d01c0a8008665602c541d91081c4002004030000390003218840700700e4100002e00e681c4800200c2d03196800040d452000c81c00b45440d80040144100e040ba0005c500e0030a201d0510140e014000d48801c03007100d20950194800011800755a505160700c0000c1100415090766920540d0030480900802c0703405a00c282100703040784482400307500684011004e1a10306a142c004a40100b040008210301680340103035243d100844d000883d84030710380c040c20064541c543c0702d02c1c000000510b41d040517013101801c2c0c1c20b00b4004200048040342035803 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 173886007 1250 173884757 173884769
    0x60a051506090d210f0306050d060f0b0603090a0203150705030112060f320c0904020a03020c030d050103020909030c1b0f0307090c0207090501050618060d020a02060601170709 77
    0x15a8911031140026403082e40800c02408018030888050050340784c1e841c1100e10440740707449041c81101d26003c19812611140302e1281c018480d025002c2c0001c0c600da00480c0441410380c8000b601c400b058020600700e4004503018505035000807080000d502c2c041105400b1010b9944903842c4a10300320000820b6800188201c11203060105048010404143c10210b80e0325100b420801c40c1c02200888071000d481016039440f415113103022160740408071801c4051244201d01c0a481c0ba0180b00c800f404025030040c1e6000c1c00701a0f082c044d20390584004d00c02081d0494005101003444d50440c010002800f8016080c054140e008000441e004100400d810040b056091941b100010071f0b04017180fa0120750801513075042c050004080741c2c03414182e00038104020b80f60308642c200c40c2c5034151881221001e000b041c0e480401404286912129800340590064001d06850f091071666500780040e40c011000c01805070308400200042544c0c050010400c0f684402030b13488440c01c1c17201c0064a01e000381d00540c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 173887257 1250 173886007 173886019
    0x12160906080115030813151e0305060102060c090f0402040e01091415041524030506100203160204060509090c01030c05091c051e0709050c07051009030306050d0302010905060a0515 79
    0x10051012a00f20350200401680d11007003415001a200100310440220045a010100d1105c8c0c081c0d45100b480303914490001030b00240340c540c540382c115190642101c0443e603030001490b440340170f407030702e8500261009200f00041c1c20b0300f55040c40ca500d402c3c1c4604084521140403c003080000321030b0010120710118900b598001a881000103805c0c1040031150001a051700d032a00c90600060411005040c41440340c1da010400358580100f000b4070507480300300160059000348080c1e1100e913807021141d18000d100400006420317550340081543c00c1c030f04440101c1d83c1e412402e146080f43d41c041c040c3c3c055415640c07a14074940309401d00007a401030850540755810810200414080100410035400300c0d820030004440f4505200501c940d640542c2d0007011012401c0c880032503c100c1590040c0c404940e0710101500c608144a20315600402c000003040d820141c0703840e00000c0310307251004035800e500d0080c0e0020541d0a03860404524052000c3e02000600b4688420440c0c0030200c0d03054079100e50011180 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 173888507 1250 173887257 173887267
    0x30213090c090b0f0d120f080c0a05130e0c04090506060f1c06030624050a060f21020706020c210f090d050105070c0b07050a020309040209121609060801150308 70
    0x4210841035603982c13150044128400074003403100c1d269221100324210342d60194560007210007100d1070b42c81a02c8411441034284030301c003403c2d40594042c0500442403409007140580da01e134a200d1014090b500141c00e2900041d00340030f117151758044c0d1580300e50240c41aa1500041a0056003684101c81c3d0b140c455080360b07600900d138070a154011100460304031200303008140801c1c2c105c5800004411112681c610301640018150406510700e40441c3d0f042d858035100285180d509035903089411070700858a00c492a014400d024040c07000d4040d403400f9000048e00c0351070001c0a10701e0005000040c03001045041c000341c8591517a00d0880b0002c1030008101a04c0c1c100302d0b80415045482218020440d5007403a02b0065480da1101e2a04079460151102c000c940e01c51100559151003003412034801601704005800c61810150000c00c92060003404100e003c1500e403148a0600c01542c94207a0409481c0c1410088103803240030709800303030440d01c00030860807010300803988201d19a440300502880002c12 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 173889757 1250 173888507 173888509
    0x30c03060d24061403070302060a200a03020a0b06030303060a1a090a15020c01080412140705060a06140a0803070b10150f02120703020d0c05010e030a09030213090c090b 74
    0x24600011290003440601c20700c02c2000320a0250180340100c601014810442c21218038000503410f044907005462149080b20f8514216003800365664130b10f240b5403c01c00d1140380e00d00304001c1c400b200c501030740c00741102c0f80721481c20002000000c0c080510079402401809019070340c80300200111a0701e00c110400c000c0301403480c41b042d0300030b08007031a5210071022800100e4003081504880c580c3d00030350985407601800001955020f800751005880404000c001e0329030746000d0000c0e680c0300c4102c10101414001c1036a00c3c1c5242c0030003100c0c0c00403502d0701e41e1300c00c1008818205030103a02c4441107404000590928041d00e81e20301440101408003803445000c00d69514a86001394040c000401035034101c154640009401d440f801601e8000520070700510742d800ea0500420b0358440d5606a014111060f0084022a02c0020690301900c04d556500c0c0302c03c04608040009005410301030b11040400e520314010044040580406500ca9a0a1081c0700e000105500c5000c002d40751401400502c0c21107041c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 173891007 1250 173889757 173889773
    0xc060f0103120c17040b09190f0b0702010e0d0615080c03100b041b0513091a100e041802030c03031812011808070b16050a030c030f0606111002030c03060d 68
    0x10f80e410804150010700403070991b110500600c91410180c80c1c41e0207080952018088000051244042140012a051214010140040c522140140741c008900000840026142c40d40d840c022a0320341c0e96041041c81c0348a11808203801001010701030040094800003082c0c03103400f0190740c442038030b98031024100b8035a00c580c80441003210898603034002c54803004d409801c0341e10554580c0c56400c1c4604002030b500c1d400703002e80c144240c20703042c419203001002400e200b82d036074480155900b8032017072155a2000e9202c030321614402040e100800001d510660050600b040000c09145010b07410400c0100f5100300e0b9030138015000b8a09540308006505500d030752900610181000100091068540006000881e0040c104007801780103513034031030b8540941d6440301e001a100310401140f82441f243c0e0340280a0b90240400d02042d08010502c807200c00b041134202c80e00da4215201040300c40100700e83c140010440704241c20603405003145135041440f00d51070305000c0103024a00c980600003100d01040412 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 173892257 1250 173891007 173891033
    0x7110a08030103080301031707020f010e01050913060627030209191b200c0105090402071406010806130b06090c0705010e0f0d17040602090d0b07050c060f0103120c 72
    0x8001026120b503100d01d80391225620a20040e101100c090100c14003100c5e03d04119480180e005010889031044440191103241010696505010040c064401c985c0c58140c2076030300c07002c5041c00001d42d650030484060503460100c0000036041c81c4005010000040300d00c07030070050313076011214260070b6a80c2c0061003a03416030b503420041701c072420001c40c110300710b0080b0b4403840210f2603522900d003082e01414400c0360b551030742d221804080d40841c0c0c045085500410051000850190002d4a40086922000c6850210180c4504190700030401040130b5001030002c2a0030000b003552540411405841d12805041f014180c244221213a0f80851044410001196151a8814001c1c8040028400b8054030f85860246032078031070094040d41f521407403094928031840080c14034196556107035910780100a410000310541c00040d49264040803030182c02a10341710741015039900703075502d540194503428004054002404100118011310004240b0b182200d5410002d2514030000406814200180c2e03a00d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 173893507 1250 173892257 173892263
    0x50901020f1e0c030a030501030b07080408030a0c030612030507060506180103032d020c01020c09072703020603100311040513080304060621020a080303070c170405040501090b0f010903030807110a 86
    0x80017900ca048503400d80c2256040340c1c0034580a0203565980703c1e0a0341c2034001280c0040c2244410400102c1804483c1c1c00034008903124a0001416611801010458000040164080745c408a1003d040050500a8903813150055407003036410b4001d8203100c0c043c610180002828845080c60b900d00d02000a00700712030403000c52881804a004c2900c000c2d4540c00c0581220740180100e055180a80c107003405214090a00d995440301c9082100300400000038946d0791701c001c00c0882c0384c4000056030303e0030050344c0920034220021141d5407551030544144e50303808034024003407070400e820010811091b80204900070f400001c3c0a690340e4403490080b00402c020381008030b400c01c00307842d090f440301c1d90560381495061081d280125020b450f0b8851503034900089901d200010300c0105107100040c0b000c2005101011104809407d042c3c95000240503268240c0040040a03030700c0486808514003040b90f512008404c1c00c08050443c21034500500c0c0c028001c140b0030a0161501c03801158860400411202c190 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 173894757 1250 173893507 173893513
    0x212091b060705121305241905070f0506090d0903020303040e040303090f12020c0102031806070312060909060b090601090506160b01080a02101b02041e05090709050901020f1e0c 78
    0x385d00c0900c02000c40d900906000d03505444080c0d0107505241044a843c05045503e607050130100b10310b039804a51701c441c40380108001070161a0010700d00d12000b21196208601a000d1460440300030380c540401c440c500c00402405160800c056200401164140c8082c080c5081140c0c0e101e0030103601400700c0031001170461844515410a000d03d50f000d800b0340001c41d90079103102c10241001281d590060112055603a00c54040d84803c07880d04000410b0b0b140d1090805819204078140d440c07048903a82e500c540d1440d40c88200c40c5c401c00916110381154640c0403507108071030b8140383c40000c0154049004545c05054005510000b8050322050040b4039503019095055560311800000e407198014003040b405070350088025100341e401807180c0340d0b0701003615200030340c04606602000068201d191b2403040c44449a03569004a520b51300610340b013801c040009101c1c0c03a181081d800100c1704010005016030b41305003c0034101d204003e0840d400302c9071400207020702c400d480f0300f040c034184a84170a814544c4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 173896007 1250 173894757 173894767
    0xa090b0705060108010b01170f1503160303090914060919090818040207030215130f0515160f0302180604060908060603150a05180f010212091b06070512 67
    0x106581070340c070413100030b11601c4001c5005540c0d03500c541448046844031140010051070542482c82e9100d0740c2030031210002b600500101c2e080c041a884407082c034440d0080c082c02070580042c444001400591800c011180c003940501c020f5481c09401544142a44030108035040c240c1c4040320300d40c541140080004020038a400c642c60380c4803e40f800c0c0d9181d1102022052460203200382c4292542540142881e0300b102000642031050042c110140c240c80c1c40d01d00d10220300a030b05808412445440241807101e0303c14000c0b0411038004101183d16142da006d84007c0700c0e0f01c04d10a400c0321010341005070700d51800703440c1d80950f1130407040c449400071030226001508070390103c02d110854040c030782680c0584d2101c80030705440b00c0a40e00c3c109021103220010498261341d980c46154040420407285400388100000c43e820242a020781c03c0e55a9000700300c540c2246911183d15070081c90303110041c46c40401e00004106450840f0002c80e1040c04d000c030303011041c4a070500c0351102c07901c00070072196614 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 173897257 1250 173896007 173896013
    0x2070e01090b0420030112080c070603020a110d1b03020a0b100f0e09060105010e030c040f0b03070801051e070912030c0314031509090708060c04090c02070308040303050a090b07 78
    0x34842c40190078800c5082240c0740075803d000c141e00d07038403560328101803600d960700307100742d2606051140d1002c4441b5a000c10110b00d20110602441000d0700066a0140c3c3e1010341d0400189440c8050000094070380103946040d0300503401655948107083d800c3c030300f040c510480d800e06904040350400c0c00303000301c0c1c103100412000d00354666200040c0d0b00b50320002d030001c90b150351824801754011202e200c100d41c85a8018051980240504400c00800070101c884004c1c011000c54190707070070301641c3c0709429111907108580d46007e008500c050280c00e0001c204a01c0c100105086030700280800c0c4404508000106640d18403451228005d4152074850354008550703880c00604400d0113510990000c0d00400313a07880701014190440b805000349005010128171144100240b508010b0001c00e06c0d4465a800052914000d01107070340b207100840500c680b030f10f241c09299000d9560f4400c6210444d04604e40034400a0010019601900c0c1c040c034005454246d5600d0944a604e20790b080110b48140100c1c2c86410 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 173898507 1250 173897257 173897261
    0x5060a0606081b0f030a02040918020913020f0f04020c0601150f030b10110f07031b0e0103020105070809211606050903030a0320070c1712120702070e0109 68
    0x440e40700396a00781c2180e580c0702001c444120a40d00181032200c0800542d4034244034000515001815000014605030341c41240800721190100025104140c3d841d00c241945051030585511442c000c0221048000641c0010307901e2038110303030043c0704045814200c0490340301da0741914075804035082201d0480d6100c10884c502001e005c902d03540010340140220000304e02c280103441d80d210016081c06c0c440e00b4071440c19101508200c40c00c5040f441005002081000e0410204004500442a5000003504454107084940264001030142141d0200420050340d010044a14280e046200a603d0701c00440004884c5c1901c031b21408180c0282c40d1002d07100d11400f24800307100d403901080740480140c0d0f40400343c03498005c80030956410340040c0104006103010b500a401c0301c480712402140160000388019550780c02c900415220f85000b414140304159042c410307000b070455440d0040c031038004072008081841c4108805103c6020a501c003241d19140200f0003030006c0c00808503803810940c0c581200c640 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 173899757 1250 173898507 173898509
    0x60603081215040b0d0807051002031501090e0103020a0302060304050a05100b03011a09060112060b0d060510051303060e0f01090b0a202d0c061611151305060a06 71
    0x3414020041c200b5146410722510452120145c138640e4054119250550260046441900c00b030140403030355240c00c0000d10086219100c610143c0100c004060001400139005810002c120f030100001070000d0b07600e01c6406030840f90b048a1507542c0755294a405403c00860440c014581e01ca03ca1120000c0741d6550418030401c581a0000c00c80c1c0c0e100080500440c07101910215000303480c0e00007007060b5510940314423035150b0b211000810344a998000c06141544140c946d445007039a140c006000600d8588402c81c2d0301001c0d80380c503c0c10f1455500d075044080350030b171000800c0c9a0742c41d895a0130445c001d1000f01010810200204a09100d030704003010f429070100e64040d411450300c0081c0b5400284c81c2d101c0039041c0d020460080c1051400c19034040d40842102d1008910b54082144603d09450407000340341a0503c00e000c0c0c2190b05042c1b5a40282c0310102c5008028052840c1300c204c00708000003001079101e051180825000d0f12013416014800c0c90880f000790141c0919030410000b0207954020740 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 173901007 1250 173899757 173899771
    0xf0b0c06011e0e090d0e030109030c0b0c0918071106010602030a051804020a0309142407090e0709080d0305191a040609020714030a020601120c050a060e0109061e030203040606030812 80
    0x80b5104000801f05401c072200740b040280403442ca00150000700c0c801c480259840740d44e50701c400d803030800942d0000e4685012882c82d2142c1101e044204204da075401900301070801c1c0348100034186541001e0010f0740328002c2180d0702040240100e5100384200c0800c202c0e15240d00044c104558859010300000d0103071500c40c8058034411203002c00c41d50565400100318800c22000c182034885c402c141600c00400d9034000d40070038100a089403020550302034041180f4099030181d140c42d0032080c904201c0c5418078019009040601d49004c0401c04d40590503450080c64100c04600010046940255001192402544142c100380f40540208140030994010640580075003a0000803411100906030f0b80d04c10f00c401040144c205900400c03000f06005440d881080c4600c0950448d140c03988007050380b22540d0b81c0701ca00020318045040b1120b58002407200090b1540740351402c44070381d0b017640d01e131000c1c8440300601041683c00030003d41131001d2030780894041d5a01c5401d455980e144110348a0400710306441070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 173902257 1250 173901007 173901017
    0x31b0b12041101180b0d0e0607080412031103042a17070905010303091a121009050708040309140f0409032604050703020607030314040c0f0b0c06011e0e090d 69
    0x8505580200c0600105545416502d02d98600740580802c00e508015106d111441d10758407001002001030080e64403c1034140d49468040c580381c149801c0460400750800f080c5840c100a07092020984130032240c2c403680141d24500341e0300c09172809000080031180328084c00c1600580c0410018000d00211018840000440c0c12854403640b20004a03803081c0f00c0240031612401c810001010403115800f0000c51034200542080040c0d81c00c0000f0020446031320f0902d058202c001c0c00540e071580305168000c900c07440c1c00c890600e07156a000d4040d0110b400750604564203000749a18a540303091600d600707414058020300c100715481c903024000d80c0d0203030411510158029440042c159502e400c05129075046001402c0461075a001d004840e4451281a02015166200b116184e07440003c1540100c0c810034454069030300c0c1c42001c2115003280e810031712070b0910420544d820b0490009030f250540c0d103c0d000381c4c2001c4441c00c08503018050154088503114841c20100300f20b070705000c6803a580e24900d986031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 173903507 1250 173902257 173902283
    0x708060d1406060a060e030627030703030f050a05061806030c030304031a060303160f0206070b090708071a071407080d0807030506040c1e0509030a06091e030207031b0b1204 76
    0x810307a0346100c4000101d415234442800200a4211400038001600a080b409000c0c4810561254110303403040c181a00480d0300c40340c8645000e40644140d40e880420000104030f00c0c1840000a91483c00808141c261107010401040980da418400210049001001c0320b03a580e40e82e01d05883c0c0c0c0c0c0c40c0791380c0d081c5000300b40c8000900141004001c549207001d1440300038480e83c00c180d907040100d15400606a0300308406004c18800140003180d0503004500e000010140c0b13920700301c405840c154280c0c0100c0417403030307080c040c01c0c030250f0100301034a40241d4806680c0c5503814040d405145007008941c00018a80f00c0d4a26106445411072484c3d8000c8441c0e507010300c07060f52013030188800c1c0e80b02d6094110000d10700300e041103505c0841d401e03c00d401c2c9000b0b2612514152800000900d01154100c051788c10580c0e03980d944c020010a42c500250b8030016200c030500c07002e22510003039240d805501c406414940f07401c0181c10020a102c0d41040600103c80010703494107001e07a240f200a0400312401c4030902c1210103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 173904757 1250 173903507 173903519
    0x31060501020a051519091a010605041413020c190b090d0c110d081c06050f0913081909033c0c0806072c010203030708060d1406060a 58
    0xa02c240c1c6140c004000706101d940c4200a011454002440c0350042548030910091440e02030240e00b004030701440344c101001c0028180038500500c103078824800d0080800040204040e02c007072030381c0c0e4000115001d181440c0d0315400f84001e84103086810095004106005000340345c05002940300f14001e18103880140d4410310070a80e2400001c2a406c0800c1000f00040001843c509014007100c42c09010f1900707030046552440c103a078000c0d401c0e00054030a110300c0e40d01001d00512400e00140411510071500540c001c011a81c4090050000302080020b1507045080c00b000804403502c0d0fa0704440900208000c17802c0042002401c0d0004442c00d01840b140900103a1201e10518911440003480b10b401800320070300340c1c10480c0940401c81c0c045003005130000703407031205005103440360241c4e44500607211a02c0403007020804800340c03044090900300901c406541d9000054035403001d140d00b041030725601c0d403030002001c02842141c01014030500c10410025030101046a9025130381c203403a50700d1150b8881d4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 173906007 1250 173904757 173904763
    0x51902010204060c330c12110702281e05010e0f1018030602030a0b0105120f0a24170f12070f050708030a0f031112063106050102 57
    0x1c8103500008188140b4040810006071040d4803d9040c0c106081c007451120f40030902d441701c64809030002ea0354420030341e45c045402004403007445501000402502d9074070f5039030701c6a90145100185c040d4810f0300705084040b030111220614049000d0b01d130040c05994511039000804110b01d0460701c50182c2c040021a54002c1d03041d101100c40040c5440207210103402803005407041d48464904100310640c0d0440039600c00031000c00038501444000d80e40746803910544050701d12000d4001c0c1001010003071a0404420503482682000a1a0a101d09a291005128050708007100c992001503030400000780d0101e030490008007100e81d0500c1e00400301505050064079040d089075400c171180c00c0394004280580c081d4004004051103036070700c0c800103140e80e100c1e40c3ca0507100e40c011501c641e2000401e80c1ea80d070b40110100c1c4031803030145000d0007000c1200c5486001800340d07261080c00200303503401060503540c9041600d08a440100c50224842442a41b04c201c0315680d10803031240d02e403800703001040f554408 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 173907257 1250 173906007 173906009
    0x5010b010207140d140c1003060503060601020d0504090509070302060f030603010f0204050d020d08120405150c03040c0506030402150a030b040608030910050304030e041503021f0801091d01050403051902010204 92
    0x1802d24400c000940c890840ea00e400003900005e03401480303100030791a03507002c00840500703a482d0b40006040b401c0005242c40c6c540080d2a090555211480b880c10700c40d07202c0d084506482041101003801e40321246098039140c5c5075000250311800120343c04684810f410013540c802c0310114001d102ca641030b241c148040f071140d03001d40364220aa201e8160054180240140b60041c86480013038a800d550f803980e0310020400f0b0f0780031a00c3d078016040420000d02c0a00c5d0081e0400b000e40e0b4210b14606055559121915a83c42024022203002c0000b4041d551924619860b480e1010441951101080002001001c846903054843c070f00d030a102054070a0000160740c1c090801412001c20000c440c9015181c07900300400407010005c0160b8034008540741c50050039240d90701c114807800414114410007002407412500d001d10315080c844804181540811068112400c07650b0009040c0d5070000f241c2c041128a503401d8030b0a44c241810700007015404402849500007280354840d0b0030100490880c240d01c26 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 173908507 1250 173907257 173907259
    0x112151d0a0504170a12020409050105010f02030a0e0405041b1707170307060203180102040902041505031b09031e0703170408030904051008010504050a020f0103060b070f03110a05010b01020714 85
    0x107000b0744c0748030992140340280321144c0d540c02c2080c0911100c000c200305a0f44107402081d220354648004222550304420481c56003041e60014508000103290028004c51011070f20314403031600d81010400340122051000f002c5a081c1034500c8070f042e1200c10400301c4130340d9503000f00c00c584144800020340720001c40f907030440c1c2d04510019510303008007510340744043d400140c20700dc4c00342e44100c16541d0740202440188014501e4810250325107150100d0b100345030664224840601c02c04204010841c50f03006060100200c0180845881d0140707400400c2c6080200d01401c09142c0d6074882c041c8440c03000044440403a80b081415a03507051581d00b4074596409a031260f002c280d4800d01c44e45250b0b103400c2d00041c0c0e02007443c0711080011640c0d920300b513080d604203035415140c640113110795030250300b00005c00405a5100382010b108003494060141d026100d42500640491000040b441c201072281819000041404d421188052920704195008003a010343d03c602501c600c3d440050404001d01c0c00d00b51004d8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 173909757 1250 173908507 173908523
    0x3030408030f0c16080a0501050a11070f08090d0b0114030d0801090c170f070e0f060703111005100e070305011202040b03010f0c0306090e070e060112151d0a0504 71
    0xc0804101c164070f40011002e11014018014049030100c010f484c080002c00040b40108103030202c1d420400c1c02c689001d054018071500b0072a40740c81520200c422aa81294001040d8a1080c4503040c1030080340205980194803082020780c2105000c446100e41d4142d9041801c030406602c070f0070040503510000d8014070008924030300c00401c04007a0b81d502510b0030950f54104622041140c1c5000d2219480440c6d100054501301d60a210300258410340041c0b010000b0b42c0c05440400d4071000140090060aa0003402c0103405826107615075400c0c004160b10f80f000600511060030040d04101c400d04503030040c907020003043c0c80050203562003405114129031074411410f5140c034040e000d01c00600b280b5981030380c0664880d401215050b45038801c0e8603a0038004d40d40000c1c914182044401924001441194941c2c40207006110303461054964640180c02424104600f040d1b000f081e42c05001d03215107403900d4070901540041e10b025181c24103800c9071318081004156645002c003030000c03682c0a84010704204 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 173911007 1250 173909757 173909767
    0x5070312020a0c03060c03050603340512060108120a1e230a02010e010504120e031203010e06040606020d02060a11090d050f0c06120c07020a050402070309030507050303040803 77
    0x90300900640000400c0c0d1041d54150403103515400031101c03055004452003540e51a0540d0140d516200340354114030100c0260030514112103401c002c08561061890880c0c004404030066680100c00b10340007018040c1100c03502042480b2082e884132030074820382109004248940d00c8a11074181140d6a140e0b40d0785030750b030700b54008040f00c90740304802e101c1045c00d02c2040079000d8110002c9074a103030541c0b100c0e8a0565500c0c152544000c0c2911000c0c40c0384803840c1c2c106424000060040c07140240001e101d4540810000d02c1c1070300003480d01180ca2410900c800001001140c03980078003c41500c00c007800c0e14203200c05903403006c080380c1e02c6a1021a20005070040808507035902c3d1181c001c1c4120f100111103150400a80000142c010103817400d0071a0236910000f150108000c051081d4840e1400881c1c00e9801c3c042d807121900000e400050031a40411400680c0004540d03580c480f010107044050000c45d01d90315145005010b034403907400240c1d014410380348002950b14001048034280d400c002c0c0a14105 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 173912257 1250 173911007 173911013
    0xd060c030c0504030519060b130c1e08010504050604090b04120306140906010f02240103050d030203060319061401120b0624160206270904021e010e13090302060f04050703 75
    0x5804140c080720740d10b441c2c08c000078595641d800c0c0426280660038000694903440c0501a02c040c50f040030b10308002e1719505011003980c0d0884010384c1110b00c26140401c080d80d4080020b8000c01d0440c0009008842d0041484207002030070308102c49840344c58030100041616008407102240701c01003001d5200300d030700000070340e10b510030031064038403540900480f4000c021840d003001f15051103209603e420040040104140441003005d01c04018141c1000c61550030681e0119440d00900c00d207000050300d03144030700010030140d81c0c4251007120341004030000c41e50b100c030600103905010441c16541130410201158141c40e00e034240c0601c0700080c0380d160680107810200080701e0b0b0000140c88612074100018500540c890344028102100b003540d40c1c80791120444005888040c105d480b03140551031100400c80141c0350380c89038001c100300c840d591241506224004a03550494024034507040052160702c0c4101402c20f407c00d0401a209800b5600c1c0c03565120100499010221409845540521010004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 173913507 1250 173912257 173912293
    0xb1305150405010e01121a041b090312090305070b0307030f060803030106030b060403230712030c0206250302010b01020c010c0b0105060903100e060105090609100605030c04050d060c030c05040305 86
    0x10800060402e1811100c51003858011112984130034120622083c046040d240b23010311030028607040f000500e440300c00b503044000381a51054000100341d140202c00e40c0b00024002d05c10040203581c4001182d1155445103a403c04c0341e0000d6810402007030600a552100240340d01030b15040d00c483d0300040d804c603071a1041c2207020740070200320190000410000400481c03000200c8240700e18500901101006a006000c0e28003089580503c000340944000c000020754404502022150125580341d250200c0260118900d0301d0103501515103801e0486180405806420401d88500c098007a210701c5505040103480d42c01080c403004104682901c014081481d1040c040e20b100140541114806421f003150201103881041090041e03510120040041c0e181c2151819408502510780043d2410442c80b800c180020a014110034403401100081c07150440d00182e400801c001032101041c04054101000100258810100000d01b06018112128014030131507044980c0b0400400b000b40d0000c035184030f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 173914757 1250 173913507 173913527
    0xa14060d031e03060b0c0a0309050d080a05180d030905030d05040506070807060e030301030b06030c0607080a030b040e07060809072103030507020c09010312020601051e0108090a020405010b130515040501 89
    0xd03d940c8140201d00c400030803018026602c039a00080c0000c1da070605000c0c01801c400c1e4061445244403408550025501109440494581e401c025449001095924103a01541c200c06500480c502d03009005256100350104116602a41902c6002060140031241c43c41580211a0090810064040018420070040016600448000440440524655045600a038415504041e50005103d050701e410700c01901059002ca03202441c050a6a580340014000c903902d02040c183e44010340000c549031030f00700e081600c01c984191816a03440d90f00140445006851494070b0340300344c0e40013150444461030103101758a503115540850303030000d60303080307001c2d10f401014001140250f41802100307840d0410494082c44c41800528090781c201c6000902c2c010303059110b64451602c8103210031000b52030782c42701d07031a034542031a0000a0fa40c4421040b441c007e447c0303c000390041e00d801d000081580c0c0180142c006550755001d000303d04c5a4480401070f0b020000055505404000c1104100c150b0088101076 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 173916007 1250 173914757 173914817
    0x10e03030f0406020f070b09010f11011d0109150b060f0d060905040804030201030e0706051c020f0a0e010906050327010e0a0c0f0f03080f0f0c0102030a14060d03 71
    0x3a1412501c000c86600c0c0390016405607015900c105042c0d41103640500800c00904400700181d8100444140000c00b60021484c4460078000386040c00c0c14501000c5d041590310314290b940030000d0030040c0b10070a0007052130708000d48022103001108041d406407405032082404000707024606040061800081c541d00815018640903940d81002565084500501d44164002c00c8410f1304c4501c1e41c0005030a80e82c100702441c5540d041600140072294002c000d446440425040304004880004103c900034800c41900c0c052845000c40c002601310f0781b105000c3c841c1d02d0280e961340550380c2c4e030740d006403800d02003650105c02c00d1080183c0b10904c0802c0c0d2003a100364407142000490300010800c00c1030b05140c1c0c111819120384100200500c400200c07030385064001d007410204a800c15107162114001405812595081404000340200440042500352424509044021913580c188030146400a201804000502c805024001032540c41d280ca42c3d112003a425440c0c100740b24941703840b488020000074401e0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 173917257 1250 173916007 173916013
    0xa090c050c12030a2d021617040906050901030b07030207020d23190512070203032116030911040b0102071d0105090603010605010f0309080904020703081e01050a05010e03 75
    0xc808542080b6408030103154480a6079a4140303c6410f50a5800c65003002010041c502400c4c1640840320180c4001401c0c031020050f2a49101c4c44a8145910280c2e00640344214150030208103908060003041150350880c000c200e10f558070310902c0100381d0b0034070000d05480c0d00840062180d07070003600204041440103050191403030b00c2c3c0d6121200c000d1482c01c2074440d0312386011b0301048007004102e00205442038495406030038072140d69803641c602011090034041c000111702c5008648082082c4d07500900340300a10038603800c9405000681c0d100031604c41c1d1040038642d05003802d441c020b20588240707540044080311036014030000d1202a2000d002c105045200e441400030303c0074050601c22000100340300d08210f040d450541040000c09016054512903450a0030070441c5a0700714190001540070390a01042002c0b06003403250a030300580351040d8100707000007844401c01d039000910b01d00c2002c07491503821031144180b8100c480f0074000d00803540c0260850909000642c0a0000044075120007821 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 173918507 1250 173917257 173917267
    0xf040306020309030a0305180a030c0602090301021b0705010302070c090902130c0f030b1f0813050d0903030f0c02030304090f02070f1b0801020307020304060c030e040e030a030b09060a090c05 84
    0x6120308a9104032282003040c4c01c00b040030301c01d03545c0c507010f907030f4015000848121070410b041050940390403002c0c5c4000c041c003c1c1c0c034120344104041350b0161542098020000c540361071070460281c94014003042005003a0003009004211907002e07100380c032b00f4185c0041d0301050032420f07c01400000c00e4265030903070384a40b001c03a4000d1400c615001d400009182651200c0c0e0040202c0405415545058030a81c07241e6540320a140c2c0585d00c188500c004014140340207209501c807003850089000203080054402d005111000f0811074100f001401224480d640d04c50b01001e10135030895a24400b80d00007549030300100020031140000d074200c42800003542d10018501002541d4521480310b00348bc044920a040001076100014160000030040c6041030080d817461810300d100030b407244141d00a850038044582000b10a0501c80c4bc0040e0003110041c0c42088070780e0301d820000c1d13a00c1d00256404c2d00040c4c03e080014a81c0d0401c1481c05000d003101030a03214005003003418410183c550b100c098010032406102d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 173919757 1250 173918507 173918513
    0x180b0a0c0b0408090f240703090f0e070809030a1409040b0a03050d030b0613050913020402030a150801020406090e13021903030201050f01060e0f04060b0f0d18050607050f0403 77
    0x881d0003a407003400722035607580c42c1c60203110504690380c4c0c185e8030605d110b030340a100b202410a8520030749841d50310103940d66074403403178183c90350b40c55500546c0d8945c01141000c030350496000c3ca264046c4c1e0b890344442415a488040c034035501d104648080001400900c02942c80324070030405071500c00c000a00c042003a40743c60020900712003003070340250380507805102d00002d02c40d01340c421500710174002c0ea00185010000c64040241d400d0350701c01c182c02400c142c00024140140748800d21011070b4014029036690900c2040c520162240c42882c1924090b04400020507281c14400c5401f1108551100c3d0205171500b4a840880e203801001a081102182610801a03884880100c5404240c0e80101010390640c14001c1c2101c0d00141102c0c100c1640000610040d07402a5495660910444071041c5218030030012401412465000f85241d15010410701c000d031001c0e00280201003001c030000c02c2280c5801c0d61052166036100006415030b0816800300d18850700c11030040211086500c01540381c66030382d039 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 173920863 1106 173919757 173919773
    0xf01030308180a0f03080a06080610060806120312150a03111c0c060c02361b0a050d0506031204060302090d0b04110a06180b0a0c 57
    0xc444800c103024100410038440c1c0d8000ca5910a04c606440e0180412000741d40800c019802c00071b0204419100185180c410042101c40ca22050b1411405031101c94020f07004607085040000d04010070175040004004181100200c800c0d580303040f10000341401c0080890074850280240d08002041c418201c01a040c20103c50880062161094001c99241c5100b0f00030048030b891000001d03165008242c014905001fa901080c4120030410040c9140107556025010040c00b01031050b07074894960200c079072040e03025800e00181d81c6025480d602d0364000d06a45000560000b5403444501342c5801142d8010009a00400050100d9040c90703005000318050031301096800f040c01045642c8800031020000c0c3c1010b48000b00c2c7c1440d0401055040000d45094021440208002980c500c1040d20a080c54444030307603800c074a4108000100c01e41e22240a460801010798074420106000c5 = true := by decide +kernel

theorem cover : BRFrame.Cov 173741007 173920863 := by
  have h0 := BRFrame.cov_init 173741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 173741007 ≤ n) (h2 : n < 173920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
