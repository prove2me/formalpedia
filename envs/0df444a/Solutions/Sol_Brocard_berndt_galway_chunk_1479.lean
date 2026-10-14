-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1479
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:10:41.51314+00:00
-- url     : https://prove2.me/submissions/0a99c7a1-10b8-458b-bcf0-721200df2ba4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 265827338 ≤ n < 266007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 265828588 1250 265827338 265827349
    0x6180c0a030e16060804030e151b0c030601140108160504031b050301050c070308102102030a0602160b07030e121b070314010b030c0d03050307051b060601120504030207050906 77
    0x140f41440b50316070512141d41d100c006100d22425501140003501405102c201403424108a2046400c40394525150183c1d203480b400b0100c0551002d620140105200715000c3d980600580d03000705a100004a00c040d500300004001040c018580156007c00c60502d000d040d90040640d0152076000e2340004401100219002d0a0301056202d0f592540c20b2a081051800401000d00142172080c1c52700111500e41120300e20040030f0303d0041041a00740d08007420a4003901c1c42e1000a040d0018040e2003c0741c0040e151402641d1107284201c0f00340c06056481c804000c4590005a8071040c3e41c581000104100740383c150300d801404a541e0461100410074003450002224000220344441d41202c3c20140d42e403900d00842c4100002150700365282c20300001c41801c0110b0920008080104006000449960291600d41000c1c2c05042004414412031a107102e642881921782d04541d00203013418600880010302240ca80c40a40d40c0b40c504080c180000030303400081007c16a101101c8441c01651000701169 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 265829838 1250 265828588 265828603
    0x2160807024e012c01140604150f090c1b0b040308060402041e1502070e0109090618060b0301061205030f070309080303090f12040605091210140906010e0402090406020a091a0306180c0a030e 83
    0xb022b01503e0000280b81030306500a504403a21504c4240f01c0d59148052480d1071880100e016004211800000d00020b129900f10390b413060004000505250b1240b259103025010080009a070340c000f40014000a0340300d507042c00c1d00b9021880185a01400c0440e1001d50000c11f21403c544940c481e0500c1741000071035080942d07000c080c1901015008914107110010f00000507481e0f010f546450400700c0c2c0f02c040102c0c0380034100c1d006402107140500a00d01c9c10b580e40d002200507020442104004502c14005000840c00f0305a000c000380f0041c16a6500305040040d01942000039120403c4104052500481a00c0c201c1104460401200d4520700110782419180510291602d140240760300c460b0403102c00c20f6024108842c211009681c0740c0b10440d078101e2080c0c402a520041d006c0c000b5002440369002445508400e00d00800107070b03568041c0b0608231305c440c9940074105d8004001c03c40c160600e10881c40c100300403120703147c070541411902d011003482040c04035010140c990002000821003041300c035 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 265831088 1250 265829838 265829849
    0x20a08070302010902130203160c050a05060f0a240b07061103010603150f21051c0c0312110406050d02160807024e012c0114060415 58
    0x6640e65a5850003d009080c80c85080303128050346603002c00142c0d414401d491268182840030071800584150503281103078a0f08048a407440340181c100300003042408200e01545104c00012480d05018480c10280c490942e01c145280511f5500c604801840740311076011502d80082d8160340c4c50751030601c2c00103480e6290424890000010000a000c0e070b00d0b500280a00c1e007181c3e2004101034807144542d009141034481c81c051002142101c110303000300d07202e104c187c0e14418000c1b1440c055081121203812400c0c035403644046403044030b00e8030505030850040401014a4202004043c1c00d280c01d501040c007a07805072808212000c500710004503807030340c1182c204009140e00241a8001807512040c41e910511080f401000b0120400201c103808180f0128107402c0c20b85044008000d02d006038416040c501d6039641c403110000210310701000d0a1207600400405030307103150828562802c4072010b012264120b9203441c0c2c507040d0f00c0340c10200d148001c44d070003041c11203001c07950b01e0343c01150041f8100030b904038 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 265832338 1250 265831088 265831103
    0xb040314030405060105150c0f0607120b060a180f0605070b0f0f18030c01150302040b01020d09092c0105070206130b0103060509030408100209010906090510110f031615021c050403020a 81
    0x2119060000501a842945c95580c1d0b0440700315140d4cd90000d417640aa18150491024007943c15601d010f1110781d044c2c021066141548581d5401c480034006940e5407024000c20030004042052101c14840a540102c038440d410105042060303190740940e00042000c2110300d000c5080603421142402102c0b20420b440c0024011fa170117421170701c45a03041072321040b441145000c004403607550002c107000c02a0059902c42c00c0300310745044440d0002d41030ba10050920700303417a41c90480e403001100103035081240c1804000159460700c10740180c03500401500101000d00e80110110010342d1003c031050540798441000300340c60720341c501c1c002e14500864004816034000d6070600c14903081d15a000d0034000c00c0c240d8404011595036041603400502038022590081c00501d200d483c514000c000c0e0801d03840020b4121040100c3d1300740040e04641194021174152111050f0840c140400c0c1c180c100c0c07a024100d0011450700c15400101100048440003010381175407074500003024180207004281320070303400010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 265833588 1250 265832338 265832353
    0x708041d070f03240f05120706050a1220090a09021801030b0a08031204030e0a1802031308040b18060c07120f020603010b03160314071b020307030b040314030405060105150c 76
    0x2500002e9017128001e6600499000c14646440c2c034001038003070116a110b80341c1d50710b06524150304a03000345204040e000e2103a100d00034900004141a030541da0500ca000c3d5160b1030340ca0200c20008000c980d640000c1e1603074010b0001c0d8010015a8054208030f550908000820b144540c0100350444001d1b80094280d02000c1002c0c0e800c4a4614600c9115900c40d680c4ca11880030341c0810003980041d94010300c900754003180f628244460207a80150340040b0294001111380840c0d03540c80c0c203542d01503000800b58880200e0817909003081a1003c01908400322040d900b007000c0f00d80ca03030755510b00e58070441d0911031900703003403d041c4656010070a4445070082c09042d5250b0312145c03200120b91080c2d400c0d006c01c41c00c8400d80c2486a11030b100e40c40e00400c42c0c0f00c3e414002e803a201c1b0101c8400060f0780a030400840d2691008005035420401900254411413218441346058280907102458110058503a08020030803c80041c01c007160450545800311511080c0112013410303207006014903000d030b070b840d84100700 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 265834838 1250 265833588 265833599
    0x18020c0a1709010801090e120f190e010f030921050712080105121603080318030d060801051305150c0f0703030614030d0503010506090103020f0708041d070f0324 71
    0x410102c00c003a02c1d00e0b441c0e41d0b41c59840301c0c21141c8450742203c0c0c0e500040603080544070454000d050400152074181d0800c0d418881c0074034420010b0f00810086842407195000558100c100d070300c104109400c041203002c01544601c42e032050034101c01c0b84c99040380e00354807035440c0c0104140c540541c0c2010701070b4001c125884d8050400e540170701401c1e04c198084000203112000014442d0308103181100740c0810036155903107410040d04003410280c070030b100c0c012400400e50b004002510102c8078100001c1140d500d000c40c46800c50b20050b00c1d0100c43e0250800c80d8000c188001425400313036051407414130b0141d442c7c5d20000864083d11160f1980a500015200d041c10ba2581142040e200000034500340804481304145c3d4a03d8440d1041001c03450600040205140803800b0303080700c020604001d8905083c40c140c90ba9030340d00503207045503404c81c0450148058244050b2403512910b10b01c080100300e0901d100084c00601040f1720031810951595001c50200d406080d014861100c205c400e10039454854 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 265836088 1250 265834838 265834883
    0x4050d1e03050d050c04030503090d02010318060603150902060421021f02060601020606013002070b010f0b04031106130302030f100e0a0308040f030302120f071101050118020c0a 78
    0x30405480c0a0038940031030f4003103445da0f00711022254000c0055280c01000000d0052000b00d8000a80c10b065450300b44940280f40c071103c10b80b4040c8103201c0000d0550840ca01a500c0a030070001d8011803e00e8a03401d40016214403044030191819140000300c22803100c040d401c03278203200280c000d4201d03108101802500802a203081001104d079000c0d5a0346964140c01244e940004a9400d40082c0d139411603d10300c48070800002000c10808010210304018105219050383e1100d1421503649c06440010428106800b014101811045482c1c9203410302d10380301c805d4a201c550b10400d2003074100180c0c3c05500702080803010000c65000c0c055030010300c5884072540e20385010280300c81e80c46040092942c2181c01c003240c443c0070203916449020700d40d25162110b42840540c0f101c200c081c10b41c01c00c8040701c10103000d254184540d004600400c19803600c480c004200385000b00904031180e05100042c014682c1c001441c1e20001844940141c031217078526196882c044204401500b41c5840008959030381595 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 265837338 1250 265836088 265836097
    0x902070c030510090b010b1c1407080709030203030d0218100201050615040f09180b0a15080d020616090e09160510020303060d0809041509110a020304050d1e0305 71
    0x82c40030303250051028003401041d103010781801001610410010b101802921700038100403d09502d10200c82c0c10b268004204940001020801b40d0341918100a00ca550042c1260b5005465152002220b451a03001c60742c0c9006400c082c02d20742e6000f0800c00c8031320300d84210b04961994002c02201c083c2d03400340000b90003041d0640d0028041c2c10701100145000010208450440d030a40c1d0001c2007030ba00d0045a20000d000c0c2c038002c020040189142c000202c0c921400541c001c52800000142003d2103840030b04078640d880d4030402882d0040703d2862243d03030300880c595038040041c1a090380440244081125550029008000744684510501000c0d400010f00c4500341441006280744045c0c46004002c032000106510b9001644100001046070402815031250284140e0308241010081c40c001819118040204059041c540c2420414030900f4003441400b9441c0d0000300340760001c0c042e8001d48a226501a15000d1031442c041c0008100c03101c100d41d02d800580000001d800c030680c1c034004001c2d501 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 265838588 1250 265837338 265837343
    0xf031212090209190506011d060d090c15081605120606040b0a0801080c0d0807030e0105040b04030605090d1b0f02120d090311030309010806010305150406120309090c270902070c03 79
    0xe4500061030950150707035110f180c20840c1551240046041c2e0804c03c0f280e10482004c24142e44030312f1004006858201100c0c081c082d1981d100f8040d07404644020b14000d80240007560070f2681e1188507403146e070884100c03140c018000100380c071aa0f4421005c54420b2103141d103c01c801c07480c0007030340c0050f06d60302c03080c0300e81a50684802c2c0d504014009042011200ca0840b0107440e01c3e90812884001070702540b1614020b000604205040c02d80c0c070700308000c06421a50084e11140e0310b401c01c12060300c1c0103001e40303100040d0318207009c1605030010101c3c0c0200651004020900e00c10702c1180001d655420f0228003040340303007408907a0610643c0000420651040c03200710b43c8020710201500303941ca00071003660800303070040c0d403559a1695100300440180a001e04441469071640140011a44890140b680a80b0000f4160303007003105035103001010008142c0c08414017502d04000700d0311003640401908030b65101441c44244248990f07000d030321034540e9540418121407000620b041000065494102103d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 265839838 1250 265838588 265838591
    0x20313022211190503090a0609030c0203010c1d060f250201090b042709120f0e150d0e15010e070f0513030227010b0c01060f03121209020919 62
    0x3001d880d5a110340591543c3d151500c21941080c0d141600c58009598806464002c90f80c103a0082e8860700c08560a0302c5068001400d0903e100742581000d0050785008030052a0a10f841c113103c1c03204983c20030450841070312690000880d9824028258180c0b80c000c110f15548081c86031603004207111203001098201e02140300d100f800100071050030161002c95420182c146819010302300075100c0880b084052095441d074880315a030205001100da9404c03140541c80d2141600551003015200800ca5141107200782203104101400b01044030517259144c3c10008046800740803014103900b010840d1011301980d9041c01c00014160300381c0384086010b03910030385a510b261141d0036800c03a80c9129525448020040c4000c0420050900580d4660700c654841101c51782d640400440996a00302039206540d000004540c2e655104020310510b0010200136030000038180c915a100028030010150040a1002061340482c107210180c0144400d00c1c1e0040c40014149000740140031629000d44400500c117 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 265841088 1250 265839838 265839851
    0x16080309030421080409050709080a0302070906050d0f060510120b1f030f0f020303040f08010614060405030703030315260606120a0209101a120f01180203130222 71
    0x181000321a011504620400e150606195074240581f0001c1c00500070402c4030303680060582428800c00703056511070b030b002d00f55443c03030548120144c4010b5000540328404140c1e0b0000051084541540b441e40e002c0da01091942e601c0390b6a034403505103544070340405c0300b0301034105040001000c506032280d0b800c82154032440c000c15082e0b921042c040d0200425100c101002e1002148c551031031b02d024144001d044a00c0c1603116040f9440c1c9044644c0200050fa441e850b003801001084080b02154010595410b414030346443c0001e95100b44511000d02403699942d91000c02e120401d00c0c40e009081e0b50920310740c80d01c58001c181c0d80c1c24812400c11100ca4003400000c20b0f500d140c400c0000d40100d083d100200b071a541d00b5001c100003010043c0c1a02e207040d01240001624141ca0036082403803004040c00e407904e40340a0300815401040c010060f81ea02220381c0014042d00260010b4019242001400143c807655180c1e039409901240400c0a503004104c5040c035002e0440d61000c00c18040500003052042 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 265842338 1250 265841088 265841129
    0x1a04060b130b07080913270c17331905090c01021b041805060f16021b03010207150b0a08010204180e1203070804060c0507030c08160803090304 63
    0x1e40590303c402005428100320140300741c40c0188903504002e0351042d00140210341c6040e40d410f10340d07001e1801e07842814100b03288403e03c46007065540080994051041d203010010500b50707240c00400c0c1c501002187c0c0310150300c0c40e03642d084000c2c103001e10180c1c0702102e55003070007450708584103000241e640c005c074140b01c0015a4444007081d1365030f0a00c0d068005140186010004e01450003c00d12503940140c1d44203104005080d02c10341c2c3c520000d00500241079176080400c0076591190000b8141006800102e03812205603900180c4516100500040d4111820704100045e000e44075034140589000d4022886c07076591100c41e400722607000c1085802014541c0d980c00c0c1d403802c0c0d01441c480c0030052101c044800000c5031854000c1c6040c1c6c494001503500214403800401896003054640e60f000032400401c01082060034403504141c20018241a414042d40350307001801005d000c2801050303000b0219110002000200009590640c0304181e1912403400307402c025543e8005205c0c8481c40700c030b0005039004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 265843588 1250 265842338 265842359
    0xb060a0f05120906160509010804080306040b0a031218080c0d061b0e01020c0406030f02270702030304030f0908030a120e0703050a05070902030f13020d15090201030608070501050a031a04060b13 85
    0x2807d001038403041c016982d036441d12509038100511445e0030030784400395800b81c0d0762050f0480002d1446454640e5668461000c0240005840b01360356402c480a060144001d00e400140f00300c500d00101c944820030456842c04c0c5002d03100908400c0e60103036900a40b80703101e17a0481480350f007400c1c081c1c0c201c0d80d40120400c10003061750700c140f00140c00d04101c020040098204828041514003603210803502e0790020700241410000c0803551031005030404400d010405600c09a140c80c411054503000c842942020030b00c4d500c03881a505c1e0f21050200e00507080111003400e8101441004021068500706030b41c07411f180c2c0e1640c0041d00121910f005400c400701d080c504910a49019030101ea181024030703601ca420030301424003203407030603640058000450000100b08003190403603600400d00105040c0d10303d10000d01036030b40d19004041c958220200500c55030742d01c8000c0d9021883c0901d004240c4401508514078008585460355800904268002c100c8000d000c00411680000084c00e10001c0e685440119 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 265844838 1250 265843588 265843597
    0x71103040f0605160b0103081213080f0721020a03030f050903041502030c070f03050f0a03081f0e010b03071206050d023f100b060a0f051209061605 65
    0x1101160004400d01a903440f800143c002140420b00c0c01e82c40c0c0c0c4442e25480d41c4104242e000716002d4000140b0074182d007840c00400c075089010210001c2c0729404035511180c0c54090b20504a41c0c0382d10104410081c0819901c10740d072218882c41060342000300342c400c0203441d41c0d282d51007900842d080c01102488444c0c3c0d0711505104040b160091402c00f410600070709904140700102c80704501c424064000031041c00c0c00160000c0004030b000411480c51403600e14103121071801882c507250000c0b0701c400c001c01c6e0441b80c81c550240801c140c4030140c420030136007660100c000c0d422149007406007400104003441c424000314090f80440d00e581002c040e5582c0508283e819600889420400d1201e00d040182001c02506a49500c0302c02818028030802c4105d280c5000710291600c9515985212400d62003030910150303109410702807040c001c01305040040b880b203100c0e00c4169130801141c40c3c90070915501c1001941e81100c0e82484202850800c080c0c1241d4030701081e94095069103000206001843c0501c0c12038 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 265846088 1250 265844838 265844849
    0x15020304050a061107030501020a02060a0e01020316080c04090f050901060e01120602031506030703060303030c18030b13050609070602071203020615060f04032103022a0c040c0807110304 82
    0x41c114606108084134000d0b4081c10100702445000303c08000aa028005005144015402017a840c42c2c403062240680d0792009000185034410001c0c04280f010102c00e03814114542e04028083d03440c1c44034902100e01c1264860000c5a1a03e0740d40b09220700d5a40003d800741641c10000c3c0206a1a40b10215400400b80700c1c2d07100d10412410900000740c4c507900515440003c030b00760186104201d8000c51074690003200d0000c00650388420510030035402d4030a10b04500f4075480c1000d00180b03003d03070005207080d20b070101600084440d80001d040011240740d0002040d840029150f0303a051408516035954054003664004d4001c03500080f07a0300080b02d07400f04036150140c0c002c0429480c3c0500101111302d417821a550805010004d060480d00b0303010062000b90310441748106c0302e040c004c40401c400c4502d40480000c00d801000854011400340c030000707108064203200b40101110303004a1614105040701d040e500a03042401c040c01c00f9070000616881565641c0703806d044802d031500f05e1601c034450f60191 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 265847338 1250 265846088 265846099
    0x8060f032a03070302120a0203120301080a02130e03070b010918030e010804030309080a110f12071712011403010e010b100f05040e0f071101020a021b1305010803041502030405 77
    0x1c070306040c0202240812580340c040c0c00c1d41c141c1c2d622500030422894054000465070b034046c6400c4c3c002c5017810032410801d8400d580b0f5250a650424030324a4540640364400784c0b0400c48041380e550009143da0040f10161801c0301165a6501145003144d0103500c00d210b41101d552404003918024451000c00070032056260b550080441d1b1200300543d4040b10140041c2c04040d9202d400100164140000f05040325298031010884604140d4162a10843d10719103201600418414200f074071200084d110303815807003020f81120040035a46000c132402941d011410303d030000d0000103489401059900c2991400381c00901c0b0010b5110341d82801d9070890085560004103240d03411007150b204914580e105681c0b450014070b00782d6070740301c0500300d50415944064004e42c1d000c00d00078016005007502a104604100940c1842d2070b8001c041d4940321100740c10100030050302203107840c43e034400e0316202600301d03c5c0e01e041040b9611005220307030329001401400b00141000051181c158000400d850485000415 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 265848588 1250 265847338 265847383
    0x13050f1f080a03140d05190b0f09010510050c06150a09020a0804020f0103061d1f060c0618020d060c02010b0d020603061c0b040f1b230102030d0c08060f03 68
    0x804889504d031050700c1c920703111404d05c00c034070000305a400b86500580c00801600254a032418414081b10f146000c940e01c46d0070035449414580d01c580440d203045441c2140d90035248140345409851350b1082001c2c24089000c2d0307208101068040240e006202082910184441c030f807a038070050708a00c100c0c00060041000c1c140002d00528042c44050341042c81890b0101d03403560780f003500000c040143c1d0040b00c8c103402c1001c00c000c10711001c10840c0b0020040049003152251812001034032013054244040c1500352100305104491080d540300c030306c50a0f8007030080010034849003004001000c40244800042d401c152030703e541803908038002c1d240550010011407071038071541c0420083c210b485040403507170520402d000c00445c40d00300301c1c0e512450140c04101102011813410181000240890340d2030614242c400b0301c04c180d40c03240145214012814420f403510000f60042c0d2860146000c0c9655450a000c1c800d1043d60740a03414501130442600e601901100038030415440d120b1120500c1682a01c3d9007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 265849838 1250 265848588 265848593
    0x1707081218041104080a26030601050f07050705060316030c1806110109080f030702010b0105030408030103030f0207090606051e0f07080a0309050a0c180c1d13050f1f080a 75
    0x2841540102d40480c40f1503d050b0341e40300941c0c103007100880c0960384c1c04034960003406440d01190180c0790700d4044002079450340c941031001030540c0c02000741142d40400d011a440301003207002c104480160000428003601d0303207400e64001004100c1d106945001905107036a8114580c062801c0150361450504c5582e921f07810220b044071880d010640c4201d842d900d400b1900c0c04160f4040062020211041c81c4c15982e01d010070029080d903d085403103504001082080001040400044d681900e500d4500090260511a4101c0c40c004264004c02c00c01403406d0000921660450010a0080040a010094048100741071001c0d4011301f1060b04c1e002c0c0003004280300103141c1400802c140849400e00188151144d1a100e141020b100e0301241c01003550f01d024004241d06000a103481100100180030b0428004e100078611942002c2a03440e1261051070300103c2d940d01e0100340e0034049680801c202034030300302516800300c2c00d081c1e40784080b001c60101e9488081d00c840d1514001e231001500100241c8803243d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 265851088 1250 265849838 265849841
    0x1090b0106210c0f08090724050702030f030405030106060806090a02030c07050304090f0501090b18090a08071b05060703210908070b1807180510170708121804 70
    0xb4040428118001200c0c40d12244501c90880a400301d80d44400344000c6451002d80141070141108020740d2200b401082400d0f46011000c0c003907202c0007005201c240d0020019079841c00381400c025458022a8a41a160a0000090011180d003100280407030f40d540c5c102521108400d807129030304940c4000018180c0c02c040d40045801c0900500b0790f80c40d00d04aa29020f041d900650000d06e669900d68005040001c1c8601950303000d000c0941e01000b28102c400300183c00707504d1000c00c420200a050001a03072800307041c007088c4030050700070030f129a44001b2850315070404204502c0018100480138004030751820440c0a90f0001035058561030302c03072310708007050300248404042c0901c071030303034440b0100d500181304080604483c0d0311420b5010340f541400541c0030003440c42038004658503842854100f00901d09050746561502002a0000303250f01c806502c0c500e02d010980110711110300d550707401545000006000d40840e80d6400c01e5030144806c100c03103500d2602c101c090b070102607081c3e107100b081146041d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 265852338 1250 265851088 265851107
    0x16063c020a02070e070302070302070504110a030b0118030605090d02060601020a0303050c1605060a1a15030a0e120315060406300c0509030c03060f010b0304050109060227010201090b0106 82
    0x10b4012501c51540d101c440420f0f0090403a000800030342c010a00b0800c050701040080054030088800b40300aa12500302c80030580100c401901c109030300c0d455081d02c5a40201c1482010303210340b003c0024070301c5e12424510054030b001e0303c40d07a01512072a90700d80c842e0740c03003c0303420b5010700da050380a40b40344c4070765840c11800351030080c00c1081d04280800112050012940c0b01d240b0742e87c847c0c4050300252400c0c070061021103108a03484900d6068441c880d611070340d5440440b0030806100b0840c1d030b450b92180341080d030060103281da001611b8441c50b490810429141006140705410107031114400040441c03d00c123890141c0d200c1d180c0410030300c126012000203984031030924040e01007102030000003044d0902c0c00b038403420301d18240400d00005110005080a2214100b140030683c014200d90501c0c1291441109051146054141e408808a003c005e000e402c101c0c80075411140543d01c074050901c07540706c840300c0525109007190056410b50155401800b68505031504410030091580c40c0403010f807410031a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 265853588 1250 265852338 265852357
    0x61e0a020f2112071209111e03030a11010b060f040f1a03040f050a0b0115020c040e030306150708071208090c09010b090301060801050c070302011d0d0c02010516063c02 74
    0x44801201170780c0c08441c450f050f25030b401a80c08412031034140060004003507080b825011140110409500d99440c00412104c80003810319060250f07650f0f540d0307003d0040031988101548050300003004200032503202c018100350380c2440e200a4105030b58800e9200711120142050700107070f2041c00003e0105184280100c111401001035480a03052952042440c200981021800204402e1005034299042000096003041610104419000b11500380d03500c0c00020030b028820780a5440d8000000ca00314203a80e010340e80281000d80758115031801284511141c804140040d107020000342010b4000101c00ca01d150000d0400d2480342d00f040c0c030b40e0032036034001e034000d50705503403038040000b60513030244103503407141441e01e07a800e46801d05442d00a00f03484c0c1802d072407100d141c4600884035807500d01182d201480c007224144907004044500c0144d4890003044024a01c443c410b03640c0c00180b1016410500c000400303040300440d09a042c0c03087c010203410681c66503c61441d4214015410725556000f81a0101e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 265854838 1250 265853588 265853597
    0x3020f0708130807120203030714030c070605040602060a1a040908160c05040f06080d26010602030d0e030307140c1203160806030a11061e0a020f211207 67
    0x100c507620384140076800065502c0c405010240104401d45040c00168090300718098400030109513a00042d0742c9001d0440080c0881c075261201d141030002c1001181d0040103020140c502e015500c2c4000741168002d48234880141c001e080029107202042d111f01072102c580c4104d1540b000c9010310030301c03004000b0b14100311910481002408032801e662000c0c06442407043c0400320169007000103101c15948103210101d4000e06040050000e9130001c104220030281e42d1801c1c0d200c400e11180490804540d07e814001c40b544c1500003c00c8a0340d010000300b400d06903007a014422804403c42550b07803407008582d0f4070001070426220810040c1000f00030911200300ba02228024040d4661443c1d00340e1080d152014200140e205030700e5201d8000320300e16440101100030300305207000c42c0c444d00361001c0499000b9114220005006a0000c9490360301c40c1c0b0203a2214042d500c50000e4a0084d5076640060200022481009030402c41c3c2c03c001c49880ca24070318540566800c0c1000b207a40221342ca100548070a0910 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 265856088 1250 265854838 265854847
    0x1270b100b040f030c0e0408090d150203011202030618030405060702010315090504022805040f020d0c0908100510031b030609030e0f0d0f120c1704090b090405070603020f 75
    0x400703880604041c041c4a244031a001c0e02d185003803c0303948207a5210480c03918079502008085840d0300d06079503840d00700383d61026045441d490441003d8010350003540a842c40070002088010705c1c04a1800f05902c203500329001502d42d100d90020010380d48110440aa200304010f203ea800c001018040751031040c14003286c5024500c941ca4030081e079a4100b800c035581e4440c2048190310344a01081c840040c4104d0342401c105405074001c4402d000e0f8001e0038001c5480c0c07810400080342d243e0490390100040e020400a0100030007005040a800d0700c9504602c1c490031401162402c810711545000e880d1011011803001d01e140d0701d2081d005c42041c0d2000994241190000c00300c1e50380d00601c2c0110348242d0b04c0c2e0b0004c00886e02040095081d29a2040c055021008068005541c046191000540144040d094120f5240b804c84843c003104000801c806602c20003920348030803110182068a203514024807405c2c100d1020b00010180486018006a104000410a4a010758000e05407a200340d04083c3c6070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 265857338 1250 265856088 265856099
    0x110a0e0f01230904060c02011b080c1612110d050c06060f0a03050f0d1407030e12010f0c0804051b0a270203090309041505060d020903150c0403030201270b10 69
    0x8450488098400ca62294086c101699084c841d80800c03210001c0f40c170510140000000f070200f94001c2121550060006245810904001c4064130056224000359800911250000c22035142840c005d211480740c0c4010301600f80c042c0082d81c0e00e03012014024456656107a080040c1521000285070308141c3e06074011004c50010b0004c1440010080014016007400780f50040007034401d00d0160b001410207004032000070360301040da015541d0040300c05030907070410090181c6c0103150b018074855419140c59000034107150451402c0744694020b400391802000301c0c10f4107000d0500900c0301039a100030502020300043c4035040b05106001c0c09102c080c01804044080c42c0d0403a0700c282c0f260341c074640c400310346da000c1c0c0d25041c0241020340101320b410507511442c05020031500e0003038070f81e08803189801043d030001d9910100714424400c0c141c000c0b500078a06141c920049039510600040c1d00650a2031550a018800700c0000765071501e8400745881448169200d075490114042d04030f000710328881100152 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 265858588 1250 265857338 265857349
    0x10b0a18150b07022724010903030509040e070e1501030501210201081003050109030e09071e050a02030702060409060509070f050703110a0c03030f090e010b0403020910030807110a0e0f0123 83
    0x41045942c4090b0f00c0c074114601e940c3d1108100c2c24421f410480203403410301c0025400000d54400c0c0001307032000328615042c8849107040000e9508220340d00f1007042e00301308a24030010b070302c0d0410a500303072820030480c2d0302c80d0f41040204c5000c24000100700903c01d590f10041d403080031595030100c0c0459100c45030319101e42d91182034036400041940065220100030710303245000c4600c10b400c1240c0d42403d4401501003103103002e90780071010303920062000c08914152030600a00031514007640c005c0c0341613611621f42d60a00c00510050140c07601132a40d000008d030b01c05010b4003c02419640907282d00c1d0810b252503a0884400c030100300a80311901030001030000007052034104c1000303507101ba16000c10740988920010600c0e421a4070803a144003c00c801003280005250450301039035015500c812042c0e481200440700300000d640010440e036000510502802640d0008000340b100072140c400314280e1f2440d1910500405130b0b4000340d2014000300422601c00e4400f030058203003e50a030340b03074a205a801e00048 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 265859838 1250 265858588 265858591
    0x11072618010e04020c06010e0c07240e0a0c120c0308181306050a03020d051203010902040501020d050715050405010b060a051e070309090c02010b0a18150b070227 71
    0x140000d210340c40e2800550703040b03403181c250754100740c6045003009650407800b50785603c10720600c91030780254004031b00b400b10200100c4000d540c0104810a0001c50304c04401441c071007036244070711502d107889001d915001002c03a800d02030603001588840d54a061910002510105031000c5615140f120760000020b06180040c0c54000c0701030b030505104000e09030902807a05100c10380d01c030a0a1812909002c10f50381d20401c9020340350141c0d5052188401c520307020b480c10704881c9508200107008000040d600c030385500148141d810a070300b41c8149603c240404c1d02d4500078104014105a4000c903081481c95959101a92180c0600d0011980b01501408690a907200050701d0001990008078510b505002d0b400c50310300031402e000c01b145810025100280030640c1070080030070580c1c035094801300c024800d40112440020040c42e410340b0940d202000311101c1c03070404403c10094200010050180400b504000488072850008e0b45040041d82c03c00440b9000b03003200c1000d40c0307240b2204610015190a009 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 265861088 1250 265859838 265859857
    0x312072a02040608010c17040602070c1518060f030c020c061309060e0f2e0b0301060e090108030f0a180e011a09130507050c0109080913110726 63
    0x1003003103100e00600040c0c1c0d80030f030400f0300d82e44c4c10f050240004c1a8000d00549000b0f6a0403141c140a031100d2402c0c10180c80740e103202810f440d410034408100d0300b03c0c42c0d614070b850504540b107102c001c0f100188500340041c0d40e0f10900001c280b000c5080c0c010907010341c00036500c0703105c0c1748183d8104006100000700740340c11662104642401401c024001c1507078130301c5080044c050324904091f09241203404442c40c0d01005111104406903080d03001010030009070290f07425545280c200c0c45081d210100c0c64240d42091040000007600c11024076002d0078200212030503181c0300d002542c601800c8500800b25a406504610100403540484a034001011030200001c0c1c50005030350940da5140102445240c0306140780283c805804102c0100d999840002e87e02e900c100d4040046060781e2400400c1d112802600c0707410aaa5080c51110020410040f00514070b0700c6040301c4000382c1021148449003194072409824041c001d041040f000400c4070460644240040c09551101101c0c0c410111111500030b035499 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 265862338 1250 265861088 265861157
    0x509160f082d1005010822050709090f0209060f0a061412010306090302060c0f3010060f020d0207181107060605030d080f2404021b0717031207 63
    0x344040d0145800040f00103080901c2c1844250815000c1f25020440810b8032003081d03107200700384004100c0240103220050040702401c200c030581d5030600ba41d6523170240350124403440c3c891000680300c0c41c02e200c00d003510040240012105030306154095900c0c0150107a00050228140140100c006500d900140030750312940d00414852001c1c64064541207018012100021051040c0340c1d8031240d103c10f403210503580100550129600c031005a04030311426242c40c0441c10300e00c04015140050301c40140c04c0700d01e66a1002c00c105c03860f00c012602c600c0304c01c4128006801c0350070101310751035285240b030310b08611000001818501c00a035401c0240d10a250454103561554010009443e06202052285d445810804c0380c52a0035a01211445030082c042905000d4030b036a2041c03282c000907081c15059102038000c558034120860f044403e8812144825400c0c40b60b1a000300305d000d1640c024940914604005600700700c2921b0402c071584030020302c540100100c0b444034240101850101950702d0369001d22 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 265863588 1250 265862338 265862341
    0xd0204020412080706061d1506090904030c140606030307030e04240f060302210702012004051c020f010c050c0d0303050708060109080d03020904140c03010509160f082d 74
    0xc122082d5511544030724041c6401f4401504030640d0700c100385a00c0b420b600180c01054000300006111400341609040c0c10442c05c604010815030000280002203028400d080c1d1f010003000302040d664401158901d4241d001030100c01d0001c3c1c002c5000d100e00c80f90042c03020440e40308550152000e0184c0403c0109a4104410100f0191210201c21000ba0940d0b280a41c07400d21030708081d091600c0e58410302d0042080c0c613000911128402c1d40070440c02084007220f40d440980d800d1080d08280c0003030140c036209110f40d410100780c0700d111407000740800da0b016107100c8070b0845500054070035010f42e21046e07910b2300452403150040d0344e440d0702d141d07640d44c0700c0d1728002114144408000c0c03082c00c00605981c18048210000d00441d200040c0c40c0c1d501c0380142c54090782d90230b885008134000d0300081491031801200761091010b245a940c000c3c5058840135602c1804a43e078403c1d203221000e828502900105200201120040740b082000e564410740c281d03400688004285400d4005c540b1802010842414000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 265864838 1250 265863588 265863593
    0x1b0f01050609090a0209010b03191b090501030b0a03080304020d060c08010314030307021c051e040303080c070f08160f050109120f050301050f0f12030d0f020f090d02040204120807 79
    0x10801d5820070f4480004140c5059680d001c180a100c040c021125888030120018964035540600c2c80241e44d80c5040034008415020143d254828086100e4004104206d0700400d555100e4400c0007085540201340c1ca401c10b1443c4c8400047d64405001640c12003803100a00001c078a06000300d410a0000c3d5462198039859400c040960150b0071800c400300d41c004006010400342c0c000b55003105000b004c0002503000c0c0b10004292101e1103041050701c0d600900c20a040c02c030303511050182040b00d01a8580240a03a540304106880d4450030a00500760f8110688240204101d880901445103640c6e030149113080c440d445480d100d000320138084455a440ba1b0016041140036035a0607014032060a001000c0703100140c0c0541180014042d00e0300400e090520550303190746c1c0c02c2c0700c81000400a880782c404c14050035030b400d4507540036030350004590781400300c5144940024400c8a107842d51865000d4140b1035807504202810038400000d0780d115030240008a405801440b4001805105210303080e540c941d6803 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 265866088 1250 265864838 265864849
    0xa110405010b1c0506010e031608011107230304030f0f030e4006030b0703150b03010905190c031e0501051507051014091903020309061b0f010506 64
    0x58100010500050041d042c1d0701c551062810b43d110301a0310042860741d44c00340102c86504c0a03401c031680c144101c150000e500c0070100c0c8e0300d0041e80c400400078850b040e09841800b0280c07261b03040003008009401510a00040c03031524000c081e54580c000c1d03074030b8175a90791986032420f2035402c001e40c1e5510100390300307404168109140c07101c03840d001d803094201e0102d0598402c2580500b02c038640003401d072024003048111360b4a1400c949004661408002d80c5860f4242090281c104a401102003850110100c03541c00c03401c1404c00894408402680c956806c08102c0000340c68040d1003115020400481d40d1035901e5140140820030407103542c000b0340f10305011907240720104c00c401450001c138075020051146445440305484c40c414901061642c405183c607000785045502e01c0844680c503d00041d041c4d450701078111440c022025181140da04840d800c00820110400c40001809640200511521400d040d0040e020031700c051030b80540030102040c0200c0c10302c1c00541c003030603d5035500c800300041c13860207 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 265867338 1250 265866088 265866091
    0xf110c270601090e0105220213051513090e211905040806010603020304050312040f1a0f010501030b0102010b0301060b1b0a0305160c050409050d0207080d0818010e0a110405 76
    0x24070348004214507041004e01c82081c103005281c0900701a078800400c3c01021032000c245400d0180e030840d1780c0c914040030a1040c0c1c07224080c60344103002c0580e480c030100e4895401e5070030350071071911080119868194100020f182e903440d0703400035024204404416603207103223500c501050080d100f240d82c5c001d0600c015500d00a0300e400482030100a10050120317080000c1e1103815200d0508005960703490f0360508030700e98028884012105039000c01008104190072841c0030405201da040000d403d121024031a10040c1c0840e405101d03080100300402c1298030a804c4080840b07418000005d5a0400001280c00c1d12031503080015201000146445001400f114294030b050492000e0705994460756001020b0b0f1003203031035510f03200349016011018454504011001072600410402c1641480c0c81e2a5448810a81c4a100035004440f00090740da440800c00c000300050a5403886801c0c0e88440600d00440107410003059550750307450f10b0840c5040d040200c110032501a01c0514140841c113420001900c00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 265868588 1250 265867338 265867351
    0x60409240b040c1b03020a0c0807050301110910180b040b031603021303060b060f0d0b12010c020705060304080c031204110103090308190e010f0f0501050406060f110c27 74
    0x141600354030750140d02040d401025080115115007030007460804928200e80487c1c05040340030383d4500000e0b44400012610103c8001317a00a000ca48844114005140a8101c1003034100440b40404100c84e403091207140c910440494182e00b48588a1400a0854000c1e4204d00d01c0c1080000c10b010001482001807520f0440305d1500350724100c0d8903040102c100000d4400103003401c0c0c8480c50751000750307585070503a2000c0c41080d20042c0c540a03140789040250441c00249405500060901000c4c6441800751100007a525001025510300c0c01051050643c00103100303680c50801440b00400d032400500080914120300300c441082c2d0f06043c20f124000c2c000c5080d60030305152805e000100025002420140c0c441101201d900b540070b100c09078640903050124489516500c0c000482000f400b466005000400090800300032503038941c014001250380a0090313001241c100c51410880c5032241010004d424103a0090325007400c003d90201e025503051000c0340401070400075a40c0066101c0e0400d4551192 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 265869838 1250 265868588 265868591
    0x609010911030f0a03050c010b0d0b01030b060d11010f12060e101508180f010e0d031103010f0e1e01150f050a0c02060903010216060213060c0b060108060409240b04 72
    0x40550244d0760042c0400050030310501103034089581c1800e40c4100300641d0040e0280c00391030140d281940d000c560901003241c0191911002c03c209080400d440c0000d07a500031007165964554600540d040203c0700c645004000d8a9a5000120120b601801000340200943c110301410203408000b080742c00b0782c0003a03040409550341820910f0340810882e400a60b02e580c0750258200c9084007a04046040c4c000742c03521341c03c005a101d8515800500e403510024196410800d8041001103140399200a204010a48a94500034401d80c402001c0c855084448076400307400d034942c080c0440041080c00d920940394500c9552041840c030b508040880850041c92900e103203401981a00074080f103e082002074000d00f0040348518080d00c09504a45d0308200054036043c0b00c02062800d18080d6100d0110354101c1c52540380d0010351280280c0300040352a0303204810814035526400115040d0000800d6503900c1601c441c00038000c113901c100d403003038001c02c50003418030000390105010041e144224003450055 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 265871088 1250 265869838 265869853
    0x1109040606022a12150f0a020a0203030a180b0c0301142e050c010f0603020a0501020c012c0901170d020f0a0b09010b03060106120f050c04031202010608060901091103 73
    0x1001080b03080d10380c054041100c00c03e90868000420800c1e000904002070700e21403000010400019060418441d00c17440150480d2580c6680d002c0080e40250708295000d030b130090010604c0c00c200758020110649444000c8078000c201511410104401600c2800c03041390000014481d51182c540c10020b996400d460a401c5812209110708016107a00b0300040d0101c11919081c8003644a68100d850125a4070024002e880f008030140d8000c14103403100724400d004400c2c0c001015400416940c41d1210161244824180d000740f03121400c40c280b08010040701d03200581108141e4400d0300c954082e207030100b5401d80340c4420145140c81c1c035014496450565001282554201800240250b010740d40305500350740b95101c000f403640c090f1507860450f40e4140110800459826440300030100d04c1c0a540d84240a0042142480b0044450580d124001940c042105102080484c030b0301c41c40c0f21045100000d580c2d541c03695143e082c20000d69010308140d4444140320305106000304080c1241c14101c019040c0b0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 265872338 1250 265871088 265871113
    0xf030f0a06150e030c10171609060c03110a0303020405040e010603080f0903010f1d100605030601150e181527041b0b031e0402180a0f110904060602 65
    0x94440c400d01e42001c00c03c601044070307200c1e1014050199810300152080164100441c0007804403010002040c4546070741c00006000d0104003030748917501d1403c0f6100c1d032505a040c071100312019000d40d48181d050250b40719100182042c10082c4610f1140640e90050b00e41e4103010400c002d40381504c0402d240f83e2705164040c804102088120b902030307800b1804c41540c403120240442e0141140c1d100d0415450701e42842144100182d00c9400000300740c40d81a00c1c03070f04488407902d8007107444c0380c014140c06a02c95401031203100345050a8102110301400d055200b040e03904001072141da2000b44008003e200c040610550040902591040c1c140494080c40e818810750516242829005003220b11088914085402c5c0701005030f202155110403c01905800d444481040003075100761810032550840790358009160b5072140c600c40c021940180302401103050410040400ca0010f000d50100341e40d1024211424980c0e0311a800b40c0b001445400c1c3e8888581a0421007180e20780d512200554000a0b000102c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 265873588 1250 265872338 265872359
    0x60e0102120901030e0f0102040314030435010e160b0412020906040e03040e040506100303080604051504062303010501030f08030c0d05040609050601081903080c0c030f030f0a06 78
    0x70034001c100001625004480c0040303015205c0c0440360509405213800d801c60000041d00240196030041501542d40004007209981d00c0c4075501c9114031407550b040c0c00c080d0341c46910561184405007010100d114550340340c500c600311000b00c0c0755901030f82d010758001c20341e04400b20159001060000000c40c01d0502c2c0c40c06500200c00813140c0280700760328400008585035641c0c3c1c006c001031442e00080b02c0c2c13507544902d8426209641138030195400c5c844c5034005090490318140c64404e40c1d41c940c0e034114071610341c00c003408040c24010f000045c3c4505030011014094a403131048100030001e2400d9507240380c54208107000c0356590503c5c007a000303034100001030000c10803030b4108100c41540101c0899032031ba500002000240540d8640c00500c03800d100034031080c4002038008416103406800cc0d100710f40da85100c8603944425000303205141803074102050300864014024680e200e161042c51324900040a80010b0035540184d80304010028003006000c000507000581691260443c001040003c1c189100c0c00c8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 265874838 1250 265873588 265873603
    0x501020f031c060f0e070e04050417070201120c0c060f0e03091c1704080606041b0e010309051002070506010e01180b01020c1e1203190e030a080a080709060e0102 71
    0x81d200800150402c0c04103255840b20b00241280d8108039100f40e11001048540f800a03210403000900c0101900024a00707442414040c40d48070b0554180f07140707014102d8a041e00080c2c01641400468541c00b5003c0c1410f000366410030f4400e0741c81c01c2e8451054503040081f1000312110506003443c0c003082c1503031054000200c3d56085c800716003002c122200284003030320411b42100000c1081e0750149551542c004072001901c02d80d4820740555006985207014041201c0d80d484a840c1d0104d107a5610fa80c2c0c0750b0050b0114204100103240200c1c540440b6140d9510f4103c80352350b10700080d0341c00585170080c018240001400341115800f00c840c154074005204603031078075002ca10403100c0d51b100301d82629603008002048000340c01800d1410074000e050425888500c40c030401c0303405009503c003024000840881198858070016691501e00340c4203210454040d013410b001c040d0107102e0416580d002c075030307510040d1100f07290aa0b43c0d076403d440c0010008001507082da1000341030003241501c03c500c9a8010403541c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 265876088 1250 265874838 265874857
    0xc11131103091b10320405011e020a030e03070302031504021c08030a1a10020d091d040807020d0206070609030e010e0d0b10050a060c060b0105030c04060804030c020a0602160501020f03 81
    0x2042c0d1510303620001c6982440140c0c80800c0d40300ca005c5602d1803400d00e0302c060310440b0b401b40c849150f1a41540341d6138105041c030150030350042e00149402000a80502144184040c0c0902142c83d480e4a076030100b13141100503410b40200742c10720802c1108610382a0010702c1c00c0c0325242c01c2920907402030760b12420640406031180704000d84926840c0d440000713021058030400001032024500e0b0414000c040d45940318125079000190900e44041410703070481e0504049400c40a109103003941d12500c90340c4403078005d079404a0703010000507918000b43e030301e141c00b03841c07241d0080b5000205d000702407a029100c48081c61082e4113204090310700c0c248545c1c0f00100b0218a541044180c1140e940305007000030801c02e140c000030b0f4030456078040456001d17800100d026010340724400c100082c0b0384540044da00d600045441d2808603108000501415124400c41c84c0c2061090405080004190380040c5070034110303801c400016804903901c0d42d1840c61040c5000c000301420b0010f03081090401c0c90064507849900701c42e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 265877338 1250 265876088 265876097
    0xf0b090106030e1903050a03150609090b0a080109210c031403070c081306020705090411150d020409020904050601030c1b0510050c0301170d0c11131103091b10 70
    0xf1030030801800b845501505130722a03844003143c4c81c50081c0076500b04001c0b03d0700081c42c280100c0d2118420060072030698641c0c1c1c8803d20b4461502c400f000241c900c0b213038001d0300f1141100c00050518024001c90011503c50700d81241c1048056034810804024a8201010000d08003a0031000c00d4000a0140744406000c001969960711070300103642102241038000d104000020727210111100b0f800c00502501d1841c1e0a580c4816613401c10000c20210a84002d0008009101c200546240001017100d103500284e25041c1004c8449400000300d81103903100b00da0498000449858524092044640c012001d08040080d5520361f80018501021210051006001c1d510a0f809101040000407140135080c1c1c014096841c09643d07034440364000307106014415504040030803841002048040d0350059a07901d588171b607110780c0c0344c403205d180d1132840f002e400425100c0400e580200d54060b0001c280d1580300d03034540c0c90070113113a6140307403036100c0c0c10580c58a441030085509560310402c0c0c001c1021018a170 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 265878588 1250 265877338 265877351
    0x120307110603181c0905030106080303181905030a0306080312041101030605090c040f0605040303050d050703090f060608100b030304030206090402130303020a0c170d1805030d120f0b09010603 84
    0x300d615600c0080c081c51481c81c890003203500c1c024040315800811a04c0381d561a07054499680c1c09060980b20306008846c00c40c0c100b0b00025040d101640a00c54982204104030740402c085025500004010110290380a41002600324412a018010380c0e000f48544070085150042100040000c000081c0c0014000015000c03541200ea1003034000b503019100003084007415045c162512509940148505000c24440078400601c45001300f094804aa0f05919072910f030450740c29091001700b90007401a002d16645501034008100311420421842d84a28400903450341841349191401000c006158441410030a50500e0380d10080191021a54142e41c00b946540501c80050060302076010784a02c8421030724800424186e00150707007003507a80515556482c068036a01440e0207803480100901c16a03004941200517140f0a0b4084524400f0001d81030260b180c88000090501d0820000d081c0020f42d84034108031404503038490f4a2a00b074101c070701003700b040c58101040d409441441000706060740c0b0300 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 265879838 1250 265878588 265878601
    0x1e060d0e01020d020d0f0c020d0203181c030503150306060d0312110f030f0f0c2b110c010f0207020a0312030b060319050604060806060d081306030605120307110603 72
    0x1015101c002c0c0720b0f940150340350b800c0c070720158009010400340b0081042c00d15042c2c250b0140041204111030b2a150701551400c0404104184000958001e01d90400204040003410643c51101c06050714803076519550340341080c10004540c0075000706c04030f129401c1481848010760310500c9003030710207a25042407400002141405002407081110403105242c001030140d91803c0700c0c4001350b00ca05600604081c081e19040d2100c1800c078000c48000c00d8400c41040a141034181104120714015080079900c61022012100d82c8243c0302501e01401c2c150101181001d080d00e002e0283c1d903003454541004500300104c0b42c001900c050b500b484040c00c6100440034040c0900c0c801e0300070001d140303000740c8140c3e5681001d080e60030441500341d2801034150314050200d10310f841c0074040d8804541001d4010211a100c180c02c01200e000c40250071600303402e041115a100c0103185858030000c045603180050301da441c00003032002012085903055402d800400050000490090801485400940e011504c03995040b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 265881088 1250 265879838 265879841
    0xa0c020708031329040306020d0e0109080306120f0d0e0102031608070c2103030c020f01090606030b0610050f1c02131811031501180806061e060d0e01 66
    0x58008020038000000d42003112400c0e80d0000c0100d801340180300c100300201c80001d05814421203440d102d01c41d01080f00300003107002d50b00030781043c110451000541900c00102c29007103a02d4550100c80b0824044200310852a14110f0000400404000340240340c0d91211083c0d10b1f88699042a818440c60341c118072400e0b4820001c9c1e410041e01403408d2202d0102d1400c00c60703159000440105d4032004c9080300440c01014920340000c400031081c06030300380d001c1c0a07902039018007020b031030000c1144229500501c0c01c4109008460800e4016400040d0050079030030000d0f0030384d200801f1030b0f000b07200b2600c69019165003d800c03145402d4001c0304e1941c65040072005000c03888103c510702c0524500215080b64400801004441110701070002d2103c4079030a070101c242a03807031008507031a0b04041440040d181480000000100145c1494001c01040307001c3c4545804094581050903164403900812800303060800c07080940b05600590569843c42e44400606244159210700c4050b9464014801e2481000d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 265882338 1250 265881088 265881103
    0x102070e09030f09130c0c0b280c031e0f0f09081e27040609020f1806130e15042706060b0a0f17160c0203150a0f0f05060904030c1703040f0605100803030a0c02 70
    0x11481e2480c0c12803324808044d007a440d11215040d03150030b4071703105200300510452031600d03030002d002401d00e05d0075900210795601e5818034103582682044500000d8038285840c0d2802c0209150240310004d24409101c00c40c3c005400c44286184100a8010107040388070640b034110046280e15121451a14080703140350281c01a88020340c0b0102c4008100c4041c1110070922030303c1e00350b200038600428081040283ca038000c021040660303801e0702450480c00c4022007910124080c00c0089480c80d540c102d0504180e115108900020b41c506889110003580b051404846484110505410b8241302030710f0200409882c0c42c9400740403070b174080801152400c1c040e81c1041c01c0d400030108170a00d0140c010380c0c00303480001410b203481450300c10280740507201031240034021400644808040e80d10365030140c1d21200e0303015041c1e03088241032a9552862005400961003588030700848001d1100511b882c40036580302910000704a84441c0e800c0c040b8500000950380e10440400d004075070300240120a0741020782 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 265883588 1250 265882338 265882361
    0xe15102105151305010e1617120a02030307090911091219060c11010608030301050d050f190b060f01080604052d060102070e09030f09130c0c0b280c03 66
    0x700441007003d5440502c2800190724014402403117416064846a500c810041c5e01900ca060300c405030078002e8400d244410714605c400b41049030030800fa0411143c0e583c2e088100a42d006a0000040020310759220035011300429034a00140122000343c03c20302c0c110b0003200700450040590000b9400320f21020020980e01052036041c10a4418950400714081c0601d1400000030806121141c01245014400e9600300d80c0d07608051404c690030141004208440305205444a124100036102d248809002810543d40c0c0c0200c10003074080380385448090003a009000780d209003c0d48424413482c0c0d8200041c142c0c01401210b0000340c917664001664140305008220004001030503541041c1110200203044c003901c8243c080362256a42c414900d01c01c404120b48000321303900140a0200d2036a051009031181c40b07002840600c2c0081c00000c0002114900c840100000314803880240500c000c1c4451343d81c004134002c1c000c1c00c00490900c0d030201920400321134460070710f43d0f4200c41c1940d2440303680030822011 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 265884838 1250 265883588 265883623
    0x3110603220204060306151401020f1902010504030203030409050109052d0408040909060204080105060f03120d1407030209150307020d080a020705071205010e0703020a06050c0106090e15102105 85
    0x20558800c102601d1072300407030603a01c0d42560114003960001400840d48030b01a001850321014104d0340c203070200400310341281030260a100110050341c007840940068500d08400152540c98a90268141c0398041e00d280c00c00c540d120030383c02801c0340d00741512503041800d25a880064803140b52800051113a9031102801d1440d00710420100101500200103c4903042c0c021711131a122641000350801c800c0700301c0ca515600106a03c001114200003814541c550500002036420007030760704544002c42200c0400001e6800684050640341c540504e403510510480410305501e404074010307641d8921100b103001480b44203400501c4180d02030301150034681d800002d83e01100e544500f0914114840c110448036542024010b03d40d40c640001e4020450350021309000a43d450223009507401e501c040070303410f01e0303540b15980885c1b00f2486004452101401c140181803c0c59000003d00c03c0000180c80c4c1c490040c44140100400c4004031102e41ca605a000314450111842d40b0b086450210315031003244901 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 265886088 1250 265884838 265884851
    0xa060b16030e130f0b0405221707211b151503050a0b010f0b0c030d020703020c030a150609050108060403030e1c03020301180b0919090f080403110603220204060306 72
    0x3280c44c4e803c400c142d89001c4c0c40902c601d841e41c180c2968100c1200f0810b80c44840641881e0011501d0010b81e0305000028600c02490415687c84048440b08880320200a00d85581e0441283d1980b000380702d0b0034030900415000110800380d0716007600d01c00d003a128590054491141200d10242110540011076111040360300d0f0f1f040300d1070030100c20301c400d00c5030ba60040c64401e800070301c0550705c100f02c40d0958015806986000390940e0800c00a4018500943c1140300312a840b80c00c645082000c1116035009004143d080240f540d5030405490381500420600c0d814000100107030a0001906a0455450309002c0740090344003111070b03d03120060b00d11484050b1500704c100301c80c54045e80158103032512201c1100c200444c18440100341c44d0686070094001d94400006030480c0031103950b44400c4910300d41c01185010fa10340714481400c3c81c0c200165016100020200100302038400031a400c0182074881c41e0852070110900560445070040c3e500403880c100300b0650441d030703c55010030043d59010b4000c1049 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 265887338 1250 265886088 265886111
    0x210609060612070807180e0906010b040602060604091a13060c0905010c021c081306030b060a02030901030f110a1107060e03060117010605060a020309090a0b0607060b060f120a060b16030e13 83
    0x380c0341f040e01c8100182c00f1300b60002c940c01c251802183e0550707180b0380003014940c48410601c0018421814103850001c540010840400c001221060040c0b4060007201d0071075040d81403040032035440806400511040d100c04003e06d0340c2148089814580444800403031010741ca200381c8000240902c001c0007400000744034125200d80c4030903541621003550f010424928500d050068038491080c2c1d201c0542e00920618206601c260058046181040004510000480040305541e0401110301020a1440003420703a100401c004140c010641403800c0714400450f0b00100362244c90600800054181e07103401903407000ca094120034001c020207040155280c00b8806c000b512a0030154000b407040402c0004a05e800095020342000080024002071810b0042d40d0360400030f0400c55030454226006212007000400c41c1000b41551102c0c4c600c15408c42d1901114850031070f000d503046a0031203401480321a107600c40e210002d00b01c250b458201101d0814403003002034529140b602891003580d042040d003800 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 265888588 1250 265887338 265887359
    0x603040f0b07080c040909050a02042315060712050405030a0b0a14060609010302160c1d090a17070515040c06030c020f190821060906061207080718 65
    0xd8031070142010207141d40300d07601c044400c40415103d8a448000900c000d1104081561003407003001e01c103d0032204000106e502150a99030040800c00804222140a00c2032180c85009564840c9035850700031001c1510500003071690180c54805040010019144180075000c1c50858002c1c090003002c17501043c210b46000022000100c1d05500d419052014003a42d00e201032800c94010740c4010009420841d10400440003504842c030000c03001c0c0d4001425502040d24080d03050042c1c11413012002000b45c440c42c000510b400c4c042c0140d0384a07481859202d000c544585803480c40640c01c05c614aa60b600c203401c046241c146c140c031854204141000030301003005405c0d80520f04a4840391818020100d00b480c0a903145c400c0c5180c0500248c00030b0394400391003080052080d001e1882102086d0800c5501c6c0c003181040c40c03e07107100800c820b640c20240301140c41c0c00480b460b80400101c56503031420090302c540c0600d143d8090322280900600700c0200380c0d6a80a90081540d024900c0c0d20440b40c1543e4170305400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 265889838 1250 265888588 265888613
    0x7081c0f0f0f500702010605220b0402090303030702010c030e0d021906110304080403051506060702040903020f0102070822061d0409120503070306053c060304 70
    0x1e0a00740b4020302030785409424043c100d0405055222440d100c080118242c404105078240c030a24850030010088100c0303101c4440d42d625402141c904034084c5800607004e402c403080b80c1c019902c601076034003a428007050450282e100d440b109010108040c40c0c0031001c81d01901802c0006c80c0c2c1400044200140268158001442250150740c1807002c80310107440503846014403055803005030003107407022404e50041a03868204030300c548030010380003032410095140d90300142ca04a6000100282c1042804400c004442c1a02e444a015a6640c1041c0c0300055035031060304e8009000e00c0c0c40301060006c0c5402841142d20101003580250b40e16907091410f12003070745c810f8000b40b80b00d01c1143c10b45600c821355011120300744e07900d640b20b810344001c660807015110300004019941c05074441c00b0420009144010580011920b52619511fa040c100006003d450715904414040c110346d40035248002d02112000c82040c5003e8040c005880303040b41c0581641c0a901040d0b03811440c00420f0104001182050b00b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 265891088 1250 265889838 265889861
    0x50114070e150a1211090a0305060a060603050c04031218060302091503130f0c030206120f0a0b060a110102070f0b04050d021b09090c0d1515030807081c0f 68
    0x504502c2007128000301c060080601c1400040c4100910f83c088140a90001c0c1c550680c0341c0b502814031b200c1200184146030740390801c4525810084c00c3c0200343c119806604050882d5080600ca9890940c00400c5a07020b1444050706c1032560065111015010300c0050412480280b40c41510700d0310382802030061340c045428140078080c200c0c1d40d000034440c00320950f8014120110030611a000d1a2502c61000010360001e50312040b65180c00001a035559000700255103108011072021310780700c10502c464080090481c0c1a041c14004a541681d40724012580d0760402d5007400f40c0d401c546a4442402809410070040040e40360003c6c0d60240031284100e00e210341d102d10300b150350740c0482c0c4a040fa2515071711b0050f62580440301100170401d04c0d21040090703200e2600000c44100065184c0011504546502c090341c103108980c0c40307414182c4040c002d040031a56011904034103140f55580e080ca1520074040060f012030303c0420441203c03c10391000d51110301d00e0f03010038003a62010b128440c00030610b1700f444 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 265892338 1250 265891088 265891099
    0x6010807061d03211c05072a150209130b28150e090a060302010e03030901090e180706080a0c03110a11030c0304060801031101080919050114070e 64
    0xc008540b98150024030100a4003600c1c00403884c00713180c21052460540907503800e9040c01500c0024100841105055500c4c080110312400e26401c0640b18580003a80f5070303040d942500d40e4402d1444520505030501d0380c030410309800c1454014107070000b4011105e0040c0e112000b90640300d60400550841003983c00308035014690203600e070038070042c5c842100104c0070a030040840100306258111a40340c80c00400390610001c2d001901d0002802040115184180b140d5280820700a55a0015250400c210198000e41c03a1480c4071340040e203408500e1284004d09510400001c180000501030680b034802d403082141d01140c0c1b10100504030180031140f02c000caa10380311124402901c280540342c3c2c0390650b081e0741480c1c880c251038112195544000008001d00c0100004001110100700800082c2503035602c3e00705a50640c030b00030030030150903040541081886030070710220100126010612070380ca1081004100c80034581a13014001800701c00902030b8004081003a019041041402c40075400c884 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 265893588 1250 265892338 265892357
    0x307080307061b320703180608091b0307050607080c0111030103020a0b090406171036050f030a0906020613050d030f0207020301231e040f0201110601080706 69
    0x5000000140e440c2007000002c1a1a1343d107010003416212050300d00302900c02c0041080080c0060b40403641c4491005c400250140601031000b8140000350400341250785070003034843c10103402c1e0641e60702a2032a0300140c0e81c5032040c0749109540c1001a0301c000c00380501500d4030b40126040050b2a41c0201c007001000e5403c00d5614400c3c0c111900840341600c0e4000c2802b81001e0401108004581004c0c50b0560455a150000b240c0940d20400070072002034104000d01c0500301c101c40c45420b139004003030b0071100c44c40c3c208040d10311511004021820250300d81040c2c5442c2e41103003455031524104032801c07a2039000001c2d1450200340d019240c403041c0d401c0d0b40c0854900d03403507299413a4140c8201d0000940540c00107506084141c0c071a8106249202c1c0c0b03c1c1c00503041015940000b03003120800fa1403481d02044141c02c400300003581c90341e2950310162201e215494642800002d0208480080c0002d0508400300c01c800116030007240442142440b17082125160740e118440281c2d141d6143c010b00010425410 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 265894838 1250 265893588 265893611
    0x90c0a06080702120c030c0a080c010e0307020a05040b13022709040b043305010e07090312050304080d05070c0203060105150d0b041404050601180902012705030708030706 75
    0xa211500600e110360050200030130042da4040a5001401000300c1d42c0410013444803d00340400004a40034000d01116075548918104282121820103c0c0d241641045c80304002580ea58040b040859a09607000b240c01640c081c0010100d202a034412114540b01050002d001c071542807000700c0d2045642c1c44014075540000820810180c2102c000707040b01c81801c00180007801c480001c1107150780c0056424421680c891034012803640c14600c0d2440036a45600401000706900c201540100c007034100010101e00310b407118504100c021184030180000000031400b001000e03400c4511024816000304201e0802030f400070a502c462400c268483d00c103181c00868603280500405410000721400305141c00d8034140c3e881c003c0c210a040050707006544080c40014420904402c81c030442c858000b620761581404126407800754562440c1c0440c614140e642c2c3c3c0107076080010824403056205c410480303da02e5a03442e80c50303480582c02080e014002c601d0f0004c0c0c84038002010380301d11403041400303100500f40076 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 265896088 1250 265894838 265894847
    0x90103110907110a02240a02012003010f1208120c130b180418020916020708030f070f0212190506060306060a0e04140303010f05011116091112090c0a06 67
    0x3070001d02c0c80d0380090b04d0b40001490132254106507102d08110500c0c15960800c0581060313044020940e0140c0d441d914131030810074895403a580410030f24041a811035041106c021401101d41c091040e05828140d000400c2c802c8003c20b0b103524008201c00c040d224544107410000381d4114800882601104002c0803070464030715800d440b0800500d224039a0220344800400002e40a10491b09111020110b00c90b00940c8451005c98418408000c240951160644000f40f910202d540111055007048c001800d2148900741201d0a068008003810511074840c000680c2c522001600040d040c41080782070003020000b82e1500c04001c3c0250b0a4400640da00001e00d900c0e0401164078a901a04242003400270360709215160b034000e401600861041c6510003500e5166a000b0303004501071104420042000f0760b840030701c944601181d58041c04c00e4000382100801d1581844c05100c00d5551100f212a04000c074680540e03000b540040c02900c802d00f418103140e9140d0701c840040c0ca01a258042010441034001c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 265897338 1250 265896088 265896107
    0x9030f12030a0209040e190c0b0301060206040602030601030f1401060201060906081518030409050f060d1a0705070204110d0b0306010b040e0c0702030f2a01051611090103110907 78
    0x40e120003030310716603508102030000d602183e142940030341e942c4c1c6005c1640c6401c00018403640782c0b030715440d0b4040040313080440280c43ea5501031400c9460803c010300c11035078081510381d00217900c00710240e00ca449e007100680140040f010150b25040c50b1000a60f403c141c188042c6040790b12a400030424207890301d030394500390f500c6401442d00759032141088010b11046c0182c00c40e4010605150b140c50f024a0303669090440d0b201f54445084141c0702c2007071050f00c3e0301c21140705411030021180300c416840d05640341d41074400068040840d4200b008001207119000300110341e589540280104541c5440007080012078029015180c00ca501d400480021400c0c005083e5050303858a04407982000d1504d6050804081c7c02001880070481c2406802c0c01601c081028510034039090000c0c054000c0100085074a141c0c41810004080080c02c0e514903a0766081000c540e81859141c481c0000c405903401c0800b000c12001021136000400040008244031545481601001c0c04880c40340c60354440c103004650381c101 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 265898588 1250 265897338 265897363
    0x19170a150b070c0b0703051c090b130201080610020c040903020102030f0603161a0f07030305040506060603070f0806190e07030b0102060606090105070204060308042303070b0a12020c1209030f 84
    0x240100500074404c1c48000740c00428440c0c035240e032500c020076029640c0300c102e000c03108028030b07100c1811504002c0040d11107940600100c1c015440365405400003046030a0140c0110301665685501603401072081c00003988068000e401400f00c0a018a0700034000d42c0b048641b145140c0012012410900d004544d20240c0c1c0b01000381482a281015001441c0c1c410404802887c84c2e810401d0070700500508020300107140c02520300186c6031825040c06810884c0092241d44240b03001c204202c109078100c4404418001e662a04108640e40c0e4030104800e40d2013800411300b45441584002417001480300038034480c9840c0c0d03809010300e0101c6001681d4608041d83d5030380e8407032010b003c003000075403041c001f03040c030b050005201144880d5680c54404907940281c204082c3c6050940c500050021114048038a030b490682c0100324062511410004138040e5050350400c12561800552217a90f00390182e0f840946001c094424060f038001c0c4090f0183e0180c50414080c0c080c071081100030140c00300e0f01800211 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 265899838 1250 265898588 265898603
    0x2040e0304051c320703060b0120061305010b031912031a0f011b260301030c030602130f080a02150c06162c040605031219170a150b07 59
    0x160751304400309001904403400a50b8050114100900030001c0204100131402807a0024400c5207400c00140040501500700000340020802074840d206d0010713001c2da0086000d00721910302126450100e000d041c2208000c1d5140c42030391a020850b1491008e0160080d21685215940880311700b0103038207480c1ea59900200e64500e000c20b4600f5030070803200100c2d140805251103084040c04960000c0700c0c130214802968818109400302001c0242180c08076408030980d0011400d40d855992409808150340c0001032200e600440e02d50302d580900307134200c0043d085400b1600c00c11611107601c00d644141003241a4072601e1504600070122001000f00d8901d00485005011544da401e40303125006200c0003d2102081540220701595a504504070903c10043c0c0500c440710300190310401040c0c8035660001807003138206420100071007030840c0031142c2c042d070306010361241d0780000310040d074011714080a048115030444c030401100c5031050303000680c035000d94072000301303059224503000059014810300244042d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 265901088 1250 265899838 265899863
    0x3151e06150306090c04030b0405071502010b031b0118170d0503091903090803300705180a1508040204050117030412080d06060903050d0521040f02040e0304051c 71
    0x381040400294003000c2c0360317810f51400c0d5036903890506658089400741ca254008260074445200320840e03a10b03408150744000e010307501008000a803910380304d024240541312000600f1445d42d008020b4102c00b820400250350a0955407102042c4501001030108003d000e4803514801c04c5000d0000d81303001e40c0043d0010120b400061550100340c03682c0303c106505120014500082e8824100010303e11511464000c007520f03140c1c0401070007410900d03800c5201c2000410100700c00b05500400359200039040a440810340d081d0700c0c01055440d442e0340c1140c9640e24900446042064105c1140b500841c800ea5042210340e9039140d01c000c0548420b01e601116800800c000c1050380110b401c4540910301400341e103480c02690000200440e02107601900200f052644100b09112040c08030554440c0385040186c9031090702410a124030a401800390304200b42000403400b0702c1402400ca11000c3d5004d001080b5008a14141c079a803a0410f20801d841602148248050350210306200303a2200d40c414141080d2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 265902338 1250 265901088 265901101
    0x4050c090d0f080a0f1101051501050a090e0726010810020c010e0f0f0f03090a0603020c010b03070306020c010e0312060607021207060504091b0c080903151e061503 72
    0x1075100440d019610000785400c007101150408004154180032070702e42010840c2050009854a541618020f0159142c5005c10072098120b1400f01c11882c000d107820342c1e0b1260390380d05c10b88105925402010080403c0010049001e8100403419188040c4070070140b400c0c0740290002c44104402d0090740c01c0b5822511501c0c0141110390090901e01060740c0004c1840a51150058070f01640c42454402076440126412018102407240345850b6110201a42c80e020440003c07586c1044180b0880040550005200c06500829882520680c000400791000706a03681041c1019400c009070340320030303946410b1001004d410000216445a601d54410003541d50303410007042080c0d0484841641c00110810400324901da05105600c081d10f81a22920385030b82c109481c0c1c1f0100c580c08020f0020303900d861840d40c60300d076400c660800c2110f580301d06003030398640940300800c5c10440040c80e910a010641801e00007108080f03030480004034010040c101c0c0582d030350000c01000c806054407142c5c03160010008643c5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 265903588 1250 265902338 265902349
    0x3090406080f0d1b02032a010801060c150e061003031103042607050a06030f0507030b010c0f11060a0c020415030816051c05090907020327040603021002060106090504050c09 76
    0x11034504c1529010040300e0b0046030600c054010040c26041f411150300d400c8002c0200310002d88002860075110540c10404042c00c4001002c2c07011788010032890365544001c405412543c0c64034645003c0e1180c43c108079025502e291902d00046000c2281a4400620b2283c004240c0303088559103040105109900112085e0040d103410002d010790056910201d000c0c0c03514002c1740700034000c03541c00003a81a1150002411a00d02138040d03010141000c440042d140c1c1d00c03200240c08190042d0b000902c100080c030f0901c2d82c01c10400c160380d030000701c04141e5903d140e8202c40a240e40c0c500039241840220f544180400e040c00d910b000c020000389051018a51615105080048040c8520201d6000d2034880d00e03400c1340749030f40103c6000007a0340000c07825140d0a219100c0c64004010b4001582000310b0003414400549000d5045080c20080c04428000740d40c40da00018020750300908910401c1c0980d140007501c50409000310004038844030b000059605007403040c203109103003003c04c5c0e40c200442d6004111 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 265904838 1250 265903588 265903607
    0xf231507020f07090e030706060b03010f0503010c1d04060801061413060b031305030c010603060203090c0909060a020a090b07080a02060705030903161b080309181e060d0501060803090406080f0d 85
    0x40c080d22047c4040d42c000b8070341c0e20454014102d102c0c903032900ea42c94007041c40391644081d044540a82d05059405080e42e41111949000340042d4a0480e81d08603101c02160003010a03520100d025803c00710b0002ea283d2020707004c248145c5090301d524014006d04030380d000503900540b041112012040000030002903000003c8400540315000381c0c2e1502d00240211820b42e0020f4005441059000041c841121000c200240c841d02d8262442200c904d0841c1d5800c5d00c4890086c8501d03600c540025400c0d044511801c025009485000c15240d101c40081c10144040d8000c14480b40240c8901c00108445a01400c00d582c4035504000c015403401c1d241020950180c0c0301032030110340140300001c40a0300c402015800c0c070084c2135510025921610880b08101007c220f03a0070300101d45120a0a01c6030310f59180f60965500c160300400c1402c5e6440f0500859000c114034880600755500c0c054002c20300c2c103c040010490b00804403800d07c09192035006c29601c540320b8058080099014100082d0103901030079010 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 265906088 1250 265904838 265904861
    0xb1b160809330c0a080d1d0a03121d1b0f011d040207030909020a1205060d020901050904081b010f0b0603010627080102071a0106050403050a0f231507020f0709 70
    0xc4110130801c0d550b4808a40269000c0c000c003c0c2c0b252002d0740181c0e0f032041d580441c414110020011404207460241c035065160001101e0581c85101c0092015440700c4058008881101210041900c0c40380344d0b4841c100501000c0d1094604d102c551200c1d6209030000150b442000700309141b100d1109041000940c041403040b42070000050002480b80020310181109a003941c8401d48000c5114a038034084403401482c90b8850480394a100303002d83c88100d0b2042c151041030328400f88130b8a950034840424060141500407880342c002c40d8002c12308040d0440072000d007242c0018030000828104102c8203000034040c400000e2010700182100c000c0551031071400248400c9402c801c551610809030990307015035000d0303030004198034881519018500106004111038900142014119075400d51924800040540111401130200d81440481010003400e0210340580700c05200320200c1031922005518505c2e250361458000003011140045152410090340a025025036824441142c000741404c40e02c4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 265907338 1250 265906088 265906093
    0x919020310050d08090109080105100504110f0a051803070617130503040815060901051f0512100611010506061608070203030310050a06020a0b1b160809330c 69
    0xb92038849101055160380074403109650340344280700143c214070740741c0d001900c0c0c0e85c5040100000310f1203a10001054400c03c03203010502c0c102100701d08500340504204030700e03801c200182d0400b10b141c104008007919005079261502c201180c000700340d12071100348150030126040280b0f11031541e45010f0001d80c4055410300107081002503880752491a0002e400400c6154014220f0203d078200b88030340c10f41c2c00201280e450070158188400301e40c1120155151446200250b0301f803403540b50080055502d086911940342c2d102d45002c802c1582102c2c442d100d07107070109140c0c4621010414060045034801c1d9009484185000c0d1101941700040442410903900400c042c0300540040e5004c0c401140503076030641c6100e0003541090200030700c08000364081404d540c0000c0c100c10000c0e400c03401c142c1c1e10004c0483c40803400107180d103a5051a101d601b404103c152803144641c400c0000103005000340c02c01c2550024881c1142d5032000013a80742e10440c4200000000c448000042d080000801c40c110641c0309 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 265908588 1250 265907338 265907371
    0x130803040203100c030509010f0608071703040e070f0801050316051017090a02010e01080f0403120603021c06060f05030705060a0212041401080a0903210605100302070b0609190203 79
    0x41000071150500c1913103001a448800b8072a40070070901401c20020000a02000b81915003101c10390740304041d2041c15505803007000c0043c52a02c00b4421303200100034001644509142019005180500a03510a030104100708008105420001518400010304c410b4045c166418030b8100660068210400c0040040b29105078480700c0c0d00b00c2c55240660f0b4810004c03c0c0940c03a600c0007409904440e03110504200d038110400442c140e02d9425281c001d44c2500b45049119010250800544a541c0019400003042505140751104180c42c10110300d00550080086030349840500502c5a124819542e1640c0110014040c5240c004002c242000050040f280140301003c07000709140c01540c440244110382d00020040c03540c010030107030b900100019003000418000d6a001e490304841e01d25920086800110744080e00606a0081000c2d02004011003815107a42d50010069403241804954100401020549a08015035a907010b101d0709e0110426008103042110000d400003080c442c100d80107002e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 265909838 1250 265908588 265908613
    0x4020406090e060102030f030c130e090a03020d1809050a0b190306060902210702150c090103060b0c2113060503040614040308010b091f03020a02100203130803040203 73
    0x100a000030030094480041041c5480b4407070120001c0103201c203042d5041004405072501c1c0f08411654807840078100162141c4140c8611000c0d400701d13030070141e26440c03a50140700310b100c40001d084265600c40c0c0e00b190300020340f4280454190400c40f01e4030710200307a0f214062141610359084a64000c901c2d06d07000541d1408480000d480f14446410141c020102c44014802e01c8503d000751006010600801c0d0320b002c1c1480701900c50304420410b03c02d088020000400c11440c0f0a128090300070912540004450415021045035644403d5085020a02e0000300003050f4843c042a5030000d6240805001c03e5170102800d800030005004564803801d104000e80307100800035040c044081e03d0303103503100360300c0749424501003045582840034984082e81c1041003000180c1d0241e001415200e000e8000c0b0344a08600300030405481000b1302032103d1111082140c49101c3d415409407007403038460383c00c461042d01407000741800c92005582502c8010368a801140214038140001c5801c0351001d0111280c3c040180e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 265911088 1250 265909838 265909841
    0x303200d0e12010e100e070807030804050d060e0f030a0f0c020604060302160807120f0c05100b06210402090f0103050d03200c1b0604060e0d061b02060915061311040504 74
    0x801517a84290b03502c20000ca0007208201c2840070301340c0c800042200d24250b455000260059200d0a480f816154141d24200b000c45c1c0c01000401200303c01303d071003c1000c04690390300e0750004208840000c41041099100030710840140d030803190080d10312440e10342084821000303503010581283c008042041040005020a00104922030081c030010084881245005003015020581030b4108520b140d8206d02042000c207482280c00030080f00010700880d68008102c00d40503904500100c02c81030581c11051040c2d18a01d00d2045200f242e80b48910341c0c46004402403070b002070002410300d901c0200c1c03004029010791f0080d0b10101c05100d103090701d9810408500780720391002c9924801508540c40c80c40480381d962800e40204403084940318140340c04c010700100b5600340c0c01d0002e0f10901005100d82e02340005940110f0304d12080c0c01803200700402403400695584c80a0f111140d00740b1600070380400030750140c81da190080314010040020308080f009502c000d01070102100000c000c04000000340c582c2c59 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 265912338 1250 265911088 265911103
    0x30d05180307050324061219030e0406090618050903030a090f060e01201608031b030c181e0609011707020a05070509010f06110307050303010303200d0e12010e 70
    0x10103040f06490b00500513005d80401502003801000d000c40f805c01c0c18507010800444c00c000100410084422a003030031030b4281e155076003103900103151500100da008400c0c2c110201340e40340800e4940c4006d02041d40e030750032601d084544012940040c408203600d1507460300850341150144041342c0340380c0826101d440481d00307a0541061310303030354030031406070800d01488000344081e064801050501c0c61418010040d08180c40c001041c417000040003505000070300c14a2103c4c080b21507145901d034078100008220390b03805004100c40f80c800081403a00345182005000e03110700c1036400b5107126240a1001c0c80140d400c0a030070203043c044d60150510400d8541074002e0300c80d844a5008144005007820110b040c0040390308460b00454480d00113000003402e404001003151100d1400e03a40002c400003400d4190b0140700c0300202a408000000000d1550190303500f408180004014941e074440c844800360b40c0c4c0e80550303514021900302c00a140c000d1400980d070904801ea1040085000100c4000e1241842103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 265913588 1250 265912338 265912363
    0x501020313050c011e05090a030602070c05150f07060c02190516051f050304150606050301230a03060203090102040906030b09010c0f09090f0902090a0614030d051803070503 76
    0x701203809010b100003000740414411003800c100382c1510f0300c1c000041028031904003c03420301c0700015031301d480c40e1a4005003000454110404645417852480c201e00030031100c0c46042d00c035042810b00368641107264011100341180c02e500c0a45171034007640c3c0d0b080140400d07010703072415409403245034104082150941001580704101404d1101080e000c451020500d603080507000e03408203404040d416003e1010718030500e2440c1809510781d034481c94a10400c1c2e0095000520041c14003100290b61034000000e58140c41c0c1c104101d01c590180c070030a01a2010721003900320b92209800e6010004140b00345c0c020350700108080c00151170706440c0d141c40703000c0d074419500c2101c0000921040251000c820f101d4040ca0090500d0000c0241c4d813089001420705502e400b805240039034540b00c03140403961035803040c820141c3c00307840d8190600d015111100180468030440001080000d050038203440d01040750111080203032111418144444400e10b040030040c40c046405104600020600750b400308600c2003840f0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 265914838 1250 265913588 265913611
    0x311010512040b0708090a08040e10051008150612040f11030312090d03050f160c171c2007050106030b04050a06061a0403060e010b040e10110403030504030b0a020705010203 76
    0x184954020300240e0300900003280e54104504c800d0016960802716021107032140088110b0303807900361541030348035503540c4800d901c040d070b094580d08446e8201d030b0503c1c4103041012280c405000b001d030502c07552303108615202c1c0b40e90907503c0000e000681e14101c0f0b440b25a00a241d418045602d04000c280766034003120840002400800802c98818001c121502418040385400d0005091000780d124040c00d0142000ac50200d44080b1040d10a2050b11403810298000900c0300145502c00031982d990f61011075601c43c0d007004003c240f0fa10303800a00900c808146845450030640c558400d48280c150070006d000ca03a95500c503540040400c0c44c0070341c10383c0544d01401c0601002003980c82d04000701ca50750343c400c0d811405c100c079016028120050598040701d401290120b80016400b10b05401417990302105580a403800080200010b00058030180d600d86203001001444a0100c4042481c05903200040009408100c01d000195000050035005012181d016090005c00e944070360998204581410028 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 265916088 1250 265914838 265914841
    0xc060a021b0d1e080705030d060315090503090d050a0b0a0b13060f0608090a0c1806080c060901030b0a120b0f130f02011d0901080f070f06090311010512040b 69
    0x75503020200741c1049400300e03403803590504140d494100007003680800b4592060302000c2c04090169070000c0342c0c0304542c05000d50b41d58104280b08100244900e0200b034510607501080420004030714031901c10302603082402541442480402c006400c014800110ba590081591000008000303001e040c0c020500d07400041502c0c000350050200e10440340400e80190b40c01e1a4003048a038000440c2407042c0c86051030400728075601c854a0701d1500030200b4000700711b041140b100203000c03442c8040450159080c0103081c00926661407406648a42d0300d01900e40c4020308100c4e1559940c001d41c855600d1034005010010040e99070345800a00c1141c0c1e85083c2d40741450941006001100c210040f60702c051001111a08011941c0382c0040a86215900038103205546000f0001a030459840005074400184138032000e41c1c43d17107102602e5525080240620340710314000819200016103014041d981d01d9a5202c080502e942c46c0d140240006d2494a03050100c200700b07903c01031051403201b9108602504000030107 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 265917338 1250 265916088 265916113
    0x3060e0708010c140a03050402010e031b09060f030c190305250f120b0603070b1b061e07030c12020f12070201111602060405100207030b011401090303050c0c060a02 72
    0xa5400e4030844008000100602c1e010030648107040c0c8107070754018500050265994401a1442a103102020f4cc0c0343c481c0e00e0310b4000c850ba403890140c0000c4419074000c1e0740c44e145d810031b000c011a891502580d050300201c4903005941171110401e21850f5500d01a400f007140d07030340c0743d0a060802c040d0202d035800b1812162089800c4a440481004028180c0c444401f41d107004503190403001c0141e00104500c00755404210030303650401c1103034040e00c16192042c0d91410354178400c03943d000e02c00c1c004020b18020340000031030740401c5031110000003800c0460002d0342d99031714400310010510030380c0101c148003010007801615104d0784054200c540840050030394801100036000703802e001c01040041103a042c4000f02200da152031060302e00c61425910200010081480016a0750203250040c9030449010a80d80b07048550000301c8108607400b0b50b406030f1441c1d81720b07000f0742e100110120403940421881c80080001038400c400410070744501c80241d801c00c0308903e0004130700781e206034041401a1b0114014440 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 265918588 1250 265917338 265917341
    0x3330e070504030b01060e030f0706020102120f010311010f0210060b03040203061819020d0b0c0712020c01140d0905070602100c030b0f0d0804030f0605010312050a080115050403060e070801 83
    0x40101040c2070942c2402e186659281c81c2c500140221030030003034980030545046d141000559007201d00c0600343c2302c105450b640024001e4003d03e04000050703600101044402e4920390000d030503260446600700c1b00041200040d20343d1f008407104402141f086a01000c48407005118000181041802c03690792070409004052400780041d102d04230904c125244440f000c1c3d03000a0355800304121012646010132980002408017100b0840034019401e41c1e81040f42d000352980060640d58880c030040300200c1255032040703a40d0001c9203490b034042200d24051f1240701c01000b0290005c1103180c400030609440301c0d42d030142009200c5e0b008201690000484891b4610180241d030f00c5101030389020881030300302c14009440540791407031203401a042c6444400034859140c04440103036030890070100c540c4600b0701d4220010301c001d110684401046100207000c00c1d2041040f02e0040c40550303034090301030742000328000468110710085004c0c0541007200000044190064140f504614030140000300c6c9007442650 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 265919838 1250 265918588 265918591
    0xc140f03071412010e09030d0203090606032109090606070f03030c090501020a11190e1302010f03021c0b031009030201091403073302121509090a0303330e 68
    0x303180c2c14002500c0d20794801d1010341c110303213610404c4241030701c0708001e10b4114071a01c81d68802a0b400081080585a00002c0c0ea5008007800c1e402c4446004204805c1d28446401002d2021440000c0204030034516110002030340104006101901e400303203a0703690400541d10310201700d000c2510751888044c4d10f40c0000381c020041c1800e0020b4282c070841584e660010407407905405200d401d0300400b95078500c0000c0d220380041d2140e131000c0761b02340c144244040a284481c0e8000c9002a205400308101c45200c0d009840c00e4400c8010b5581e10a26101e080402034494101c800760540b083e01000414410745018001c402c50007600001410281c5080c041200030032404002883d900c00c206800c001010000c2c000a520307040d682d125100301c0c4842e00c020300200420250402c041c00480c12460100241d0800c0303000d10580c1404280800034170040c40b60000c0221120b05140c0c104000b0180840c0c02a08030f4041809841c2d407151006010b0000c4800e0b072802000baa0340000c00d8842c0c240183c06152641c00d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 265921088 1250 265919838 265919867
    0x1404050109020f04050709030807051608030301090f0b010c020f01111b03010e01090210050c071e090506011418030309130c12020702032116030503060406270c140f0307 74
    0x5d000a18120101420181c60343c80018800000003412605121090100c10101c0c5d00402c444202c196665690903500d400a0180585c1c4501c0d014a41e140301006200c0c1c807040b0041a100c1c88942441a001c00c0042030712907220a0500c1400324440b60058024020182c020340801035101f007800c181c901781821541d9450312641280e2400a540c0d0160b0348411004078039006e10310700725075102d40d41520030703040c00e20701c1c0e1003501c2d85e5549a10341d595144c8801400b1048d20002041008240e540200444110b200032a01c17034486042048260a840c0405c50078050107a400f500703c0e450300d01110081600084c81c0d8011310415580d03400e03a62149540301c20110b40d6400e4245081d810040f2a40000c0d4881301c02143e01c1c0c1c100152580c52000d105120380903900400c21680001e0300c000002d007000f400c103500444241e032190b032401c4408a44103050f0229903030b4040c06031142d01100034035081130100810821840e0000c0c404001d900c01e040303c2e8094010400340c00d10b03058241e141d00704080302404e001124443c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 265922338 1250 265921088 265921091
    0x1109092104230303030f10030f0f02090609070f11150405030c160303140d1b020a031808060109050601110a05010c0e090103120c03030f1406100201050106211404050109020f04 77
    0x1607540b0b40d4000080d203400c10780090f5500c01c5511460050301c10803629500003400e00410a030305009002d4000b4104140500948200d240d9a80b40c0b410022800021240040030600c0d040003951103510074451040725001410448492806906d003800040c00d04450445442c1c4c0002100480d02c5414001c01454482c00108401e000b17046031340117051201400310b155017000000c00d8020784041e43d03030060310303551a40b100144903141a1140007502c070140f0102c103034017040381d81a808806048800e01d050403180c0500150500707908000307516008d01009070246040200c590443d80090105002100020740708030000240c41340c580402030f00180a040d0414803a00c000001007000c16808510f40d405101640b4101402503800d1800350010503030a40d102c00380c02c0ca460701c070b8190420005031645c003640c4d084520000348003540504900340c03003003409100001540307403d048103900020084840d05000440b03020030081c141d0040001200c0080342c1c10b5446039145c1c4208025030030400b507049440f2794103560 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 265923588 1250 265922338 265922399
    0x303070809071d10240e03012d0b010801060c0b04060e060708041103010902010507020d1b080106030309080d050415020a05011505010f0c0308070c1703090a140a1109092104 76
    0x171207090750300c040d1484c80038171925608910300d039034082d440003011034810705150000d5001c8042c01041080600708181c562482c25542c600d503503004146441c126405659102180c41c55070381ca41c3c541003400352046500e95242c0c0d00c5101603400038060340307128440da03541c0c00c40c0303500e424204900ca8603210f403421400390345802d00c0b190160368440104c50406805031207400322068070b8038240e640380a192031300d09204084040d000c540c9000640040d001c40e4025074030464265110712049403140712034800b1602260007040200800300204642002c1c1c0ca4550058601040190300c50340e007500e03a15400041826140d90040c4800c0d80c0021943c903001e0303030070310f00081d00c1401c2ba54090030a52018040405001040302403004009103d0400090b80100054a0f43c880c146400300c00da40d100c0048040751681101c00d48141c00e804c0024230620001e030010b02c0f141141c40e0305070500251500262213007426000340f6001c6881101c0e1962200e00001903101030507642d501d0409290502401041460400c900441 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 265924838 1250 265923588 265923629
    0x1f050903030f07020c0a0b090f010801260a080d0f06081c03051302030f0109062414060c0a1a010603020c070b0d02040305190c09020c0303070809071d10 67
    0xe6a92003078605402c2d0742c803034898810583c80c140750754405544c0070000e01404150f014103035019100050701034801510680041006582e00301090041d15908901200760194280c00d2940400300320f40000c0c160341202d413841c0c5030780c1e501d9480803040003119600c0daa50b0126a00c0036100d03001c020321066006c0c1c48200e50340b00c5a6a20301000c032112104041e11240803500e010f8004100f42805640101100d074010510240b490103020a001c1c00c0e20001c0c03034a805a410304030943e00c03003000790302c0504d840e0070400d06114a250040c0b862040e0076811038010f00a03080503100802c01001f910303000c1c1400450070314210020402500c8140c1020017003600500085c100c00700005240016a000c0c403651030349403100d6400c0b10b8001d019a0707001804034801d400300d06403200c6088920050070b03030045d010321f503005480d8441c0400364848c4d494800280d500c1000019001803084c40348540101c09002600d015655a503034841401c952040107404803410501800004800794801200070107148010b440305030320710b8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 265926088 1250 265924838 265924843
    0xf0a0e0d0e120304081c0e01020a0b090102040506070f060f270f080708030a0507090e0c0306010908100b030c1008060616060213030201120902030706050708040305010c021f0509 78
    0x103140c0c80103010090846101c00d0340c4a9050580c0803145100b260344640d696080540d0702e500540084000f81e02a00c042d846640c85021b1180240350180c00400003882155282f440c1030000903d0031226560902010845942e50001003240d14001d0040301c2c501409400c001c401c4520001528840910304a02c1c150401a520111000c80c07a207003101414070441400e090401c141c3d0302000174101000060b1140c10001d03094084c5004046080003040311355200001a604045140240002840d06800140880c40c000300211b03400341c010702d0850122580c4110041c41c001081441080440d00c0b40d8148045003000c0241c0081c483d41110000d03c20081d0100280c040c0402030150b502521000564820000320010000c910550048045540341001401c0c00d80c19400d07404224002003400002d04942041742c0121031131203800502800300b040c9002819901c6501c06a411900344030300340400001f0400a10034444900c81c560080d00c00d0101c2041c4c501030a40802050f60700080c5485d05214040000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 265927338 1250 265926088 265926103
    0xb010f080403091a040509040803011e0f18150305010204050f010503060f120a050a050a030e030a0b221406060f0a14010c021815010809010e06040f0c0e010306050f0a0e 74
    0x80c1352030030402c40000c0601401d880b0300d80040341c010144100b4481004000d07001113048030316500042d00480e503100c07403c0c400d02d20a403003400300c1840a1031003030142c01024001c4001d07544541c0307800140c400c404141d080301e0246a91080e20a650701050801440c01c06440c0d104480e5400d181c01861071421000059060740083e400358010245c0144044e84884100000400580c000040310803d4015240c480c0e9180c0f40b4020032400100c03151886400b6007400142c0118103984101c03000400e0b82d48000340170718071003c400a0381d1580450401c407000300385100d00c07074007104c3c0c00c1d44040c00640c0761400a201d01125200340041c040d210032b0904000028084110304210301007443d06610404950001070f103401000110600d152450400740300044c2440010001b0551082e25848000e03074460a80d107003250005e04103034055410030b600081c001502c3c01004044c042c40380783c95990300c5865031035004407240260400c45003150380c1c0c014004294072031010390742d003d40d84030018411070300c050140356100d120307 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 265928588 1250 265927338 265927349
    0xa05070602072c090313030804030201020106050d03020a11010207090609060e16020d030209150d0e0c09070c020d0c1d011a040b0f0304170c01020a0915051209030c0a060b010f08040309 81
    0x10000b003000c03104c040c000c0b900f55403820750344a001e0030344038142201543e20500c8100c0c059883d202e0006500e0a10552481c01a900f68001c0c0c00321003115200c84000000b00c0399594114000c040020940c1c595903c1400050802031800061807410443c10003040c0c00c0c003138a83c4c4c1c8901107100782480160340c00181349a48180c0780c42d016844003c00c0300400d1060281801002e248540414601c020030b100e0b60001c083c100d9513104440301d0301c140e002800a09003081c2e51400c00912060b19290240c03c00140310712550f4828031a851410b0f03030790341e4100034411461002019100311003004000e51028908800380600412161030b140c1458113010307200074440c00e80000902c21000c000501031000801c1039071520380142e85c58a036a50100c52000c0c0c003d6200a1240c0c020070706c81800440c1d15034081e180510300b29040e8070b40e5450f04c8003001740c2640c000002000b00c10300780300c2041030740d040240a110b400c841c903101d080040b424000c40400580000141008802000903403800c01011981c003034101012a60b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 265929838 1250 265928588 265928669
    0x60408031e0f0d0903121509020c100e01090b010806010803030f04020103090b040b0a0627090f05010c1e230a17010b071403040602120306040b030a0507060207 70
    0x5180c81014118090b501040100c581c0115001c03c11440703e8010b006414840d644141074401c041e40c40b0800c90b18180304d103402c20741c5003600510000d4456070003031500c46281e070300711141036078522204401e03601c2030000c82c1200d0f5121031f64082044420340d64240980203030b8015094542c103000d8410ba0b00c0c000204105441e44210f0301182c2913900a600c0095001c1c1c01a42a01c001e143c1810040d14540065801c503500f075242c50000140455030480b0700204843c0c158003200c032181d00b500f040c80903007040c62094915801c4c103081c0701c00150007445402c000c54101d03140d5401c0c05042c04200e0784041e121507150010302c00d40740c000700c1080f440b40a1240121314580b020580301c90f0940000c0396440c814081020500903004008505070450030302030980940700301a43c0740c0502d9686440c1c0d4590060f0301c2601d000d40e20107841c1901068140000e0b5074800006840004c00ca142800040c1c60b242005105881c6078100c2401400615410700c101c601902d20b0900c480d075100d801ca102c5560b010a140654034861 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 265931088 1250 265929838 265929877
    0x121908060a0e100806060d02010903021e100801060f1b020d05010221060f0102070503100905010f05070305040521270a060f020706090e241905030c06040803 69
    0x541e6807a50030710141200002c628450b02e450350b21100700c0d0400b40160000c034442d04001452500d448031102e000d042e8103a40c2d01001e640384d50f0030302000c0d440b800517103890403440d521100055110313140d1a06c0050380c0b0b0b135202082c65141040c0a44581c03456030140c0100304001020700c0404100e00c0380f104000740c0c10788001c07000e031b20a070900700e0090103200d08150386043c135142140d450300f58000c030f12400364508440645458150b0307001a80c0d5002c0b0341c801e071505038004c2ea46024100309554824001d840c000c2002049811103041010103d5008a424074082540c844c203001c01c0c85410007500000c81000c0642c0e04015441251020090240c602501c0d200000d0403510884290440b030000c0c030100c40501030820362904c808015001a40310644000148503102000a0740e42c403c1c04038600f107580c075905522103900c8900c10703505850151040c40c880c01d4100303420708007035403109003202c80c4507a24442510240da051404150400e030001d1072032480341c80c06100c00d210f00c03500403040742c0e00d4001000ea1411700 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 265932338 1250 265931088 265931101
    0xf0301030b070e0a0906030c09090b16111c0e030111090609010c0501090b2a0301120201180b0c0c0105040b0919080d050d060503011a011103040b03040503040305121908 74
    0x50083c4040d141d009011000001a240829040101501c0c410882d82e14960707244c0950348105d03000d211000d0030b4164204003060035401400717000d10508101e4505040002c4403080c03c5031070001d552099803450f03560700350b03441200d50380580514100300d4120001c3c0400d0041d6441d003880c1e4000e0b13074000c512402d0b0010f83d20013140e001b59042148941e1060081c40062620b051142a816044a01d64a4418003001d41110641180c0007091400c13200001c05007036900384104452101c00d035240480c14850891000400202006044001040e02c0381640303541c0c50a5450312401d068000e250305043c058148020300c000c071100c40503210000000e842c1051004d03481c8040300c03800c5800da400740e8000e010f511408186190302800904040c0c250341b0050280c1a540c4082c1401c8804044e699160f65404000c1c8812070b6102c0c9a01d04000d54003501102d0800d9218600c29603950b1054408907501d070b000040800030007806002480e540c001c0714080301c0c14910102e580568502050300c01804014900c0d00203100d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 265933588 1250 265932338 265932347
    0x120a05130204060f09050903160305070f061404110a050114030604140f0f0601080f062103160c090603020619020304170d110d3002160b010b0f0301030b07 68
    0x18550024002e2003a1a52605000013403d224000c0807a8142024009140d09600204030703a8500c148181c880c032103c40c07035202101c25400100c41144c1c52614541000041390490080a041102d203403880202c1c0e080030b00d0003800b0681826100ca0160b4001c8004009680c2c1100c18580d000c2c5400e40b0310ba6481d074458000034000c0091004807a02c10072a0010b07c001c03c0802d15101b40301d80e0211508204984684005465640040700e8080311031620714001046424401c2040348201200f0340b0010080c1d101d0181c2e1415030700001c0740880751082c00c00c044030500c81210024002071000581c00c100d00c40c03e60700440d210303218500c40e6180c038a4046201041d698420030445004105048024110301ca00c0c80030181c86000440f09800003e0400f20002003201001c600f03140c8000c3c154491a88070500000e0082d00c0c0012114071100003090100c06a4030194240004d10a81140b840044850b0406141013075003a80306800070340181c0400d200018581404104890540307070030821042d070340d81e902d407000c45 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 265934838 1250 265933588 265933621
    0x60301110c1e0102030105150a0c050706023306100c0611030103050105060a0b1801020c090403020f0706020a120806040209040f02030907090b06181201060602070504050c120a05 78
    0x10600500007805100711007000c1400c20600c0341c40182090070582e111911802c1c1d0000b801070a03031001100c100105c08102150042c00a01070f2414410781721402c079100d65081c4030907a407040300940c01c0030021100306402d0503e0a4228050110380d41e2070300641c0304042404010007005c603030144000c80c15200c05680600c074007120040d8441410700c4410080204020075400030320044400358200070108089180c6500d011058514030b90305141858034007918000307501020818141540603c5e09000000d880d034025091146001e41c0007803c030800300404551910b00164000c0d000c41d088000047d0001d5443c03c1c801e81c0d0126689080d41c4103485040001e0002e00c15512034075803051501100d103200c00c01c2174020f0740c450060345003a1a0055070303071041101904c410002c0b4507406a806c0000d0a00c0b02d29030310f48074001c9200617244020050001549a003110503030380198000d68800101003006240c14029079900c88003841031075040100c98403400310414000382c2141241e984070000944100515003100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 265936088 1250 265934838 265934861
    0xc03020d140708100617060408090d1401021324030c050c16030308060f1f020a020306090109060c050a050316140a08090709020301050d0303090f020d05010c020609010e030d05060301 80
    0x790040b41d540c5003031581e50041c40f00e00c0d925060505400003401d80e001c990070100725070032001030440c0c1c2e03983d80d039144080d60004040383d030f004c0480c0d001f14012503080d14001c4110703011a800140d5415140d040416611020ba014580007442d080344017050401c0f0810795011076103d414046010540c10405031824001c01e8200c005900c20903d0700741d925130300d43c0d04000c201c902940310201e07142c03110701c18008542c02104050360810701e91001c85c0d00700190140010443c010303a03c143c401c40e61060340040c1c10130800b555041c0413a0344400328a014040f0038443d605908100c0d05003c1c4c600380024001404500000380726014008c0c0c084001c044490240b60080c942142c82c1c01856550b40f41c11078094005c4c0e10942d5018540c1c8036103440800c51100510849050f110014554101c030f0700c203650114007900b0b0340d4108441ca5240900c42074010385032442000700700c41c440c2001140c075001c0c80308002d1074a04000c0c9140c840342c0c10038001072080031002c01103901c0c46440400108940d80c5200129004d403a851524 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 265937338 1250 265936088 265936093
    0x50307020409080702040c021207030c020307030203151e07080601180b041d0a23090106030c0b0c0f061005040c0c0507060e15070c141c0506061302070c03020d14 71
    0x150003008403c00c02402c00600c00c881c100561000d6803401c030f95590505100000e1510204102004a4000c0e00e0b20038200388018111000e4603240d0780402d0925010f58001c1442d6080750b41402141c044400c1c3d44222410101c04035052482c00103070003000b000c4080c282038103110b01001400301d8404022080300c003030100410150f560700d94540f038602082081d18004002402e809011440100b0f250140203c0d0030748120f6000310800130032202092030f10001c0c0500007035640ea5032000000815a00804c0e0040a00080301d0b5101c2c0c241503c00c9041602c0c0718003101150300040c003088a8003440200c660250390302918000b844034100041504d054600d1000500f56200b0380c0400540f203948005210034410301a20555560542c0c2c08443c0002e01400c0d500038800503000e0000d104c100600c030b04290750500010720b54110040400200700303c003042041c0a640359086801040700f6030402d100c1e1741003a180c2000c411407800c00315440b01c811903000c40c000244211446966031040c410b4440c00044440d9030f0381c09 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 265938588 1250 265937338 265937351
    0x609040f0b04050615040908040504020a0207171c02060f0c0904020912010903110d020a0809060405060d0f060f0513020c24040302192004021308070915120803040503070204 76
    0x10084ea80b1030085581400c44049881c1c3c2e1807890038140114403541d64440f200c141064140790811000c0d40200550602f184140c1c800002d100484580c10003000e00c0c00406001072500895041c80d582d01c607e5a20010b640c844c500344054131141e010703100d130302c0f1240244441d203a0383e900002802030302c154054254420416608a07050403419808800082d22070b440790208541010411a2900b40207619200581c001c1544807012a464400604102000a00040c5400c0e02c510028a864000014904009030b440d0b00c1d890a81c00d00d0721611028168059504802d03500c0c0100140310000d2031905001110740114642000c0a02003204a80070494100300d08460f00c1c030301001000c9101c1c221003d400510552040510581d800104181415000300c00d441d46059014000c0c24900b17041d034800c41d0015820130142c0400304903940002c0140c2a210080d10a80f8500700c20082030340c0c40050035525030300322000100102184140000001e6038442d11007500c83c0d403581041ca00318000e24002075040b500303210 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 265939838 1250 265938588 265938593
    0xf12020c0a14010c0314040b04020102010603230106080f190609020406170c04020306100c030207091a01020c0f0102030a1224051030020f0a020a140a0201080609040f0b04 75
    0x110914240c4461030000c0010144c940d0084090343d080c241303181d040300074010100340842c6040821075400b50040c0000f280e816500d0740c2e1515580d6100c200658041c02e240c2038145060b05c04c0c0078617001880b1034401014403004207154203450b01000a44c0c0c15034070200e580f8610801140350840da000329001401001501e43d6103d82c10030a0354030480451040c043c43c0d088050b580307060b1003a44c0c024080500000c07174030a10b024003540c03a01c20300c403170550035403040e00300000d076200e2140540c0d0008001c07891142d0704242000006840e24491030504c0380708071a400b10307007200c0382d9000040c0c0e207028580d483d140c2c4100c0025980c60006002d290018a01c00404a4000302c400d1084420324003252419034080022030b003038400407610f060090012030002d80c8031030300c16012244c1950f0311510013010743c00018a480c1086c101e0340303019030000101c5009a0840f9040e00148240e80070f00c1a030241809c1c026040f00549940006c0c000e080c0100a14448e80e260404181400700c00c141c01c0d2810b55000004842a040c5030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 265941088 1250 265939838 265939853
    0x6060a05130e0a0f05071d151f020c03010b0a3c0332071413050a05072d0f0c0501020a090321080a0905010e070f08010501060f0f12020c0a 61
    0x44c1e00c191039901c601c007000610b8080c0d2404003440e00d0a052440203a584503100704072000210794052581c4001303000c440200041c8811502a5001c1543d0001c140790f030542c105242c00d4890001119110f480e00650420064201850224403000c5139041003583d00d94044401082ca903e98404201500c8250700101c00c10450410140c0917025a00e21208124038400c00d8202e075250351001080c850300501c80400040e0340580c0070064104000f8a00842118401d2208044403c1204c0090314107450703c00348072046802020a001440d11402000050780000824210590380341090030100000740c113200c030f44144204d50b04500254002c0003555544501100100414010f01003035420b14019210f5500550b00d00b485014110300307580302c3d040c42c3d513983e882d240000c0c244500151201d540b0780710282e1780003106000304c601420b58200000d07681d034208000f0301e08490051300442d06104040c05400b80658128481e07042e1091075140012101e0584024803004e4024481d1001142c462004501c0030007500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 265942338 1250 265941088 265941113
    0xb13030302060109050105130b0102120c0a020f120d1d0604062106050112020d0b100f0e0303030f0f070201061809050c100906080c040b070b060f010206060a05130e0a 73
    0x1039070031601d903642c85203c4142118000c1c4130701503100341c2144180c07004a1654104489003501401074460242680c14139140a5100c8040032840c0e40104140d80c0442c80d000441d4040f1000940e000341418100d065425a55110109070b502442071000b07075058540a405020f80943e0b03c003800c50764440d6036600000e03050302d060300d5010404000f95880e0000b506200e01c1034000301c842c140d4814440707440840b0304100952010000141c0943c9581d405003854541024810b20001c0075922503000c02801040103181150700d01ca514800d4204106101d11010072107203086e0030410140311000d103034848450030f80c014029684070b0b00340140a9002c1e142010180e5010b440381c680100e081d64030312682c05d41081b80c2241340c9400340001c0341092000f807280901c00c02c00c141d801540054003501d0141c8610844043c6e421251044980580fa94204100c2e4106032043c07420718a4207000500c1d0307600b4842d00007408281540200f50141040301100f0780c18031215084041807401c0d220644194140c00d0915220900d20b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 265943588 1250 265942338 265942343
    0xe01020f040e18120a02070503070602030a1706060a0503060315180d08010b040b1b06010f0f09050702070501120b09040f02100f080a1a031015090b090408070203070b1303 75
    0x900c800140d400d40001040036054401c12015103601d0034225401240c175006048040d0461042c940080342c2924100a000044d00e9550021502e40e030740d00400806000c2c0e217880060304e500c143d1090000e180c403550305584080c842c1c0d04001352245d07a20783c0030900e01190001455a10f45440041c014001c0180e42c1d4036401c6114003007658061503003000d043c0c03010003007849950000101008100840a1003501511204442d03034202c0b1a2555160794281c50010700b0f801c084004003c1c3e0b00200a50800480c445008004e200818030092400100107034803055940304181c1841082c1c3c003560003200086d0700101400200a107030044c542041d050040f50480002d00481c003070007018101c03c082d580260b04008003c0c3c595602c2c040d265852140b480054018031442e000c20001000103500f07195018807802c1007505500000048516600044007002c940a500404c0c400d07103402c0c00c0704910740725046443d0f8050741003072809907200e0f8a8070110386014040c0c1d0202d1540b1002107090305083d5608200502120b0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 265944838 1250 265943588 265943609
    0x15060201050105030d02060112170a05090102190b06010f030216030302030a050a14010b0c03040906080102030402150901090506092b05010c181512050a0608300d0e01020f04 76
    0x3e0b00c4006240e0750341c494031100409a070101004100c1101840306002144d4410884908030b01c600f510502c0813034120f0002c107000305d003010611300c0035942e0400109024507558070300107020001e152030b42888680d01614040c10042441c4c0e2404842e8025012103510316011500320312503140c0b0b0300380140250020744082e500e09040c1008140302d03400c603002c2e256420162103e181160313442e11107111010350040442408078041448005036592252241c4e034001c3c13007100b0000d640c0740ba152040121100400e030003081c8104e0140211020340e64850003520075100c00345c0d4241d6445a00200240c0b12030a524050a8912080420b500c0e01e13032441041588224405d4000b4071084c000040180c500d401822150403943d8500c1d1006c02c50382142c88401180000d040c10840d9100c041d0210006c00c3e01c1e42140c2c40380c0055226a02040040c4042045008011800e1a00c0c209001c1d9088d0820011540121b65045980302050700311042d48030fa0702004d0100c244000855644010345158101e0350840d00c154000013 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 265946088 1250 265944838 265944841
    0x4080106050f0904240b04050709080f010911120a0f05150f150103110909090d020f0303060d110105040f030606090c03020307020606090a1e0203011a070519151506020105 75
    0x40c10940e1a09000d190312174000201c2d40c030101c0202042da6650148203a155454881d07004281e02c1380d02c40d050040440341e4618110074200a00b40380341c00d030286407102d0241c0c03501071b4403808904651000c10030b61a085a15019032803003a08110b1a201003080080c0c10711145501203820404000340107080f000100700c4a90056480c81188440d07104116280103082ea0900c42c52505580b01740c0c0301000001e4529501170800b03041340302140c000441200d41307900544c4100c4050004d181c041184180c28240c0100440c07561600b030010803141c0300b00c07800040c05401d58500392400c9070b01500c15a800b6150780c05a43c2452580e03410020081c24491080041061030001d10309c2d00345200380201d82c8903c20a8009241d01d0300c405080c0700c003018004107a8201156a80705c00c042120765401101c41d41148a507007d40caa504004260002e603003030f98082010204208104000540042a01c8111240049814100781e80718200f411181494099604986280400007072241c007415a0380b805450f40d9074004c004d80e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 265947338 1250 265946088 265946119
    0x30c04111b1e0d0c020d0c0e040b010515071106031e0c21010b03190e030d09021011060c0d0b0a03030201090303111804020d02070b0903041d010303080403080901060b0408010605 78
    0x1912041d0f0380310400101002c070361402504004030010806403081030300604403980c800d041101c2c80c1060340d04407450329030306004010604d0f00b590308a00e104d000c40000f61901c00e19903101594000401209405641c002c000a83e5140c0000f002c14408042400d156030b60b8584013100b0425544042d800c04a00b204002103110080a140c90300e505032804a45000d203151103448003111003d0031881c0c601741c2540ca4030300803c182e01050000e4281480e4510010900a141d481000341c50100481e103030040014449160040380000503015402900b500780c03880da104008400304025000c030311700c00c0c1d80082d40340780c1c000101581503001d000100d01a507400c101c1c1d0304100600c070300703988244440200004c2d028125a00e907450940c1c01040f54808040c001032400300300369030f940f040c030030201c0c0c11008a8101050401c02c5074605464104c1540111500c0242c40d8155076000d0302000010f04007504019000740000c7c105072003588035201034101083d07840e03140c5503a501039901801c0c60780a1580146019041800c5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 265948588 1250 265947338 265947343
    0xe2e0f09090c0612060b0d06050f0603070c20090403050918010501050301051e03010f050907080a05030a0e010c15020301060f02030711010503060a0902040f091802030c04111b1e 78
    0x2551010380310b40742520301042100c03000401d0204a016a545e980c000929120070710040061181d00707080852003500c0c1030308024100403114426400340d0402c004000405901c90122542c0d181e204403401d84090407070141c58004d5030040f41c00c0b6008805c1c42c052009260b00800074048002048449070500c54540700c038030b424441c081c4525404540d003840107020078074001c2080c02410041031800451612000300103420b5442c001701201c0100c1c1e0782d03000e025140030180406e40c050a6200000e0407006805d40d40c030f907900e204113250705042113218a012001a031041d00b8032191680c05c03d186000c2407181c403070132100039442071045002092041e411000c00a0012059801c81600b0032607204c3c00200c040c00568050b80001d080350303808036150744007103030384401e504c06072020305000121a1822400e0900c01012191558118048210584010001030b60300150ba07a541d00802c0d0b078089144604100700f440d0314040c9080d00c0040280d002c0100142d540001015a48002e0001d0000c05c41050522040d4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 265949838 1250 265948588 265948601
    0x103080414040b18070302070c0f061e08010306020723010515030a0201050706090303062616140d14030a17010509010f0905060d0f0506040302010c180e2e0f09 70
    0x103400031048000349194644e54035440f50702c0300d0302d401c003d8545001544c4003901401075400c02591141208400d001c8141d00500001000d400304240302c1500c180550090f0504405210040800e90002441800c11a10002426141c4e10904038115055002c3e400d41d4080d000440d030a00c1010344228000c5110702e40000c907103180305e0301a110f0500e042e01035200c56003c0c14044000b40e040c16142c41c40020141c41620b42074000340c41040c014201c01d0302c5004482d04100042a0325a816810300c0010b102411a282042c141040304603800c1e1404056032420700802c0d45107507c1345040d40001b1035040a070542012911035034501d646200100e0b0382c0c030381d01001110349081c081d202c0042082407040c00100d4a50744615003045004208000d004816516400c09041c07440049900e90000d0052004064090003045801095800c100d440c000e41e4041c40f1420145074455028a880d141003c240c6207030f01041c0c080c24291681c10382c440040e4504228101102d841e106040114184060004588520f441f130f01 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 265951088 1250 265949838 265949861
    0x11040209010e0402090612010303090807060806091305010b0411040519031a07030b130c1107080d05090d0206030c070311010c17040206191206060207030c051c0b010308041404 77
    0x102101c6006005010003900008045c03030708500e003042110342da076503041c2c0064002c510039135807400c0c2682001005400c0811030780c014001e01030603009000e42d550f100c04580d0ba00c1034000300c1c0d00f000c074609400c010740540300324420f854201e403030005014172030900e540040041c5c0d50182c82d05880e001d0f00304421055003c052201416061110041e2112074182010701908425203143c0400c042002800090307121040010304001c603903861102c10322a90308100400400302004c000380502c075240811003511144403000c03507010850000381e054201ea480c040018042c68016140540300e24202844245503032061f8010340204030300c900b0348018108140900c0f8907107000d9603079a01c0d0360703980d011402003036210140041380e000c4414000b81c0c07800c2000108490001c0880d80c1da000c0701c2000059100300b00c070f0b015003150f401c54103c060140003089031aa810790840742d00b502c030300881741700d40c85001e00740d1402004000e040c10207080002042c04030086c0a8416a0702d094507110311050300030108400c907038260000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 265952338 1250 265951088 265951097
    0x261008060f0403140f04090519090312020a11030d0e0c0607031205060d020d0f0b010b1e030c090d06090b0c04150305071e23040614030901020412050102071104020901 73
    0x40019108509844a65110010060170000e0040c244251904160455028241d5032020401200705402040841010703c4000300715405030780c2c500502004003907100340301280c0c0004040303403800e00c00d070b014500203200c1a055a403500070041005c0c0207840c4c0c002c44041c40d8802c0f01c108001c180740402c115501c290341926040950001070074614081c000040c009940250840e504030702588483e42058441441025182e0002c8560305c0c0c84000c003001078202546901091044c0c00050f15114801d90640d102c1d03030801030310781e650142118200d104100701c0b44d03000070040c0307400401c01c0602d40044011038861724014003265075074030b40038105004034825070f15203048189681881d14040e9010640009142ca040d01702604801114901e40040b810391000207620312101c10f0344611b0103402c1000415551225603d00342c64110010b20510038052071006c124030000214100c04025130403a0010801e001c0810101d4030f40f030404a000350840003042d0fa450410a0070141c10745060700c01c41e00400416102c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 265953588 1250 265952338 265952341
    0xa0e0f030318161d072a050106051504060908010506010e06090103111306170601080609070c0614060405060d020a140409050708030c1612030e01261008060f 69
    0x109a420503100900c103500398000c03441041101070700c400c00c103c003810010002d000c00c500e07041e4042c0c80e4520300401c000c0400444d51a400796000c0614000308144580355003458030010141400c500620407940115404a0403400311400343d140a4041c10444045441e2074240c0c59540350100c3c20b84000f00c81d0103000420518a0020501d001c9024144852061400080485030070b0b4410105078040340145514990a200030070219a0201c3e12199401c1c0c940306480c802d050410010b000880e0140c60a480744551100092085205644140b412600300300d00b0300030a80c40800c00000014241e803001d00135414800090803605000a214147c03580c0682072000140c0b405400355860040c1000140d441521034400c480441c41c1000108054012000034607030711916030304083d2402619404146242142c0c140400c508003104944003150fa8160408100300207219004031044542c21218100380e402c65400c51080410783e5608038415a401da445000c0a030700e039113800d90766001c04c039640c40c8440c22220 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 265954838 1250 265953588 265953601
    0xc08030622050406020904060b090607260304030c0209150325030821070c17090d06091a070507111c05030703020a1707050a021e040606080a0e0f0303 66
    0x1d01c0302031905004580095810361400148050720301c1a5401c2d15102e03004500445103181c10302c40c1c0c800410034004030515020800c00818007501030303a00c018041c1400ca48041014040c04071102c00c4141c841c100c81c960764641440c000c1e24580040009a00035061340e0002000c00101c504a0b1043d048010014040d403400034030030342100103195a9001401342184400400110800c1c054881c000044940e101e169420014842a43c82d00512042c100960481c507003001c40d01e03038050344c65080078215030140d85003421408900008120800181a28079020344101841001e150b031403035000b81c081c2070205070b0716001c3c41260b1034062480d000e8040b07038050043c0c032001d00d0003c10320b000040c8804008600803096484440c00c6400194040c0c0c09030304564056001c01003c08690310340501403500d201d00340b00075074035040d40e030307c216640090080141e5100c9881210000346070840c00c0c2c00040040c003180f61203020040c001a401c0d10000040c0c1e08090103100520f42c04560b030b12070303089001d0085007560b0710031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 265956088 1250 265954838 265954849
    0x50618040609020111071205010e011e02030601140403060c08070e0f0409140102030c1b0d1b030c0501180515061008070c120c150c050a050705070e0403020c030d0c080306 75
    0x2a8100e061105c1c50481104c1107800b4843d05008081040c0c1842454176941099420f492804c2451141645040f64146203020150f480540000940d1001030302c0350346440050345c1c1e80701000b548031a400c9000c20008204841c541009410364000d5503011902e4489020945400010a000c0c0350f1280c0000843c0700c06d03042c207520030305003207008400c10f07045412800b407035a08a034420b58000f402050000355640c01c20b080c02818100000035200104a8503045d20402070941c610294845540280c014149003072510841d0f191780444d80140080101c51142100e96084c0c0904038022203550290890f00b000940c008460244181c0d00500b01030f4034034074802402c8070400f00041024003400f00440c054800b058035424190b0311a0740b2912080a28000f0781060201c1003032b0040e8000b009418900203110899009081d43c8800b482c1341403041e1201003d150880c1441002e42148012032002001c00007030550000785000901c0d019020344181d40b84107107040325850080c0b180603204900400c01705400c1c3c1010f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 265957338 1250 265956088 265956101
    0xd09030504030b0f040309060504080624121c0305011409190203011d06060715021803030c010c20060601080c09180f070201060f0b07050304080601030f060506180406 73
    0x2914080d4501902e0796201d204019099030721146100c07211040008140e0840f6885c1c1c098225820040e041900d8070458556500d00240b02013118040390f008420b50034030890840b60481c40c020000c11401003401821566030103501c007218040f01010104a000e54000d12815040e204c00c0c0f040c41c0c080e089500e090051a041c00703800b80c0e00300850f108a0f2903419460388041e6018050706500780d200d00244d004240000075014040c40e00c111410800d030300008114601503004140058400741c0c69030000c0381d200321070004014205030540400aa00c0000c400b041d80a81c1c503a441c542c540300300b4010a600c4803000d0003e0040400d1080d0f0200c0e01003500e42d0700401b501340d446616088024034012000c000700e05560180c0c8140c50340c01000704140401e90800c0e05000703034048910310080159528000e2403021a80961049030440500060702d10140542030080b140070b4020301088841d2941e4074504051035000b615415035019140030041680d51074640021a1f808004031901899a11180c80d0350004050 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 265958588 1250 265957338 265957343
    0x60a020622030e06071a0405030301092007020915060a0512150303030408090d0804030501090b06012a02060c01060f03051005010b04030308280f05090c03030403150f05240f01050d09 80
    0x24075000c40900c2100c80081303601c11423160000c1c54903545880005015640400030815000d0441d068144055540c003090b035a02d00d4040f038100d4083e40710301040046403070909170071030340000340002d9003c1681c0e0840c0c002c02c1c0e4207100800070225542d0f11241d0a0f01201040c41e03903a0b01da041000880e0108003031101a01044c10000e108200082c09643ea60f0220f034000c2c0d10071100c1da51a130580c42c0c240300384409519880a02800c048030561031142d0040030300c00c6c2c4a45c0b032020700300f000b01024081d500c1d1042038a0308060510b008100e842c2e181d4581e145005003074070080314179119102002c1e13061145801002d0480c2d0504a6030f42c00c107401c50790160750b220b5000704501d00d6840d680000400c403840182d00d075a5030381d107903600004860031801040000d0f0303000104441c8083d03000c011445000d440010440702140c3d0003003002803c0230304540c030740400792403c1d405100c0500d0400091051005002c0c00e4100610020805184981111424420b0018908658901003441440004180452600208000d52 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 265959838 1250 265958588 265958603
    0xd080c09150f2206021b030d1103070c0f0806131101050703050d050412030f180b0702030c0601080303010e011d04021302090301060f03110306040816030e060a020622030e0607 77
    0x1480c03803c2c40d0454003c402c02125a02d410180401903190140300201500361103e00d500c07040100407010a40e108203a0008204101c0207115001d1080c40500c00d5640c5d4980c007100b0100543d030348400c054400b60750380c09030148a004070380114802d000c0b030040403c8800d900101c045140c058840042d075a03908280e40c19030a001c810045e42d682c4580724801e90348590300c00e052050a01120394002001c592010010a48080c03a080090100c181d0146042d804290f03c0810b400d080d030350b05c00b412400c40c080c1050402441c8102070000c2840600030024605032001030100f1466aa030721003408000d14503214448058000ca407000c5405410034043d180c00e8100104405481c01c007885002c2803c685c1558401c01080c242e140090042007a0304000000300803048004003031500f41034440c18802d201d0b0342c4900030203111003203002d000c02d4000d12805606484c01408151102c442030030194590004032414150b03e0000440c1c41075103620510f004c40255016556501c040800301d040c40002c2c1e00010090b100c40 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 265961088 1250 265959838 265959847
    0x313144b03030a02060f01050a080c0f010302040b030906090d050306011e110322090203220f021f090608091009081207090e330a05060c0d080c09150f 66
    0x203481c204002c0c66040c2496005203003901d0700c250400d5109006800840c85045c258801b00880a00001c9401100800310344d00082c00803102c0c0180c0c001d00c269401840c2c00b040120810240000c003144c524440c03200b003000d80d4150038600904803003174802210401d02048111103030084204618100b842e1004890030b065105022044a1a01c0d580020805500040c640c0c0ca01d08403030315410140800500d0b071070030290b082d13080110a01c5651b21001e000c110340106070594101c140010303400043d041c1a00581642048100200c0c0f08403144e041c034030240b01003a900310000400510801c1a6885003c8250240c240e050b0000c030120060803003c070080d44d07903103c180326209800d8608070075107003c1c0b0219150241f80d44e15000040c45c8001c07004151865202c160b031420700740c1440d800e0100a0346544c1e40380320450001624005518054190081130300880041b500c1011400b00169804107080542ca510380389503200c5030006980d1268032461fa13003082140c00d6802942c6003550280a0b9a1034420302c50307050 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 265962338 1250 265961088 265961239
    0x302240103080d27050c0409030203030c0a020304180b0126010b0d06030c0e01030b0a0606120c02031201030b0916080c040902150703080406060e06010c0b0702031314 73
    0x34003100281c4c00a41d410000c0c2210030401704102c5410f403014282c1c3d0a01c01c00c03a2986002e500c0340001410302031019400120702c01c4661080c8100d40150030b8440040c43d103240401544002409103610b054041008101b510310045044d025944080025203900d0038560b00345100300007540c111140030031420391105d90100024001c61540c1001d8101040002c0296240d41400c0009810180451080f03d240c89001d004c003c0d8400016071801c09031040100d041c50f00908100c0c070354800e0700d191340042d4034000008002c202c1320071070350f0780075a200c001140c44d1186d5081c40803030303d44900c0c8940c2c58964000e138250b8a0b141010781245007064002400c0b00803c10200d00b21841981c0401021800100040200410890240320300f502030300d2a01c10203800c0c0d02d04640003910403894690041c14001d01b402c00207501510800031035500540c1c00d40303918030b002c3d6900c9800b4044459000d170a88181100245071404109000c4c1d0900004003000800401101440595528800103560429015100a0601c95 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 265963588 1250 265962338 265962371
    0x80a15110405090f15010c05070e181903030e03090d0f0204090b09010b0307060e0603310c082e05070302120c09040501050a0503070608270a0302240103080d 69
    0x2107a813103540ca4072460b103481d000c440b82081c1480361150600070f00e140c1d80c4000c1a00041d030700307083e5503120800c03418039210040602e00210b56506445400d02c108850a00c0e10307603000d203056080038441c1e10b041c80043c031013071460342c0c0b00d01609442503040420451181d0206054a00000b6058000752000480c86100d8483d050b12410403078900c891070b91102d40d07a12540c02c0400031600101260315110140c5061100000c03500d100240102c2c0401000b5180f1551426420994107040401400703594490f189619049803d624203114086441c02803034054005458200c0d0075051100711800400080e00c94030380e0b040c2c01050302070501c0b070401d9824442c0d074080c04011002c03240aa80354540b0f40e501c4a040c0707010402174a01c141c0006029450b040820083c6407000150350382901e590f8102120b01381d40e03205400d02d100304424048210081c401c45201840c00700403d03c0c480950082d800c3c3d41c0c41840401400300300b02c1c2c00d440f1700c141c2202030000400120303079420080c00c1d02040d2000082803089440c2120325 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 265964838 1250 265963588 265963591
    0x60f050d0518030c0d110a030c020607050705100e130213180b0a1205210307031802060f120903030603120a0522090b09060f010c0305040305010e030a0306080a1511040509 75
    0x81035a88051817100e0402c2e040441891000d40910040c102418150340007084c03030b0b2002c0750090065402041d20b8080040c28459003000e890058010013000c41240c02c01030100c141042103034024840c80000c5031541c0814001c075444c14101b902d102c845103117481c80041703c0c001007000020030aa941c004c100415605c07140e80314001d180f040384040170003205080240c217006140d0308840c003000044054440d0303190b031082a26881100b40c1400554408003c25503005c03001c841d00021340c41040007403a80310f40454400035005400545c01007502c166508040607a4a00c4140c076115032503800b107200025840300340c600802c270040081c5801270900c2d021098620382403030700e44400001340c10350f00c0c024071003031798280304a20100c041121a1007480c100750700400c045900d030251040c100902003003041c007414005d0049800956001c0003c0180e00d08104400c0c0e03e030f400c07138a91503000904045001030240d20014800c0d600c03940088107440c01c103044c0c1c001c4d02c004204000c1d041c10620814000010607030785485246 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 265966088 1250 265964838 265964857
    0x1b030106020c0a08150402060315060c0114010602241909030306050906030c060f0d14130c060c030f11011e0207051e030d0c030902060a030e07060f050d051803 70
    0x2c0034540e02d18020403070101540e420494299000d80d4909070015501050250416010b0f5100c2d65227880382004c0d10103220313a0382a56030304a50000b40c5100030080c15400103010b40d0615449a1840c0d0300c07100100d84840c0f030303045400c802c00d80031020854845071840f10250041c4500340e03174000190341c00d210f107026074250f0792041d00880d41c2d07000104480d04041500b07a5104100328041c1500d000320400041c3c09001c0d90482506040c0c0c0450300707092410096015110340340b80f90403c50710b1481d0142c200380e850920b10504072480131001400141003800344c040011060780c5074881c40c00814070b03034104407285252403042c410039648900c0035804845a40c02030b00110741c0106000b41c0e541620303003002c034581861002c00c07100d680040030f020590750030044117071820840c0054010940c03408010b021005000e05c0302c1c01030b40c4550009141c852858056001000308841c0c0301c2a1782c201644c0f580150b48c542030f51951003021510400030a84044401d0f444298440c00300c0ca0a041c483d00311900300341c03868101c80c101d0b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 265967338 1250 265966088 265966093
    0x3060117010b10021e0d050403030c05390402030610050903010603020603090d1106070507030c030e06030a060e13231204030305041a13030b0c0903120409270b1b03010602 75
    0x20174060007140090b0013903081030001016075141c102c0b0010083c0c130440c4409810030042800c60020401c050045400482110100080d180c0000c0340042c0c0c400e07810b250a0803c2c2d49500f0f2082c49905140c025a80f092000800512540d0440350702074910342e0120100d0ba41c5550303100c50110059030389030f01a50284d0310800c01800007524011780a00034408000b00c010080c1c0c052010025601e0713008040b0f840c3d540c2d062a2a0198521900c0c06a4145030361451899009034040108021101c080d40400704966000103414010703282c600a4500c4006000c034045c5c48400700c1c01e01050082c007403103140328191141808551280101508400803900b140d08201d002580000c0c0400074a00c000d1240084040107982c020724005074081d00d845c0704e1003140320013000800d40100140c21044000306844118101a05440100883d0b010f00c400d1a07016001e100001c1e49420b6074450603c05c0c0c480a8000c4e640c00d0002490103640700c2d10b48840e4050010810000d4910558491800103c20b034003850080c0f116400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 265968588 1250 265967338 265967353
    0x40609060f1e0605040608060a11040e04030f03050a0b2b060f02030601020115180b13090c03051e0327061810140a030e030408070e010504150503060117010b1002 71
    0x1d01000f60790850388001d21480c1440e405000c030040c0425043d420a4890310001500001b01d11410401d0141307502c455400c1802c03038100010300d604422040c03001d0074141c2d01003200fa6900b404050894414a84007034101e146207c00081d10301d20140c0210541007200b903412030302c40f210396504064444850001d0420343d0044180700586d602401180812024642c41681b2182000d041e80c485190510347c03c80c01907120203602d030858407000741c1c081c034800c1900010301c2101228104020500c0603484100c03036602c01d490342940588580e28510038021102805985040c21000118105103840307202c8203213502240480189540c0c0e213800400441e02040c0034405000050020840f8040601c607002050025070080c1f48120060700782241c03041555400c00240440c10b00114a10714092608040d840303110b050340110702888859031841c100c034002c82d02402400030350000e200e4100f140d4072485070103900100c01801802070500c54050018440d400024010301c84000080ca024502080500580c0000d0b0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 265969838 1250 265968588 265968641
    0xb0408010b030309012109120818070b0901030b03031b070906050303120105040e0705032a0f030606010c210302030a0c030e070612020408010e0d02070609030506040609060f 76
    0xc1c0c1d040c0d10300c102d000c1c50a00b6103100c0082e200046101809004a0340520380011000c43c0c4c0e0700c0207456a40164038004174250510025000003016900c00404103240860b80a00e8400010386100752030034041b880b420212000010740c081c02d02c980c2c416074180400d00ca8166460b400c52f00301550214804018030540d45003945100445a20781c004d0381c001d0708100610034940544e03001407811910151400038400c0100104907040c44695001a58940510001c40000800583c03458610f00703104606081c0074926103040041d07951181d03090b00d805821000000d01c4a60103180503040260091014100c5605c880c108010030402c03010420340440c3d804010701009203141d11072120250002e050420106140e010003c0d980c42c8148145010042c05a20000d0280141d40581d1300400c3c81c200280080d00b44140000e0702c03101d900344c8050051007040341c0003c0c001d01c286904412603400c240a0595030b03da503110b1002034491604186d0b8915181d000c0c07121800182c0c0b00300303111b0000a840210003140d000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 265971088 1250 265969838 265969841
    0x4030509180c0d09060f02070f03090e060d021c14010f1103040203071401050c120d05060607150f090503030109060608091606030908070209161b0b0f060409021906031b0c17130b040801 81
    0x4ce0020301070f0310b40350310030080d4985841c4003c40055030103c41e4407540890b80341d000d400b034041d503440040c40207040301d40c041100141500900500f0381c4000082c8521070070401900742c14041168040e500d0744c466601004401e81c3e812500181003010301d05203203031540d60354003103103032040c1c0382080e00c804507001540f1742700c0110300d10540e50052011211189032074059128040c810154442006d4019503030000804560819408425000d5020040c1c0380c480d030b51035240b031004041904c030320404502c503940020307410704000c0f0311415003142000d4950241070900104a0040c201c1c008120340c0001c0030801140541c0d91800204e01ca11200b804941d030302c8013490801095005003c0c43d0308910100b080c01e8100013070740d00709081c2d400340000030380000641e10000018003030100d0610203500142403940990768011844804010303a9141d031024040160301001d40745400d800c40c0d8151001542080002d00090a01d255445218054a240c0d07814203d0213038079840988400d84c00441c010368006001c01c4125000e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 265972338 1250 265971088 265971107
    0xc0703090501030c02100b0613080105151002060a0b010e040204171b0307050d1b080d08070206013005010501080a050708030408060f180604030509180c0d09060f02070f03 75
    0xe10f001e100304204010040e41e04d41c199a00d5001d403a032074660281e103e0b1650016940485514000c40c0b80050780d074109039000703040554000d0300c0401d132035507000000d00301003540c00241162640102291790703502d40c01c440184070f01c03440c4604100d035900f01e031700c07096170f0b1400134101802d0074000c1c80d862050380d0b1065610b070942c92083d80181d0440704c22440015035001c50800c00b1a90142c90f0089140002d1401007203410304130302e08000c52404e444010441690001d104418056580c03a00381c030701d0722014401c0e41e88039002d20031000007014400c0400c03004145054502c900c0f1100018102c52058181e5816080d02d03002d802842c01580f1403a643d000f030160812500d0020840003024524090030010101e445400003031000030340001403000301d0420b05a0305030720411b101c002819186a17080501d002481a03000501c0f4610843d040f8860f503241d400504910782c05641907501043c9005820241440608600f0030b041c0c80c060350302c0c244030b0540515030000348000c910441040d0300c00e01c0c1c14a40035101402 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 265973588 1250 265972338 265972349
    0xc0c100801090b0d03120e030f130f0b13030311010209030a050f12030c040509090f1005010501030b040203070c110112050c0703080f0702100b0d062405010c1502090d0b0c070309 78
    0x141c028860010940165200003d8006c014001c01c0790301e0b41c4d0302c1003451031054000c5c82d00d007111300046800018001061f8103060319018000e00000070343e00c5002d00090301440c110001c903550015810000a406240c04104840c10f40c80003604080c050301c00a401e102410710140c401c0c0d0840c00d4103114100f41484440c0e034002c0440c2c2510300310305100c000c400043c0540d0040e10701540796980410380f007083c10044a040b00041d40211000420600d0149021f03000a11070359003c2410b100303004425140c14006d5a128100a54170302075180c0c0280c48101e41811018075a9041c00469442d9840111b16800703018400c1c4420108076688940c0d81c64010055a0001c0c000c58a01c0c03c1d11f42448070f1315030f0102c2c001045203040000070030b13600b901200161200c06c0c030f00390040c03c1d40d02d00601d400d4510507014988404c034084a21310304a8a0b690401512100d000400040085001100c5100d140d000c69025103241400540081040480c50740c071201c000000b5202503a1040d008201c40b800c1603402040a4040d00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 265974838 1250 265973588 265973599
    0x10906021203041707082206030603020603070315180518010212040b0702031c090507060e060702150d110d05010f0e1306110d062907080c0c100801090b 67
    0x6080660101d0903000103003000344642d12131008144600007541c00d0710011500018480c0e541c00c100c140340800050020f41040340e90f00b02410015141e03020344601c034101c0390050f040a185503141c0300201c004048080d4070904410b520a07000c504103c64280300b84410700c488034001404d040452040180c2c1c035840311408102d81c01000300f0041140816401500980c1c4400f8012880c0c40d100010b9003140071302d0200305040d1080c1d0511048809098115040c2c050041055501040c0c85000407644026040040d540007401000f010b170041c00c01c40108100e90b894103070300605003d40d0305000b0302035401c40192442c5244c0c02117141350459505108031401461820241d030102c504c0c1254000c1c80c2a0020300c01800b50605192400501030107410025444180c001c88941d11914210503400605444c00340d07510803440c403803501c1e8050b981c04450303882d8401485450b0f4204401983c54995540c80402c549400d80100c2610034103d8030742c1020706a202e07003162134014031076050104980031070b800c40e403000e4800e9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 265976088 1250 265974838 265974853
    0x4090206040521030a36150c02040221010b0a0c0602090103240602210301050f0d061802090603030a14030703140f040302070503060103051213090203040c030201090602 74
    0x16564402101e040b202c0035540820501c00d00c400c80342080c107503803214415a00001950501c02179000341501008031020345506000e08a42c1441c2c40301344208042d03402111194541840748050b11202c1140300702e002d140541c0465000d03804a01640c05c0307000c06599142c0c0390078016100003843c003106ea001d0007000c09041d06064005034000c0c4011840329001e00000e50005542880da407007904958221140e800c6802c400c0b412031448945241d0b0b46100700001806071408107255080030822800600050060583c150390800c41004401107080c81403a92007a4102014400600540a82604440c100d0300e4000c071054240103200300b4000c02440c4030305c01e4100308258651541c201c0c0710000d0801c070040ca4940c4907034900c1c8094000b041003a640004c48511803007084120488481880d210754070903030030b607071034180d941c0249a44c9050a01000740b1542190180807200311111300a05880c1c0c00c0340210040d00c61b65405080d080b6401601c00751a035988400e010302c00e55070444015001072165100030840c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 265977338 1250 265976088 265976093
    0x60905010f0c02060a030624020c030304050a15022e0b090919080f0c0609070806011206050403031d030c06010609140d320105070905010c350d06050409 67
    0x8442d580200078070901000c180004082e10aa0141d070281000094400030741c0c1e008018502c4880d90842e07000014440c40f10403a40a090200540b03088a801038883c88806003000120303c0002c081e0203800c4114826a058000d00c440d08081011071078101035540038000000000c0d000a540200c0c0010b4003400d21142444060b0000046512501909480703101112150780340c10082c03031044040380c207007145020540c146040b00215030309014441e10320482e4800d0350782d1002681c648030248203400d10b0565440c0a00e010400c070390041c90740140f2a142c00205c52441d82072209602c1480640280e980d0b0012402d180100d100704241800b400c69424203899075881c000704401c81d180742c9020580910200b801c41420042111545410614525003002c40d200c9808150003001c001e002104080b903082c00e020400240c094a1540c055070010794549040381c0403625451011142c00e0b40c995a810300d0803484142e0802d500b80000030250034184004da07113030b90b408440d40c180c44042e041540303d14a04841c6000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 265978588 1250 265977338 265977347
    0x10507090f0902070b01060804171c0506030f06040b070207050405190e0c0f04090f0c060c0c0b030103050307120e0d06150f180b0307090f140c130905090c06070c060905010f 76
    0x445500c1e01e23146145039250714240000040b815500ea014000200350a000211070b5140341310744030040d42c002c10482d075854040603581e102036402039400e82c102c4400301d07001c45d0001d003555070301c8039a43c01180c001c00d03900c4010500300c80044031b201c4082d440d021072120300c141040c0030301c0c3c61030b10b0034000801140c0100c400150751075440c06034952007256511600020043c1814107030355000e405c0501008140d6031a500913042d0302c211041201c800d1220074002c28003159002c181c9042e290004015428a42581c0d6150000900d400c2080107202d00f46100044994402404480b041d01c070b45d00100399800310300b2500d03242104035003140d0130002c4035060505c10760550000c1d28141d07242e118401b180e02d480c808007107420002070360064452036007400500c1d02500f0b1581c2050910f821295400d842c559200090140d19004541049801c16580038040180c68039542105070803160000c10b540080c1e000c01d00140391588030700400c44492580400402030680c01c171411a00405c020f00b00190305100c41e100080 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 265979838 1250 265978588 265978591
    0x30e0f07050603190509010b03010606020d0507080d09051c0e0f0114361306030201120b030129090c0310061209020a090e0111091806060705010507090f0902070b 71
    0x60003900c2c0800040c0d1000040304642c101c03040070880800c8942403840040c1d01811254040c00d0003503082c100300040d01480083e81c0700040c1e0319039a5a03418103500d07555028190303000e1450740070000d84a1040700042a820f004050000402901028a01c90a20320140050003407206903446000c0e84203c40d0b00c1030360800f03a03000c041800795466aa4500390802d6102035442403ca00e4004079007502084607400030741901983c03100070112900010000e4a007505015a5100e01009002510400d43c40e80350320b03d160402400c24100900102d01d05012240e117000c008a020040c83c1c000e100510791601038101480e0b85034000c010290344501d580751280441c00c12031341c1340c850343c01007054160454509103ea9407009040c0f50b8028a1640e119540e0030440c0040c0a0f0041c0507040c1c3c3d4a8443c100c40340e000303c0c80c00c89800c007101030200028585a121507110003040240256082417041142e400014800e00c030b0184507105a0321500d4405080407007400b203010941d00135010075032040082c5004030390b200200a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 265981088 1250 265979838 265979849
    0x10f030f0f05060702060108150c0f090d051209040501090605031c1404090204090b09010609050103201210270c0c050708100e1c030b1c0f0201030e0f07 67
    0x540261880c540700c1895400000050000e020b2103060141843d404100c030b60407a02c000e0225000c107103101c442c011050005a1308140040c0c404c21068907180e0113000508103004005140c501c907460243c4415050014810141c1096100010f40c281949050f110325030140c070320180100b110a0034074003c030303540742c1c044408462040b088c0441104070354811a41c0100002c991a682d54071295207910800207908280134481100e4100b00310781c4900e051003640541269440d94500d800c030351802c0c00641c018840e4000c100c041e80550000d041204089000400a101d500040c0d00d15070320302003002c001c101c00070b0740000a1240304403400d104980c003540648481520000e000081e1042c0307100d03041d02c0200c0d205074020064083d20400261000e40401c1c21410b208400d401800003110b0101201e8680481140c80140441c00c40000341c003a612a50000308103031405813051410154500c001c0c0c0103140070f14404c58901c002951140c0855a146c01120b40d9180d20300020300c200b1012018486d1150340500a4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 265982338 1250 265981088 265981103
    0x60b04090902060706060b0703030b030606100819090c030c0b1204080a030b1201050a061e091107080c061501110a0b070509061612020a08180a05090c07110306010f03 73
    0x54020b55450804840182d54007407800c0004e680c0d150b9100750903402c10b5406031b000c40c0c9170401e000d0003404d000c129a0310499009280081c86800c159060343c250802510407500307068001c010303501c29042032058110326406040e030745200c94075514118400395044c0d0842074646900388141c0c0003c3c2143d072881600258428111510307040c40f078000324001d14514130440d03400110302c0724a1591001c19072020f8015810300609102c200c0d01d441ca009140c0e0445003074807040030041c4408010307042140d48504051121425400d24020060721084155002002c0f0f0741015000308042c00107401c01c0c10f05c03001b000d0f8020300740701174040d4640905907140e40c000040035195004450004041a02c544100e0b40c405a0040480303407500c83e9580e80c0110b969150400316500e00f907000c00c01c086240002074003140150302400c0c86141a41c14008031943c50007a178015034104100280105043c0d480a00144c40f07003c056220303a4071280c00d8240202010403800307000e8041d4000d07100500a40d080796022505580c1c01a0a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 265983588 1250 265982338 265982351
    0x608030417030d06030b1503070b0a050d200a0e01090501140a03111603020705030a1101110a05120c0c011701060e010e090708011a04062a0510021b01060b0409 70
    0x401c5003148100000e00d00441d15241020003044088210301e03014a01c0b0000d12000020b101090507501d210900414050134014800d05040ca0320a50050045011001000c51107034008620034141e010681034044000e81e0110720344000542c00044490402800d01e41010a0382c98200041c1c2211504992038990140000301601e03814001d0f000707207c0c6001042e400d20341e64100580d001020202401c070840050141c1e96002403145000200210003c1e0005048403c00400d000199078020100c1c10a8270340d03025a2010202141040c4040007160182d052072654a0303848401c228103003000e800c446e5051280f400121114200c00c101d1050540c2c4842c10b02259500d2040c0060701e1a07009004040c0d07203d40048d04115105500007012030484181000010920564880b20b1070240600d012340390014181c2d150720006040c2d801031118102100500081c04006d203030721002d0504004440084159400240040b41c2d06040c203e10501c113400d003030081054a05010040c0b0103840f40f4410100d10b16103a11 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 265984838 1250 265983588 265983629
    0x2030a030804051b36090c0f0f15030403020a121e0f020601090209010e13020406090b030112080711040912140406090909050c12070e0a330911030f0a06080304 70
    0x71046449090070011701c06040c41d00b15902980c0c1c0e56000c15280c0100d4000013040c4050034040094803442000070306075180d114040b03155042c2900014415011489150080c0c0cec040341c58a4083d244400003696400807041110302240c0c1d81d000310815103403c1190001c098a03501e0f03404940641074a088400141c1c0c0c4078003d0300100c1d12040102141d50707015581680c2c60b84021900d5004008483c144c0c0c40d0b148000340d0750060300150b030209208d8854000300e003a0000c0c0024410100800c034840c0b04106403104c0c1010b000200701100c024030000c132004080c1d4502505c6564000035003444014103d0001c07490309091403802403006080e40302c4d143d5545c0e140c0422008004080c0003205500c3d9000c2d151449030102e00c12000d5580c5d42d14841c02655224240108003d01058011140b56910030903280c0c00c003242c01c2d0300811610000d00485c1402008a1901060707981d13640c080c28115003036403040c454032810130000e503282c1c402c405440c40b00e155180080402c6000c0000c82510f0468110b11a609451140c52 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 265986088 1250 265984838 265984909
    0x1602060609060f0a0e090c0904030203160611030f0a0e0c0f190312120c0e060304020d1a0a0f0b0a03170d06090203010b040311090906190902030a030804051b 69
    0xe03003405601c06004200420300178545180c2ca441408071034101d4044940a0b024031143c458142c8029005030010802020784908805071403d0007849184001703403050f511010200282c005940b507842c0444580140030010380030b13010341c0c0c0d8854201006019501c29800c002141e007041300080501a08400100304400c91020b24010021038201b00c0c0314805000e50342004044402c1e45041e04038551800c0301c00c00c15684902c08015200c0d1010b08904d155840300e4081059406441000b15112500035541711700c144030140c16030703004103201c0001003510403610200718180e4901a69403809009245400c10204030034900400c1c13201c0c401840e00e50f44801c0c081c1903202a003405e801c0511a076000000001e5400c00d05002401140e001d051414000c0b44030300c08000450742e0507213058016902c100d010810301c0c8402800d600d88000e043c000001c01060b26804030342440381ca0345060703020804110800060040c1844022048030f81c20b913844034a032407031100240c0c070701e005c0d0201f290046030481c0710002d0b00c5814 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 265987338 1250 265986088 265986109
    0x15010203040312030506010801081606110a050f0c030c040b06030403140d020703020d0f170609070c0c03081305030a03080408070305090306041b0603110304060c2312160206060906 79
    0x4003c2c280c01420003038010703001c2d240c103542c0c0700d0028820500000e090100819100c003601800c00285030740c5460601d00312509444034800d403c60740100300000300018010804804041030040150441c2c40012042509090340132282d03901413424520b02402d00e85d07894003221761051b814101038091040204081c0d0090150007244015140700040b00c07010716400040801c50b5181c10f42e5003074030303100203e00200e40040342492401d0406520030080b03852380c80c004111a502692a1422203081b03c00c94507602000c0c0d09030b034800d0321702c0715001800060703103c100c001000242c1410350003002d400745180e4000b02990801440a4500c0c4008a401410103104200303e8181c614018101e4841e4101410040d422881b81c08199605051001d00003511a00034080c0a08100400310a64155070703c40d103400b00a41090584001081800c82e503034082e07000c85654040341040c02c000b070f130751b201e5001005814002001030004954800414140040154002510b0fa40050241c0d08407903075444040206507120302 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 265988588 1250 265987338 265987343
    0xf050a0c121b050708010b0d0213090302101109040506011103030112030c12022409070612200408012706021c050c07021804020a030206030c0c073308150102030403 72
    0x2c500300c000501c1030008211064803020b000030803c40d91600200324040f9050381001b034000d038005c401225410056804092454040c1c01958901090135001e50700701d41c01c0c0c107031441000c08046101055802c8c18802d6650080c02030038022500540390701040e9803030005108055002d12141040000c0520440c4860b20403030380301c0d041440b11001100c0c0a51101c09892548a5110704c15802d07403101400307048020701544903400644000c5090a10403a914481d00e00e42002181e226014030981c0f646400c00355007000c6420604a843e03505085c8690700391042c4604001c2d03050f0891040c40c640702c00b01d00c0d101c50b5030303a40329000507a10000c1c45409000791200050b00c83e00b5070302d4001003090001c400d00003441c040380f0884020003440b091414500b80000161006034001000d103c0900040c11300350011a00004454070690030094052a8285010020b80005a2428041d00c0c0c010240032002d4000c3c1040e2604040d0114000715068006d1542c8002444244912811405011103900a00071a4080d64 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 265989838 1250 265988588 265988627
    0x718122a120c150c1106090117010e04031202070b0a020a0e032a120303011e0e070221090f1c0204020f040e1b030403050714031201060f050a0c12 64
    0x35003a061007540c12440b0301c1004402c403c00c4021102841c0701c1d1860307a282503403000e001558000250180940c03a04050100ca0521500004d040d94004400100358000c0454140151440c0380078034000304120200c000d40e040745401400f030400041e0403c42540e611006c80744006031180c070ac007501207a0714081d910020b601030050b2840d0070041c2582903070b1150305c500c41c0c1c00300c0864004c034542407100341d0300360406042c0140c00600c01481100080999551a1030950348908643e07900c41a035003000c84419510000541e2100c15075103000c402c456104031400c00c4020300386081003182408100c90329490107a0510482800512444404041c44c180c0203076900a00119101d625624180d81240e105004403000042e441c0001f94188400c0120a9480424500c1c6241140c030f550303600b40c90076040a1011100c40c5038141d04011800400c0011300000d54001110f000329514103040a0821000310002030100b09003009040c0444d0741114080c801e059000e58030101e07604010004890440549035000e0085 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 265991088 1250 265989838 265989869
    0x3106050405010b03060606040303082a1602040f02070b060907050d0606020120070c0303110309100c110a05030c06030c0408011d28060903090e0718122a 67
    0x401c05501002070340310b0a4040f1703030040d16070204001c098012480300500140100002551410f410148010b1010440d148411002d8100005000300e03040605403804170000c6085900542c0340078012a1412001074200710b01d060b08039112000351940c01400c90b400b5809450104010324414011611050f100c0e030420003800381c4504000740a82403018041241c030b040c4c402d070307030420a207000202c0c2d040d568800380d000f1101b0b10710b03a019205c0004a00f140000b5000070310800d5180d0f02c480f017944c0090b01456840408460951400130340303050321403100301d015002042c0140520b8038000f5078541590801c64680d5101c0d07a84148800d00c2d84240d40005000e5402c0105510940080c1c03007100c40d04642c107001750340000c07080440120f20903440004901040000c000c0100204100790300601245020b4504040025119080c43c0310548058910320700241c2d640000c0102c000d000031700c1001905001100e1a00c40003251210400c5038441511840001610105a003540002000c80b0004240200251442c0e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 265992338 1250 265991088 265991093
    0x606090315011205070815011203020f0a080714061005060d02090312090a06020c01080a020a0513140a170303040201030510030507031a0601051309050603010b09010b0307020d02030331060504 84
    0x20403006143c122180c4c0300310880414101c4e070100d40365000100707105085115030720b40000071508880794103060f41580101c508518901030244100200240907082c0940e903400203243c0100541d100c0201018550044001c2c8243c00001007418411100103c61950312180b10301070000003482612801c55252058410318000000c0f071402030602d204007110000e544a955890907602c0340c2c075003c03540d80017900100004000c0010740d8003505507004685446030400c000b17440e2040170102e00d82c10403600c145d405140074250b0320b44084041c020f0901c550300d60f8040c001c0c0e805010b0303403030001800003418507450b1400280b08010240009000f0758005d011035103040c2ea6801c001c0e4407000064100b40c0920300c0340c00010100c2d400b4504840220642152004440f40b4150310380c40206030160401d81d065489035041030141d55005000b9010b8660512075540d0381c00c6c44100030b8604038086481d9010754005000300089060f0956008009040d0003200010b02140e00700c1000a50041703007c002d103403c0c58071003403109 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 265993588 1250 265992338 265992359
    0xd0f020304062a020a120903060c08450f030a110705011724031b040c030c05120406020d0515122a060903010204031a06010314060609031501 62
    0x703003420010600c04070f0016414a0014000500f1540c101503404114180c000404c00303802c0d5a465911450401c113199120707a030b0002a5160404800c00141602d010b10038079846414903607070a0242c04402200400707200d0981c00c000c0a903405440c0901e45450442c5121610911910010441c00415079684080c52074014104001c030202c00740062080041c00300c1c85501071802e021085050154044403035880f034503010801074024a0328104c2a00040c1c501c20b03641c50400c500e60001c04003000441400d10035000740000c403006455040101820f201141c0e042e01d070040e040360358483c0300346140c0d9015621814480068451111120442482d00c010800d04800102d0340b201c91070011a0341c240400c00600401d42d130f500843e0304d82c0c1132262030000c1d400c2016840310002c82400001400407810090203c0001c0e0032604903600c162600c48403070384080120300d0b01c0d05815501100900302007101c400d555a0b004000d03d0b004010b01e0003032100052040655800700594600c0403090010125551b031903260082 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 265994838 1250 265993588 265993601
    0x11100507030905090103030e120a050105010602070302040515090412110a11100305040b1303090509101818060b0d1401020a0306090207050307030e06040305010e01022a120d0f02030406 81
    0x240091410b9401007802e242c0443c459049941564a0304850300d40ca504020810b05004204841440380b144a0390004000b030180c240200a5034000d46040381c994014001515401080014207152011300600c255847c1d0f9846900640c01402c0201c00020074081643c001d104001018051b102c0c1e40b9007075080241e102c0114024000a591800300c101c24144140c09641c02910000c1064141da00020201d40640d01c0310701d0114042e2a1500720240d07500d02041c005030b03040e5603000382c0c07101111090101103514903a40d00a03481c0050100800d4a1240764003035540792600d0010041912140078002d9542e03418511003d443d04201c2400c40c818440c01194003d6026414a030f02083c144031000442a05c58420350302190340080c082d521345a5160350032950700c98081046980481c3c14000403000c10401d01c118bd84014600000503a10040125900d8a407a80806400003d400321054810306603c0031071704e0410390302c030058400c6e02c804403010000c0c00780103185141c80840384044200320500c005a0803a1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 265996088 1250 265994838 265994843
    0x20f03040b03011a18041a040509010c0f02150112060b030f0a03030c09030b0109050c07080d1418030d0b030f10091106090d08070218070810050301022511100507 71
    0x80300004c061800c0c161903400f07240000440760884000031692814250025028811010219080c18164a0000d1704503081a200c8001c4c682d0340e848000b140e80e03004082540d80840030300081c00d000da40c05034248070280050141c05540c0050301c4400c801c01c94aa04002420300000b41078941400420816a9803901d403c0c0d0300340d0000b030030010705200b44c0e402490020140ca0704140308001503802c00c403205001d46005000e02c180c180701080300d04042517882c00a003030070200106020813911250140f6942c2400c1c05400070070708440c44040d0b101025400070450b207c00c02850800310f01c0710403290020b07080001400340f48205010b02000d01c0e5001120780d105004c0c0c01c0c0f041440218151003141806000d000326503400d5045100520581c01103010240a8022188010444030324003034140022a1400c2c002d64132040031031480350500400b41101c840040c054030f001c3c0c00850810300348028802440542404401032103001308070b92000e10020022201c1c404001800300794038840321400041c500d500c43c0c0001e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 265997338 1250 265996088 265996109
    0x20a140a030801150207090b030a0804060504141c1e050d0906080c03090705060c10020403080a0e0102150105040c0c061103160201061401031109030115050102010e0109050d0c0201020f03040b0301 86
    0x8164031000007800c200d40c0880c0c4c1e00405c8691f0501c0415802061004c3c0348940c03511580c0342d80e0002611000003440a45a2696090349440c603040c4c45641042140460a126144241e00c0d80101c400c1e9490781c1440c1504081d1761400d5403800140401002411100500180503802148203200d40000e2240c044407850380d81e9001554410441c00201d01069036440b04540210604000172300e490000b40407405101c40556015600d49501301080340d11640c81121070070004a0455103942d00b044181c10440028005081c200008001011034100140180391045995004801c0b4140c4581e482c0595a94040c03010000ca20b00c60342000025081101d813211400e244540c0384000510602800e0300311000c2c209004810f0025100640150001481605010f141071104c80d25683c1d090003210f10301c110852480c00d0007800c1800080c20340314950f1a10400c0c1c4e041018000010f800080c50072415512440c000d200c200e01480102d00b0803a14840001d03c0b444041404105890007100a60403120020013 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 265998588 1250 265997338 265997341
    0x11b09090504082d0705010b151206041107140f062d060f100c03020124031227050913030e04050a02090613031407051e01020a140a0308 60
    0x490905075041160001c2508105101903180c2c88440354280300c410920083c0c41c0c40030780b900494110190000c50003a19940e450b19503480d620f062400c540005c00084d1070710785240c9140f0300040844074502420803030107117544990a80c40d10121034242e440840e88002015111181f42c603106075610601ea0343c8103068011a0081145003018000d00b28100c0b40b100090000c50644159480b000d450050880d074001c019030424240079030700c1c00c403484004005500c42d00c5071186c01e410001d0840c3d00d007600c1482d45185d4a4000140c1c0d4400070000c82c2101d90003440c01525008040d07003250130381c0c040380d8500e05440360b1a4141e00b140500c0c02211046d540c0c150340d10b21161341d0f00b036070240e41d4207900040075001c288000215034107420180c211903806040b020002d49808001004124283d2000720342c206480c810362000d008102f110203d035803000c3c00c2c01c1c0084c500e030381c14040060740e9500b0f4050035650000180440290b180d0082c8541e022058025a8001503c4150380d0b003540c82d001902401c50020780c0840 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 265999838 1250 265998588 265998599
    0x80405100806030607120914060403031401080309121e0304080c030a0b0f0411030d031a1e090411030a03030b0f0414070507020a03080309010b1003110a0c080c011b09 73
    0x10759007803091000034000c2c00e00781c41781c8000703440124109035049505030722000c020002c100700390143c007101c100389001000b891409040040459002030051800b5030901c4004101c20074001060728500e0500b1100c0e072140000d210717111441c04101c04040900d44201c0c945461581401101504c01c4860072801d850510490108064858001180041c14692200d000c642d60344001c4d0f800da44c0c81485500c11b5490b0341e0035400040c0c030305903120505400194079070101c2030480301a03c1ca20401e0503c00c1e03820b00b50920500340710350028590810384501941607100050f0031b00110300b400000c00740b070180a8032940071082c18002c01900c928050b581c003c50f017031000c111031410184540c03d400f809001070707034009840b40c00d801c5609074041030050b40c0c004408100800421031400081d401a020302c2c00001d1800c2200017072103002c0780c4450021060500d0000c0500c402e000900855010b01c0442c5014095560507241c50a19401008020340d900e61a0500781c0c8500c540d1101c440c0454403541d114010a980c1d1f51 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 266001088 1250 265999838 265999847
    0xe0a1b0605030f07200303070f1b03050c12071b05091314010f061418070806011808010c0e0415061205040201052218060501051c060b0708040510 64
    0xc0c0305880000d00104000381842d40240003880d044042c600c3c1402c0102000c03014482d146940b00c00321159034000000b03125519070030a140c59420441750929440b010b9074082c1d50a4442509400502480390000352158400c1e801c0c050080d038042001d83e1541c48544a0811440000c00c0c000c949a12900c030007030200d0103140c0054482e204080d0444002000c203020b944503403218100c08180c070364035901c0f402d410354440c1a5002d00d6000d030094909051850440408019540042c0c1d01c0155011003010180400303580e0160407543d11a00c20309120b00c0ca140d405202c4c081600c019448200c480d4038101c00c2204203503200b50201002c0070101e40500440450b114003040d010706500c0b1303c5000c01c080d000c486022016a40015602600504245003020003801c148908040c42040c440110361000905200380002c5641204548103164001c001c0c050034040080e007544034008000c21500c00d4050f190200013803a40005015040d00c00d4084d852309940e2800818a8101d40030309032150034040140b68609219 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 266002338 1250 266001088 266001143
    0x5010b0105270a09060905060a06080402100c031b060c0305091623060f0403060e19080903070f080d021c091715010b070515010302030606150d0e0a 65
    0x9407140000d0160003403210122440c1c441060700d400800d10100004d0040f42482503000501541c1c8010030a894044200400344d43c0c990401003d204003132062202580300e4070034448180946040c03074444c00005080c207640d0414240103502072540c28003429010003420350481002d03503403039031028005500d4140b02c1c02e4840040a070b1000000280010410810740c0e01d40d441d410100d01200004214511400801c5c0544d010f002c40c0180c20720000307010800c10a05228408641007058098031076000e2028000380401c1c0a907101910101c40803808040c00d0340c0503c0100018030001d48002c1030281e60b503980c40e403035a0042d110a00540603c1020012080c050707241c002c2e0300626070780c1344004181401c41603800454030084c40c2129200d01200c00f2240c41031040f0141c06449008a020344503501440c00c1460318100c1da07442050040480d0040006850000b07810760040b00450720a0318080002e018003400b4000d124034000c002e400e0950040d40c40c1c0002c41d02c05a0240668102d000c40300c50b815100069448 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 266003588 1250 266002338 266002357
    0x370f0c0206040506160c0f0f05060a09110424141017060103020c0709060b0310140d14010e010504150507020715030b0d12030b0f030c091909120c05010b0105 69
    0x61001901c426628807001650806c4110b40311036445802d100c403010a000c41f1051507400e030700b1081c040e04001c0705a2100d06001c00b40007003003482e6a070003814000c000500340110b4807620003001003211000e0345510049116030070725000e6950390340380b4524030600b2125402a8510794031049102e02c68801003550800c625003810301e6440711001100254807a17489884940143c4101140c6560035010381d0005009840c0c00c2c640701e0074040302e4001000040c3d844502215684641c01c2c5107a01c401c0c40c2030980c1600402c81e010b0501c5005400c9000d06903c000c41e0070305519107000c03c000c011080b84000922130f1403c01c204100d6448000590b560f1055020b44200c28407508030b001d00c0c25110360001c03c00300c1000382016040c180c059940d2894086200c1c80e10000c2512504189407030306103c4508004044120011f02c0c1c041c0703640b0b0120b0b040305e801034001074106001e4015540544000e270032107020303998032400009000c0c0c8003407002810700102601c00c5070070b5420505070308e21035071041b1b007070354190272 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 266004838 1250 266003588 266003593
    0x30b16030c1704021504150905040c03020702010c060b2103031806010f140d06020d02090f04050105100c050f0706110105010905010605041503060b0316030612030503370f0c02060405 80
    0x1140c0703800300122468403e17100c070b0240d007040001140b201c400c0100424070080341d071506000241404100801d5542c18240d42080500c140121000340c0e1344a00d011402035045000003400200c80c60101e1740345188241072503801900b6500c440380410300000110b12440c81901200001804502a41d44404080c031a9090510421800f403114a4220001200d0b0003801005207007a4400d079a5098280e0f042190702d451807a41c00300d4990301a0415401e28110808215003c00180d03041c800040c00f1480c408240030100036079004c182d0300b0400304010449291074102c00325600c06a4405004001e0b0204802808040d428079000040c20300d400c1c000c1c28140c44940d102c4078140b50a20301d50290300d00c5d9040000c020180c84240018000f8800e800440c0154500740052582c50030b80f0402405075551179100e20045010f180caa9804250300200f901c1d0400c5080307410302c20b90100d42d2848516860720f040b11002c050241d0400b512003c0041d40103400300005240b0074800700a00303403402c1e40c50b428200c0f40941580c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 266006088 1250 266004838 266004841
    0x4050108060417070f030806010e040c1e030222031401060305030a14090a030302100c170c1c02030f1e060f091b04030501021b0d0c030513030b16030c17 67
    0x34001c1090740c0442c50f8aa086541000c1181d240e500f0340149404068000c2010703074003403110300d517031005080c00041c000303907000d003c0001203000081000c180d40301d001c41c008514a1220179250311980407115406240c415000c400e040c0c0a00c81c3e100c1c01c0c001e1000b140c9040003007240c9200880c043c065001140c2d080000784d401c1052660081d50303680d14500720007a42c00c40070090002580e031070480f06001707940603500030b120501418400d41d0440f0400010441072120b40d02d00d00c40e00e074060f981d0079980310840110960312601c000c0100f61450b80300c14419a070301c40c0080108500e1162444503103218120901d11400781159098106000300000c1c0c4c1c00d01e4000003a00e40111840c00c01c0d5510582100c3c0300c400301d031595500000e80d04440d82054104450b565000070748034180300d200c010210707079a2541202178094a2041c000141c0070308001b0b040181441000701e07107420b0741010714076240011900304000346154a41039054047d440203c0d00718101183c54028802e0031148610840c00b00580303500c01c0c0d140103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 266007194 1106 266006088 266006093
    0x4020f040603210306030b090c0f06030106020c090414030705150702010b010203030703091104050106030906050a050c0d050c360607020a0603020a020106030204020a05090a05040501080604 83
    0x80c90a110081c00415140048241420f050850005240300c01401c103402800f0749034001707401010b2500030007a2004000c00d00101f01c43c82201d18540b40042c038030401110740030a010700c0b00181e201c4816800c4504121060641041c042d1074110000c4030b0004115242d80c0c03100340222503d4004100f1071002d84141c0e440260001810300003400040c0034580002d41c1ca0000a2042080685a245100c180600c1c2902e414030414003501c14091981c4aa00242c09030983c040100c0303440d858030000030950f6501d0311809028941d003410f10751404038001003a202804004c0c2c000107a0410801464001220a1000c0383c2c103401260250902c8881e0003605480000b080b00c5c040f400340400b04000401650385c0011401030794079608005807603004810301240108001e80009402500c009036041320b140d0840302070000080100c80a08101e521842030006a501c2031040c095958801d1022800 = true := by decide +kernel

theorem cover : BRFrame.Cov 265827338 266007194 := by
  have h0 := BRFrame.cov_init 265827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 265827338 ≤ n) (h2 : n < 266007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
