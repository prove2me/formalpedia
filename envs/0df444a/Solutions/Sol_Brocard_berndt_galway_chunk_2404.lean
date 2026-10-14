-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2404
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:36:51.497331+00:00
-- url     : https://prove2.me/submissions/8deb1334-c965-4df1-a522-f5ec49c2eeff

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 432194244 ≤ n < 432374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 432195494 1250 432194244 432194249
    0x6210c0e0f031209060f1e180103090228090908030f09070305100f020f1b0d0e15090d020a0e161d060a0c0c23030f06040f11030d0c031206 61
    0x4004900d801c6652007001117a40141c141140041c0c01000584420a0304000c80d0a415040c00f9090740c03200c40f062403e040b881d8526001c43c5c101490706240b80f0142c0d41d11441da80d107224a21030358111100f034480601241402e03039001580310768108003448040000310030003180710303a4401000c8180e6403100408030342c131501d1610001c1d2503540082c0c8450b600303454603032003e13003092068a001881e0021041e4180360b66004102c1824a80740011240080c0c10018451804480d030706142c02c142032a20b80001030758102c0f980e0000211100085424010360b00c034101c0c04168250018003070078030b040d076840311a161454221004400c42c3e070700301c0310810140d0213019030011a2140c10150003144036802c0a001c045c0d002030492400b04003c22030f000780420291007004001c0e0070882030007020418410b41022440c203054460700c0c042d50007a2000c1440c00d40104031160440e03400926046060f06a0420038020f0749104440d943c1801041160102e4030380001508c0c90340361003130321402501c0c010740e9194401c4641c03a1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 432196744 1250 432195494 432195523
    0x6061101050133020106051c05010c030507020d03020702010e1e03100c02070306090227010f1e0e04080c01020f0a030e0a0321020409061707120c06210c0e0f03 70
    0x8002055036050b00d884102d2000300f80c8000101d855407500000d1003e00003040070b60a0941c56860181803040070b000d2040714061234107041c4903d04003d98000d558140050407602055404110350301168450364204960a4008004510001d244450503614840d8800400c0c4030b4807a940411900c1c3c0c01c14092900b4500854024281551079238030f500001d040b92003030407039102c21204c602c6c0f000c21703d48440c900c50040c107140e4001c0c5c043d81403858880780040940c10020181410b111641c00c2d00025120141c02d4a4014444c0e52054655280012080c006d07440440f02035400030418010303c1d4100d10280911040640c2d052002e00c1011221945403500300c140038001a05052103081c0c403000f24407160388d5410107000700510386942c0308440c0044400c2600000c4002c074070324810100b031110410141c3c0140c10a00d04043c181c401e60f0b49c034442c11010a00c122400d200c8482104040c941c1c92000d24511205902000e010952440400a001e0300ba04010306201c0d608180d421811420300150484414014 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 432197994 1250 432196744 432196799
    0x10f0b0a080718091109101e030b01170a05070b070201170103050a0b0402130e010518062401030b0a0e0f0901020c0a0201030b130c0801080f01020f25020301060611010501 75
    0x102c0d0012405824182c909945030012210b05c07920341d4540341e0328a4418000480207103001c5044c1002004200718400c254011009500c80c1400444c45400045045420f07071000c8403041100d451285050100e1800b000d0424040c0140000d1072445540090615038400d9a503514424032141420303000a03000e00000d4510740c0804074000014800e00301c4660040e0008081d8001c4c20b149a030101e003681d40a03040b003c1913035118000d2102d140c901c41c0d242d8400b0640d940140900f071a00c0d0386d040d084060341001041c400c030302d14428000180d01176400710311200000392000103415200d80800c2d2200b682a99015812040b00000901020042c406d03580031840c11000b4020000c05600110080d045010000da071104210403111001c2e6054402d040d01c0f4003d6440b440d54540c0752814440c1000d4400c900e0044603401001000c3c82e00000300c00701c421b0746807550306441031028409001200036a0030a4002d40541c03a2010110368540c1204400820440c0b0750004c0c80b050f03886840140b0220b91103210310301e60201 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 432199244 1250 432197994 432198029
    0xf08070c0305031915230f1507020d081b010e06060103021318050403110c0f060703020f0d02010605100e030304030f022e090801090b18010e010f0b0a0807 68
    0x2c102c0c011600000d502220420f103003a06000340d022964083c2c03940c9004050b9210420150f000d05015080c800c1c0680707048071100030070707034003103641082c1e80907030f030741c46020107403114014500050103941100da0041c0c4032190b00e0001c0c1c6090307800d0b640400d00c1c981c203242e83e00c0c040703107090001400b0320500010b2400181c2090b496070701c01035000e134010780b840d070b45042440500403801d034108440d202c08030744840501180c9400c0c28240548541c1c2c00f1290340540d034014104010305a11031040b603980c02001900c403150703a641103080c00c90400300008000040c60103081d4a00482c564150004016103100703d404005281201d80e0681e15008850b00d0940c264009020810200f035a1480d260f4101c1d001804140c41c46807102c0d070841d0f1030161540c0003405010b01c0c081c007429156024503001c000d012090000c10003607000ba2507a010b00a0010400030150603000d803200401c1200390000091810480c0c002c1c82005ca07568401c0000c4c011002c03010703005600e0803200144540c1d0020b82e041c02c446241c0d614644862 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 432200494 1250 432199244 432199247
    0xb0906210109020619080c0c19020d0803070e0906030a05060a0b0a030f060c0e0d020d060e0709090305070212030301060f111203010b120f070e120c03030c0d0f08070c03 74
    0x204038140c10032440d541c818652000d604c07408014104030100c810404c0e071a18220300041e14002c80a010701102c64001e00c030754120310b1030000300c11340901041422071803001c0c3e161000848507030200070010200300c0e010060007140303500040d41c0c41c02e18604491640e8559501d406041e03407501841006001d40d030042001c5015a440b40c0d0007440d05407400303003a0480060326600d40c18000c102d4050221403081d0740d1400b408129038010b84206e1140001c440310320b040750050b00010080c004127580a00a05da4846045c90f00320810030880008081514090201c00f085040c040c5c8640c0100707405034041d440c0c540d0310107000315011003100e0580c1d495444a00d08014409001c417440c0c030034ac41400c0880d2003501e0040d00e681c1640c6000c1c0d4024144540100c4d9075140014002d4210f41c0042c00800103082040140401c02d034200320051101142510000540c0000b1405a803820f11054031003901408006102c0041c188046010000303062241c58002641c0d070094012641391504464140000b0301c85030040700000d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 432201744 1250 432200494 432200539
    0x30105071d121e0d03050109110913090b010602070302041112070f0c0b0c183a020604031a161b05250f050a03150504170304030309060b0906 62
    0x80116004890018840caa1a107442c3c844040180b4103e5201460551039980c0c5409080c3c09014800818401c04052092080f1039001d120512849925404802d55040704960700c002841900032464003455696801e0183d21203c403030005900850402c81d40d07084407071343d1108960486054007210907140e6100402202c2518000e90080200110981c84402280c6800e0b01741d401104280b42040c0e40d2000101c0e4220400e28262110b0b0284c0c101d11714046160914500340d8001c0c0d850114411a2074020310b1213101030304401000203500074030108010007806415203000440c4d52042c2141c0e0426140e82102140c43c0d40d075400050f00203404080e50b003001d080401b180c65078652040703044980080d0029400300140c03803559a03054200d0f014140030455904025000300c0100029500318642c54215101c01103480400d0b164a11042c1d12400881e0401c1302c0d980c0d0074100082c41c090519242d0400d07140c010050700031b03480e081d2a803a0034000307903959605e0a204041e010b00c000609103500e206145070742900d0b4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 432202994 1250 432201744 432201769
    0x40c140607150b0f0111150702030724110708030c09060d0c08100915090b0a030f0317100b191e0302190806010f030203040602090d050c030105071d 65
    0x84202403000c400055018420502400440000460356003d10000d0109001e0003896680c10010380d0011044600004103074641425a9100203501c960740d4020203034590f2040d010000c08020310101018800f1401540c1c04010f00765250003840000c2195143c4019030080309405001d010080000c62485903a14000b4600c02e10003800b01c0d8240b070f03500f100d90011030300c026141801058802040008010481c01c070720001d840107000401ca01c015142141c80d40560f40d01544600d9540d4402181d403517034038829200c0055034000583d220144480c82e00508407a801a088524080c40d0000b14802401c5003850340103807030074040070714140040041280388030310601a50f181070042507012812040c4d10003044203001442d54402594540c0d00c420940001c201c030701c0340c10007048010340c01c0c40759582c0c1c080032514485d0614075001d0784a8456041c801d00038401d10380d14a60040c04c90b4034800400401051a4082040c01c8000700520381d82d24006440c038035400b4262210b02e42051154141520b0300d204840034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 432204244 1250 432202994 432202999
    0x130e0a110307030f09080f07021504213003060506030f0712060302031e070e0402030a0f0c180f150b0f07110915030d020d0807050a1206140414040c14 66
    0x5d1000702c0c3e0b00c8113211b503400301013004010400004d0100a5003011404070740303a03101780030406280a01d0200c145615031418004414042c0c20184081709020340c250060074111a2510100c41d00c480c81aa020b10b102c0d5030324400350119051840014072031620b801900d228001000002e5050356555004940b0450a0502c01213141c1e0b4508010026032810000410301d07162a80244d042c0140303072010145424019030101504a600c0c1007088010389000c58143c00c219403143d46400d03040898980042d10505542042d003018503140f2680201e008660001d21a0080c116020402404501e400c03500340c11a0380a0109000410001c0c0403524551030010700701c160203801c400140342c580e100021004c100030385208040c2441c01e00803003090700d4140b020b80403109050001340041c0700d01220150442c0750003068913040c42000310b1003485650249031071194900e40d00c9000c015564071520800000244444600e01903440c1c00c060b4684126888102c50246401440d00d403046807601007804040c0018a54064 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 432205494 1250 432204244 432204251
    0xd020f150712021c06031112010e1b010c05060408070c09150308090604030605040c170303010e0708070903080304030c0323070609060b06030901050105011d0d020d0512130e0a110307030f 82
    0x144040707040c0c0701303403000b031b41c4aa00740e6410b80303601c0402c1000700002e400c40d241d490707450131340e4003c01e0000c000f4a00e001d690005007500071107410340b00180c1d001502e81002500310f001d07010812003003004040c010014107103d1203503000074a0b2030b010407408561000d154503201c003449880078000300c0d49010280c0200b0340000d06003454162244d0300c200903a001500d003140e81e4002c0c0e22047c80300340b402c1c200411010040f007004505640c94150020800305000d00704e003003884000741c0410350f06445030307911001445d08100c02c29528180761600404001d4411802ea00083d51046032049183c0d03c2291444580860000c003410701050791602d100510496204036041d40d55500e00c4102c5071110b00281d841101e120b400020380b50700d0700002600300710304040586411110280e04084a91703c0045d003200c800d4042d070b1644585a0704d80f80851401c00000100f40040001103401100f109203444018160780000d010648103485000c12001651211054070101c0e18043c40021196842a4015400d0030796450011 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 432206744 1250 432205494 432205537
    0x9060f06130909110f0604090209040605040606020d1e0e012a053301090e0c060d0b01140408030301030b0a1e020307200c1e030d020f15071202 63
    0x500e0701e91540220012510f81c000b8005101c0a8500d0204241c025907404a0404c194000628240306602642e821b41d60701148103c1180c445600c96005041c1c050010880c1544840c000b9540e501c06001990018042d0b104200c000c0c1440c0c44d00007603201e4141c4400250078140350064030100280e5407041c941311082d0822403080c141c44010521303840d004201030411a8101031000711620415040c2c1c028040c00300050002d9150400d00346811105144070019070310015011043c2030803e040d500550104000c0703120300c607150032030740803c8184400f6201d60540302002403a5060358009c622543c0038941041c0010804a2810900c031903120709000d20004265501c0c506c24401d1081c00c0d40151030083e03021007040191504034140045207031b100c05c4840102038140d01d840d580ca6110002003405070070f000c8403c10003090f041085156004005064441407061400025a00d0060481d0b0380c2e80340c8502e03407a0036251000d01c1e80450080e0703020f80d030303800a02c0452942c02d00a0340c0901c461429550501081 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 432207994 1250 432206744 432206767
    0x30504150309060c0f02071409011403100f0e0106050406030b0a02070302070e0a290a031401060b04080f1903050d05040f05010c0906090b0405010e04051b0f0a0212070209060f06 78
    0x10b002d135240d0a0384696162802d450320007450f000b841c1d000005000d010180c032a14079035488540c5811603030b641980c0036007416607001207820990042d400078040c5007059034501104805404c044840c0d00504000c000c1a41d40e40704010a4448511014000d000c85034049000440399030020034441d4081d0040f07896260340c4008a84040c48201c3c3e000f00c00c56590f80001e4403a41c10244200340f10130f20050248030701501a000580c0711442c912005124004d01030740203101e8a829001440104083c2005944460356541000c0e01d83c2c0c3c0741c6c005a4200c0c0a200d00c01d441c02014141c101040940650760282801540e0f000c00c2c0040101a2080c2c90445141456000084090107001450a00c0b555041c00d02440c141c0e0151051090f0740202c02440e00030302051219903808031030f200560008a0f40800d4540380c45040d46509464018160302a143c002000410103401100a101c07095007582100d250501003203035020a4040c1d054000e50000445d80441e541e8907040419184080d4010015458603c1c000072 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 432209244 1250 432207994 432208001
    0x1a06040209120c100309030e0909010f09050c041506140304050c1c03021e031806041d04030215010e010b03180105070f0e040203040512300612010903050415030906 72
    0x724030b140340c1c41882d642c0b000342480d10701400311140354101401100c140f80d41c0030f06121203422080b8000c001e2031001401c012000d400c016a00d001258003041041e096061803500d030046200d10500031030400c24000003075121600640b0072a03a250b602c48100d11030810309086680c1c4090000d507114855040d2111542d81c8806001c0420414650f02c11007a407400d01d006810b10780000081d003103400095013655041580481110214000d044003160f0744520840000c0b428000c5d03400245c0403903401801e4040241c0614505030040740640c007290b001c900d680391000b100c5507003409070101d20552400100040a500c1011b1074000c501e44810084a080c10490507084400441e091000104c1d164015020b141c2c1000c0360100c00103090720294510300d016107417281d541280300c200860a5400288404266155071b8400d0240c92142410088906000d11054120403054030301c00d2040c0d0b00800f07250300c07010052051a100581c0b649825040c076207018061000c0640055002c4141601e665094000884510 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 432210494 1250 432209244 432209269
    0x6040314010204180b09060904030f1b0b0a060e0109020306061606020915090f03060405030915040812030f07020c09010b1303150609050709030b190603080d0b1009031a06040209 78
    0x9050b00502c1e003082901c0700087e14150080300403909102c0400c1d4042e44104000c0c03801c1c200b0990a00619501c50380303040030217001034801070b060403e0201014643c2c0001007142d040071441801d41e41c03901032102c1284030a4413807950209040000501c1803000b150280e054501803d00107081030080400300d40012000712800011010019401c0103910780b803401741510040a034001d20580c5003d9940503030340c0c0f01d40f81031517200d103403142c3c00003c80c1050002120054903a402c01e545002201c01101e10345038000382c50380945001c2600001c0e02d414800a182c1c03031154002000001c50740d290490001e51a44036a01d00d510844030301c01c010001c41d00c1d103440018600b41590001074aa803800500d03e00b16580581140c1c10049410003c20100c4c15079210550055941410b8841c010b05a0400b40004c150340c5c3d0000f00b0540011695401c040c40307561000c06512000d07500e0201003030810400f20f4030059203000081c0124000840c0728034100e595021280c2c4560013500c01490f0207424030000720340c40e9214 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 432211744 1250 432210494 432210539
    0x80a09230d03141303020907020109020a030f0503040b1617030601020a030e010e0612061804150f14180708031306031d0316030908030a0e060d06050a1d1506040314010204 75
    0x268010400c60504901c09230748401644001c200045140c3c0c0003504022035444003030150b0301071040030420700030180100c40c0105120002190b50342050150b207810200b41285c19513041800c426080f01802084049078403515050b4007920540780c0c180d03020f403800b80c0c14004207810448202c040d00410b48945004000440450742c240c1030f90719149042089890483c0465410303161084280000a50350403042048084a0b0f28040307025800240144c00519000b4003800302d050b601010702944000c6c00c00c003014221403810903210481d40b0381112507a03030710980f1102c43e4034038500d00c0e041000070b200364000809920413181c0415100c1006c0b100d10710356004098010300a4040b24041002c0540052001c002085200b02442c01c040c0c407004064002e43c0041d070085d0041e440024441d488880702c2c0d1025001c1c2600500329000c1030b444000c3d980742c091000c10101c08503844031000c03807528030f14801d0303d040c819001490b651505095035121042000007941740311940d03400f407001040d4810000c00e40c4c040035614 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 432212994 1250 432211744 432211777
    0x20a12030e0c12031c1418011406100c020a120b070f14040605070212060a0c021509120a110d0804021008060102071e0b07080a09230d0314 61
    0x40da1015040007041d0141a01c00d80c00440c10212000000c81505e0f914190407542400c040c0c041200103001d4903401d074058002d0f54588041144400c1d01080c1005240c440340f000304601040070411154003a01610380b03503406016042c1003a6800d11035452134250703e01c040c100012190740c9942e031801c0c401c010741d0f040711003800301e20411184581c0140b07449010b441c245811281c50b10300d040c64400c0ca100340e0050b43c0800000041540954441100d032005030038100080f1640d0b45440c0003000018500d1010580041c003400309090b80030011031440500441034440136165100907030300722910382ea000103204400c0c044049a00c4546450612403424481200d45901e613041c90103204000c0f0140da107514031401c2c0480c02041c8030341d40e680041e020080c2c40741c100241200d0b646030741d10042d42010036400903009410000c0c241e000c00040d0b601030961002e035a110100999214101801500e01100401d000c01c5101000e540082c40d015074441c20490180c10b0070104540f0281460700b0030341c005401110510300303 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 432214244 1250 432212994 432213011
    0x209150c0d020a030f0305220309060e0111151510090810090b0708090f07120606051005030a23070206090f07060c020f06090904030801030512041401030c020a1203 72
    0x41070003440010003075403001d04492001c0d13981c054070400c07288140384201551000012031000c40310466400d010880c0ea040e1150350109d01c4c0c010281015402280005a410745107404e280d40240c601d0910031400c07002401e40400c10300b00c24100400001c1c64841262108041e9164945941412010032180350ba103c0706141c1c2003e03111841d00d2080455526142e01c1e00400c6408a00003042c00343d0010701d90b01d0840025220351050364a403092000c101890380c010500c0010303410f00c00000b100c086504c81c150174060319076558208010b80d604151506d01103001000014071003040c42e84603a001010a901c0740040f5200c100150741d911104540c650096400301044c8a034080003085140640703201da00050041e68180540200340c188001c400900964000c9455150740d0f54140940c1c4511034090206a40c07480e0606008290b23500038032082d5014020710114219142002003144d054816016442808801c00c40c0114000c1c03840c00c20303540440c0650b040c14400152030101404050940b076401080305035 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 432215494 1250 432214244 432214267
    0xf0b04051207030e100e060409060e09030f03040201051e030109060603140601020d0f02100e03131712030a020909090309030c04060e0705030403090b04060201060f08060f0406020d020915 82
    0x4004108070709610014030103000026801003480301070340301c16910346030340b880510020385000c2c2c00c450301942d001c0000314006c40d0158a9501a41c112103002d4198801c58881b80001622441076900da07020300841040003c02550141c002402c1c030241030100d40c201582e040900c14507a802c2a008660341c035444000c00c00039a541170140282c041d108800c0d03c0c0d2241080170010b95101a03450f0004180880d000040185c0c034000d01c0518050f0701541000c2c444d9088908015440368041d0702d04e09007803056064081421070410248800e2030040d040106070390b1010030800f040c1a00002c02c5115501d07000c201c103487c103031141c24880e801002070078010364981060800305400e001000c078150703000303600e002403c114082d0000005030b0443c099052441d0340b42c5807810708403035110781c0d50020740d54400d000800240d07480d030551003941140d21a1405000807611041d00e1900e40d0340a030303541540b00740f90b0000724000c1242036005180c0c821078070f60010301e00b8051201103020543c00300907011500c500400d034540243e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 432216744 1250 432215494 432215503
    0x5090d080d320403030f0207051501033003020318010e101b1407050f06090c1f0c12020120030f070f0210020310051309060c05040b04061b0f0b0405 65
    0x30032422038012540d10355082c0c45840000007030000e0704158941d83c209840c0442c0d03904a0300341c55003000a4501705e911026801c4d400c031074213101c03c5a030502e85400a6403014114290895100782c0030031140c0b0b00501800307044010350001341c0384041c103100c9500086080b94092290440a2150001074050700000d510604100c89450702084a05070f48a04144030383c55102d51942d0041003d5400182c0380ea0b00c40c00c110303141a00701c416982540c4150010312008410000c5d081245036002c0310b0031f03500039640724003520f03c0100c201003040c0401e0000c4074000015054481d07a00904c0d0552000180c10411401c40880c1003189400725031000300c0c00024040d10081d0b00c07088990081c1c1c1e07418068000706e002280203550349e400d006204a096404404116902c1e00200c0c1d1000a000080440c50614030300e00d000780c000c100c043e4040362101e107030078250701c0b02900450a44080f80c036458401801c144c03070070405580b100343c200c0ca840001110044454002440c0304820314800b402011140d08610f818608140f42 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 432217994 1250 432216744 432216791
    0x411152205010201021306080a090506070908061f051011060106050a0e0f0d0209040f02060403030f12150510020304050301020708070c09090804050f0607060e100c090b030705090d080d 81
    0x442e4010480c4105146d041d4515504403440d40c50092615556081c42000428007c20003c1650080310103000721264003001800503038411030182c46c1141c55038006031440780f00019074511054102c107410041c0c5d29002c44800e1058426082c1074800c0e4070a04429820300b10240c001c54003240c0c022440e40c0450f94883d01d1240066070642d10fa08100c0221070009082c0c00641200031320808040000404101548a0390303030342c1a41c040c016903112074903481e020340700041e0303484040c000422280702c141e4100c1b500c3c080c00f01d80b031408400d244a014100302c01e1007040c0c40200700560541c4000c010015031f0717840c244020070701d260080544944464251501130071101e851740c010304429040400080202d42c00703404490454508440300d10740300d2441008100f1030b0041d4000a882c1c1d40c60b1a4018036a0180828044210b500700c0b44100407000903694142c1d002c11190242c00041c1d03205000148150b40038200405240f0001040751540104a07a1440d074140e204450030782d109a120140c00c038401c4041d1100c000c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 432219244 1250 432217994 432217997
    0x12120e0f0d0309050319050c07060804170a080a15080f0303040b0c0c0606192105010b030304120609060e10140601030b030c09060f0604081b100503041115220501 71
    0x700d54804d031a52640c9002e01c040d01d5550032032803030010441501490846102d001d4950030b442186540d43d00282c01518122010349148500002111648500d68221140002030351510a5070340c40d01c0100c0802803072905c100c000c0d840c1032031b400031881100800180941021384030041da80ca280500d0100842800075013401c2c007800092190444091012030001d07884071060f90403c01c00204403822b40a0070625511000f0031b003800d102e00410064214840d403211501540c020b100d842810018103641e44954801c0d1512220131078103290000340e45030419200140980d002080742804880f100f0706010440c0d00380d0315441c0c1d0300c1c2d503903451000e601005c15600100900b020041d22400d68040b27601c0b41c403403441040c810484440015a2565062008032105001134141500e07103031920341c200d9450503980d0714201d6000f0103201950061408074040d03c01140e180d50f0fa0b0b41591241e070345810b04000980c0304281d212081800121050900c0c40207403c1d080b0310032200b030100003d100b4100501900542000c0d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 432220494 1250 432219244 432219251
    0x110c0a05011d06010f03080702030a080c0307050115052209050105011706011e030f0302010f0c030b040b060915031005060304060c08130206041e031e0314120412120e0f0d03 76
    0xc6284100a402c0460347c1213162075070340710600d00c000f80c20074603d010014080c1c5800300c0d43c10039244000004d0808180308038000c114450030300c03074045501012407040d2903114034001c00008103007a21b41044030145001200218001c24165505401d5640980141d00c10042e180080e04150008001203401045803044548012000c10300d1100d109c02c6501001d0044d45081d0282820507101358040300c4400d0a9100800442c406c18500401915010720403910441c103010220700305207011401c4500408000380050141141802c1020140d040108525007052209400240700c1d100d6100030752003180300d00c0c4009003030002c803032024002c40310181410940c0c403001402c00c401078a42e0011282900c002c040310604502c401c5840900d6225640c0000303002105820381088280f0040c0a42d90030305210b600e94100c00007081c2d0042c82c0601035011030410140c04040458041440e204102c1807881c0325107480401c01e81d0341030b10038084c0d5602900800247d8042c0d000b84007401014012441c0e60b00700b910303050 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 432221744 1250 432220494 432220499
    0x20f030712090e010b0f070317070806040624030b19090b04050106050315131104030f0c0816090209060d1d0f01021c0b0d05100608061b0d110c0a05011d0601 69
    0x170149010304c43d0070320003031140080c1d01d009160090341540b14041d0b5440600340350b1b20380751400600b40141656014000c0c0d060003404140028845000307452100300110a0001c0507103400c0480103841d0500c482038103d0382004444800d00003034204100503182040d00456050302c2002400119041640801e04000303051051100101c40c0c60769800d20b6880803070700000d5900d1440c01e01001440d441c151000c0500d00001e00004201c0d4400040f4001401032000601c103564945019442d0158200d060410300002a02800316007520b40c094490440301034405030500000070b020000305c1d81103108007505000d0120011480541c01c0100141c80c5480500135070500c40c01c090303d401c1402541c01c0503640e650310b50500403202e8031001e0619001c15080021206c1900404a9000c0104490301680704507006190000d043c80d014109030030700c004402c055192411005212050040489a407000c1c080d042c1013040300c6100600708031445895004000004070420307400000e4104420344140d182964100c0c4004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 432222994 1250 432221744 432221759
    0x10c170105010813060b06040e0610030c0206160905040e0c03060105060f07080c030f190f170c0c0c040c0512180a140a02040207120f02010501030b070f020f030712090e01 75
    0x2440d0001c020f9101340105082030701d4110301602480003040d422400100b030000366844080d000c5400340c0016100d0304034104880c8404c400b03494004a01c074025030301840103d00e40192000c3e03a144810050325041450315101c4000405481041d005040d4a034001050003c1c0c0c0d01c4d061000300d0050030121001480c150950a65407094003521030098003451000c104441000740c140101c6000c40d15840740c803039480c01064001c3e520414141d6200e00000c689045007140319001d11040c2145403421a8241c41070b40e15050250107682c050701c44104140143c12115200b43c985000c0c4c0c001840013a2550360700c8540e4a8828581c07220003c1c078481c40c1c50012100c890f9848008260001210341041c0d41162403000c41c0916171802e001880001d41082c400079004050101c400c500601100c865921a00c982d801008200d01703813042030001410000c0c4003004510041e00a84544094a81c0c500507541442d120381401d81c01c58000c040280c0c1c040c402c4601401105500103040740140206040484c081c3d41030210 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 432224244 1250 432222994 432223007
    0x120608060a180605010b07050f06011a0309190506070e01020307020a1505040b070602090a090903120c2303060406050612010306020d02160501061a0901021513080c010c17010501 78
    0x120181d6940e1000028030007610b00c06909401c581010041c80a940e441c0042c04032035000600031b580c04c0c0900241d0940780d8001040f101d040722569403106580a000c882d044080707a101410140e110700ca0511400c441035265811604654000c10107000b540c07515a90191414100004160454000300030810043c0d84503200001910031601c010b40700d4403420034080d00e0501c1181c200032030222000c1007000801c07100307400606245409440a4040e240d541d0740c1001540c52600c40100030410036103800c00d201007658000c140e00001c40c9401d20701f403601e14004485200c028250114039110010070090b190904d4007908000748810398a10f45488801c1c06401024103040c0001031101c0e40000b0008202e46c203075019030303030b0308056015581c0410030303280317001c60003015644201901a800c0f2840c0380c0c940300c00c8000f03a07030780348906801500001c09480c450802c040030041c80852402075480041c000f103100c85000d0078603082450000150240da00300042c0c8020a0800544c3d8200035420051140366030050 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 432225494 1250 432224244 432224251
    0x50c280f0c050a1415010b0c010b010923011e030603050706050f0d0b0d200102010f1802010507081201081b09160c020d060524030705010c0209040f021c0312060806 72
    0x13810000d00c0340400e14a60401c503803e01c844480184150020410100d02030080c16440150b90003005820340c01c1005403641314852040000b0a80c4000300f03102c04c031020551820814905162908041d00002d082000d02000c000c400000255109d105000b0003400f005600050441410200e080c0502840d80101c540f01d00548182d4040d212402a01143c4500d01c000880550103521b0a001c101404156403443c00310081141c010740c00d12448100d014000c3c402c1400110303c2c7c0203800007040703541e0015549a48007000445d190350007008a422190494101b050107454608082c04180940304207400c21101d00900702c2d03100740c070780c00207100c00d4404030b4240800814007828180c48441ea60300004405000090024100c1810401004900f0b05281914000c08150b120b81c0519041e4090500d43d68202c0341c06403a001c50b41d600c4202d0003614120142c1e070390040c4100207290b0814025030101da0311404c80c00c0300d5010500d200070384004258000e480c0240200680303804000c2c280c500f24205990f10382c00b4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 432226744 1250 432225494 432225503
    0x50913060b09010915090b031c03140106080f060429010c150525080a051f0311011404030210081b0c0304090509030309070b0a030603080f07052103010603050c280f0c050a 75
    0x8109c0142a40071350404000b80d000c0b42002400e40d80d4813400501420811203655a2050b00140051864071302842000c1079404005983c640b551007480c040300e084680c096003141803000281683c00014030031441007079841d040d100082010f041c1500d040c400c8011444000d10300ba42c8c1e601070301c0c1185038403180c60b5610901c00307140030a03140c407602031288a1074111070418844a001940100601462240380b031821002a83c1e0056800348003081003405000c0d6000080d0300419040c81c0341c100380d1080c5001034102c0f000d00b00300c124080c0caa4010783c2c86640b00502d040c15070f400c0800c0401c20098903205842c0e101314008007452a6180c44810992a020b050207001c4a550010400308211751090740044095a880b02e000d5a80c2d0300e40080a4005030040d4100f19103902c900c82c404017a001c90516a00048581500c00398190303400c2c90f40a902074040102841400790040c0907107403208004660076034542c02c0020034110030b030240400c001e00c11604107160f0400d014244d0303040c100003400041d40c1c84619412 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 432227994 1250 432226744 432226783
    0xd0b0c030402120129060c0a112d030114040f060911060a0305091c09060e03030d0614011d0a230423010e01050913060b09010915090b03 60
    0x841c4005104250720030070b24401503103013101103142d02c10b58080c203104c5a600b01491300301c1c021001c1704210503803094039564405074202c0f91030203000440844038500c60b0f007001082c1c504441c10034582c0a490909070230031100d0f0081c15584510240c01c0c28450500783e9102407141c032034145490380301c221040003041c00c010141075a8101200c240541d4404901740403c00500e030a03a114107110008010f07010a940310000d60148007640e50850041510680c4a240d10b92254450189041c6090b103007000748201040c1c241c0130400164940300311034400d04001d0802c80d0031505c0200d1a0b20001000a442003001c1508000c210507640c1050341c500f815601261010080915070501482d0070402000b48005aa0b8215080025050320a9070a582091003451402c203001c096a80c2c0b10042035100c1428030441d40c010314000b000c1500113890310b4074001f41c140941c5000c00e15500500203d03030a0642688113618095881c40048031502e04030b85018020088000c052103041c011800080e19954500007003c9030140 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 432229244 1250 432227994 432228001
    0x8070c030507290c04051302160b090c100f020c01020f0709150314060f0903090a03020d0501091505010801060e0910051b0706050f13050c04240f060207050d0b0c03 72
    0x40c003c0e4a0201c1e070450310b558a10304000d004480c1c01c0c1c1190141a11600290002c1c1034800e0b0903100740c1d10840c5218004040748601c5441e10403040001034401c024600845100c3c1c6515107450301940c10162065581d100d8802d40500e0090070140040c959a0440d00003001d401c0c0c01200c0020b20600340c0c1c4294000182d00c580d446401c41c407030001540300902d4210700c001002d840060200b2034a200c1c611019000000b50344c0c80d0541510f0344602c103280d50b80006050707000e01c0903051003071010316414410000001c642c0306580700c074111940c00c00e00b030b80700716600c403001880020800e000b40320040802040100040c2044209241ca5002c0d00d40d0914145907a0400200070011341c2aa41c50507c103140c022aa8504840c00c11002030207046901c8046e440c2140003150050b6446d0b04880800c1c1c0d0048003a0007410080c0d8200800790282e000c402c0183c41c02007149183e00c00c4000352400042c80140010b1059601d4582c000c0d003000c80719480944629440c99000d4013045007c840e1540c13000071089516a240d5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 432230494 1250 432229244 432229283
    0x20901020a14160e0f012106020c012f03060f0409020d0309032003030910050c070e09060a05010503060406020904111606050a0b01020c01050705070302091608070c030507 75
    0x142805409040368400540b14001c007030303020a54100d00303000b10381e0503032107291142c1c1181d91065090b503c0c01da15003000401000701000301e03101c40c0080090000542000011921400140c0c1c000054807200340c0d540c1d1301e009214605c142c0c0350b803030b9501c2d61104544455458007909140d50000800e840d000d00100300e0662075a0ba6a0303402084010390041041c10104d28034140100390034078501040344c4044aa00c941c510703202402a0b10541d076200240154074040445051003680c2c59244000d0060140a0026032519034061000c10702603c40e0000340445403510726007041c40c080010700400c880358030f001e0040c001900d006c2241135216402c1003001d03a0710350b0301d01c1c0844c3c02028203041c004402d41021600f40c0407680398032003204060f80940c10610190f20783c0000c800407140c811544c41c0c0503038081044940035502500c00341c03040500076420394030381c19901d40125061038011603440701d507400c0d50762052007000e4100d405c49800c840c0c03a281c242c4500c299039501504603c03d0010113090000651000c00d10034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 432231744 1250 432230494 432230503
    0x80708101205210310050303040308181504060c02091e06122b02010b0909031804060e0901240b0a12020c0f030a0e010e06041e030609111008130602090102 68
    0x82c0d10980d82d403c031045998200d0003103130030554542c0501a18070304000785510700001a202542d40118006180c119440035040c50f002c4084105034100585400565040b18500c01a00042040f61124600c1505a204101420800a20f0754418409241c81003002d0304000381001d038050810381c2c1c2102c948100d050154a09074600100e0812403509620400e980b140e442d0071014104000d40082c040c810301304041151404046910030080d50050180d080d05a442010008042c4000b500006480b5181c0c01c10728100d14040302e050b41e00d691541c24042d2181000a00c00044100c008214868542000b41032105485404045000c02074142c80303805001080350b040701c280750006811100b00c00d8040001c40d03240c0d0000c0382c142d40070880b041c0002c0b01550140c4501d80d04584001c00c5989000d0034841c0c00e5100c0d489000d04401407d01415000c40000c40c103220310340e4114021464001e4052001040203100070540700010208600c803c28041c0907500080f060460552005c0d01680322011540101e107070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 432232994 1250 432231744 432231763
    0x9040f062408130602210901061d04210306170102030f06150307050901031b0903060c0306050102060a02070c0b0a0903060b010507020303070209061c080706060b04081e030405180601080708101205 86
    0x24084124141f1801c002c0542c01202202e445000c0486204104008109505401c0720082d10b80030060148201e40854031800007a03101d243d05000032400c2d2515448002a41c0d41e116041c49030394000b05000203203140b00303081644200100d40d150842c0034600c0e015030f203078080a00188140000450002c0c00c5e40c1c042d07008008000500b0307030350280d40c5200140c010700c0140c9911003560003510b800340019440d807203401001c1c1a500180c0003428a43c5514040b0002588403c400b580c84030103908006c258200c0020050842002960301c0f0080350b819428504103c3d05d0401009061000800ca0000141c60103c01c1e2000590100c40f80d451503501c40000c11000402d642540400988114006040066010240203494001c0400b00810358441581c1c0c40b440c4180c1c080c0c0603256000000c0c403100c9009801100b2000d20180041c0c80c24140c2e031384003050f0b18414040800100841500802c0b20a50384042070750f40c4008a40f91091050401181e806c00101860060560152503030343d40005000003001581d44 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 432234244 1250 432232994 432233047
    0x90c170604020d09060f050705130e0a091208100f030b0403051b0601091a190506071407060306061d090c0f09101e02030301150509040f062408130602 66
    0x5444124540300006014425013100e00747d00c4c08020580062061054882d0100444102d0080c0d0b4203091201180500052841d0049a1181c0290f40012105080f0054801841e01c8000517410401064058008582c03c4040c4612015030b00300045840074591039005501030802641e51101c45030701119084800d000400584100f41c00001c074443c15030310020380c0c00c81c0d05e50726030030402000d810408025400640b502412004800c240503514208005240700c0e4402d070420000c2c0c0d031804002c603050044c3c07948110040399845000308005a00610310203c0a900380c4c8201c88100c02031800200b007980c0c041c0c606c41d44090003040e640242c3c0c1d84403044545e0301078010840000d50031404001051303006015580c400343e41c03660404c04403180c000402c0c6e9060300c00034404020507001002d0100c41c5a04403059607039010381ca0f54000228038010744111409070034845102404849028026094500f0b10b50a04040011520801c100c28044801c3c0045080d44660050381d2102c40100d070480400d82c4000f40030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 432235494 1250 432234244 432234251
    0x7020f030601030b1816090e10110307080901023118151d0f07170f090f0703080d02090a210605011d060405061309031701090c170604020d 61
    0x2c1c00320103011030b031266182c180841700e1600621855500e035040e40490011140c4c1c03068050203440c145800602e001c0c0050700c11036426582014410342502e60366410f2414045000090000c803d900c00003155004500c0c2000754607041d69044229104040841c990b110441c6086d0060386500c18045401c00a00900010701c10900c6003295080003804903080d40719448411038000100c101e80b43c00c41c0255214408504445947c4007008103c0120000f03250f44104412056800c0c000c0074851720f424002c40100307403c40410300e05640710500e0303d0381450301142d5662001d1030400000368400304a0745000707400b07440980c48500c11400300760700c6070048d0001084400c00e44d044401601c8048085d00c84039025620603c00f41c1d0ba5100049042498451140610450400050705500740381d0071040d044400079029100110b15940c03031004840c0711010490008031720300b0541c0d81e04104006690f01402292904000301c0c2c8107260050082101c4408080005207000b001810b03a95075a419581c1c000040740060 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 432236744 1250 432235494 432235499
    0x40e062b0210050f0d1d0d05031801140916060305010b0a121103040f0506010906050a0504051b0c07060201050606120414070305150702190b0712022104120807050f07020f030601 78
    0x17a005080f82c099007216003120840600c80319600040c4410214840ba01d5062541d00c1e404000310303a1003082604402259290350031855a02c2420746014424484440a042110f00b9000700480c00d521650000d0101030801e00140300d5100f56204131840302a103802d1550f8540007034600900a00000c040702c200d00303a8044200b0003845414201c01c4440751042d81a24480d07030320780b032404081780c030540685174000c0c15a10040c4800e007482d41c0301a03003258501505044115421500385299817240c1000c05140c1c110500411246070240102c50304030100300c03900c904042400a528130b0007030000b0700280c18110b10345010000c0742d00c1130011001441c0c101c0c0a440040c211114125101031041d00c0710b10040c80b410106030000d03269a190403240a5000441c40256181e201c0308952118030b90031001541c0d54200880300d0103505c018403c004080034054201a01d15290801890441050719601305204503942000346803540042142c5000420707070070282c1c840443d800401c14990f60802401d801d0310408001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 432237994 1250 432236744 432236767
    0xc060203090108090f07050409030c05121c06030b060d0c03050d0302120f070c0209061801034e0504080303040b01050a0807080304151103040e062b0210050f 69
    0x41078044800c0c0c940c1105a2580a071480c0e0726450700c10b0400194109600901c821b00e0290000034009009141190b6501003585515041070180540411003035070009549000103201c82d152aa0300fa40d20301d040043d185191213000f01404001c014a1180fa40c41d03c00768100211040f210000d140c0100413216800e00b45107014000750300c800403507a030f00c60095002581e13000c400e00c445880345156980303403241c06000d40c1c280240c5407805000d0300e51004d24070f91400c50101c445a0000d0082d40101600610170102c1c40d0101030a410a070072007404258582e041c40050b8420102c0034200f85c0042481700b0114046010481d1240981e030800c201d1400000180024012007607240e038117880341190341c10741c1203507103000d039a40e9094244220031281c3c200388010810340c02c451401c00703100151410300088500c50351500310308641c040d4020074161413a401c14803105090401540e0340180149103020020040350041700307459803006200078400d002000490101b1407107a82a140c0c208204410a911030020455 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 432239244 1250 432237994 432237997
    0x12040f022d040903030e030a03090b0f100b0a0e060315030106051906030203150d03050d060506070c1211190614030403050418060b030103030302180a050a0504180c060203 75
    0xd0748107034074840c040041d40003500d2540380d1198184598858151099050202802070400f040d41803555800c0704c0686420300b48020885921242d40c0004c82c0ba4030b5191600d2843c6000d803904014814900c03c02c41440c0224664905460020401035280e0320301e2001110b102c5604180b580e0040c40c0030052000b01e11108205c0600c010048000b80120b646400c140f0415100d030106031100c03080f02e90f00400c0140d0184d801181c2206564039810400b11241012501480c041081280002c0001413903900b80c00582c030601c000b414017119001e14182441c0c90310040540b15000d0b210540212030180c0c003c2241b040b40d800c0001101400f00700c1a0b085122505081131a17610418012030f4221601049000c04541100d02c0346500d5110a8101401e1159081c20032841090000079581d45c0e01d0082445030b6101c019500071172281d0b40c05692800a08080c2c0310764140c23810054050081d002007400142d840150072401c0d00d10503100003441c0303207100c100200b45107240381c1d010300034460206010403a150f0100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 432240494 1250 432239244 432239273
    0x804050616110117070e040b1801030c09050114040b0d0b09031b0a0b0f090703150209040e0a0b04021005090a0b09010f024c060503010605040e0303060d05031204 71
    0x9403002001c010300544c0d8241d11220b5134505022808001180c6500448004040c0280500009114030421001c12103004800a040781c001c1403500040040010554021001d0800040b0a105951408180e000d401940c41c0403a40b1454541c04420041d07140d2111880d00b540e00310f640304081d810501e846d60f450340d01050b0240c4406460780496000e014000403004107540c0e001c1203804c150b99524030f1359036030300802a084d410300380541c04000000c9060484204881c110410b0010390704d44540c8100004c40301c0d119100345540d003090030303628003086000520300e0b4401d4055807101f1204e40104012101841219540c590000c0300600220701c500800740906169502a00d44206250300008140c4e034a11391800c4203e503010000106c00b00150075801c466104143d41e850010a6a540590444024140880014a484d6600030420540c5024014100106026501000080c001500e25910780c031008000c40d007d030204400c40e80c01c0000410446030b03000c0c0d000c0300c046c40a007450f20b0640ca07240c0108 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 432241744 1250 432240494 432240503
    0x19060216030c21080c1606080702060f0702010b060a09030c0b0f030c0f1204031806080114190e01030b1801141302040609050c21010506090d0804050616 67
    0x3003442941400e8100540000e0720703080041c18040a280c258003040003c01905880154528141c1110025441038060090780c11403901030898081182e502c4c000d200300c1940080700b00301c0901e0500482c43d40210700690028248145110300b59690442640540001d00d00030390042c2c8002a042016580b000c20308e000d8904c54500c10b102aa1394091070103290141c000580d40a100400c0450501c01c07a440040040e9030504180500340203940b941c0403075400e4100e4044d0f010413003c00210b44c285049c1000c00c0060051800c06c410294144012503a01d44100700b800ea0150307003a00707250340701c106566005000800190704049081d684915002941c05000d0710400500460101c3c20442c1d030130103000d25a058607450a0048041d0384911440d003042c96119030598000b44c0e00d0101240307401c1e02d4050580f0403514118450b50b03480200b0324401346a40140300007688103000b50f006001035500c001c102c5207a91011106651006a03078241605a80700d25444143e001400203800c1c0e90341c024100d4055100c9004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 432242994 1250 432241744 432241753
    0x918150307090618020304032010020d06080c100504060e060c1209100918110702040e1e1c050705030c0f0a021201020c100e030c060906061f020703080711190602 71
    0x1654031400590001f5030380140411091402c0400310700d00c0402d05098400403400b00c405c901c3c0d5801040e42242c1c0482d0941071141d40b2403e05010380c1c50100701c083c6c240901611441500c0500140c010240c0c0039078007558003005008080300440c2c1d5500c82c15100c500f001401076451035003814103c900c41c2d5002d6040c1900604800c00d45580e0213014041039811a00c1610b03220030751442d036100c1c10004000102460000e60020b1144402580355031059002801e0100c00400024078460b109a1001c2e4030600c000b070391544240c0c00842d402c61200744e0019512030504100e070700e03880380b40b820742d00314003802c0900d081d28480c089115020404c001001e26415000395031940d090608031000a00340e1150800000031070340720a1582c0902e0000e5030040b2946031442c81503d05004182102034285201510b401c00a50700c588107100140c548846104074180c400f034003540700701c80c202e800651a00446d01c005490010302207003e0781480841001e04940305801498001041d0880b5680c040d00f40f818010030006101e0b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 432244244 1250 432242994 432243029
    0x5070201240b0a0504080a0b10050a140609010516050c010f05040806070e0f03010f0f0e06040201120b1819050901020310090b030f06070903061109181503070906 71
    0x7500c10003181040300d0104030100c21420092610380c1c6030b21141c840ca0400c00c1c100000a00640c0070301124560301d104400c003024500b0564056034090b1020f4105502c212088201007020303520940f031910540750240c41494984440c5401a65035001e4851408100c004691203201000350100d40ca40044100341ca0314584413404c008200c0f0a40a0750190140350750123000414001401032214030000c2200900030a491050000400e09403070580d039581c8101601d444410043c2505401000c0103148070720000c008070f01e4581c0000748845844840d2040041d580d250008050300c83d10a0303406881c100300782903801d034100107541e4041e0419482d10f0040a500e0301020440390031060003124020b003c81c0040441550501e0604c2c0c0c028140c6511030f40d070611916400c5981040140021441303140d03242c5404240a255007001e005031146001c91003420001000001540d40d5100d1444480206889140c440d590ba01490350303040c417802c0c880181e4148106203000810000603040740d410303529402e02d0b96006c00c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 432245494 1250 432244244 432244271
    0x10030b131e06050a1a191a0a08090a030503060118080303041406100f0b1303141f060609060503040203031c24080a12090f03060f1112010b160b090105070201 69
    0x403102010140c45010080c03140d1312070300e4501080c8000c0c00042c8021031000c2d9039a0004802d840c180480d401140c540490310800c123540104401d035000d0700d12009040f0208403a1f070020241d200042c13401f41070185c1d86a01c0d540d041c0b6196500c0c001f078090501201d035242404e05007450f05c45e03400749400100748194000280c00c44e802c15081170407500022200c00000b400c0050f50303203517500006040c030442c0d030110a0002c0402c2e03401c19414122403461000e081d008695542c0003602d4010702859801190a00500308042540050400101e65452502c1ca40300e48031840028114440d20002c0820030101140d0484040302c640e015030070182c01c480700b03a0302401c800d070b01d0b6030140342c12403151103e150803241d41080401c0ea04292800307256641d10303050038460380301d40e421107a0700300940040c0c42c099510320724000000784c40d11450a9480012081d242020030b00700c0039080550301401514005000450b4010f043c4081d1400003c205074001d40600b9546008540c29009240c122081001982844084100c12 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 432246744 1250 432245494 432245501
    0x2b0f0f020909010b090f0a1d0f070e09040602090315060f030d050702090a0b0d051011030115030905011104140f061204060507020c0a08031e0310030b131e06050a 71
    0x25800b501c5030540e40c2c6031909141954020f0001a50018504086050290f8445c004440503142c4080c00c3c2070801c40402038250131000090140300c01d8404001404400d6030021448120620102c44071100f594852410340040d000d40b0443c16054840c03001c20605595222a04500c00e81d419114081010102c108043d80da40b4400d0511000c10400c0000c0c40250504640c0d031980180341e42400302e2003072140b0340841c101d46001402034580b50444d00b4000c000440714003895410881c1c05000506550600c80c41c0025440f480802c6c50500d03a41d51a00c0741003103802e400010380884900c601d10b449076924442400c4e55007000c0410b510403000d48100340140d03c0c02c8004e494005001d90a0b120f1150340365580c020080c003010380250254419010400c0141d40c03543c54071400303070000c88065502c48030403076804201ca400d40901c007214000c4c00d204015145900c50308003002c0b613030011a03110039a115800100025035100f140a17111914104840d0441c040108031091001d2069200300f006aa40500c00c9040b03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 432247994 1250 432246744 432246757
    0xb07080a081005180a021306120c090e06120a0b070c050c060a020604080f0412060c0806120c0103091704170f030f030a0f021b01270c09022b0f0f02 65
    0x4030b040808050301400e840c001170f800940000c006282c545010448541d1050f5903010038006580400c2c030f034078900d80710f000c0c540e00e0701e00c103007065401c45003040c10041c4d580f540108154000c1010340305012611404001d0341c031074180c01c500c0c078141c0c1c0c0c1040d074001480c01c03a2208045c0c03028820000001554240001242e0100b40940d0260000b521a5a9910751030ba004211562100c2000d10010030078034030003010000b9891285400242811800740c018001d0b450050000d4898000e860043c039124001055860302d0080c24030f40040d84900510700080d0358140741c0d0103000055000700b000f0642820071040c9254020a110466149803070404000b552071040e070800b80700224060000c240000c145800220203030300412005814500c1d000d40420304004250904007441c1c1d11140c0150308000070300d0602441060f1030301481c000380281e441e00300203207100e0701c6000107060303000400e62086914201d00c4810100c09000354480c90f50341c0c1c12400058070b507440400f44603c2ca030aa220820400390b01c2140d00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 432249244 1250 432247994 432247999
    0x5090705060f03010b0703020a150b1e01020a080310030605040c050103200406050a0504120605160e011706041407020f0c010e010e09070909090501060f0b090a140a0b07080a081005 79
    0x155078200b1320320350246e0300030207806c40c20b500c00e220106001404007070040075107041d001d10015590400400300080d41c0c503000400140c50081000c1d1600340e0341d010070010800d640088260390b603a165a5014104170b0b03400e0344054042c80c03401c1c0c01e01c0700304201401c840c0c04549091383d00b4030508210200c00d00a16032581c040b5800f8000c2000204015030040c0081c080c042c90900703042d81061b58034071800d841c4aa65080449580750f0784d20802c600031550801100490380c40d803501c1020f000610300085c22a902c4000d406040119075800102d142d66940c0040714814004402800182000d03d00030b9550b1300c0200c5050003d01078048075000d00e5210f0302c010031030003c05a658500100505080c0112103001501c444100721a204003c41c000720940910b1000c1031041000042a624020350a07103c43d0503608a50a0341c4020402000c441e5184680340060780c8000c400d0240d40010314002540084550f031140c100d1010115546081c0007815002d40f1040004e61030301c8040e6610130b011544d080b5011300407540d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 432250494 1250 432249244 432249247
    0xf0d0302091c1502030903210603030406030f020403020d120318030f2d0c15020f0f03090304121119030203062701060b2203111003090f0605090705060f 67
    0x415024442030308403180c6000e0442004a03e5069141c0c0091740c0c4202d03076020150740000344500b101200c1124021074003c2c40d8031200f00608140300003a48038031951007100c04154803051000c01510860741124000c541c01000340b0481d240900d0f0090050f4036040401c0040b07460103543d48681d008440100c03a2903980b43d03a51f001710040349101640c800b180f944174850275015035200c441c5203441d4003150407801c19140d150003000c0da00b07501d8001d4160003402e080501150041c456400c038600311300b041c1e90044104240740da80b03a541d0044400e246000750342c007801592070303e0001d0b01c2c240031390100000107025054501304901c0003050800050680d5910009405a2011001030f0f85800d032141c011003400c0e070700035001c80111443c81c60306082d02c02d180c00040b1440000145010301120001c1c003034050841c00c45090060b00d11755115658140041005140120b005000304c043c118400da0000d6400380e842040c24034400443c1c10000020001100c3c01140303482000380100750780c0382c08801e42c0d442c12000380d4184d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 432251744 1250 432250494 432250519
    0x1060c020603070e0907051902011104140d060c030b0f1f051b060f07021504030c0303050a0b09100504050a15090905030702030609060712021216120e0f0d030209 71
    0x46050b90004240d68204102140300d800b01d030751100d0f0100d004145540c1c8094654100c1a120040c4082d0710342c0003030170f680c0b41090401c004881300b4162400c6036a10707064410201b00c01008180140380e024001440d0318904209103086a816601c020024482070342c03440354a5400a0601c1101d8512460001908400c0001089418440c5004250a800c8150048d0442c07480c1007290b40791600540d02002800c698074100080c841c0c3c10003a00f032018804002e41c4809007044e84000d02400c03806c8074060304040e203401c0003d001000a420035280c805014011403101c0c50302014080a0304030341d016181c8260f0912010880c1c18040740503201c1850515a1058540c0340b41c0030710000113100a060803151400144160809a80c0900241e0f01c40c04401d80909807e19203054002c4c4065404541c0441d41441408540d0300e208414044507440214091945a0b900c0307008000c3d5118111078415680782c44c200892801d01e030744081f4251440e840070a003251001c2c032070010300b80c040e4051255440c0e04082c010280 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 432252994 1250 432251744 432251749
    0x1401050f160507050d020d140c0301090b06030d080106080f04050c100f1707090e06031e060117150c03090a060f02180d0503070b0403140403140607030606020316060b060d06050109080601060c02 85
    0xc60308c00040404642d46031441e000420f0079145c8580095901414060410904e408e0500c11501c030382440c0c2c90300d105198101400a4918880548140031201c040000101000400c110b040c500b01802080c0c82c00211141c040200342007002024000000d0a443c000404428240741c424050880f68940c9030340503041c0041d100e1440d40040c40b540c6c0c5031251440c0c10000b05403807148900103d03002e50151001d981022100c642659031000c1501c41540101d07100040d001d80d04401c180c1000c40c04c0b030b05c2e0b60349445040c0c0c0300f4504641020080c000c0c61030000e805100d070080e54020f00807083c04c05252484030450408109048042d898040c055410400200d00060040e1204552151281c1000e0300d800800d4000c084a80d00320390811144078002511210000104110540c0d021394186000d10029090401c025124002c3c00072800b0394580c0c00440310100485034119081d84800985580d4440c1c0140b02000094402441682d01055600c2400315041001150307441c10b8440c0d503210200f1855840c0d09 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 432254244 1250 432252994 432253013
    0xf0f030912012c0706080103020d1211061f0b0301080304060507080f2704180b090c1509040c020703031b03030605100f020c06070c1401050f160507050d020d 69
    0x201d550300c1a00305440c82024150503c0c1070314154101560b0011140d60341e241400742e030449800e01850b00f00400050f03440c19484001a50301c0f0390554480d030355224090314542520085103000380100b5040000e41c8211152004061665440d4041841e44d81c940c449070610080c01820004d4004020174000940100010070700e051255040a01d40809000700240e40d0300a004080c840700400c226401140e40d080c04101c1108004580411a020415041c190f060801682c01042d0000f0800060540340c41840882c46500028000c10341c1245440300c403c1070750f800204031612581c505032150340c1c0103100282200c2a44e901da122001c0305c0d5000410301c4140c024100c421020591611008030791a1200580e43c00e28210300d49404040b1004118041c0c1042c0303405480070702651713040c080e40012a041d0007100c03044a400d0350303010384080301100040f03801c5d10402c18001541d19001810145401d03001c511550a0303401003040c1e680d81c0380c981e000c020100303d5000000e0740c0101c000d00c8031004250181c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 432255494 1250 432254244 432254269
    0x1103030c0c031b10150b09130e03162112050a06180207030f08061c06240317040b0306010806032b0e040203010e011a0c0105180f0f0309 60
    0x216070500242401c1c070301032802c0c154400010354100034a04c0744a800e0700c0c000e5040c000c50300765105201608046054003240500c54503544115041480f030302083c14944e1140a846003c80c0c10b8a541b1400241c152403210103900f4101e88098141c041c42e0b207044040e90345040c80369515641d01140100205040c2d0291001400700400641c3e10440000c581d0850703094680f011807504005615107a05060243c03031805440c00190511080f0020405240c1e1049088036000483c14014a0460441d05100000f0060042c0241c42550103411740400c0c00266403400c41268070031060406400e038000b1005845004910880d00078400903c04611658040c0080e1640114040c0c11201c1441c1c1103013103002840f842002c64400140d50050002009600611308809510203450661465161071800e81542c40140b194507088180c007820600c00348400811500148032802c000d102c103003010b21240e1039003440b0708201505803085540d00488403001240c402c60b111780249c061400c00c174100003400b44490408 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 432256744 1250 432255494 432255517
    0xc0d0b13060b0a0f06020105091c140702150408071d180a0b040b01210c0506090a03060204061218051b040e07140f01080912070f15050a0b011103030c 66
    0x14040001030f52030340800d08000300040116410503602d084070180c21a14040d0884d000350b0071200890024555484040c400003d140c5011901e0640d201c1511009001310346000754030000f402410f580300b0302560044c0080e902103600351200a583c0e4130b1054400c080a42d2816400000c0303200160710780c40e4070500c8050101d07150042c1c88010705c66903035490001d203003201d00701d440904040c018444004c0401c14102c0244003409aa1718103501500c5620603442584100e0784140000207202c0043d440b11001c2a0065500038415512291552400307030542c02c5480d08640011700e8824030218502083c0c00c01d00f051508103014012401141402c05405540386031350700d0300981c03a4115412003034010403000000f413182c24503035002140701c2001c001e408190307034900e80d040029081c14055800780c0030035003184c000381240c8031955504039850070f96400600b0789000b42080207223501c03900c5443c02d150821482201e51500c10003051060100554a40b06050300f00343c0542d0050002941d0240c14400900c001c1081 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 432257994 1250 432256744 432256751
    0x9020607080c0a0309060c050307120509191406030408030a111b01090209010e0c0a18030b1303031b020a0b040614010605040801051015180801021b0c0d0b1306 70
    0x11601c03050301e1680031a44100860f40a40c860500f416413004051004d0041c9140a0244440c0c1c3c0c4c0b03500d0303580e009808018040212107928900218082c50445281400241038103e03072010b21900304040d10aa4480c030036034000e414050004030301d00070049a01c6950b00405803030458031606984802809500e04d400d10f82503080150f00d140620820f5007090038086000089800001441484840a0182d220507400c905070000c1c400043e03110380c15100c0303043c1c1a01d814003400d102003820b00a0598135030f202911905031002807020504a40c080001d40b940282c0301805041000003881000450146406005030041e019042c00078070034143d050f4100e40604008034402003080c4868640384401e07440b640100d43d0000d0104800c1e075081c000e40da8403942240040c14541c0c58051602803c110548114080154038103c0405000641121401528000000710b4840c4444d100c040e8105000b45a18200c07845103070030803205071510250308940a41e01403d401440c1d281c0c107038600c0142c081050200d030744944 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 432259244 1250 432257994 432258007
    0x1a2502010f21050907080c0f0117040305131805090a03050901050a14030115080a02040302031902130f0c02150103120c0f06020a020a200d02130e012c0d080406090206 73
    0x2d003800f402c0d000b402c280340600302903480d0031001c0789403070001980ca500a81c05506000000d03038000c40550b040381e1403041306145c240d40340e1804a5083c49002503d40c44a0b803002004515a41c03415030344010441c011808214984850742c0141d83d407001504001d0000d8800c00a60a5a500c030700041c0143c40b90302e051000d942c843c40c54840c04503400036081461042031031901e072583d2581c4414000d0704030750a12411483d290554020030f8551000040c06003541f80400703104000c54a8440c55045c0c00785444000b00000025a14160040c18480d2075810047c4911010800e0194110315440d040302da00400c071404000e41da0340c0c15a280100003800382d80030591100e884020965900080240c1945580940342d51011031421000320204041c1d1048038142460342c3c0c0d5503030f40b0390502d080060368040f41c820380302e5a4008510700241c4480740a025041d42429000035030442884000c00c170070003078601840e410b2409405825640e02d825481540000d4560300483d0214503070364070210280c0d0003d020f003443d00c40d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 432260494 1250 432259244 432259307
    0x20d0605030709090203150f0606180301020a030c12140f07050f0f090103060e010b07110303040801090b0f070e0907050f07020a03241e0203101a2502010f 68
    0x181d42e4400c0c0319154444d4419401c501e801d00441000c0d40405200518a003020003058003184802080d140c011900024114800442c07003000f140c403e00010002e55941660400c000e014040b48050381307021030f05d1250b0052041c1004c6c040d920860742e041491101c3d907602e440148107061405840402031080810584c40c251101c10018000762041351515a9124006000181225141e070300039002030742c00100511030302001400300c1e03800c6c030740081100d40480340807030000b81144950f41c00a0500d41c40c000c68601000401c1030301c0b5125440e0311301c02d841036036660741003515580703200312016500603000302c00280420302440140104410a480300760a1820a5001c80c80d407442a0f041501c0352240b080b0400d042c0820103074810f420b0000343c001400646152006080c015504401104441e0740102c00030301e10304a84102a0300130414404480150307101140b41c504a54490041c1d0044413052031120200810031100044100d0340c1a9548504280c40000031200445000000550510850035080303440703 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 432261744 1250 432260494 432260503
    0x311040b014404081213080403080d15080d0e030106380f04030210090803180402090303040902070c08060108070603020f0c1c030c14030c070503040909030f03050f060310020d060503 80
    0xc42c030683c0c85030341c1c8017081c004d03540342c0300c5005019442c801d807216507130030016454005660440781e2200c5141d443c0c00c590302005001d0074154280203508807001400084400000803840c14902c06600c400c0c41c12841c031020716090b01d00c0c50191005032040580320343e4210f04020742d0100a040308404002c0c01039038280d011840ca40c0300e460799a1001a003c501441540740c1060b9124500c40c250030302c0004a85000d000300e8076806403807604011154008071850f000d803900d0f01200ca0071f04004040e256600e0b103801c0e0103002500480c405840701600008007084003080040d07050f0607203105031f000706112803078800d04402030f6016030003401e001141400040c00c2c0309001c1100d0078180c00d001241d1200c04012860050031252490a04003c01c901d00521600300d800c8482240e40002c03161040f02c1c1d540f006401e12515521903607004407051031a00e010401070580c0406c80d2241c82c802941c003405682c4400300709d2101c0e20702c10b64070103074107811003648124142407030750040203030303200011001c500c8685d542d00107800c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 432262994 1250 432261744 432261751
    0x161404140d050f0724080a0203090f060901090605010f0e0c2104050d0f020102390613110604050112150807180b010504181a0402040311040b0144 64
    0xa0380c8107130f400384542d18500541d05d51240b4000c451500c0b865420760028940308018000001c80356000011070b6940c0024021900100802000c44400c0c1c148020100c0c001d250703242c8243c410750f00e8070001280010f20794007a0001c4564184107003040743c076181500c190f40c1d80281a05d116851000344040803801d580c50300c01c0d101c1c900440251540001c800d030050403012004c1440e8086910400104580d400441c400029401c001c04040c850440d4000e51880416400c14600342e05208030820400210391540310302c007116101301020040c7c803044109000003801079000e9203001c24000ca428821040c11a03101069150300c01d16040712642e600e5107410304040c09500851034201b0540c2c0c1c4080c9004440c042d0b842605004c0c41c10174585441c1c0411007080088001c840e418054960104c89102400c203051203120003001081150354641e64a8150110080881101e000d00e00704a200441d0390f01940b1039074071b034000d40448030032442c0141020340100c8907850380b45000f022403042c0e803903545003200b05017a20 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 432264244 1250 432262994 432263023
    0x2112110c071e12030c2114030603030f0301080a03020c01080402010e0d0204110414090108060f040b190c090801050601080408030a150815090f030403030507062c06161404140d05 78
    0x1000c1006090007074840300b1802e40c80c801c10220240320003050791311003c4001003680d046007058494441e49c00103030451048400b07500c0404400703c0041561103020510b1400d50f8460740850307040300143c000558080d00b00b200c020b80855066603004a040c10800f0461891340c0c801440010000030856010101c0d4000d5004074146007040c010000450034824100e0740980380d201c000341540e10b0700070300e001d04a490003440204004048808540b48200f420740c1d041036200301040038814481c00c07602c0207100c02d005101e42c114960030100840e0b119400340d1030881c0129044030280d460340c1d603035805240281104064154a031b241d03007800040d17600c0303051005840d03400c0c1c044c41d034020301e0070214443c610b4035402e400900340301d4100f04402c03c0040d4000044401c140e900103404194419a560180405808000c00781040303200045000c0b261100440c0d40c0d84203180e03110003003159810080041321036004200c1c4d91659040100010301c80c250b1a14280401d0b0701008180390a82c00060b40e40e40d041502001d6140c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 432265494 1250 432264244 432264257
    0x5090f0708070f081b0d030903060608150f072f12030f09030301230a1806170f030f0c07051504030b070f08070305042112110c071e1203 60
    0x403890303110280080044c1000c80041502d4206030040c0c03030400805102542c4070300b02d950070072800c0500800b490401940c000313804010b101c0c0d0714007216071101008290107105404210004074010040003c60b8001e40807540c44903005100031a45504020f0381560303844a4040741c051108401004120341040b04000b00d03500c5440e0b040c103940c0e1420642001d40440000e410520040c0081041e0315914030240d0301144203100b8640b418008141c24407001c1d0081c40b52440a124000c003001c0603a041f110488c3c14074810b9061103042500ca0076240c0340d071401103081c01d4000300b00c607224600105003d888041709103c15a168035a4070b600044a0400d8410380e421a800301050410500107002c82c501d9110203e801c00c2d54440c01c0c1264000c2038200000c1807a03042c940d5400c0814140905407210660b0b0452400d13009000010091001d0007002d09012010076982c00e210745944c4410042041e0b4030742081d400c00424a0504003503440703d420090a00d0039004188941000130f40309043c1400c9105c1c14007030b480d8079 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 432266744 1250 432265494 432265499
    0x13080a060b010507240204030b0f1e0601050a030e070b07051501060503010617100801050c0903061e191b0507060b09010e0604180b04030206061207080606010305090f070807 76
    0x24094504103185141444014840c92000c2120580c0c0e801e48040c45c1121a41c40018441c6414002c0c0203503040680056514801c200d0034502080c960f40c0159210b00c10b600100c405401c402c42c0c84501202e000c2c2c000f17001481700060312406500600700300442441920b80042c6c444039184203e8212070b109407800da1140c0c0c521304158400340c1030180903000703500c1d080b46151b040c9140900704e90320b407068101c0107591100000301541c3d4a0b01d08280904036282c000e100700e08101e40404025000400007510030f0051a000c1203422100e1141243c200b180040f035901c81c2c0c0d0f19491840024850003244203121904c9581c820b061900081e51140c010582e85c49a50300c8000c00c0c01c0c21000c82c1d00100e6400e00841c1030302c0060003840b40144000d40d0100085a000c1030782d000c3d0030080111103840c407000508883c0e010003440109600070030007520a800554416030580d0b041203500350340f82440d205110468005802103961548640c01040d40240910200e80b06003074100c1d4204c0c0745c21074590040d525034100000a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 432267994 1250 432266744 432266753
    0x50f07050a1d0c090f18060f030102090d020f01170a020a0f02030a120e03070b010e07171003060b0a051009050306070c030203190c02030d170f01030317040813080a 72
    0x458040c0c0816007000400381030500302d00c001010301815000b1040c40200d680c0c0b0702d507036030b00821048401c0c010701749100541030042559031048050711038520500001e00500c0c0c8504051080d190400130003010185114020b0b000d001c2d5139a040ca4850f4108030007140a501c0784400b112805000340e410140040c0d441003403510041c5070090040c0b094085410401c51402155449804010302c0721092200041c4041503d48051851089036001043e00881000000312a030322411039920038091174071491520703450281c0f040c01d4a10202c072603202e0751050380c030140040380159104080405018002014245d1103c0008004418003041900000c000140074003841c1000d02c0303583d40040b407500b880182e5400d26a8003946134025000181d03030326503041141003e440e2280c0561144541c001c2c0540b0f620410310800140f800c0701d1f4054122481d01c1150110b400c1c1000c50b1001c40c100d079019035800140d110110242049200041d0041e40c0a5800344141d00d4004484ca5a0384000c181d1080100418016841d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 432269244 1250 432267994 432268009
    0x50c0709090305090907020316081806071a060406120f02010e09010602120d0912360302130b03060a0e0f150c07060e060411280b09010309050f0705 65
    0x1001a40a007485601400a50050103036150030b0030444980c1c006542d00c1c0c00c100d2450046650f503c40000907028114140105403000f000a00e1484082140308445001408070030706c1208001403000c5040344900c002c034501503510a81040c0b0080c0b010070084d546040c1c10f03890000f444019501c01408104840840d0f802c42d05e01a00004203503515001c5602d800f40207500c617540c00e10f4110b00ca82c400581c12081e5115644165400e0340d00c0900c0c15401210541e0080000c0c0020358161201120807910b0111103140000b860a2861410450303d0603a01315401d0005036582c915400d9003803600c40c6450f5040d9074040c07045904c41e10004a0005420300300c07074912890300241041c640e88640000aa080103956803191003035024001da5808c913901c1e02d0628101009004041c8004110301440c014070080140d03521f0110b106100880c0c562045800305014108403020643c1001400100c2800c00c00c542003490005c0d080c801014140082e030490103448903410444c00480d01030240d000948103020300c1c6001003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 432270494 1250 432269244 432269249
    0xc040504080c060906040b060103150b0f0417031813020d050c13091107170c0307052a090703050a090b040c05040507020a0c03020f270a0e0c0d06021810050c07 70
    0x402890345d400c3c0340c0c550388141d41c0044c03c540e04040d02c942c941c1c11150b0b1104100d034010100541007959031000112454841e8206025001103403e626444d608007910001c182e4207810144038009044151402c20041c000b60342144c4001e00725000c0c00801a1940c461003441c1c80b07184000c80c40c56a4440071690f003405c030052500080b00301440c201d01820300b441c0ca4419500002d501480d050a6130045000c0303540e56015400d81d01c2070038480003441008000021800740050040c1044081d5600e45007000c5c00c85504804441542216401d40011406442500055001464910300080b01d01c41c0e501c078500b01d007808903015500c0d141c40f0a82001581414806c155002c8500c0c80078011040c079a0340c5040401070f25110281c4601380368003c41c031090703a0b04055a81008045d0f03440c103041404c0d24044071701c0306404030b03940b400303580c5050b20b00d51422801080749521440001c0842d401c040c41a52810025003001d00d403591940c41c00d035400c0c10380740c03038050132038103c80031036100c454541082d0614503181202d1078 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 432271744 1250 432270494 432270511
    0x5090105060a2c030a260304031d010905030102070c0815010f060c020112020415110f0d051b030c060f01121e0204090507120303050c0408060c07050c040504080c06 72
    0x30085696015404400c0072a1000303042c03ea0030290207500d021040c1d0421801c0003030f9060203900d0410b4200105019900300943c04145030464070710b140ca40510003408200c60280125005051150044542503010516283c0504204800f6525240883e01b26000300d4012120007400c41c00500c1911010003c04541c0c1d021420807140941c10031498a400d000d0070b1140747c0520101d070a8940441e0700511300340745c070000e03400703070840d1030b85e68410301070b0321702c0401c03010403004191585d091040803140070480f100d00300f00003c01003805402c0408101c8095000c8488036900160303440302d04035500801d20040074604d540c240149920b00307056090896940b41070740402101c81096020341d001907500131000c0100490303e4038600c80c6488600205c0c01074482c0c0840202030b402465804200c1c0420a00e1840d02c00d402a0307010231450760350410010a81c8514000c040c1150321090004000700c81030300050034028480d4060703507071115400b804181138030415102143d240501060b03c12555008000683d40603e96 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 432272994 1250 432271744 432271747
    0x8120d0609050912030c090d0f0212010c080112050709141023040f021201030b07032f0912010c050403150213030b13050a05061e10090c030b0d03090509010506 70
    0x120b80495549000e40b8681e13074485000310014100b084101c0907681c0300c3d075001d401c041240c000740c50090b92075000c810040b8403640d0152888003ca44051003400402e1003503449a0703d882c2d0900041050340c8064a20403a65032042c01408900510030b4020b8425503031104c660b0b074565003008054000038820319001b800032041e5920342e08059019140b086901000d00b6140022241910f180707400181c41003041028410790a40d0000041000d001121486001c0558007041f07951a049510305070309090344104840144442108a20705100700001c1c69400c00050006025030038058409081d101c008400d800030400120742001031246024440104000009045217032450b00d401446910200380000f03007c0030784290010302c0f6100d182010842c01d54005080300c85c4c0d1b10041c078001e6601d140031189041580789842c07030202d640c1d58004610340a6451039001d00b0b4010b04004402c00180040c40031041059224201d40740d0315102c0d002c0d0b41590500036502e9610250031f00301440003a41041c0d0006004400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 432274244 1250 432272994 432273001
    0x7030f060e0606010234120c140f0a1703250b0a0905060a050702010e07030804050f03150109020a051b0c0306070e0d150207020a0b210c09010e0102010608120d060905 73
    0x1b203d644802c54600907045918103409062800444159900001c1181c40710002c4881030045141c41c41003221841c031b944031204070185040c40b0401400d0025240c004010710414008031040e59680b5911003030240469040c035100441e00c1d1024440e019100c168032012004450a119800303002d141e1281400e0428032030092181d45032961004005c0450001680d15408540c01920070340107074401400c048100c0782030380e45904004509030302501c40da61203410740300f03510940b909001c079100d01001b0b8081002002a0301c0c003a0a40c0c06544440c0d807420400c42c04200d052002000c500030031801551040040452022041c141480c20314041c040c201403001c01c1311313066541da42d041d034110244c5a118502446004031241004040d016001e8020f5000c0c8201101080800760302e406000d01c82151840c8015603040d824800b00310a8055940e02d44c0d64000f041214000e500030005c4501074001031000180c0660348040040c2002c060300c260800800e000145240b4010140c041e01c00903018501e400c00007800e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 432275494 1250 432274244 432274273
    0x3010203060d0b19020a0908010609150b07080c16061205040b01060e04020705060708100b0304030f0c240e0106050f0f01081e070c0b0f070c021207030f060e06060102 73
    0x41d440b0000800403a022000200640e074612450100489280700039034668510381406840c000d01402003c000e5880c2c010000343c81d5a03103010b20541c0e060188407c45c4800d04000142c1e8950780040c4080e10840410005106540b40030800c8007409210b16120340445818850010701420300ca0428810341800c1c8002d100200740c5500384181110054103040220201d001c001c81d001e4054050083c103680500420001000c0e00000313120700c82c2207030700c400300305090710783c201003000380070944024000848107504140c40034091588440300e94021952000341618207900c0100c480c200d00c1c0907041c40c85c2c840020468000b402d00880002e4101169a0a040303144c3c0f0020a180804808065040115160110b07003094003d05400100e0501c0442644242c980b22720017510300c40c1c0d40042207e41c0d4411100080440e01100c8031540102c03d01da980fa4000348560f020400c41495000c002c4199010302500000027410710b6242c100d150f84911000b04074142c03076034845410020028034103410340d0425240200b104 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 432276744 1250 432275494 432275509
    0xf09020901260f0a0b06030f06190204170a15060b030f0a0b03060702060609010f080307060c11070f050405070905010210020c0c0a06031e0b240d1b0e0301020306 71
    0x15145169000001d02c07500e2046000414184554081e9010708480801600b40c04034052801502540d2682110f890308801d141c0d0f40d1280e031040d4882030308440046014001d800b03003814a00442d0300409414503031148440102c1440d016031201c12944007000d8501049034207062007034200e1800104100e000e00d0001012035512006089200704a00c0c000026500c150503030040d84004006003ca0310149402c001c042d56401099a855208080c2880002242c0c910141804181c48185c1c000d182048095680c0d40c0103001041d0b03601c014841304002c40c601c98402009440010070302180407503050b0740781070309000407108050329500030840321200512032660006507145003501c08000050750741c903000b130505060400310704026a2083c10224000b07501503160704204a1000000c10380c40c1102d0014642c4c60132245030b003110f140c0000c9000400060b00c980c4000d2480c0c40103600340e000380346c04940000181100e60041205585800c07a40700e03103000035030099a95000c4903040d4002c40c6581415400944038 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 432277994 1250 432276744 432276749
    0x30106052407050a120e04061406071419020f030105010b03060108090a020a0b07050606010c170d14010b0408063103120507110c06070c030b07021c09090f09020901 72
    0x320481d2281e40c5000c410030004407201e064002090781d01104051801c42401c10310b0580c4030000548681c04d05a4914240c801c0d002228003500040705100321703100901c02d490f0808c400a40c0c80004200041c00201800e10140c104401401400b106040d01d0744104850700300301d4100540030343e14000061101d00b44400442e41c018100342000b200030b03074900c04400d150810042000790042e408400000d51080c0603000742c4400f038803600c00d8034241e550b40c40044840c06103500010b0a81c4d00300e411090000f0150200400950300c0104001c18261900d143c1070040020a07400418000000901041031640620816030804480403a0103540b1100c0020340001c3e02c030354071a225140040551f1a0101405a031250404000340b210900007403600d2071000d09012401d090307400d540d0103901c49540b42d80ca4050102d0390b01c6507105503580c01d09811501d07501055000142110250f2084100c5020b000b001c0c1d014190403e00e15070350f40c4409900700704010301503941c1145800003c40c1032410400050b501c02050505 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 432279244 1250 432277994 432278029
    0x815060d02060c0313050108131511090a080309101e050d0b09182413050705090103060f060b0a0c0212160806041e12110c090703020a0e03010605 64
    0x9204030a0000402500c6070f1181c165031840300003152140320070321141000c102d48090301d8030b41503603460110180700b450302550014a80040ca01c013664001d020b07540081034900c082170106003800c0c0240c02080010b821508400ca41d9880421402014541744001c1f00700082a490692604c03000480c883c41d14441030440312052201c0482e5004040d04503512010000c1d000604401f40b90404013801082041500640801400b5454184103804841c045e07094600346041005103040d61050f05600c400345d10b10070100c8460150003130010740c9036141e1b0104d60195004a40000d8000d58405006040f18100c0e881000c041d10107000c07080c1140d800c42c80c00b03c016038043d1100c00c404210220b1850034510350b50320350f0000072820b0b0004601c413100010518070a0f44124030741002030f01c1c4c114008403201080b6400804054001a075082d8043c800c6084021a035152801c803100b82141d20700107203958008480c1c002c0081e90118001c20915409001000030391410740003080f089003002c021800302c1a50141e80d44 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 432280494 1250 432279244 432279259
    0x1110a0813080d0c0503070914060403080702030715080f060f011205072307110301090b06061303050d0f020c0a08060a0b0303090a09020307142511040e0f07081506 72
    0xa00030300c40110743d00c145251504103c0d10700000c03000780664005a610200140d01c0b01408164401020519601c104004000c242068a15921401c0e15030050380100c0e098014031a00003407000701c0000b103447c15561910380b4040ba20388407a0f40d4102d600000d00b018420210b0400c106031030b07600211340100c010320b60000411255503000f0107443c4010314400384c801805242844240c40e040301000350892900c90141e01558412450405090b40d45001c6c02070300c61581c003804204d4501c0c0a60042200354014281d80c81680c1d584e4882c0385c2819621400c00c004a0305250003a0241c0ba41404081384c1e05004a6070341d892582001580b41c1e0b0790000802c00c031040f0359120716501807035a040007070f208900d400a11007080710351900d000c04040e4000341c03001c40101d00004c04454041c10340c001611403c50550755510b2800d0385d81010081301d400324070025195282484074180058955020702e90440003400d00410800510b10010740c070380341c25a40841e0309608180c8140c0d81c58400d46141c5900200c003180c852 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 432281744 1250 432280494 432280531
    0x20d0201031802030706090524030a0207050f03040b120f0f070828020c0c0a031e0f08030a060e0c0a1e02031606061e05090412031d010204030501110a08 67
    0x1a00800b8414065810301c0b07141c400240284e806552030040e41c4050364865043c0840600c41003042c0345060b22140c07040740600c000307140310000e40d0140001d40c1c041d1044491000b000c04503d801e40e4003a801010072144001401c0101800c440111034200381403102e000e05510301100b40b1840e06001400707500405c0410401319101c0320120300e00020f00100106000c0e03440500d03000c040000e60101c05840090f000e0181d040c00546801c514040032250010791180c4080107980b1051040d2010840880e02000340c2c80107807000c40c80a4010310b20844141c0c00010b00903080c03503c000d103401401000064610404c0000480050b841002140b0003521204000206240c3c04002d074294002d100d09203001c140d1609591050100d00d40110303049a031024408003c200c003c40003240184c04038010a42c01c40d2051000c60b0000c1c13418020f03c01c15580c00d160025000b104a41c1c0c001890000010002c2c142c2c0d0041018402c1c0f240070300c01c05c44507541da41c0d416460007800000203814214000d10394040030a901114 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 432282994 1250 432281744 432281771
    0x30c0e09211b060f01090507020a060c030f1d060105060f040b0c0c0306040318060504060c140c0a0f0501020601170c120102070501090c0e060103060b0d0b03030d0501030501140f04020d020103 84
    0x50300d401d000070b41c5100079107814a620072a51000110703001ca0700c035000704000080c0040540300d03448c064055580900100301d01074440402400c00e4102c82c07410541d486c4071515504466100d065011030401060111920b001e81050f0300d4058103800081c4074900400c100c0340c1017468101181c1c01c59081110141e211002841c06c2c0d401d01c94003008960305800b648040008040d130003c1c0540d08440c86891410311191070305000c44560042d03001d0280414401031300308000c154203070746510009034810200c40c90391074045c0100f032601016900c505008044144103126540c1c0510100703016140306003032070003c0d64041d03078255603400307140080e00d0107001c40441c1d10784040c1c1e0030340454141540260082c02134624600c1d110f4003100c0c003032091003034041110000c0f944640c801d012f50380440d2000003e450030003d549030242d004180d2058060f44c144400c100151641c0c0d001d000e8103000358020400000c81080440c50f05d444000c00174088991440c1c00c200700001a507031850550306030798082c80c0000b92103041c40072 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 432284244 1250 432282994 432282997
    0x1060f020f01090308010e0c03040515270601060210050c0708070c0909080a0e0405060a031106160c060e0102120a030510030204090b07030e0109020102060610090f0e01030c0e0921 79
    0x10209180c2d42040d040700281a001280b142c100ca04901141c40181e4030210030a80e240000d4900610b03070703046820620605140c01502d81c1d000310f640c900050b03401c030210f01c10181b0520110380c41e801542140340100302044e014458007403540700c4c440080c04140382c02108130f0294850303a10000d04807000842d5000c18405060b21400140241d101d0030005043d450900041d03a0b000740100030300117036041d040510b0a0174140501e41c01048003405601e0b01d1402c680d80c40c400d460301c120540d908040300f808109404444c08000c00100d5019040c4000340034209600201045c0d00741c0241c070305545c018504d000e61400d0100860303132110403514001a46444401c25030443c06207a90000c1d620509084e8510305012a90340001c0c0039042d07548042000390302d41e645031400d848003004081c0c00b41c0c1100000603034900344400e21803499241413900244682d1a03e42c0740d030000b0f1254000c0ca40485484c4010310410010045502c068640030a80c402c4c0c42c81d10501d0f160307440f000000111202d040080c2d082004504160 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 432285494 1250 432284244 432284263
    0x7120515010f030203010b0d1e260315060a050a0e0f040f0b0f04051005040509030909100317071e0c170d180302030703020111071a0304051605030601060f02 69
    0x49400c05156034500d5544510b030080d0109a02c294a814103141c89882e04402c031201031030b8880103d121841d03040f46002c82600c83d8103010380d0078a04644030031465045461082080c109800891622401c04a01c1150256142002c0a018010400c01c61852a4200003507421206c250314244003143c0c000d034080b07901004520700d59a0864280828400091b0302070300500c2c1051300c203503080c908100c0c0700000c0005844d01560458041c640100301841241025005154041c030340000b1a442d04d4400703000325050f1501116514805800d541042c030400004806041031003400c458024245109501c6e81070070100c840c00403a2100681032007400070000070207046801010b080c80c00f1480b0000000400351554101850b500000f11500300034149901d070022610181c0340c001e0001c1940500f19801544d61101000c3d6130003581c42800c000140002d40079030580545c901c401440b0380c990902d13290442c940150183d000701401c076030050500c25920b0001d84203044500c2c0345084a8011034444043e4208050744 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 432286744 1250 432285494 432285523
    0x60c0d09021c120c0809060c160e0708070c12081302130203150612070c0c08070b090103050901020c060f06041d01060302011103030c03041b0b0a080f0a0e071205 71
    0xa4041200c0c0078149503025148038001e0f00f20040701250640100c0d0000c58900c001405240d062050300603a08141028003000700c0c404003250b0703103096050407448100c911544089505464407003000051540280116007105a1b030501c0c0c2d408c0b11260380c50b1001c1c11142001c0c1c07000c2010032800034519840c50f101c4400c50a402804203000710307a4000350701c03029500499182071200455402c0c00d040c4d0074200210380305501181c1c0508100d44500c04c0c02c80c1c00256100040d200720b0b80c00100401d008806111140040203414034640d541c3d075171000003500ba03520003011404286d1040c002030141450101d421540541e0a81031010745a0720000001c00410714424040340000003083c036912000310560206065134000d884132700320b050b80550b2165076840100ca1074100640103001082c006000c0d140e40b110400a080302000011b501c94007a000c10b904a1501c03580010b094405008041494500142d040303a10548140801078a0085a9980741d07114407407070b020002043c1c10101401802d210210320503584 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 432287994 1250 432286744 432286759
    0x4030b0c160f1b080d02070308030c070c1d060402121303050f0417060108031e13030206030c07060f02040501093f0c0e22150204060c06050c0705060c0d0902 69
    0xd080508945a00c1141c11149942064003c80e44d401c0000b00760011a0f26603005000c0d66045a03222001600701400c08030340341005100b00000100c401d40f004010b820b140a00118181e485800c1d6007207554043d040600542c0f041205c4034405481d8298240d100c1e6500e402a4019016854111098403908403107460425000c10082007090b1006c100010348505401242c1046c0d0300c4103550b030346a01c680301a0124440b09142d2205014036400050a0303058040070003848050f48c0ea0300810070300c0c0e02c100c500d00f1032000001043e808020b000d114180c9088800c4004508180c00c3c0701c0040d00030358460244070001c1600c98071465840d251144000202450b4254002d5000ea5566006203081d02d0a1000c6030744e5003d203036022811500716814a4442c03001e88406140f8041d4004070340c11410f4000000f07440c102c0700d45000d09401d41305400280018007280d560221240041d0a11034226070000d00324900490b801c00107007000c12030005000303400c2020000c00503650040c4056520040100c0304002390000070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 432289244 1250 432287994 432288023
    0x40203010b04050108090d090509040311010606030e2a01030218041a091f03080306030f011515050403050c04020310090e100c020f06071101110711040c0504030b0c16 73
    0x3903480141c01210005e803a84e10382c0741c0f90413009941381d482801603400000d003c1c070010091441c00b000242d402134000d042402001023890400d82c29900c07260054004030f0786801c0048055031080060300b05500d890190001c1444215106a0444203050111810590042000380d960513a054548148440041040003440207042c101074440744071300c14003889202e0070000103205441e00c60ba0f00001d1f0030074000c1440d0041c00c5545008840d00090419034241c0b08500e107800e03480700c0901c51416141d8020600305460f514200000d0071800039000c008c800c010301400208000303440040c20b0054a08105d0300543c60350b854014074201c24001d584046001802c1c030303412107425030004c1410244c842d80d1000c280001c41078410141e80c1d542c00340300c8403640c540c041c000103034203103104111541c92000541c0c00481d00c0c40c080d8242c0c00b05900152420703106911060f4007445c4a107014852042e0070685030503c9414685540c4078040d000f4001000e1207207910300000c041103c0c4138043c0c07151640651042c0701224500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 432290494 1250 432289244 432289259
    0x72723040e0a020306011a0f030411060c150105150f0c0a050304060c03080105060307051804020c0a030e090a0605090714040f141002061603150512060f0a0c0e1002070504020301 78
    0x5031940b030160b01030b0056070000300d1001075040612040019450381d0070b2424410080582003984001c10990b0748080302510b91040b641c901008210350020b8200a101d20480a40e00010808045e80001d20804941c0b03188480c2c1008002501c041010100b14907480d102002d01107801e140006c44000e02d82e01000070042a51500210801ca00c0d034020b030b5810045a03250814080720348070a90300c10307011038002e01480b240000c04440c0b280c0301e44006400582041d41e0340d1142454507034a00e0301280856030040ea11041c90403d0300091380e0040b81c860062042d20f103410b002c14030359400a071901d000c0101030301c0034280300c20041045030000c010800d0070130b1400d50365041031007000140f002c1b21481121800000c0f0701c03541c80080c101c0c1c05840b4214109040c08083e250039401010040000d40c600c1c4818100000c0f1a41c030010301c5114505200e01030800b41c9000c5034a070109620003081d1140c0307285803464614013181e0140c41d0021548082d03031040b5030740001c05003c1c2d02d00031a6910423070344240004000326030320 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 432291744 1250 432290494 432290503
    0xa05040c0f030e0102090d0b0a1e0204030b150d260406091805010303020303060103020702120a0305030712050c04050d11150913050c0315011205040b072723040e 71
    0x1200c00760307002c100f4001c280d101e80c3d00b42d02c143d81da541c1c1c1c410780010b02c1c01c1c08200c5109400f50403452a8600140585410103441007440c0344d42460280d80c2d90200f000c1041c400c4101d0403541c0b0020f80d1246044c10405072000920090205601070030344c04698856030800c404804504080e40b864514140c0ca456480100070302c4c1003141d020700303e00842007000c4130703540100f98000c0c2d40c10381c1d500d90061400d5590704401100250400c07003050303900c0914181521b011a1043c00710080d01406a078a1a03524a40007101810103800000600e80305440d2030308011301030070160261015143c04582a29514180742400718110040010300e603400b15011011541600c5460300903c582041078480103a5840300000c12411698122241030500500300002041c10564498510041e101410300c110711b54185d50901044810440381216034401800a0014054100036078240004456024034040d02c52483c0e04c00c41095188103103409407003c070802903107482c0c0400802118400240c4108146148011400e546 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 432292994 1250 432291744 432291767
    0x4080f13080606131b030c0309240509030406170403091d1006050c060a020a05130902030a140105010c110f0d0c031a04030504030b0903070c0e04060c0e010e0f0a05040c 74
    0x920003500a00801c2441e030040c0c58400c5a038602018840c0c007008170540182c001c486003401050390311040c80001030903186e03581d035242d0880d554820468184840c440100c800c05401e1500552007407200300300a0b5032000c45007192500021104500f0b03102c915060b180601c403030308264506042128070034854020314038034070b1007040d2003015507a0b46540c5400c180c80798450380002c0100c81d002030001520b800302c42d03002070604200c1d9280c02403914040700f0303200051581c190030524006e500042405030355030460044c43c110400c10030144019524110001c0c0ca200621440103080c010307a80302d0280507640341540d01080c4c400103070442c847c9405500d00480c6800070780c0030880384501c10b1a542280007002c0b8480314803940d49619440e1809080d5254500201801010001d261008020315000248200000c80c01022000340c0704c2140d0070726140c40c00c04e86003a455800d081014107403011010760f0b40503640c2107250800340c0c2c600c1880131580010403045c00f0300da0825038106040c241548002903002880024 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 432294244 1250 432292994 432292999
    0x70c0b0901020c011d0d081902030d0f1e050411060f0d050a09020a120501110a03020c0118081605010204030203060903040303200a0303020a031815111204080f13080606 74
    0x2150b200840c0103441038844200c1d5017142004030500c1132024203102c00504141402400342c241050038002c1a8001d1910141e82000140c1021079641242c0610340a042d401c0380c40c41c50306020040c055004494199420455506641e440300045030034044403600101424002805455441c5516584210640c5c0281c0ca0042c0c22450b15001945030f903120701c9030b00741460340208202d4032540742003424080c001c40c1e03000c10341d10355607914829800d1010200c01400d072110903403030250300c45040304242400c490400c00f64800d01c10b5004600320000d01801c007240ea40d4071a5900700c40ca03221301d45c2040381c0240100d800c001d40521071031040c0140e01b40000050700c00c0701c1c0709a590710030603108000003a11a20302c05070004025032018180b0f10001e8000e80280c01444994940001e80c0d0025800300e08626000139416130701d8140701e100c150003103089805898035141c18202194640042c02c2580c2c44003102c000e10290205501040a0008042c4001250312030141e8884d8130003c0341d20b9140c00c540303840040e2011071 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 432295494 1250 432294244 432294253
    0x3061d0c06040e09030d05070801170c0906190f03060b0a05010c15020d180303060801180c120602040b07050106090f09050309280608061c021c08070c0b090102 70
    0x98440010311480000001d07188904107072610042c0b5250382c1d00500f03040d000e40402d101c003945d2200313103220f46403040049903162051549400d060050154014110301802d4000c03892084d10380c3c4a49001c1a048507041c0c83c000e030220100c0a089051003c2038200c0780304045241d20001c14000c168102d071541c104100c0d04000f4181e074800040d580b8008901d0001c24030b150003840400362600603409054200600f0a01040c0c0a00c696540e4040b002c81100403000b003544d80009200c02402481030703030303415810181002403212664840001e4401c243c03240c90810403000180d81d04104d0150141c4000300002c062054490901d490494060602c5d03001d507a01031807520084486130151801446121030b0803801441c0b805070b030042400302d10b03914442107100c00050051003d4280c100d2610640080a07143c0c1c030b80c005070a2600030050001030060300c0c03400c803458141d00140541d0301c0380501031042c02244c0a00c0c1050802e403508034502d004403075002c0c00e000078401001905a9202008000d001001d030b0907039 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 432296744 1250 432295494 432295541
    0x70527060c030408012c1b040b060a1d0108060a09020d0608010603080406110c0135090703020a0b030103120807030906020f0c061e13080d0603061413030e040c05070c0306 75
    0x110b00d140000212410340e031780141d00c4400100d41c0c404141861f0b5101034804192a800f007404690154022007003903000a01c00c0c00400d8800310294041e245961003480e203246141004000114070041034014140d8140e8001481404030007154400307001450700340c0003841220364a0038850490781082c4102c0e00450b00703c0c1c600d03a000800c00306044a000005854007240c5000c0307050444101c4d02c2101c1c0383c1650214a8603080c22002c11180d941c1d10038160640240f01582c2503105006c1d6040143d030003082070200c24001800055408031001c0400c000c0d624110003550355000341200540380c2c0c484081c01d01c1348000b6080c00b880320168010020b001580e0100c982c03a0302c814608080748407400c241400c4440360b400200f03016080f40701d07a01c81c095024200340341c2406103503424107044501c240e0044403034540d00c1c40342000c183c103164034155100200c61000b0310926038548026003440003100142e40305650b60110041e00394003407000c0d920216007040c030f4584080d40760b19005c801090316107501d1118100c0e4548a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 432297994 1250 432296744 432296801
    0x140c0a090203070801031e02131a031c030510170607031d120d2304030f020d02100915020c010608010e030403030e0d08040803130e070527060c03040801 67
    0x2c0301d003e00380c269138040c010f81c40d540741d00144a000d01c0400c0d10145104140c1ca001d60380d62000c22600103110b010003e03080324898045198002906c00140c0a600581c0d4010410403800c40c500d01c0122880c1400b203010342c0c0b4551042c8501045420205461602844d0400514800546184034840c1610100f141c14462403500340c10404005200070680c0c00740b0030074004200103030064039610303240d590007227840c48880711208000180d182c00e480550303a48100300014036600003251032813a00980060185084d40081c0292904005058240210385441e01031040000c01c21541c1191002410211740701c1656588007400b808040c81500000e41c03d008010946000c0801141c04899041d02c0c4c80c0000d140300010300040c211040c405a8081c2c40078000003588a40c24402082d4010800c80c2030401641041d00342807900102422041c1001750510200381420850350017400805082140080005042d0000070130764890404504101d00000c40c0c0001c1c0384205400c114070300107450f0a8030400078000c000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 432299244 1250 432297994 432297997
    0x151f030816030915170a0203040f0620030f0402010908030a09140303040f1716030206041206270203070e040b0c030c09090c03010e09070b040506090d140c0a0902 71
    0x20142981104020350216a038031510309640c0700c1e1280c1000f00381181d6035800c2d0040076043c41c2c40480800c0c1a40c48008560401c180da1513401076220310b0460443c10161109204040c0c000f0000b89044d030b850181c00401034024030550b01031103000702099036078030b0503c45083c28200c0c10780d03049000c5034000720045a8a400442502e0681361159942902103142141d246041604602940d40600007000007050f0b2808410450b03010b45210105d501500081c8803255103007001b03600b10001e15603020002800182e96200c100c4045511101000d155404a410150300801250000010400481c0918207419402c46c0c800a4441e00031015118515030307444a456551208540040c44050004000b03441058240051900003101c140c81c0307414415408082580510191180c0b5461100840100700c843c05000c0c103d607000072000301800696140059801d883e001d9401558414140440c2000b403e481e08508a101c0681000340043c1c1d030b00002c01d05c292034003100001540208001100403a45003551700 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 432300494 1250 432299244 432299249
    0x9080105072109020d02060a09030312020405031c17160e0405040206041a0f04031a010504200a141201050f01080907140d0b070e010306080d0c08070c0503151f 70
    0x210803898000c0030b41040005212a4034200da214000300784150250701c410700070300b8803035086444403400d060542c1400380070341415014440c800e50040005002948020401c0d0000c05511100d100800045032400c1d82e000041007840c40702d00c07a00d8406c010000d86544401221503966444410b14681340d00d00744000c0e104200c03006500003104010030098640c1d49050bc00342a1624000103007082c8541808100035489640f091320030349130380c0440c1114103082e0840a4010402150100000143e0803000d805441800c1c04106980d100802c500c0b9805012760100320076807034111085655100c0c6448411a0000e0a018050003550201002e4126500480e05a40031b442c5030001803546620340000d11004c4110b40302ca0a070000c3c901d58003000001c6218034024080d188a0300e60f004900c404000040031502d40b40c1c4044501e03805a42c000c0a100d03003200c1d07144000c2c0d800c01500e540e20310351401c19003680307400b690041e038061141002100941d026800043d006041c44140054141c01c45c104200d03001c00c02c1e0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 432301744 1250 432300494 432300527
    0x201060501140d0605060304080d060f08061b0408070f1823090c10110f030307140903010b0603040c140d0c180902041d1027050c0603070908010507 65
    0x9844404921040042c22400c4146000030890545401c0410091f8006071003c4491540215580c080c1c8903240c02140040c0a40d843c81d0701d400c07450006015500c407001b40610062000344010011185000c01c100e4000c2d16010301103c15030f540c0e44003008200360b040d10075000a140003041147d25481c05000e04546409101800070f0410500f200d00001968041c20f040300a02c00c030385a09906840309504440c07100015102c0300c90f090000094075081841c40070071072171076420070810803135055001440c1d070f000041007901031b5851b072402c08046401080540210790307200401204000420440614444c00c3e100081aa400404e9000007031040440c00600020304680c00030307809102c2110301c000303058001c071940d5001241000c62a0041000c079421160100d0340d250616072111260031007000010555024641c08005e00e00841c0340210b5511080a2141c03090500320307613042c0074080300704036a91200100500306a034900340004003800d070f12103920901c0859402c0400040c02280a085120b081d000b00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 432302994 1250 432301744 432301757
    0x601090501050a050702040f020a110a03020d030b03150108030c0d03090317190e0d0f05040f140102070812090f0103090f080c010e01090503070b010e1003120e0306041109070201060501 81
    0xd1400540c0c158201440036810820140841005651240684101041d0720f00380142e40b00c401c0310000345504643c410301d58142e400302e080310000990009201107c514280b4001620030107580c0000c0c10441281071044910101000108807014044002c103140300301c580c2164400d00714100d0a80507102001c0000e004142400360100d1002c0c10640303508d83c0000c20040040240100b407000c103085a4090441c00041c1d4090a04451982d402130614a0008040e08015091514028210058070700a02a66400080001e10700324541d008102e5100a0090501581c403841c0f9038080c400c8154001828491051840b80750030b00055010340f0420902c03580002c80f941c401407007134581c2180c0c0d6104410020380d0359079841c107007114480f0a201d41c1c0b4415102c2d1014550f01c81c00c41c140030034603440c10f8003e1311032401d94009001c031b21303083c0c5521201180c0c1e01c107003164081300e01a50706580c04031031030400e141c0501450f400c020800480d21260514484100d40030300c0e40b501d03480822400c0351658001c071800700d400d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 432304244 1250 432302994 432302999
    0x91c0c11040e0a030806010306051c08071a0711211b0c0a08070512061014030c1507151107030c0c0803070f0506090604110103020918090d0305010806060109 69
    0x48119803980210006480030841001c02c454881c50719400c2241500010074800c140025981d05025900052804551038060f10399000e0740c41300e0701d1f04100070080c07520310b001031043d041200300503070300072220054248000c862404900103000c240035038030503031003500135880048010030380402e00c251b0384550303111058144006040c48410980011300d00000b603208402d02e0914564813070810b0380103440780320094004a4681401c0c00000504540c544c074041c1c00400800060702407801420301164907c0e0801d0034003036200404a41090010149180c100c0080b080d140b4900c8a040000c0a0192091008074003600007596858216031009144406400e020440007001c6480b4480c200c110600404a00038940c0d030318010b1902d5030380014412564034201103500e600340b00041c080300703502c428040d014208600d429900e1310381c2500d4154a50341459030200b60b03031480740c42d01c06000c803041c04451a1100941004a04580d03907505030030039100000e040000124041c08041011030003048103848030a0b4250 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 432305494 1250 432304244 432304253
    0x501060b1c0519020c2505091f030c0608040b0a05040c050d0c080303090601080f0a0201020c1c020907080a0c1119140105010b0d0b030607090b09012303091c0c 70
    0xb2000c0c0050250110350480c40307508501c3c80c0b000304081340038003004110620b10301c01d0404180464600c1c410303130120001020010f58560941c0c4985c0045840503040c41000c034a040200c800c00150406080c0c0741e550440440e80d03e801003005806075002d4218058180e40324039184c9c2c1a100100e4000b0000c1c400c1400800c4542071014039240154803a9184140e29030301d80c00d0b001d01e90f400890300c00d0500d50082004100c034000520242d403070010b0f00000ba0003c00780640010796aa07034084d507058003c140e40b0260f1b111020000c103582e103480d640109a8001810210002080c1c1d040941c2c80020701443c024444903840d020b00300300c01c0c2d04056170300030304102d2444e0007426942d502c800d10161540302c407490270000085002e10480d400f90a100c00150b441c3c03141420407604590400c042640603511420901070b42d59002203d20040b9504410f54540e0781130f003d001203d895620040c1000c1c4400041401030b5401d22a001542c032549010049509071000c503081345880424408400001c0b60034000e1110115 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 432306744 1250 432305494 432305501
    0x171002030702100e0d0e0a0e0c070609021309030311130e040507080706080403170906041502041a0c10110315031608010203070e0102060c0d0917160501060b1c 70
    0x148841c010b807603000e00c03803d568078107aa00601c103158098010320700850090360002e10b000d20400c2e083e070f401031850341400320721140124050010141814042111001c01c1040d0304481c4200307501074078aa5821954581540c054140301c041200440d040001c601c103001aa00181c8904098032502c0c888a1858521101641d981c050001d8609000782c1e080032904250070440017008040c03964511a00380340604000b0002c254145075038440b203548006102c3c81c5900001c07140d030060b8200f01c0901d2142c00b540074400003489a50721903d100070048091140c07040d40917001d420750064800a03a030826012000302011291007902d803406984051000c65030f5041c240d0620807003981c0140440360140c0300003030801c8000c2419800700109039000000c03c4902d607842020314440c00700a00041c030250501812103000c9015141080001d5952183c5890902001803c0400040d005a6516940711000f044c0002101428001550950300f0010000340901c01c2c07208460441c60b56603204665522100c024801a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 432307994 1250 432306744 432306751
    0x1404030f020a0b040602060f060405062101060305010f0b1201090f2607060b03010e0c06030718050619080c0a080c181f11030910141b03070b0117100203 67
    0x114410410218200b05560300504c080c0a00b50010011481d103024a00300380c5034014280350056062600303021280d00c400350750f1aa00342031400c0b21600c13001c0e1040000d00501032941b01420545c08c0000d031000921a60744000414807064400c03458084038094490b0983c2d21291004040602c0203d0182c04a44004400c9083c0301816403025141846050584001d8208050a91360350395611900075072403501340b1034900913013812400f4054003882b1100044541c00000c0c044002e00c110510b00020b00c01e13407101110701411009024a8562520045010004000c0c880010200301c18401082513105078506032040d0403003c1c1e480d0700450b40c0b100c051400031340101078400391004c2c3c211190401036442492403c15044040301d500105031201800804001c600365206000b60000c001100e8640c80c3c0036880c0c0d0400f01207081c800c0b171000f00c0d050555590300c6210440742c0349805800041d4805c0d4008801070209900030842400c1d0350740c0b03c010151240c5042c00c010032282d03106000590b42c516290300034552 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 432309244 1250 432307994 432307999
    0x1f0f06020d230f0f1305041d0c0f0409020909030d050708250c06050f0a050a0204030503090915060304080414150a03051b07080913141317120f0105011404030f02 71
    0x80120110313401c003032600003022200c0e94481c466000d000341e040610640b40560310031240b100016454040650302c0714984109030380203103440b10030001951101e03084007400030340c003821401d16440d010ba601610780e044000343c1c08109041001182ca1a8490920030703014440241010420601c4000011040013019112405020703100121002150b054800c00d403107008040c0f9800d040c2d160a6070f10004407070008003416000c074410f104c01e00c0070420001c2038842c3c40306e05840702134042c2c8507400c1c0800b8500d00b011400342e120f84008108002c21038080098801c47c1c032624080003030182c0c142d0030800034684603035060582007414421140d80b40d11a4004540281060000c09101800f00c0050a500e40c05141c1c1901c600b000080c4104580c00d00340c0396031072019000c20301040b200076244850300d40843c01600403c8684a080f69413014001c907003084441c5040d41da06102c0d5984015442d0031080750080780c604800520900000409500401040203010400510380d4038141c25a03660341100c0012510603038 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 432310494 1250 432309244 432309247
    0xf27081902012007150302030a0b101403060316080a030e090f0403030207060b130903080a060605090d240903030c0206040b011a130803090915090a051f0f06020d230f 73
    0xc2d8882d400b19070400751161707079070050380d28640034801409640c0c4c0c411980b40125a0b0034001e030282544122040f503200c0001e40206d9880c0c840c000020700d0704aa40b089000e10007404140000c071100c0014400c45014401d494801c80d0b01c4030340342005051001151308100880c0d0310000100041d204c1e50040c480c8174030403900041d49610841c04107590040480e01214400e9440440b0340034903420030f6401e079202800d40380a00c501c9040c64801403890103a41d041c1070090644188040c00c11a01d00d444d5051415820070090a000700c546020003d0400642c3c160080381c5088450301c5141d102041c180c1c0700369040a8010307290392074060491680b030b48110f040380150005012034200a1501010f10004020350001151629001d0081014160014142a8079080c000c0c0c0303505060384030390f400168803030103441000410383d461003d5030082041515402541c403250301404070b010326450b4602c1c81a505594210390030040f49070000d0f0b40c951914441c90554407508108400782481c0440100641c905508003076 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 432311744 1250 432310494 432310499
    0x10504080d05071215090e07050307052403190c0c0201020616020a0812010305060609160c0c0902030a060806091612110a0321030207120f27081902012007 68
    0x11400c44e03215175450074034185030010402a140341405115140b0001c0400f503c03501c0c0c50040000e654400c9481400d02800d10a2400c4a07012920400410880000d44041750b581c94070301842d11200e1400782d81d00025600e000c0c03842c44c0452003007a4208156a06800512258641a0021542207052604a41140700e44000c01740022035078400380c107a042200151002550661404a041c070344018038050250220340200700c1c201e0480303071a00080600501740b42c1600e40b0b05040031425654190407a121850000052211440d0160710000c103c0d00031500791507172a00c600b180d01d0f480c1c1d5401c0f541e2000480c4240810b000d80e540d81110130340b0051040e4894169000c01c0c4002c00e401c080c56078000d8a1103409005500213000b442d010066440526241c11032030801e841d66a104070001c0541000104600b100f4546806400b4030038903400b0800540c50242c01d001c980c000300d164150680140c440742d0080d4041444c00b40080d54940c030480d0746c140c403681100c505a42ca8500c0400845811955610992600 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 432312994 1250 432311744 432311777
    0x52109070f0303031a09101a043c06050906090d0609050f06011a040323070b0c010f1112070c02192103080a020c030c010c170108010504080d0507 64
    0x1c00075442501c02090b2098000d0a00f503984401500707182c0030301d14801c10030420004c01c21001d010784008020500b02d0040d403018825a80c02150003040c8401003505140607000c1d030416160a540a0300485220141e4007014403800d170540703e10800d000b01c1c02c144084a8030b407030404d0240149000c042c0520b40c140c44075885200030384142c0002a10240c201d44414052407109124071405415820003221840360880644a081d102d0707071001a00b0200d0800301c10030403120780c000c24010340c2d041c80121007050741c030781008040301c2c1e2140340079904541ca403079005d00d102c0a407030042010f1300f0a05550581400c01c10f15580c001504024880002c1001c581ca22200503520721780d2020f00c16114090004000d401c080c071844c002031410080c11010202c0c41e9007040000d5001d038005a0040c4a00c0c800f680b0382020150052460248402e460745075400c100c00d8ad0788081c3c0c0840343c10300d0f210f00c14041181d6a43e0700c1940c1402ca9000742c4e009410b020b030070840320b0540702c8650080783d0403500d02d141c2803100c030200380807 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 432314244 1250 432312994 432313019
    0x2030712090e090a03020a060b040b0a0303030e2b1407330203040b0403030c020313080c030105060d120309080702120607030b04062601150605071205210907 69
    0x14120040303003070444103000031082c1c07072451984007a14200030501c8000d40d45020713590700e01c44000103200c1500d07a0603240454a40ea041542d47c000050205803c09859140c0900078200001210031103200700482003030511200220703000784001c0d001c61641c00081078070017281c1c003c440302c2d0141c9045800b0410384000070030000c048071030b0b04000c0300c1da1404890000492908582d51801400803140140306000203e440503521980043e454200002ca642440005034214054410814400c400e4080002441c49011480190100c2e045008010503510b0000300001420f0505014010f0903244100044480c020b92040714203501501003a4103102ca0f560000311000007005001e00c0c02d40000c8280001d050701401901c03101d50007100c0511000b0308090321800750703c00501200c1034402c0011403e034003402c0290300c003110b50041c0e6483e0301e82d01030320b40d074001d0126817021404481c100644030f40c0f00d00c1039200710240d50f4070325242d04030070080c10030540da0000040b80140200070700380242440050205036800 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 432315494 1250 432314244 432314273
    0x10b0a0b0f130b0a1229030c0301020d020414190311030313081b0108090c0405150d0309030308071404051e04020310060e03010606080f0a0204030c0608251e020307 72
    0x3603000b955000100801402031000840c1c0c200c2807800c205444115800702c158061b045440907160191305062072002901c0d240252043c40c0e010b51001030144d8070500709400074000c1d10501d00d00d40d2a5030200300280900003003200e0003004020240f007020320005444824104031148001e003201d04001c00c065900d812850f66a201c11959484002e84148501c00c481c5581d83c3e06c9000d09041c0f040f4584900c003103454503030b4804c050344103d6941300040c1024001c104070f00c2c0ba010b405080425003621514012b08032100b98042600031034118000542c1c564401c1c502ca420060030000c107241000d207040e0911080d04050000b01c00e16801e40100c0140645551000c0d52007550138101d442c000600d810000303484042003020031802a414039400744580364014900c1c2c2d4000300075480b8514039941d47d480150003030045410042c41035969403000241254028245400b0300001d40132000021a0340d1075080b002c66115100d0004980c0301000000f040d244150740340c94450040c0103403890203003207541c0c1e110404c400c1c9 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 432316744 1250 432315494 432315509
    0xc060f030a14072d0905040b06040b0f030403020613031b03170a05010906060509030a03080415050c12070c050c060306012a121d040203060a030f03031d010b0a0b0f13 73
    0x74644c0f04441032000d00c0c1e8183c140034650003401d1030440e0000040921003103026007802940c8541001c41152102d0701142d0040c03081e000080d49803040004010f403a58000d4406a0040c801d25000c2146a0020003003a000c444c0d140c0c84003650f1203034542d003250109040c40c000758180101c8640038500080300b00c03500780c45004110340000351907041c00c0a410480e440c0781c21040c104002440001150385000441100594260400015907a0307031389041948980099a4000100d0402040c40788005501c00500402c502400c030148942c2d80d20401143d204040c10170203407040d400b405280c07c00d42400001503821500626051080f88414180305c1d8490b40b040071400039100e03801c4069400c3c0b01d001c10108100810a03d4240401890b661510030009908080e481c07040d036001010801d00d994599001004541c0046007602c04c0d1050301740940100310240090000c8203a907500701480302e806101d41185c03e000104030342d002508010100744a0b4000d06003010b480c03103041050315140e10340121030400a2510 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 432317994 1250 432316744 432316757
    0x30206030702280305070b0903070510060609060302090d0b1b0a020a050c0306010321031b03020304111c1b05120d0f020303012d0e0a0b120c060f030a1407 68
    0x42034a190700740004400d0fa6001d15032008044000960100c00c0710303440c1c0e40041d0340c42c4403500d84861590441c070503010000c000e031049000c94990784c01d840d00094211015521546101991104140c050f4400c0a4031542c2c8100f09168a2000980c504d807401e401440d00d060810340030349251040401507101d01101c0d00980c0c0600b00c000d041010070003103c18180001e0b4041d000c554510382d41c8205d0b140d5850403810032a441c442c21009401d100e940200705024a060019001c3e00d250100a40254000c1d20140c0b40c001415030850b00d6030070700c100c401407109000d61211100c0c5616848613107600241c0041e5a04281c11240700155a596a00b58a5100300030348014040c0348451200213480c8252480902c3c041d50030910040001c0402c00c40d01e06041440700c4424088454140c000002d0780003160009101c0c0d903005003d200342194298801480b08900341c4045150501440840f1b540305000b880260340b00c04c040080144522030000a1904403034607600110340c402e42c40c1522180070070101d50700c0000825 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 432319244 1250 432317994 432318013
    0xa3228060f05120303061e0301110d2906090109030b09011b020106080c0d02030f011d100e07090b030f0a0308060406120209012601020c01090b061503011806030206030702 75
    0x2020351010002c10303085507a2042c00c1840c00010b0b88a0000404061042c252159035207031060302000070484480d0010000c00401c4030141c0d4803075142d00440c03001a8181d242040440080003407803151151104601d0044d25024111410003c55620071014a410001d41c61000800521102d04607402081102c00218040080f089100101c062800710b000c1160705019003044449004645424046401c0d1214100c82d125030002c640b80c00344080d51407015620b80031b15007240b809420b07820707000c0c00c1c6c3c0f4909440f5030744003160311101076500c00035080f42d2640004404101000165000518101d07010301560f02c0b80503c90302c2c903424560042030950100b4071002c200030082c501842000068504002d14407030030f49103a004034044810501503001803402010740303511145906034042c05d203804160000d40d60744c0190116a80a4402c650046600289603000303d115440d0408920010381480c1d800142103a103003903210320745540700499154000303580b05408400350f00c0c1c0c6001540f00724015001401e1140 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 432320494 1250 432319244 432319259
    0xc1306080d1704021512040c0602070603020408030d0b04140a020a260604050402120a0c0302091006020604080702240316021b12010e0706080a322806 66
    0x22080440d01d082005500c0c04110a210303402409030007640603546111070b142c501c461005903100e095042a03c641050301040b0030000c090007100c05952441e03003507034880c9031740b0102a4280d0180b0f0107400705982060010100078820340c1d00c03040064000030004911004440418034050b80c044c0c0c0d00900c3c0d6500090042412908541074034880d0803000c2c2c4440300700135003005200001c180035002d00d11480c0c0f21008202075544484080c1110888001901c1d821394030f928007001140c41511007240a0201c02001403a04081120000c0846003580c000c2d010a9a95640302001c2e40e10081c407c0381d10103d8045444500340e450502010750210003a411580c0b81804000340c070810314007440d49011540180c1140b03204090740701c0b04e002444420784945d802c1c40d120350451405006103030b024032218070508100088141e84103070f0a5015002c2c0600803c80c01c68582c04840c0078055a00d40603081d0419941084145c484110315198421041ca079600c00c2c3c09241c181646242131000c261500c800e40300d400900140 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 432321744 1250 432320494 432320503
    0x3070209190b0a06050f0d0b1306090f02090a0509070903080a050901031407050f070602190f1107081903050928090207020a030b0c0c0f062d0f07020c130608 69
    0x2100103c6a04001e079140c80d400901a03c5024250880c50801042c002100c2440c1e8000c0349666400802c2c0c07044030a0b0f00108040100307083e02c101411181001c0b407840400d0542d1080395171a040241c000b11889007800240002860090103c10420101001c00408180c0c240050300c801095651869514640440010142e038000240030703070204e45402c1030001e000c3c0c1003401ca66000f0343e10390b12681c80d07103c6e47c1404030083c09000250051000640040f51450364400f401c1c03005004151144000e15680080007550741d0442e018130030f810340c03200c0c0f088a842404000d8100205200349001443c000300788004c1182c200c1607411141c8036a103036940d80301c0704a4405e04100003800c480c040840c18000700303800140f0580118031000e0070b280d542c1008038900310f40e21400c503200c040503413007103d00c2400e00030b820720380d01e0320111804440d04c44141822030710350101c640185a11908154081e0301c54940740f03500c42da440000303400c160652007181106052500c1d0501030014000d11a140000c00310301e8288180c0c10b0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 432322994 1250 432321744 432321761
    0x504080f21070e0112020c060105150708070b0109140c0904050c04031e0501060b0a080c0c07082b030b0d1b08070e04150203190915051504140c04090b030307020919 72
    0x17044c0c018001140e000200158080c1141c030101e8441b21010030805031885c0700c1c4148080079155801c009000002e00c1003c213483ca0480f2202c02040001505a8016840307805054a103421100010031644c1110300d8039070801600104c40d85409880d1503a1303030b9100c00c6008144084107a694079419004801d205082c03194500a040c2140c050b403900341c00c03190081c4081d0001300041d00b241c2021400100102d0304201c0346000e080140d00700e4890b130480e181140d840450100c803846e841e81c03122109a4820740700c0e005070746031194050070720b9142007c0c0d603440c02c008066401d20b080b5002c40000d030008021804000480080650f896401c50505050801900c51000000e588e010180104140000e0300c1c0c0450500640034060034000554000b5450504449035500241500c01404c000600c4075420111400814140e403caa041100140c0490a075041d5082140e9032203851200f80310810002c0c3c1260040508610018141da142880b6036000400c2c0c00c506135141c0103113410384130a81c441880b007807161112 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 432324244 1250 432322994 432323027
    0xd050403030b10020a03081e0f0901110a0509040b03010f020f0a022103040b0703060b04030309170604020901051005090414041709030304030311030c0a05010f06090504080f21070e01 80
    0x580c42906001c1e507240c5d04110020300300700c6400d000460b81001c02e02042d143d1100401000d0150501e102800105e041c140e4681c009540307040c8124003409000e40448104500307c3d00c0e014101000801044000c16503031541726095522003c01003065181c910003001b08014020701640c40303540f40c020003440c019019440303006044202c0c00c81107446403d0f406503a03200d684180784d51031755070358480300301c02411043c0d004056074040410080b00b050b030425207040c15507038140c081c0309100c4a848405a40d503803050b14082d4000000030014441d6041c202e209a55508a90606500c0c0c230407a0804102291106501001e400c0c13815400d01080042c0e07509890b060400b01d00d051420300b4031040009850b4802c40c8001400d204900c41c1c0494040702c1801502d003d64480010b80e00030190314240117019044060038540103601d0507801180b600000c0c850140501e801554050410302a08400c0b11180e103c030919158090b00c40700802210b0070400780d1b0911408640c3d44004050344508005052007013a03241054 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 432325494 1250 432324244 432324259
    0x30703060503010b0906090405070f0b0d141605090d0213050f0105060717070309080d08181f05090c1c03080f0402090708041e08041e030305031506040b0d050403030b 73
    0x3c0c01303680c03103100c07090b0040f108540c2910301382c40f9841c03c545407018684c4030075502ca03124000004c4a0781c503180a0600707109800c109021340c1140700d1405100200480c0c0d448051105401841e0307049214101510f20000050858500d180d000e40010f4850300880034a50070071600c074810814000b0034036402c3c5004007020348400b81894143d5607001c503561495010500c4048000c01d540080c1031150002d2801084102d0984a0242c0c00001c01080344104603841c2003525058031003020103076000a2110f404404c07070b001a019440251a00c3c00207800e0207061b00c0102d00ca1500701340c07003503550b00200d0303120b18000c04903411422030389281c09029000700504507148800d1283c108405a00c1e09860076502c08118600301d451503640e0701c0c00f09403c04403500d504020340d492800a60400020300d0013402a01d0318183c6802c020b03410415245a00f450303c1c000100000d00074404580300c50b035064a24012144002c0080d414161184c0c4d5260454000084001c081d5840c1c200740018140c08d80324840249000f69200f0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 432326744 1250 432325494 432325511
    0x190203030a08130803090102090a06020708150411030f03071b060509041508030f07030905091e1009090c03151a010f02150a0903260a05131202010203070306050301 72
    0x251280075007000e01040c8100c1c100000c11085441c01d404078010f0b80008615203c2c00c0401084d03000b0f41183c0d240c0c2e80174120140780411350500000d8924211030070540100812401c0c2d952400c44010003600c100d440da144d000620101c3d60303060040e01ca216a18500039a103c0c4520304180c1d0344a10f01980a10b0b00141c0c00e201440026408000c4900340700081e10b0110390494901c1c450200101a80d00c0b41e00e10740030218482450070b40e10001000c006001e55200780200c0d80b01c0c03040108402058502d10600d024042d60094117600d090b00c1e46038405d0070407807031185d070340c1d80c441c2208150383d0444411940c441950109104001d0f900711048051034581c0420000e00080d500d01030307508414040d0756814805454010f4140c58400c01c207502211402d01d5154046042c0406605c0140c0050a02200460003040904944100e1280321a5889421030100c203110303119056000001c28024100c03003200040c0040600c003040c8030b07201c07809040c02c1503400103aa80ca8035a0008044403480c8d0041403080c2d0601c80356 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 432327994 1250 432326744 432326749
    0x6090f060f15160305030a0e0f03090d1b03050717030307020c090a060308120403020c01020d0206070e010903140609160e01031b270c050306010c1704081e1902 70
    0x610348060800d65145682d448180c0380004140180e1001d0240300706240c01c91000c1640c448003460041607849018032025040c403403816210007141d103466030710758001e01c90780c4440d140c1850340751542402045180070012096840f88003956198000352010b03400f04608001000711443c20404190070400518111f06001c10300948540c16041701c64419282130b03012a400c05811f134000001184c1c01850341c2d5a51010662078200c0800841d0158003500030f18041c203102d940007040340303207652806901034035050fa28010161040011076082504000a8032400f00c00502044d44a03212000a00c1c02406036140c441d010510703040741c003180101c500c1c84102c0b042060324410112903054070f50100007600f08030340002c20b000701d40c101a44000040188418403140a02c1001c03400390910407804030601c000360075210b0a41c3d03284001d48081d40012508850080403a0300001c0c1c001458440c0c524040c0352581c4c1d220940d190100d807085030688511035214460308078508216603483c255401103900c0c6c1c0f5041a400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 432329244 1250 432327994 432328009
    0x20309070f03050a0605090304150c0b07030921020a060e100c180b1b031b060f13060207141e160f0501140903030a080406290d03030b0d0b06090f06 65
    0x1748856218004070701005014003c4d24040d190540c100440d01012440c01003801c031200506541c400201e60200b1030710340c824028090400c0c3c001d1040c02004d0011840107041d401d40001010450088071a0b106c0018414098981d207943d0303400003410391003a5540355000710b810140c44074050040021a1a002c058420440021076400582030b540703544000a0854519003e40c0324103840b4040042c5840c10074045000c01d810600c1090b0440f242980e0f4081d2089204005803841800044482c60860008000c2d8000780603461141c50520240030190318054601540e4980c5514018080348004104680c100a61a41603027110035409149203000008044501903014060402000c0d0031041680090351044030044500582125607503481030070024000c4200303480442e1118200945420f0035841012843d02e6a0900f803000c2c3c1d070050801c001c000130740c02074807412400d140d15003c10102d580e4440303120144050041c0034110941c504541000307201034004020280c03c91030081800015103038a10f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 432330494 1250 432329244 432329263
    0x5240f1c020103090209040b07090905130b09011d0d0e030a080304062003090c130212360705010822170f030a0b0a12111504080303010603020309070f0305 68
    0x1080c000003100c1c00124041e20a200001c1d422101e024244402c00a041da50544100c002d59603401c4843c1d2a8805030080d2030081d101085c002d281038000310080b80705064110380000900d0000900078000400241360203002c1e200118040d000400d07001c1c482c94220003000b07005801100030f4032400c03115942e2034150b80030141c00079084a50340e0001d003400d941011428000c507a0355180094032441c0c0310b0103903541c8010b081401e46c0038103084009516584418002e0318401d514080b03c0e0b40503a45e80288a119043c0070700d02002040152000c10846401c4001203c001c4900c844051b0600c94140000545159006001440c1202c620082610003907003075580d01840c0c41e40050004294900728803070110031b02a51a00d4011198000103210f28810a036100a8944400356070009000d660b0f038035401051030440030060b02605000780100c649190107010b1000403910000400d0401d503c45c80c2807481c1d60400d80150f004a9400014085000310410000c001454807403a61400a801c6a032200d4917179200d40d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 432331744 1250 432330494 432330529
    0x50918072007090b100c060b030c04060605040e0609010f06050a0e0a060215060405070905040f0f0612151a010e1212040509010e100612060905240f 65
    0x100081100319100c1c00d80d0120440c1c14185100380458401407080d190301440c4141d0062034604240d07030055050850070401c41c0c800c0c40d100e4000c0343c14291140c1e0007070000d240415900d40510fa170440002e03039031841413002910960307951316115810094100c1284101620140c42071003a0320040120f40f5072410305009030303507841c80c00342e4a03000307801020f881e10104403c01590010381800b000c03858560004200800000c08101845142c60718000d00c821100e00b40c0d030705000194040001d118034182074104c11400b0021000020715011070007000000c90b000750300040b5040c040e203d0090240031042c6100130300b000b080c00d0200402d10000d25081d40d040400c01580d418012402c8052102e60b890502da440c5951645041c0c1d01c40c212200c24400300d50b0b1260003960700c143e100c0000440c540c800104614403603443d05482141660401d1019a9811000c258211179036031591404210020140103860095a544c1808501c5c1b181204250140c0401d1481d0385001d0525186043c0f983d5844032039070344004e03004 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 432332994 1250 432331744 432331789
    0x408070303050d06050a0e190b0f040b01170403030606020d14030f070e0a03081908011203080c0f13171f27140127020907050408010e0c040b010509 65
    0x100c03c0386006098a030b40482e42c0181c40d135200140c0202140c420038071602c074100c2410f00c24900315070500d0445401c001c201d44c014202007a500801c0c1041c2e80902401c550504000b5100303584400c11641c0214210f0b03007140001d031114001c006c85601040300030040c010f141420760210200400b20323155070000601a920110071280810b49207406290450004070010b40000c06860b10790500e01d080c0c0d40041e6140034a00c000c0c10175154414802c0002d507040c0c1e004091070000c0040c00d601d08031030b400000b070072090503039004001803203201140100620038885a0040b4400191402c27451800c0050413000308021600311500e6445607910f500c01c681c100104103200040c0344640c143c40701a0307882800700302000c1d00e410a030702403040c41181010009203500c0c4e000280101420360066601e000d09075440046100c540c1024400141341c4401c103280e10a15070310f0400c0c280740e070b50700c042c40c251001044c0d900d00170317000303043c1100d49418140110740035400d0070b00b441403900c1d540c400815040418072441800346035a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 432334244 1250 432332994 432333007
    0x3121308071e08160c05010c0803060d081207020c150f0a110c040c050d05060406050108011206180819110705190306060e010e01080a0308131b120b0606040807030305 73
    0x15002036244030b00307821040d49038503100702281015400c07181907004c0da1120340c4070760000b0702c0b0b42c821213201a007075510060700380c11034a428084c0908806a078904030f49012040c026112440140c0300d410b44111075580c01441102103c1050041081c01c5092201d20581c00300203110852214030225420f690040c5441e401d40d41010100c2400d05002d0800c2d02c0c0d11600b0803501c076008540c002c01905041da030340e210821035611142c00b08000c4a400e440b86034082618940100a4240d808036130742e00250242401203043c5180e89200b1b401102400011141700e500415900c6070400900100010a050703424004166080300310b1032079486145210300b92041d01e0240e100c4041d00308031050f0500031a4426001d101e100d8540c0410b140350701c0700b4002c94022000d00d000000748500d002a050707840c540c01d510b840855484401112000300d00c800000d403920b030300c0141000310400e440306481d402040c46c801701c007a104206151940000300007400040c80340400340010301c0320001c0498180e00f180e51505040d5035894 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 432335494 1250 432334244 432334283
    0x3040c0608090f01020f0d060b0903070605210708040b0a290604080d0207080d05030c0403030309210e100207031e15150603050705120a0b010c050604050312130807 72
    0x5a60410502d031135400407520520100303241d8041c10300264401c9051044035250740d00900070303004d00c104155140d40040010401d150185000b062500c560b65031140c006141c50400340800c0c001070f40c3c0c40c0000f681042c1040188000000441c1c0c005181ca1424443c1d100340f800015000704030204594500d2040c0e103507074a4243e0344d03003044800401003941540c614081054010b51502114886c4980e10300030200c283c3c110310b00c1330003101c2c860740d035074801c882c181800d64030704400401516408035a05205041c20304540808400c2e03000d540c901c16900c04070038500e401c05010400030904a40d1081d94030058080c000035030780703000d0706004000001d40c0b00aa001c841c01c1c980c10141c944070031400b0141c60011110007003a00d00401c48140caa00707880602098035502002c0786c01d44a80ca11803200051400c011030f690403850b41060100b203405241c200032541c102d0300c6080c20814140d03800c50fa0b990001481c00c2c1c14040340c0141d15808001c40c0b4520381c1400c1e003912007901c2c5102d1400000c0c042109007200c181c410 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 432336744 1250 432335494 432335503
    0x11030c1c05190c0b132022060311060304030207140a0e090615030a150c021509061006090e1f051003090c0608060303030403080406090b011502010605100903020609060906070819030203040c060809 86
    0x10542d01c1020303160b01c7c0d142c0507404002c00030b600054070005105c00c503c41c05810100c0c1101e02481e41a40240312141c600306440c03c0c0c10708100596076100b0019400000e11220b14812035000754284009400c15043c0003103191118810402a64041e800010082d00460103101032040c00340b1802c6130200c0c1000e0302c101c00328104600340b81400e0320104414144561180005400352248108500195449880c2c1d1800d0b200d12229204800c411545c150000700c072048003003003003810340030441040040030384c442c0c0000781550341d034200401c006591020110180400204003000605041c00c0c00402402c03e4030109840348002032014041c0320140340461708000165000b5508907400c144c110141d941c60f800200754035604011020300540c00c02201040c0c030700c0c0c0020301680c18007240c2c6400084910759801e02126030460301015500040038404c2a1a5883d03074002881410712440391107039149030440c0c0d60100040074011030b0b010940305208100001e4029802441075840304e0400300310743d0f51014685440d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 432337994 1250 432336744 432336769
    0xa230d05060a0b0316080f0f070f020a0c06020a02040b1507081e0d0c03231303030b1323010b070b250f11030c1c05190c0b1320 56
    0x183c0000100700b184114220b14035104413080b0766100b030b280d03840300c40400d42019010f4580345404000c2101007044580100c1c0c2d01501c3c0700503801036482d240c0407a203c4841b06100b603400301000d45c00456036002185010300c0740080d100320840d40071551041c0d1a00e240e0282c014500c000300f1710303a030000322041c0701c020440684031040781e401c144a5072215007070714400180004030001c002103420b00360b84c40c1034a101282c00e504492a90246050325a45403583c040c1052200c200c1135050540d6410904000e0b1a036001c0050a01a0604049880301c802001b26150700d8408405d0304c030010000d13005100304030410049480d030329040a1441c07002d4884500c0c2221f0548206000a0309449a001c1c2e00c09458100c402900c1c2c000345030722625900c2e0707648812240c81e1300c205002c813061034211110000404c0c1d5242490010b403215450018102500c550b00c240740b505001170788c0301c041011500c0c51420040d84840c040c4e03001c800352218184d503041c1d59079101c021222540d0309092582c216110f82600d6107603500d550dc0d8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 432339244 1250 432337994 432338009
    0x1d0a090807120c02090a050402150a09050901030c032907050a11010c030e12040501140304030201200d0b0d0816110d1a070e0d03141209030a230d05060a 67
    0x920b1805820050561444240e040303005069440014881c400a8031030140f0551f00a00105c44242d03200c4402038855005940d0102404550341c2c0c0030850392070340b2500314080d511031881c55003210b044d81400c0c019140300f2241c0000d0003881c0c04c5000c0c45070b4034143c1140e4101519061080c1c0368100e40c1700c01d807a1412815080c2c10203601e0306187c001090b43c990070060350042414140d40102103104040180c81c803550150078007041c00c841d22511100708840c02168032030b00030f100019001031008460800225282030344107200002045248420311540700311120020b0480303210328240b11703d56a10501d4055040e40c0e003640b8400c164841c00b0300c4405030101401540007000313144003414600d04100c800180c42000c03c2200016000260214040c29500d84074200007014070101e00d01e165021114074103400d1200c01100380911030894810b030491174142c0a0000440a503880791607a0750000c00201504407030780317800030b2101c01c2c0c00f00001150301205c0c0a000840c401190035079412012400e0038203183d01c44c03103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 432340494 1250 432339244 432339263
    0x608040314161101020304060509090402120f030304031e1e0e1002100506060403031b080408011a01030c0c150c0e060c0c1302030906070302072a0f1d0a090807 70
    0x1c2400c0b20b1010b070054510710502203140501d14441c01241d4074056809401c010610402180210703181140ca5154020310041c011101e0856103242d860130070340c0580d1500002e0380040103000030150450119031028090300c0c1820215910180028540d500300030150240f400310310450540d482c0704200d029070170680070f000740050354091070f0001c0d41c90000001c01c0b0505850103000c03414614180045600704c1c0c1d05a914044407141000c0e0b9042642e0f08070001312503c003410440010005800c2c040c03500c0301d20016180c110420885000034094413906010a020001c80d000880300044d07000176800c005c0301c442803002554049100c0180c500d16041f40314150b03c10300100d0400c65601000800b0202083c5c2030714a03004030084402c0381405c1e0301081d03a40b44c4940d00f000e000204458400c1d405030003060b01030782e00c41c15050019501071b141802e54881440208500144c14065201900c1e8810010b1030b0b880d004034400d000c1c503400204030500c003030545040c1d1034580c0620000c1c01421004d8404030754200031000c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 432341744 1250 432340494 432340507
    0x5091201090f0b06120705102a1b060305091b0103060b0f13060c110d02010e04022101120b06190b0f030a05280b010302040b0a090321090608040314 65
    0x100302c0c40c3c3e8112049881107200c812200c403034500203d03007842190005000d00301d61405e130340010b4844c4245400310140341410300300c440100390040070005101d94080c1c3d80d41c400d085402d02c1a6810090250000303428981008144180c0a10005000d02600503503150390101071501030040b406820141e02003180070801080e8550b503941804001c0c00c8007080030030040284c3e40d0b00d000565612425074405030004003491082c1340350b4100801c500d403c5c1481450202c4400003400005000c0360000d48080c40403004178030002148240401d801d90252103003490348a24120107a403102420f020003130a032801051070b142c03201501014440340e14040c04005444903100c5200400c0c40400e81c1049412098481c00e040c0030800380076400c0c142e00b0908104044031615000c00740103081c050624060564101a070030031001410000002c0548694081a0303180c0381400d01e1800d041d052400c20182e0040c541d00980c035400c1d074941d040040ca8080703600900304441c0c2c80d5182c0c2400d03220456540303030f08c3c0003140f00001e42c0d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 432342994 1250 432341744 432341753
    0x303190e0a060f0b15041a04050d030507140325020402040b07080a020111070b01060f0e1005090112050c1204031103070c0602151b0705070305010923010203060105091201090f 77
    0x6580120340c020f8040002003010b000700030a50665240310900e00c102003005000d442c90052803803450b40d0000c0801840c01c0e40c4d481c08281d41d952000c2c01900080c1010900000304990f81e41d595112030100720045080c5400340700100340202c4000400228202002099011925140c040d1001800d81c1a0303103e032180c80b031f400e240c2c90342d520901e15407006500c1c4c00b284440c034221400039121440d4100200103101d80c00c1c014140d8105954091681c14081103400c0000d455885c0c0c82c04540c2006127a030354644460081d0300151461042c901502c2d5414241000c2045010b44241030361481030743c0c03c035910f10075251403c0603104101003904503034250100044a81c1408045001e440841c0c01076405c4450201401414080c00c0c00190b400d100c0d00c2c076a90013040d040a5405010304415802030041c0e0f0445540d99803604c2c216190031004490f1824107001480c1c42102c02ca44540f24001044001d518618104000030701030b01c1040411441200d03401445162500254400388a0990040d400740e01080701d401e2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 432344244 1250 432342994 432343001
    0x11030102071b081f020304050c190f05010306050f0f01050421030e0105030702100b0307050a0e07030b06041503090303140a05090c0a030b13050f1905070b03090303190e0a06 76
    0x30b0362451002400030014007007400241030442c801802c0a1400003c80c501e115802075030000d0400d032210711800c1403000d06a03a60b4012a41c4520200e28540d10680c584003140c5584011948150306140c9804410007031911107540c0581d0000085078000d54010000e40107880b00c1c092500724550b640360404203010514040e1031282842c03402a01c406202c0004140112414441221814010b0704802c005101400481d00003c014600060599100c99210008220140125441280403075188400d00c1240360b0944541d0401401c01d5449924103814070780c500740a550702c05c0d00001010354400300102454400e40c000708030081c500b000c244a9050060117040546020344400328140190341801482d890032800c5101241d51021400c100c0baa01d030403c86808170740b602400e442c18000e0048402001009122003903074145a45521a80b08a45040c051b18009281d0410030700d490080003804030f5100004103580e0701c00107a000c01d80b200b001100807100944030083d0520704521694143e8410030440740c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 432345494 1250 432344244 432344273
    0x2030d092a1e1202120102190c0219050d0308060d150e0606090115110309031e060a021c02031b1318050402090103030c030201140f0f0f221103010207 66
    0x1a03440040751550403400035114098420640c0000c03520f0200801800e1255184e484c007881070000508041c40001c031241c0c0d140e03840314510000759031251140300310b04e0006619802d0510311401c410b50141080301040b90f28404060141c140300030400080c8540e6a270005071015141c0c0301d003921400400d11071a1078090009600042043d024072030000d025402e000c21030341e04a071700480b01084491080c820545180030034800c103100310f00003040300004685007000038140340070400341c5540b0341880a45e0302c80c2c10403001a0100281da0b00400c1441d5608070501503101020f00c0c05e58005070b50ba01c4000310300c03010502d080019020780c880411010708414031045120700325140380b4981c89042c1d803551340140c22150202e4000350700c80340013001480400d00c81e204800ca454460700000a0b0000c8210840300e6901088a841d01651644810044c05680360898a81c004500007041282414109aa001c01c100001100f42e4007906454000c014418004098400d150740078000315560106410106001250103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 432346744 1250 432345494 432345509
    0x9060910030c030c180b1c0305090607121e0207060f0c061406010210060b0d0518030304061d0d02070308030a09060609020a1b080a0804060207050114100504090302030d092a 76
    0x603402c0c908296041d01a904070034030004d0000046d44800407c40b07140c03200c1040242c0070041c2c1400504050385803017006006060281c0901a0000149440140703d00102440f552502c1d40700500340c8142c540010b030010070388040c0e007010b01b203001c15840c08817800415424007030041400c0401c002e9000807290701441c020142a400d603001c0d103d00200308416284c1500c1071201c0340368200700c08110400b181d440b0740c0d001100541d00c0d100f500c440809141c615041910155242661101c400209864030020280c4c1c0000340d03c0544608071550130003075150005840082d000c070100000040d580801540814401d981c0309000f0045c050715900150300940185665001050f8030b0b689064822031420790090301d80794804003007461300c01050011251000090011149143c09118003400181e080c01050680450011000c0c1c00d407a10b000034000713000441c0d0042d07026030314044610002c242e01004075000412840408101ca558a1429034a010a185641d484407420f06c4084c0300d586440d28000002c07a1440c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 432347994 1250 432346744 432346769
    0xd1a0f040b060a0602062a0a05030a0605091504270506090d030504050d210f0504020a0b0c03040b0705211b01050f0a0905120a09050a0e0609060910030c030c 69
    0x81d40203001c3e002c0c08600070440943e0017140000c41d28501d1410380a080554488081e5400d02482e5424101c1d82010340e1000100b0000b104005120500e0f01c01c100040c00212900303405410255184c0010740fa0081d496030140d070700c7c0e10084c640c142464900362400b425030441c1d4200114030742401610f800099410300c045002c0d400100940c54400e0003410302036074119020b004d280309400b07000d40307a42c81703000400c851402d51858400380005580c480e0201000c6031100104131407401c0d20402038052216001000ca0180500100c84407407000410384d803d803580d000495540c0c1d449400c001d0f181045040404105a070704100902c608048100605128000303400b0380c542606a003c0c2450907150f084034405034030452080002c4003503046800200a09000d601602c1e181c1003005c1c14540304d603210f070900c04007081c01c000b420049070401041280c0140700c40c1400c408541003000000b10b0f81c00010781000d10405c2000c02040440c0c0241d43c001d0025030340051441c42159a81c640303885030481a21030f084c1e28150 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 432349244 1250 432347994 432348001
    0x1a0904060e0c12041a0403050d0b040e190c05090108010605120a022b06060602010608250303030905030c010204030605150f0f04020307020312040809040c020d08060d1a0f040b 77
    0x1000c950450007604400141810042560043e03041028000c109a601c11614044000729102c40c010b202d000b01e00955503030b0381e1f400803480b2000c1903903689002540203600e03206021b10013050101d501140e0190405400b16a12158200304540343d00a40145a000e544c1400028001d04158821030844030140ca032030403500510500641c891500d030f10302941200480408103602d0070324503406444080f000050417000a42520b4040c00c0310103a40004000d0f039500c0106000c0742c082000b0344603d400310702c003081444800c90200c8152061141c0b100805054981240c001003150505c00e89000ba40180000c5454954900b0080c3c045c0c08103440320340030041908101d9085040c000d02d01d20f030a8402406004c3c0700d4400409010095200618000c114041402136100105884000301d020714010b001140d1a48500001c100448290808441c01d56205241d170990060f0403150302da510450485d094100b141c51418200041c041c18943d0603034504115080144410302402858010b81c020200c0800c16034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 432350494 1250 432349244 432349259
    0xe010203092406101101090f140706051204061b08040c0504022104020f10091a0405030703121202030a090c150e1e060f040314070b0a0e0103061a090406 67
    0x203942d02c4029110070700380d0300154442c2030140b50b4405406403807400d0700c4d9011018020f5821121980c0b82204c09040d940c4001041c441440d0340c2c0c441c0500c40c0c0700580809032401101038801c0c840c080700e808507410313840000380610000758041d052040684070800000740200000901741c080071281150b130104460404103103418144255800d5040744035080c01003110806030355110030310052040364013106480351040035846100c040300500070a615000c00c4a801c182c121020212001000c03001c46009010401070366900050440860b60414035203048403110340d004480300d240c094840203040f0b000009000c4411071035030100d06d90f80e0044200041507038a44907800028444844a6000614010007043c102d151107821a00b10106042890200012040c04217191346c00800600120150100c1c00b00306000d80c01021000014640d006000e20b5818081e1603400c0780640600402001381007104100c203640254460005044189c40c0024440114905d00c1404e038000c94034a40070750f08040b40040d070b85 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 432351744 1250 432350494 432350533
    0x90f01060b041a070b061c0204060815060303070c0b07080c010203010b0c0114061005340b0a0903050304061d0105190b0607210507140106030b01080f0a110a08010e01020309 76
    0x5a80c170140044c2c0c15260703482046140011035803100000b151b004034600c01680e03140f00301801031075420f000d48506400e80d1001121400300400c486c3c00383d0410400000003c00000700281074034403100300a030b00c0c0d0351a81011f42c6a03015401d419046503100000109108a4080c050005c0b1485000284090903c4019a9041080c266140d80d04000a0181901d445003d1409011080700c540c0301404140c40386003003440c40c400754503154450860207050407424448490307850780d4042c0c61078070705000030a840d95000f0030b03a100c000c0010f030029542d04000c3c2c401802d84005a490340174000000e1080341000c450359946c1d40f904200540003945001c04544690900b1400e641403940c0040424564480b0341e403290308100040a114010420104104800291812012941c90184e44000124103086160085102106802c11055a40a84101600030400013041e0b00420703881190441003814110224042c01c60a030805080d550a200d4020b010280560245200d640103100300c5221207070385201c48805 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 432352994 1250 432351744 432351757
    0x3050a02060325360e071202040905150a080703110f090906061002010b0d0f020d12031a0a030206071202011503061a0103060b0a0c1e05010f050c030618090f01060b041a 74
    0xb000b0392100101722894a0029284d4400e8803402e007101c00c410b00680d04422070b4001c0d041021590358400501c2005141070340d6802d01d01d0025140302c01e4003410504100c0e541e5515200003000c93380303808941c184646030103540c0305980d203000d0892205d5042c240c0744c2c1911000d08652607400b8450a2007080311320f61050044420401e000390181d00c166049450300c0c0c2120907064400e0f83c21058078410100041c0a044607400c07020715541d000618442c52102180310340f1a000c00551040d11807840900c05a80d5641c03c88010903800045410310421000c4280c1c050499546100500b0a84000010911105801480201d14030032600c1d17111160b050300540440c4d080c0d00076010602814410354081600403803002d0070300340c050304180c5a0f075440c1c507800450b220b02000d13080780e683c0d440306030239281403c0c14007a003074000500c038460500710b10707040740403c0170900b4003500d08200b8081c080100d5401c401c01d00c030a100440c50b1000030b108280e241c0103440102e0380684201b50303c40f000715202081019014094581 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 432354244 1250 432352994 432353087
    0x4091e05010b1e090405011d16080c06040608060d020901080c04060f0b030f0405030903060709060f08070509040906112214060a21060e0601021603050a02060325 71
    0x141d0140f00d03003403060204d40200100d503990358030982c400407a00032104241b49503005d800100344140d1200e10000c0d0071002503000641e558400540c0a94a0341c03a1019101070b01c0c3d2910307103451180d440500090040030a40e40194002e01c41c00e00201d80b444021424011103030060364140700159036044101048803080c80781c201030b84028400700c0c0c945c2203070094158001e40506c040b20f040c02d1000e000241000c005a442c20b0105210400c20040c00341c221a0800c03048146003082515480c01c027102400754803a52080c00d202c0e560f0307000028100b04966222040d00b00070000c1098803140003006e41840341000d480c02508100101c64001103504203400e2440107504040c000d0340c14100001020740321100c2881d06598081845032104882c1031081c49050300a007074508030b1244a00304040068180f8101c2e10b5500d80f0007503c19401d201241d800240034809540c15203034144d803507944140384c2c081e8032100d01c200404105413602035180540d20440740b4034029021450405d4416840ca0903858100440503c0380 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 432355494 1250 432354244 432354289
    0x10915030b07050a0c0c260303070c0305160602030a09140604150b01090e0a0507030612030e060d140f09060c0c0a0318050604032406060206130204091e05010b 70
    0x12107080c030a00180c1130b00d1206003021140308060341d60310854044150414000540082500c0d001c880c0811149071000c0044409180345080c1160000c10407200d510015003440800543e540c410400d20104000558108504545030b04014441d9000781005003015600d0f10250b91004030710003400300754240141c0c0e0100c03c2d03413052032400405402400d00c02112a0612a40d4400002c60740e06800e8030900c07940218a0010310b0380b40901010301200c0c03994001d15202c0348109042e60000703800200001060008880c060b40740c008589848002e4001c80458902141c1e4007070a00c4011401004018042c100803829150300f6901c07000c05907101d018242c9170704030310360000000c200400d0080c02e1a030a01d003802c1c40703401202911440414010342c00740d40200c1d00ca0100010742d80c16036000301c1a030209955030060602140b8074054000b07581d14805007400369140c0040014a045641d26413100e681540d102d03d5840e40031103210005032850200c07010aa6903942410400042031411500203004000e01c00030301c4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 432356744 1250 432355494 432355501
    0xc33060b03100b0a0927020703020a051606050406030f060b2109150109020310080105090708010b060307020d1206090c0503011e050307091d07030c030c081b1302160302010203010915030b 82
    0xf41c06c0d600756006c0d801d914289014296844206800241001b40c001d400501c40d040345403410138904030b108d98030785132121401c0e0804d01005500100300d40c1290454580821041882c407034403001000700d0390290103d42c2c03000076161955881c6e030f86041e0200300c203449001e4044da20681480e4540102d00010300c400d042c40740051007035407159405907030070100601c5840c81060301c598045084a4003074503145602d81c848007040203104800d0150203140081680d9003421805d0a544c0a0769039990b500c0880203019942c4030b00c41244015500090050210000078000034141c0320f005007003540b00380110002548200b0443d01d1200450910004403640680106a00c0e8540b105490040c002001588070040880880c7c025502c403c010780809180141c0f00580054511301d010085104564040c4002d50844c03008000100c9040c40400a448800e4031401011050103840c00024850f418207039496030840d200c44002c0c154150701643c16100000f0302000005030005400641c0e0000344401045401c1c0c04000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 432357994 1250 432356744 432356759
    0x13090b2509170c1018051c030c02031213030b06060918071b0515010617041112030a030c02060108011e02160b070f030b010c33060b03100b0a09 63
    0x403441c0c502c454000380d41854000f1400903e076071148030741030f03400101c0c25071350007002c82204c03480e060040600321101904881e040c84844810750b603100000d000e211808200e103003551400c1c0400600d2080e18011a5620703020b100d240d102c404080c0c04142c80c90008c0c9400030f4450700306107003125811000100800742c007080802c075021001500a00400422550400c010701c6142d40c042c10350082031190300606140241c100d800103821205a01002c10040c1030609901403248820071250441c0c0c010011900030751084011031042039605404004900c00000e0041d01c82d50300d039002c081045055801c5c0d66099a86410301800e0380c0d000c2d400001c06041c41c0720030125162490b801021080009610005100d4260f02c400d06a1002290003a011613008035a0601480d45407280701c612000c2401c00c0c9041c260030b6110300d4050b50704540c1401801580d001c009004e216000c1d98088680642401442101d0b221200f0441c1c5030000d4501417201811200c010400c0c03402c000554508406580e200092240303000322 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 432359244 1250 432357994 432358019
    0x608060d0f03020705031b031504020a15091a0c0106060e03121b030708030a0f110904050402012001240e0f040c0807060e090f041106070213090b2509 66
    0x1c110154410480000f546440c2404500b0601c0d4030a40308a08450308039003454101003060046851600c0300101300801603a41c1034402080e9000320740b60500044420005690891040e0040b030720080900c100e05141034544e80091080f604104007d004241e90381c00280e5034805001e03001e03a4150030824130046d9020842025048d00c1243c103c440ea103030218402024210b034080350080e0368114001040004c191801d020390f41002c02e640204200076000c0404815450151280d501e1181c2d803500081015680b1460b01d0f15030740400203001c0802030f5200581e542c000c0044140b20b040c1c0c06448070000840100e11003035a811900301070080982a59410281240713070000500031240c0c040f40c100c3c04642140c040050701d000c2c10060310388000c00c55210040201241000308450107505943d010003002800e50026990001d0301694600c1d01e40711f00340300141140c0d020030700b20700074585010081d42c00d00c41090180c6004455040b10040c080203610030030a01748128508640114503032000070000b85d5072918 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 432360494 1250 432359244 432359273
    0x2100302090301061a0403030f0203070201020a141509010614090f01061b0f0507050418050a03200f2404031407080d0f0b040c090806011703040b0d02130608060d 71
    0x20000a40c2d03d817030b15040c00d1250503200c0c145032a018049003d000301500a41d0018004519000550804041e81e00003035481000007801090000c811450545451041007507125100e40d5520300440c5140050120b07000300481c2c0300b140205e42c2e05001096a42c20440c0c4014052404ad0f801031b406a070900d1001d030783c94003040c51b821704484101c106101c00700d4042c921b4528814400d03400707094440d2500e400c00c001c1d031314034007031030703084580c00080b0203001850010350860350300c1e41410480c0119030031102c0a481c85200c80300704074141c0500d0303000b80303c0d69501066150122901e8110003a40c413401c548640d40300b05080303c00034040399524007114810365001c8060100355120380005032920200c107480c2c1c410713110640165074055807a0750140c4013524141c046d000b00c581c8103240401c15035140160b0740d6600c3c0c3c0f043c07145100101e51107a81e0002c140081c001c0390040d01c1c0480300c1c140c1d0380f01c11110303c0d80254403002d112840700c04890b00c0490074a00ca00d100302d018042c0180318a90440680d01c0d03042c00c02c0307941e5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 432361744 1250 432360494 432360499
    0x909050c03192f030f0c150f03161e0306031502030105030706030f0207152c0c01050304020f0a030804030c0b030c07150902030706090e0108030309070b0d0b0a090f0e0a0210030209 79
    0x119443c0c1c40c240d8041000d05a0002d04102410318002480c00f440244c2c02d0055031a001c1620900c092034007a1131070000d40b90701903003508041746500051081a9000c1039140c504601c404c018060010312960141c00242c116071103480ba04219100001a05040380800e0050540c10b80205500700b1141c0c1c0310b9048642c100111f024014603100981d07031882e10368164034440c4d0490300c1d1942d1502ca0f11400c404022184c240c1407540d4034140502c410034584d110040b444546044c004040041025521061000b88140c0c1010b00008071040d16410148400c1e002484101c400c034000781d101090b940d0380042900c1c0626944601e0600b04043e55980d080d5050810340c55210441d546c8402c50056581000003100030800d54403071030031550600050015485058100040c20b60041080c003800d024001045421100c0500380a500c8103000b26103d40544041c601450b840100060f020a035200154010f90401c82c1441040040c1c465220303401d80c0701c1b800d501010354072003c01d413141d050250194004190340ca400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 432362994 1250 432361744 432361823
    0x207020d0210140706050106120908090118080f0f06011203080103020d0f0203061510020102042412050a05061206040f080d060f03060207030e1f05070c0909050c0319 73
    0x305149050365400015061782d019440b00010440113801c618004d14190708030100740412205516558028070071044124100030040c660032981c0c8250301c02c140040c2c24103006032501c004002030718a59a208280322401355001d10340002441c0c400b03492142e90160f6040e20350b00100c1e840c50302004000e8180090680e800405028090010b80d820312440388201e0041c1c044800040900090000022501c4901c1d401e5a10401040c06054503004140c04100702c65040704480d8018400c040310f02042044c0305100a6090405000e000d200d690001030bc1048241c0341040724058076500c0300d607522015500500b0f1050041181340c04168124020101004c004801060441e034035509104140d9090f8800e480e03043c2c0c003082100c10958483c0000c10011801c49100c0714464486090038082503207881c5100c02e00c4000204070042008110600c0001d01d1700800c200f0200d405401c1468a036092100010310034003071110341d116101e0034a408900d1040d049020024600c500ca184000400304405030407114807007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 432364244 1250 432362994 432363017
    0x1404030206190e040e0339010501080d053c0705070509060f1309020f0d1401060f060c060207150504031d010305060904030302090a180608100207020d0210 68
    0x40d200001c0500c0c5142c0d901c0c0c0d01030300c2801e65009006220200841d8896800c0c40507020b0428000010b0740c410b00c1c0a120b00f1440d10014190400c8030520301b410307001590782c0c4001c01e05480c96041d8400c50490344500142c1d0180a000c540c00c0720b85d40324044076559061a1101c00855040c044a40200c5119134006499401c0245d041050100e1b08010000c503035a5001c814203110358103000308402e4101d80c090702d030003020410550001d80d621040305071007202c2543d103c10341300542d40d0311401017000303020141c45d184d0b00040a081c5505045038a50b81022190b0030102c002540302c1800382035100710b500760703911902c0d4540160384001c0030390702c544810744d52051820461603004003144101070007680f1907140e40040500b003515580d194100d800540d41410300d400104190741e01c0d0500404d901c541c1c5880d00680d502ca0b454000340c00300900d0b410038803408150013140b901001c00d41e40b0035000e0b1060312088500e401700456841081e0b22450750001d4010303c812083d40700508004050840e08842400d22124200 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 432365494 1250 432364244 432364249
    0x8090a0503031f0902041a0f0405040f0207030e0a26070f0e070f0201060807050d020301021c0e0f0f0a0206030910050a0c0e0906010914040624090b070c030314040302 73
    0x100709950090940d122950020340b0a0f2207050390600500c0004425802c0924109042d0f0300c48034010000d180d45c1c44002054001c001c0350304210f41c050700c07008201304200c0b07142d1741c8044000e42080108030041001e00300d00c5ca810f41781c4800c00b801100c0b0720300174610b03080e083c5100140454554400c0303101d1512941d41c011424517009080d00e00500032041c181c009071303d042040108149044005a000d6903d01071003402880c0c4040740f0507043d02c50036030f85180e8600262010900a00c90b0074218802104110040d8040d440c55406c1202103151070b008407103081000107a50340d00d503850b0301c140c549981d10407401a00141007180141d80d00c01c3c11041a15031480c040c484900a039102116400320060352420103101241c2c108035104445902601c00721303640c0c6400c40c0080c1584186006e0500c83e42c0d02d0b404010f060383c0d07580d0880006400310540200842e800f0165000001540100da08007280c40b00742d020070f0100d070381000da41c807194000c21000811403071512305030f50402501030801c034040390800010001d40c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 432366744 1250 432365494 432365497
    0x2090c0304202220070506010e070504080604050a0c08011a04050c16150f05010e1503070f06080f0106020105091203042d0515090a20183408090a0503 66
    0x10162000045084c240e00002c6600740d40240b400c241c0c400d941842031402050b400182c0c24159241d1f01049003880e22807103400d8a40d801903a0201e8801e00c00c1204000402c84045034201005110310f800a08041d29800010b090f03a9170798108614110000d8000c00b8a031030650413454101b040c0d002c0f580d151241030006144030307695030601500c00c8010100c800082058074803448810000c0030f0410000f55040114100c1d880c1c1000d41000786c0e102e8004003020196400740f10410040507600d80b08841b040d582c220180c0070400c21946151313812100381c00054042d0060041da8450540000607205c15003842654148540028105803a40007200c805800300310002800e182c0198128071902e02401c542c0d18003540703041800340424000030102d50500004050000d254465240e100c2490240b410240d0201c3c50041d0107059800c0d44004280e481c8540c50040c0112b850040d0a014011b41403540c440420a192442c550860070500c003849540d0040c00307104215061f005076170b5000b03645140a4a4179024a503 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 432367994 1250 432366744 432366799
    0x6090d08071e03231305060d0f1a0a05060a0e090a020c010606080a050928080d05070f0219030c11011115090708060f0403030b061b030702090c030420 66
    0xb00d81001550301c103195008130390020022104401514022986403900000c100b01d200701d038001d41d000720340b151400490783c00143c00300d01d26500c20019900d80121484407181940c0c500c6000e8034407008049040d007052001c0307c44c0040c0984409440404520601070202002000f9440b2f550b424041c01d400c490003030249a00030002036440702d109040c205260404c5403801b610750101a4072085c002c0e40b40303980680840c450381c1da48102c01442c034001820940000e10901401002c6146001c082042454101120b1401000d043d0300f01c1e040940315203403c04450440340c00240104404000c0e920000e5206150403001c2d03601803400900c00b100800c0a07520341040842e0310030210b41490700700904208200200c0c4010700c07125005201500380303201042a032840290000d020941ca403411801691940021500224100c8030552005022811945e4880d08000022071050f1201c3c404600c080b111a402d40b4002c0c3d400618060302d02034000007540c2000c401c010310682260382880024002d528031083c4401c1c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 432369244 1250 432367994 432367997
    0x301080304031401050702061b16150c0207060206060f04060503030d06170718240f150c02010f0819180b0718090c1202071b0506090d08071e03 63
    0x4940341185080106403004440c201c501303a140c402000002c6900050281d00711100c2c030300721054183e5503c0f0300020380c8203800d0302c2d03d02c100c4132000420402000c005800403107910010100183c0d020b840c0100d8540c00f061003000d0050703121b400440d12505c1c044500b010f980200400014890340d60300c1c0400d0941d00000e5180b1542c5039154410010010804441c000350000d02014040c55420b0130840854034150742410003405a60300d04182c541240c5510b0000044000e4011800c02c90b517030043c08209000718080d24401000749000d02d00564081e07045201419416142c00c0c200074259131086907075101c004d10310048040d200289481d119410710441c0c1c4007010341c0c042910910301905000000c3d100150941c0304006040c03c10100f000c814198a50554200c41e00108044040420440304007010f80700303c1120b0342c8009101010444c0e0030910207490240f90144680d1141e0f5003082088034000c001d000e54100c0c1500c0c10302070014800c800189a0140318012000c1303001400c001c20b0f02c20500c3d6403070480 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 432370494 1250 432369244 432369247
    0x31706010c170a11010b0612150405010e040c080a0c050111011b05070201020c0f06070f050304080115030b0f06090a0c02030705010c0806091317160f050105100501080903040e071403010803 83
    0x1810f107900805150004410344000d005c0000340002150652003000407a181404600c40458200161403c08801008000f8000d0060356141d0454900e02e8900351003c8418410344000090480c00128176140940e4015003000c4080c0c4ca400b0055403445482c0c0014440b41d541c1e00d844c20600343e0b0702a10803039201d059507140b42c1c40d0001c80c4006480c0015001c0c0d81881840120210401695114202d0706420b6100c0440c045044aa141c507915500039600071041c40d501303082c03441001940d51902d5004807405500c04000c107480b15014924003c20998015030006540300004500c03a0329600300d41000e0110784100c80ca030881c10784983e030840d0000c030342076000100340340240084c5240c82a0420303048140d4006480c00c15029607503000d6003103a041c180b82091000070031145100040540c10101d007071340000b06000300c2c4903141b802900910080b6000d87c4a40f05140001c50154440c1c9030140c032500440005501d41401c0400c4d84613a0750006049504020100c420580503c13140c00286008062150056 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 432371744 1250 432370494 432370507
    0x1206010312021209091305030f070b0f010b0315040506030a05060a06030b01050604080307060507051b0601030512090a090b1903050609191e06150612051003031706010c17 75
    0xe003450b204a45140c0402410b120b403012680d41c5811154001b031108080b10122400783c94201c0c214000d000c440c0b6803001c0042800740034441d56000841c410f001790803c5000326a210703447d01c596800143ca0140030010218807412450a0a510003900460020215403d07411700b079441ca40b500c0e4040b01c0750b44016868810401c104030303441503082d004d08030807901c0a040c0350501c035038199640074005000d00380d2601c90010a183c24020003c407418a84481c0c15401510354104070315545020a100031a500c0c0300e4a040c4403040300030601603d114080041c4503580a514000002018114507501554881407810400e204a4051100d42d002184603c014103880d240a01510342801c100c41d62003444a00804100b1000852022914242c0c11106201074a0700710300e070612030300420250f9000d1040424000303003ca481500400040c1d4907004000e020b1190741d40d4007110200f010251710008011070010b00352661039114030800e43c1d41c4841c0614004800500035103e40e65004500300c03801041e400c0000d1031303 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 432372994 1250 432371744 432371747
    0xa1701080c0d410604050a080f091201020c10051030051b0901060f2729040302030303070518060a0f020f011a0103090c230a09060b0a0e1206010312 65
    0x21003c0d602100009081203103020707103801e0b0f2145102d50700248400000650314100800e59800d88002e40009001100f542a003042c203031b8000c0d40811440f06031445030300d12401c0818814081c083c0300d0102d04041c0b0246901e000110098280c0d03000c00417400d50f805c42c4c00200d100742c21403058618107024000815200413810403e030340381c07048100640d018250840040c0015a00080c6000172640c013883c0c6080c21906100b40320481c0f0700160b049056585102e40c000800300741d44600f040300404842c19415400302e4900b2247c1142c42648802500b5030014000184014003c0018240d600ea070341c0e0111030742a03020800110340781e100d46400004a000c0a850304c0082e54100310034042650888020030030320b500c0350f4a00e1110455092160b0405407103200c420204500822603100805000107e07221410900c1c035013600011544c8891401a2014400081c0e40002c4d802050704503800b8503802d51034480d4060003107402c104e8000210344c2040c80030f00903e00300001086114025801003030300c82e04600c02c0150 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 432374100 1106 432372994 432373103
    0xd0f050d0f0e030309030d03050424060e0604020a020703061805010203090705090601020a08040302010807030b0d14010f020c070506030402040e120a1701080c0d 71
    0x1840e001081e040100d0740c00c8030900d40c4810320ba401100c4107065882c0110001503034164410a20100f20901039448140c01c6401100c01090b11105160084030031008001c1c00903900d0b6a0303503010020314410f0440141c0120044030190300c0d1004900c4000e55450040c04040c18040c0d40344004600c1104503041c907803049500c030700259103c0c54610b6400e501e805039442214001c48030540020082d600c042807450740c141e80140c4190420342980c00450b616a0000c040d0f03400c3c9660f480c4080116a00c02100307400c21481542008071110f881c0383c0107401d4551090700740e01c1c3d2500612011100d0080070a90a003600c000790340d0252030703a80d0750000401415007004070102c5406041502c524040ea110014150b480f07a9480e4a03e41070304000281000002c24458000b00350445421103c0390701d0042c206112080c09100c90000501e4400c03450315041900b002c00c8025a038500805420600c001817 = true := by decide +kernel

theorem cover : BRFrame.Cov 432194244 432374100 := by
  have h0 := BRFrame.cov_init 432194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 432194244 ≤ n) (h2 : n < 432374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
